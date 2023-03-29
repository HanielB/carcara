#!/usr/bin/env python3
#
# cmpr: A tool for extracting and analyzing SAT/SMT/++ solver runs.
#
# Copyright (C) 2020  Mathias Preiner
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter, ArgumentTypeError
from functools import reduce
from itertools import zip_longest, product
import mmap
import os
import re
import sys
import time
import statistics

import pandas as pd
import numpy as np


class CmprException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "Error: {0:s}".format(self.msg)


g_args = None  # Options

CACHE_FILE_NAME = 'cmpr.cache'

RESULT_NONE = 0
RESULT_SAT = 1
RESULT_UNSAT = 2
RESULT_UNKNOWN = 3
RESULT_SYNTH = 4

STATUS_ERR = 'ee'
STATUS_OK = 'ok'
STATUS_MEM = 'mo'
STATUS_TIME = 'to'
STATUS_DIS = 'di'

# Data keys extracted from log files
KEY_DIR = 'directory'
KEY_CONFIG = 'config'
KEY_RESULT = 'result'
KEY_BENCHMARK = 'benchmark'
KEY_STATUS = 'status'
KEY_EXIT_CODE = 'exit_code'
KEY_EXIT_SIGNAL = 'exit_signal'
KEY_TIME_REAL = 'time_real'
KEY_TIME_CPU = 'time_cpu'
KEY_MEMORY = 'memory'
KEY_OUTPUT_LOG = 'output_log'

# Computed keys
KEY_GROUP = 'group'
KEY_SOLVED = 'solved'
KEY_SAT = 'sat'
KEY_UNSAT = 'unsat'
KEY_UNKNOWN = 'unknown'
KEY_TIMEOUT = 'timeout'
KEY_MEMOUT = 'memout'
KEY_ERROR = 'error'
KEY_DISAGR = 'disagr'
KEY_DIFF = 'diff'
KEY_UNIQ = 'uniq'
KEY_NSOLVED = 'nsolved'
KEY_TIME_SLOWDOWN = 'slowdown'
KEY_INCREMENTAL = 'incremental'
KEY_BEST = 'best'
KEY_UNSOLVED = 'unsolved'
KEY_PAR = 'par'

# Aggregate functions for keys
KEY_AGGS = {
    KEY_RESULT: 'count',
    KEY_SOLVED: sum,
    KEY_SAT: sum,
    KEY_UNSAT: sum,
    KEY_UNKNOWN: sum,
    KEY_UNSOLVED: sum,
    KEY_TIME_CPU: sum,
    KEY_TIME_REAL: sum,
    KEY_MEMORY: sum,
    KEY_TIMEOUT: sum,
    KEY_MEMOUT: sum,
    KEY_ERROR: sum,
    KEY_DISAGR: sum,
    KEY_UNIQ: sum,
    KEY_TIME_SLOWDOWN: np.mean,
    KEY_INCREMENTAL: any,
    KEY_BEST: sum,
    KEY_PAR: sum,
}

# Keys available for the user to specify for printing
AVAILABLE_KEYS = [
    KEY_RESULT,
    KEY_STATUS,
    KEY_EXIT_CODE,
    KEY_TIME_REAL,
    KEY_TIME_CPU,
    KEY_MEMORY,
    KEY_SOLVED,
    KEY_SAT,
    KEY_UNSAT,
    KEY_UNKNOWN,
    KEY_UNSOLVED,
    KEY_TIMEOUT,
    KEY_MEMOUT,
    KEY_ERROR,
    KEY_DISAGR,
    KEY_UNIQ,
    KEY_TIME_SLOWDOWN,
    KEY_PAR,
]

###############################################################################
### Parsers
###############################################################################


# Parser base class
class ValueParser:
    def key(self):
        pass

    def match(self, line):
        pass

    def extract(self, line):
        pass


class BenchmarkParser(ValueParser):
    def key(self):
        return KEY_BENCHMARK

    def match(self, line):
        return line.startswith(b'c args:')

    def extract(self, line):
        return line.split(b':', maxsplit=1)[1].strip().decode('utf-8')


class TerminationReasonParser(ValueParser):
    def key(self):
        return KEY_STATUS

    def match(self, line):
        return line.startswith(b'terminationreason=')

    def extract(self, line):
        # Possible values for terminationreason:
        #   https://github.com/sosy-lab/benchexec/blob/master/doc/run-results.md
        reason = str(line).split('=')[1].strip()
        if 'time' in reason:
            return STATUS_TIME
        elif 'memory' in reason:
            return STATUS_MEM
        return STATUS_ERR


class ExitCodeParser(ValueParser):
    def key(self):
        return KEY_EXIT_CODE

    def match(self, line):
        return line.startswith(b'returnvalue=')

    def extract(self, line):
        return int(line.split(b'=')[1])


class ExitSignalParser(ValueParser):
    def key(self):
        return KEY_EXIT_SIGNAL

    def match(self, line):
        return line.startswith(b'exitsignal=')

    def extract(self, line):
        return int(line.split(b'=')[1])


class TimeRealParser(ValueParser):
    def key(self):
        return KEY_TIME_REAL

    def match(self, line):
        return line.startswith(b'walltime=')

    def extract(self, line):
        return float(line.split(b'=')[1].rstrip(b's'))


class TimeCpuParser(TimeRealParser):
    def key(self):
        return KEY_TIME_CPU

    def match(self, line):
        return line.startswith(b'cputime=')


class MemoryParser(ValueParser):
    def key(self):
        return KEY_MEMORY

    def match(self, line):
        return line.startswith(b'memory=')

    def extract(self, line):
        # Convert to MB
        return float(line.split(b'=')[1].rstrip(b'B')) / (1000 * 1000)


class ResultParser(ValueParser):
    def __init__(self):
        self.results = dict()

    def key(self):
        return KEY_RESULT

    def match(self, line):
        return line in self.results

    def extract(self, line):
        return self.results[line]


class SATResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b's SATISFIABLE': RESULT_SAT,
            b's UNSATISFIABLE': RESULT_UNSAT,
        })


class SMTResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b'sat': RESULT_SAT,
            b'unsat': RESULT_UNSAT,
            b'unknown': RESULT_UNKNOWN
        })


class AIGERResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b'0': RESULT_UNSAT,
            b'1': RESULT_SAT,
            b'2': RESULT_UNKNOWN
        })


class TPTPResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b'GaveUp': RESULT_UNKNOWN,
            b'Theorem': RESULT_UNSAT,
            b'ContradictoryAxioms': RESULT_UNSAT,
            b'Unsatisfiable': RESULT_UNSAT,
            b'CounterSatisfiable': RESULT_SAT,
            b'Satisfiable': RESULT_SAT
        })

    def match(self, line):
        l = line.split()
        try:
            i = l.index(b'status')
            return l[i + 1] in self.results
        except ValueError:
            return False

    def extract(self, line):
        l = line.split()
        try:
            i = l.index(b'status')
            return self.results[l[i + 1]]
        except ValueError:
            return RESULT_NONE


class SyGuSResultParser(ResultParser):
    def match(self, line):
        return line.startswith(b'(define-fun') \
                or line.startswith(b'Synthesis time')

    def extract(self, line):
        return RESULT_SYNTH


# Registered value parsers

OUTPUT_LOG_PARSERS = []
RUN_OUT_PARSERS = [
    BenchmarkParser(),
    TerminationReasonParser(),
    ExitCodeParser(),
    ExitSignalParser(),
    TimeRealParser(),
    TimeCpuParser(),
    MemoryParser(),
]

def register_output_parser(parser, agg = None):
    global OUTPUT_LOG_PARSERS, AVAILABLE_KEYS
    OUTPUT_LOG_PARSERS.append(parser)
    AVAILABLE_KEYS.append(parser.key())
    if agg:
        KEY_AGGS[parser.key()] = agg

def register_run_parser(parser, agg = None):
    global RUN_OUT_PARSERS, AVAILABLE_KEYS
    RUN_OUT_PARSERS.append(parser)
    AVAILABLE_KEYS.append(parser.key())
    if agg:
        KEY_AGGS[parser.key()] = agg

###############################################################################
### Argument parsing
###############################################################################


def help_available_columns():
    return 'Available columns:\n  {}'.format('\n  '.join(AVAILABLE_KEYS))

def parse_par_tuple(x):
    try:
        n, time_limit = map(int, x.split(','))
        return n * time_limit
    except:
        raise ArgumentTypeError("Arguments for --par must be N,TIME_LIMIT")

def parse_and_check_arguments(args):
    global g_args, RUN_OUT_PARSERS

    ap = ArgumentParser(formatter_class=ArgumentDefaultsHelpFormatter,
                        epilog='availabe values for column: {{ {} }}, '.format(
                            ', '.join(sorted(AVAILABLE_KEYS))))
    ap.add_argument(
        'dirs',
        nargs='*',
        help='run directories to compare, not required with --starexec-csv')
    ap.add_argument('-v',
                    '--verbose',
                    dest='verbose',
                    action='store_true',
                    default=False,
                    help='enable verbose output')
    ap.add_argument('-c',
                    dest='columns',
                    metavar='COLUMN[,COLUMN ...]',
                    help='select columns to print')
    ap.add_argument('--full-path',
                    dest='show_full_path',
                    default=False,
                    action='store_true',
                    help='show full path instead of benchmark name')
    ap.add_argument('--ignore-cache',
                    action='store_true',
                    dest='ignore_cache',
                    help='overwrite cache file')
    ap.add_argument('--ignore-suffix',
                    dest='ignore_suffix',
                    action='store_true',
                    help='ignore benchmark suffix')
    ap.add_argument('--ignore-dis',
                    action='store_true',
                    dest='ignore_disagreement',
                    help='ignore disagreements')
    ap.add_argument(
        '--no-strict',
        dest='no_strict', default=False, action='store_true',
        help='do not count every non-(sat/unsat/unknown/timeout/memout) ' \
             'result as error'
    )
    ap.add_argument('--time-limit',
                    dest='time_limit',
                    metavar='SECONDS[,SECONDS...]',
                    help='use individual time out')
    ap.add_argument('--penalty',
                    metavar='SECONDS',
                    type=int,
                    help='CPU time penalty for memory out/error')
    ap.add_argument('--par',
                    metavar='N,TIME_LIMIT',
                    type=parse_par_tuple,
                    help='PAR-N scoring with a TIME_LIMIT seconds')
    ap.add_argument('--compare-real',
                    action='store_true',
                    default=False,
                    help='compare real time instead of CPU time')

    ap.add_argument('--side-by-side',
                    action='store_true',
                    help='side by side comparison')
    ap.add_argument('--swap',
                    action='store_true',
                    help='swap configs and columns')
    ap.add_argument('--vbs',
                    action='store_true',
                    help='compute virtual best solver')
    ap.add_argument('--slowdown',
                    type=str,
                    default='',
                    nargs='?',
                    help='compute slowdown w.r.t. to given solver (directory)')

    ag = ap.add_argument_group('StarExec CSV files')
    ap.add_argument('--starexec-csv',
                    type=str,
                    metavar='CSV',
                    help='read StarExec CSV file')
    ap.add_argument('--starexec-output-dir',
                    type=str,
                    metavar='DIR',
                    help='StarExec output directory for incremental runs')

    # Grouping of results
    ag = ap.add_argument_group('Grouping results')
    ag.add_argument('-g',
                    dest='grouped',
                    action='store_true',
                    help='group benchmarks by lowest subdirectory')
    ag.add_argument('-G',
                    dest='grouped_top',
                    action='store_true',
                    help='group benchmarks by top-level directory')
    ag.add_argument('-t',
                    dest='totals',
                    action='store_true',
                    help='generate totals')

    desc = """
        Filter based on column values, e.g., -q "time_cpu>=10" lists only
        benchmarks that required at least 10 seconds to solve.
        Availale keys: [{}]
        Supported operators: [{}]
    """.format(', '.join(AVAILABLE_KEYS),
               ', '.join(['>=', '<=', '>', '<', '=']))
    ag = ap.add_argument_group('Filtering based on values', desc)
    ag.add_argument('-q',
                    dest='queries',
                    metavar='QUERY',
                    action='append',
                    help='filter results based on column values')

    # Filer based on benchmarks
    ag = ap.add_argument_group('Filtering benchmarks')
    ag.add_argument('-f',
                    dest='filter',
                    metavar='REGEX',
                    action='append',
                    help='filter benchmarks matching REGEX')
    ag.add_argument('-e',
                    dest='exclude',
                    metavar='REGEX',
                    action='append',
                    help='exclude benchmarks matching REGEX')

    # Filter based on status
    ag = ap.add_argument_group('Filtering based on status')
    ag.add_argument('--show-sat',
                    dest='show_sat',
                    default=False,
                    action='store_true',
                    help='show satisfiable instances')
    ag.add_argument('--show-no-sat',
                    dest='show_no_sat',
                    default=False,
                    action='store_true',
                    help='don\'t show satisfiable instances"')
    ag.add_argument('--show-unsat',
                    dest='show_unsat',
                    default=False,
                    action='store_true',
                    help='show unsatisfiable instances')
    ag.add_argument('--show-no-unsat',
                    dest='show_no_unsat',
                    default=False,
                    action='store_true',
                    help='don\'t show unsatisfiable instances')
    ag.add_argument('--show-unknown',
                    dest='show_unknown',
                    default=False,
                    action='store_true',
                    help='show unknown instances')
    ag.add_argument('--show-no-unknown',
                    dest='show_no_unknown',
                    default=False,
                    action='store_true',
                    help='don\'t show unknown instances')
    ag.add_argument('--show-time',
                    dest='show_time',
                    default=False,
                    action='store_true',
                    help='show timeouts only')
    ag.add_argument('--show-mem',
                    dest='show_mem',
                    action='store_true',
                    default=False,
                    help='show memory outs only')
    ag.add_argument('--show-err',
                    dest='show_err',
                    action='store_true',
                    help='show errors only')
    ag.add_argument('--show-ok',
                    dest='show_ok',
                    action='store_true',
                    help='show non-errors only')
    ag.add_argument('--show-dis',
                    dest='show_dis',
                    action='store_true',
                    help='show disagreements only')
    ag.add_argument('--show-common',
                    dest='show_common',
                    action='store_true',
                    help='show commonly solved instances only')
    ag.add_argument('--show-unsolved',
                    dest='show_unsolved',
                    action='store_true',
                    help='show unsolved instances only')
    ag.add_argument('--show-diff',
                    dest='show_diff',
                    action='store_true',
                    help='show benchmarks with different status only')
    ag.add_argument('--show-unique',
                    dest='show_unique',
                    action='store_true',
                    help='show uniquely solved benchmarks only')
    ag.add_argument('--summarize-errors',
                    action='store_true',
                    help='Print grouped summary of detected errors')

    # Output formats
    ag = ap.add_argument_group('Output formats')
    ag.add_argument('--html',
                    dest='html',
                    action='store_true',
                    help='generte HTML table')
    ag.add_argument('--csv',
                    dest='csv',
                    action='store_true',
                    help='generate CSV')
    ag.add_argument('--latex',
                    dest='latex',
                    action='store_true',
                    help='generate LaTeX table')

    # Alternative compare modes
    ag = ap.add_argument_group('Alternative modes')
    ag.add_argument('--aiger',
                    dest='aiger',
                    action='store_true',
                    help='AIGER mode')
    ag.add_argument('--sat', dest='sat', action='store_true', help='SAT mode')
    ag.add_argument('--synth',
                    dest='synth',
                    action='store_true',
                    help='SyGuS mode')
    ag.add_argument('--tptp',
                    dest='tptp',
                    action='store_true',
                    help='TPTP mode')

    g_args = ap.parse_args(args)

    if g_args.grouped_top or g_args.totals:
        g_args.grouped = True

    if g_args.summarize_errors and g_args.grouped:
        raise CmprException('--summarize-errors and -t, -g, -G are not compatible')

    # Do not use a set here as the order of directories should be preserved
    unique_dirs = []
    for d in g_args.dirs:
        if not os.path.isdir(d):
            raise CmprException("Directory '{}' does not exist.".format(d))
        if d not in unique_dirs:
            unique_dirs.append(d)
    g_args.dirs = unique_dirs

    if g_args.slowdown and g_args.slowdown not in unique_dirs:
        raise CmprException(
                f'Invalid directory {g_args.slowdown} specified for --slowdown')

    if not g_args.dirs and not g_args.starexec_csv:
        raise CmprException('No directories to compare specified.')

    # Setup columns to print
    if g_args.columns:
        g_args.columns = g_args.columns.split(',')
        invalid_columns = set(g_args.columns).difference(set(AVAILABLE_KEYS))
        if invalid_columns:
            invalid_columns = ','.join(invalid_columns)
            raise CmprException("Columns '{}' not available.\n{}".format(
                invalid_columns, help_available_columns()))

    # Setup timeouts for all directories
    if g_args.time_limit:
        timeouts = [float(s) for s in g_args.time_limit.split(',')]
        if len(timeouts) > 1 and len(timeouts) != len(g_args.dirs):
            raise CmprException(
                'Number of timeouts must match number of directories')
        if len(timeouts) == 1:
            timeouts = [timeouts[0] for d in g_args.dirs]
        assert len(timeouts) == len(g_args.dirs)
        # Timeout for each directory
        g_args.time_limit = \
            dict((g_args.dirs[i], timeouts[i]) for i in range(len(timeouts)))

    if g_args.queries:
        queries = []
        for query in g_args.queries:
            relop = None
            for x in ['>=', '<=', '>', '<', '=']:
                if x in query:
                    relop = x
                    break

            if not relop:
                raise CmprException(
                    "Invalid query statement '{}'".format(query))

            t = query.split(relop)
            if len(t) != 2:
                raise CmprException(
                    "Invalid query statement '{}'".format(query))
            key, value = t
            if key not in AVAILABLE_KEYS:
                raise CmprException(
                    "Invalid key '{}' in query statement.\n{}".format(
                        key, help_available_columns()))
            queries.append((key, relop, value))
            g_args.queries = queries

    # Determine result parser
    if g_args.aiger:
        register_output_parser(AIGERResultParser())
    elif g_args.sat:
        register_output_parser(SATResultParser())
    elif g_args.tptp:
        register_output_parser(TPTPResultParser())
    elif g_args.synth:
        register_output_parser(SyGuSResultParser())
    else:
        register_output_parser(SMTResultParser())


###############################################################################
### Data extraction
###############################################################################


def starexec_convert_result(x):
    if x == 'sat':
        return [RESULT_SAT]
    elif x == 'unsat':
        return [RESULT_UNSAT]
    return [RESULT_UNKNOWN]


def read_starexec_inc_output():
    all_results = {}
    for root, _, files in os.walk(g_args.starexec_output_dir):
        for f in files:
            if not f.endswith('.txt'):
                continue
            id = int(f[:-4])

            results = []
            with open(os.path.join(root, f)) as infile:
                for line in infile:
                    result = line.split()[-1]
                    if result == 'sat':
                        results.append(RESULT_SAT)
                    elif result == 'unsat':
                        results.append(RESULT_UNSAT)
                    else:
                        break
            all_results[id] = results
    return all_results


def read_starexec_csv(csv):

    # Check if cache file is present
    cache_file = '{}.{}'.format(csv, CACHE_FILE_NAME)
    if not g_args.ignore_cache and os.path.isfile(cache_file):
        return pd.read_pickle(cache_file, compression='bz2')

    data = pd.read_csv(csv)

    columns = {}
    columns[KEY_BENCHMARK] = data['benchmark'].to_list()
    columns[KEY_CONFIG] = data['solver'].to_list()
    columns[KEY_MEMORY] = [x / 1000 for x in data['memory usage'].to_list()]
    columns[KEY_TIME_CPU] = data['cpu time'].to_list()
    columns[KEY_TIME_REAL] = data['wallclock time'].to_list()

    # Incremental StarExec runs
    if 'correct-answers' in data:
        if not g_args.starexec_output_dir:
            raise CmprException(
                'Incremental StarExec CSVs require the output directory ' \
                'to be specified via option --starexec-output-dir')
        results = read_starexec_inc_output()
        columns[KEY_RESULT] = [results[x] for x in data['pair id'].to_list()]
    else:
        columns[KEY_RESULT] = \
                [starexec_convert_result(x) for x in data['result'].to_list()]

    df = pd.DataFrame(columns)
    df[KEY_STATUS] = None
    df[KEY_EXIT_CODE] = 0
    df[KEY_EXIT_SIGNAL] = np.NaN
    df.to_pickle(cache_file, compression='bz2')

    return df


def extract_data(full_path, filters):

    data = dict((f.key(), None) for f in filters)
    if KEY_RESULT in data:
        data[KEY_RESULT] = []

    if os.stat(full_path).st_size > 0:
        used_filters = set()
        with open(full_path, 'rb') as infile:
            mm = mmap.mmap(infile.fileno(), 0, access=mmap.ACCESS_READ)
            for line in iter(mm.readline, b''):
                line = line.strip()

                if len(used_filters) == len(filters):
                    break

                for f in filters:
                    k = f.key()
                    # Value already extracted for current file
                    if k in used_filters:
                        continue

                    if not f.match(line):
                        continue

                    val = f.extract(line)

                    # Multiple results possible in case of incremental runs
                    if k != KEY_RESULT:
                        used_filters.add(k)

                    if k == KEY_RESULT:
                        data[k].append(val)
                    else:
                        assert data[k] == None
                        data[k] = val

    return data


def load_cache(dir):
    global g_args

    if g_args.ignore_cache:
        return None

    cache_file_path = os.path.join(dir, CACHE_FILE_NAME)
    if not os.path.isfile(cache_file_path):
        return None
    # TODO: catch read errors?
    return pd.read_pickle(cache_file_path, compression='bz2')


def save_cache(dir, df):
    df.to_pickle(os.path.join(dir, CACHE_FILE_NAME), compression='bz2')


def read_data():
    dfs = []

    # Collect all keys from the value parsers
    all_keys = [f.key() for f in OUTPUT_LOG_PARSERS]
    all_keys.extend(f.key() for f in RUN_OUT_PARSERS)
    all_keys.append(KEY_OUTPUT_LOG)

    for d in g_args.dirs:
        # Load cached data
        df = load_cache(d)
        if df is not None:
            dfs.append(df)
            continue

        columns = dict((k, []) for k in all_keys)

        # Extract data from all .log/.err files in all subdirectories.
        # directory structure is as follows:
        # benchmark_set/
        #   family/
        #    ...
        #     benchmark/
        #       output.log
        #       run.out
        #       run.err
        for root, _, files in os.walk(d):

            if 'run.out' not in files:
                continue

            if 'output.log' not in files:
                raise CmprException("output.log missing in '{}'".format(root))

            output_log = os.path.join(root, 'output.log')
            run_log = os.path.join(root, 'run.out')

            data = extract_data(run_log, RUN_OUT_PARSERS)

            # If benchmark couldn't be found use relative path in 'd'
            if not data[KEY_BENCHMARK]:
                data[KEY_BENCHMARK] = root[len(d):]
            if not data[KEY_STATUS]:
                data[KEY_STATUS] = STATUS_OK

            data[KEY_OUTPUT_LOG] = output_log

            for k, v in data.items():
                columns[k].append(v)
            data = extract_data(output_log, OUTPUT_LOG_PARSERS)
            for k, v in data.items():
                columns[k].append(v)

        df = pd.DataFrame(columns)
        df[KEY_CONFIG] = d
        df[KEY_DIR] = d
        dfs.append(df)
        save_cache(d, df)

    return pd.concat(dfs, ignore_index=True)


###############################################################################
### Result processing
###############################################################################


def filter_query(df):

    if not g_args.queries:
        return df

    for (key, relop, value) in g_args.queries:
        # 'key' may needs to be computed in process_data, try again
        # afterwards
        if key not in df:
            continue
        dtype = df.dtypes[key]
        try:
            val = pd.to_numeric(value)
        except ValueError as e:
            val = value

        dfq = df
        try:
            if relop == '>=':
                dfq = dfq.loc[dfq[key] >= val]
            elif relop == '<=':
                dfq = dfq.loc[dfq[key] <= val]
            elif relop == '>':
                dfq = dfq.loc[dfq[key] > val]
            elif relop == '<':
                dfq = dfq.loc[dfq[key] < val]
            else:
                assert relop == '='
                dfq = dfq.loc[dfq[key] == val]

            # Remove a benchmark if every query on the benchmark returns False
            keep_benchmarks = set(dfq[KEY_BENCHMARK].tolist())
            df = df[df[KEY_BENCHMARK].isin(keep_benchmarks)]

        except TypeError as e:
            raise CmprException(
                "Expected type '{}' for key '{}', got '{}'".format(
                    dtype, key, type(val)))

    return df


def prefilter_results(df):

    if g_args.filter:
        # All filters must match
        for pattern in g_args.filter:
            regex = re.compile(pattern, re.I)
            df = df[df[KEY_BENCHMARK].str.contains(regex)]

    if g_args.exclude:
        # Remove all matches
        for pattern in g_args.exclude:
            regex = re.compile(pattern, re.I)
            df = df[~df[KEY_BENCHMARK].str.contains(regex)]

    df = filter_query(df)

    return df


def filter_results(df):
    global g_args

    if g_args.show_unsolved:
        df = df[df[KEY_NSOLVED] == 0]

    # Filter based on result sat, unsat, unknown
    key = None
    if g_args.show_sat:
        key = KEY_SAT
    elif g_args.show_unsat:
        key = KEY_UNSAT
    elif g_args.show_unknown:
        key = KEY_UNKNOWN
    if key:
        df = df[df[key] == 1]

    # Exclude sat/unsat/unknown benchmarks
    no_keys = []
    if g_args.show_no_sat:
        no_keys.append(KEY_SAT)

    if g_args.show_no_unsat:
        no_keys.append(KEY_UNSAT)

    if g_args.show_no_unknown:
        no_keys.append(KEY_UNKNOWN)

    if no_keys:
        for k in no_keys:
            df = df[df[k] == 0]

    # Filter based on status ok, mem, err, time, dis
    status = None
    if g_args.show_err:
        status = STATUS_ERR
    elif g_args.show_mem:
        status = STATUS_MEM
    elif g_args.show_ok:
        status = STATUS_OK
    elif g_args.show_time:
        status = STATUS_TIME
    elif g_args.show_dis:
        status = STATUS_DIS
    if status:
        df = df[df[KEY_STATUS] == status]

    if g_args.show_diff or g_args.show_common:
        # Determine diff in terms of number of solved queries
        diff = df.groupby(KEY_BENCHMARK, as_index=False).agg(
                {KEY_SOLVED: lambda x: len(set(x)) != 1})
        diff.rename(columns={KEY_SOLVED: KEY_DIFF}, inplace=True)
        df = pd.merge(df, diff, how='left', on=[KEY_BENCHMARK])

        if g_args.show_diff:
            df = df[(df[KEY_DIFF] == True)]
        else:
            df = df[(df[KEY_NSOLVED] > 0) & (df[KEY_DIFF] == False)]

    if g_args.show_unique:
        df = df[(df[KEY_UNIQ] > 0)]

    return df


# TODO(filter):
#        if len(g_file_stats.keys()) > 0:
#            if g_args.timeof:
#                d = g_args.timeof
#                filter = lambda data, f: data[KEY_STATUS][d][f] == STATUS_TIME
#                _filter_benchmarks(g_file_stats, filter)


def get_common_path_prefix_len(df):
    benchmarks = set()
    benchmarks.update(df[KEY_BENCHMARK].tolist())

    if not benchmarks:
        return ''

    benchmark = next(iter(benchmarks))

    if len(benchmarks) == 1:
        prefix = os.path.dirname(benchmark)
    else:
        prefix = os.path.commonpath(list(benchmarks))

    prefix_len = len(prefix)
    if benchmark[prefix_len] == '/':
        prefix_len += 1
    return prefix_len


def result_to_string(x):
    str_results = {
        RESULT_NONE: 'none',
        RESULT_SAT: 'sat',
        RESULT_UNSAT: 'unsat',
        RESULT_UNKNOWN: 'unknown',
    }

    if not x:
        return str_results[RESULT_UNKNOWN]

    res = [str_results[r] for r in x]
    if len(res) == 1:
        return res[0]

    if g_args.csv:
        return ';'.join(res)
    return res


def agg_disagr(x):
    results = zip_longest(*x.tolist(), fillvalue=RESULT_UNKNOWN)
    for r in results:
        if RESULT_SAT in r and RESULT_UNSAT in r:
            return 1
    return 0


def agg_uniq(x):
    s = sum(x.tolist())
    if s != 1:
        return 0
    return 1


def agg_diff(x):
    l = x.tolist()
    return l.count(0) != len(l)


def process_data(df):

    prefix_len = get_common_path_prefix_len(df)
    unique_configs = list(df[KEY_CONFIG].unique())

    if not g_args.show_full_path:
        df[KEY_BENCHMARK] = df[KEY_BENCHMARK].str[prefix_len:]

    if g_args.ignore_suffix:
        df[KEY_BENCHMARK] = df[KEY_BENCHMARK].str.rsplit('.', 1).str[0]

    if g_args.compare_real:
        time_key = KEY_TIME_REAL
    else:
        time_key = KEY_TIME_CPU

    # Reset timeout if given via g_args.time_limit
    if g_args.time_limit:
        for c in unique_configs:
            timeout = g_args.time_limit[c]
            df.loc[(df[KEY_DIR] == c) & (df[time_key] > timeout),
                   [time_key, KEY_STATUS, KEY_RESULT]] = \
                           [timeout, STATUS_TIME, [[]]]

    # Determine solved, sat, unsat, and unknown results
    keys = [KEY_SAT, KEY_UNSAT, KEY_UNKNOWN]
    results = [RESULT_SAT, RESULT_UNSAT, RESULT_UNKNOWN]
    for k, r in zip(keys, results):
        df[k] = df[KEY_RESULT].map(lambda x: x.count(r))
    df[KEY_SOLVED] = df[KEY_SAT] + df[KEY_UNSAT]

    # Compute status columns
    keys = [KEY_TIMEOUT, KEY_MEMOUT, KEY_ERROR]
    status = [STATUS_TIME, STATUS_MEM, STATUS_ERR]
    for k, s in zip(keys, status):
        df[k] = 0
        df.loc[df[KEY_STATUS] == s, k] = 1

    # Set status disagreement
    if g_args.ignore_disagreement:
        df[KEY_DISAGR] = 0
    else:
        disagr = df.groupby(KEY_BENCHMARK,
                            as_index=False).agg({KEY_RESULT: agg_disagr})
        disagr.rename(columns={KEY_RESULT: KEY_DISAGR}, inplace=True)
        df = pd.merge(df, disagr, how='left', on=[KEY_BENCHMARK])
        df.loc[df[KEY_DISAGR] == 1, KEY_STATUS] = STATUS_DIS

    # All non-sat/unsat/unknown/timeout/memout/disagreement results are
    # considered as error in strict mode.
    if not g_args.no_strict:
        df.loc[(df[KEY_SAT] == 0)
               & (df[KEY_UNSAT] == 0)
               & (df[KEY_UNKNOWN] == 0)
               & (df[KEY_TIMEOUT] == 0)
               & (df[KEY_MEMOUT] == 0)
               & (df[KEY_DISAGR] == 0),
               [KEY_STATUS, KEY_ERROR]] = [STATUS_ERR, 1]

    # If runexec reports an exit signal and it is not a timeout or memout
    # the binary probably terminated abnormally.
    df.loc[(df[KEY_TIMEOUT] == 0)
           & (df[KEY_MEMOUT] == 0)
           & (df[KEY_DISAGR] == 0)
           & df[KEY_EXIT_SIGNAL].notna(),
            [KEY_STATUS, KEY_ERROR]] = [STATUS_ERR, 1]

    # Set CPU time penalty for memory outs and errors
    if g_args.penalty:
        df.loc[(df[KEY_MEMOUT] == 1)
               | (df[KEY_ERROR] == 1)
               | (df[KEY_UNKNOWN] == 1), [time_key]] = g_args.penalty

    if g_args.par:
        df[KEY_PAR] = df[time_key]
        df.loc[(df[KEY_MEMOUT] == 1)
               | (df[KEY_ERROR] == 1)
               | (df[KEY_UNKNOWN] == 1)
               | (df[time_key] == 1), [KEY_PAR]] = g_args.par
    else:
        df[KEY_PAR] = 0


    # Round some statistic columns
    df[KEY_TIME_CPU] = df[KEY_TIME_CPU].round(1)
    df[KEY_TIME_REAL] = df[KEY_TIME_REAL].round(1)
    df[KEY_MEMORY] = df[KEY_MEMORY].round(1)
    df[KEY_EXIT_CODE] = df[KEY_EXIT_CODE].fillna(0, downcast='infer')

    # Use string representation of result
    df[KEY_RESULT] = df[KEY_RESULT].map(result_to_string)

    # Determine if we got multiple results per file
    df[KEY_INCREMENTAL] = df[KEY_SOLVED] > 1

    # Determine uniquely solved instances
    uniq = df.groupby(KEY_BENCHMARK,
                      as_index=False).agg({KEY_SOLVED: agg_uniq})
    uniq.rename(columns={KEY_SOLVED: KEY_UNIQ}, inplace=True)
    df = pd.merge(df, uniq, how='left', on=[KEY_BENCHMARK])
    df.loc[(df[KEY_SOLVED] == 0) & (df[KEY_UNIQ] == 1), KEY_UNIQ] = 0

    nsolved = df.groupby(KEY_BENCHMARK,
                         as_index=False).agg({KEY_SOLVED: 'sum'})
    nsolved.rename(columns={KEY_SOLVED: KEY_NSOLVED}, inplace=True)
    df = pd.merge(df, nsolved, how='left', on=[KEY_BENCHMARK])

    # Shorten config names, remove leading '/' if common path exists
    if unique_configs:
        prefix_len = len(os.path.commonpath(unique_configs))
        if prefix_len > 0:
            prefix_len += 1
            df[KEY_CONFIG] = df[KEY_CONFIG].str[prefix_len:]
            if g_args.slowdown:
                g_args.slowdown = g_args.slowdown[prefix_len:]

    ### Compute VBS
    df[KEY_BEST] = 0
    df[KEY_TIME_SLOWDOWN] = 1.0

    # Determine best solver for each benchmark (max. solved, min. time_cpu)
    vbs = df.sort_values(by=[KEY_BENCHMARK, KEY_SOLVED, time_key],
                         ascending=[True, False,
                                    True]).drop_duplicates(KEY_BENCHMARK,
                                                           keep='first')

    # Mark configs that contributed to VBS (multiple best solvers on one
    # benchmark possible)
    df = pd.merge(df, vbs[[KEY_BENCHMARK, time_key]], how='right',
                  on=[KEY_BENCHMARK], suffixes=('', '_vbs'))
    df[KEY_BEST] = ((df[KEY_SOLVED] > 0) &
                    (df[time_key] == df[f'{time_key}_vbs'])).astype(int)
    del df[f'{time_key}_vbs']

    if g_args.vbs:
        df_vbs = df.sort_values(by=[KEY_BENCHMARK, KEY_SOLVED, time_key],
                         ascending=[True, False,
                                    True]).drop_duplicates(KEY_BENCHMARK,
                                                           keep='first')
        vbs_config = 'virtual best solver'
        df_vbs[KEY_CONFIG] = vbs_config
        df_vbs[KEY_BEST] = 0
        unique_configs.append(vbs_config)

        # Add VBS to data set
        df = pd.concat([df, df_vbs], ignore_index=True)

        if not g_args.slowdown:
            g_args.slowdown = vbs_config

    # Compute slowdown column
    if g_args.slowdown:
        base = df.loc[df[KEY_CONFIG] == g_args.slowdown]
        base.loc[(base[time_key] == 0), time_key] = 0.001
        df = pd.merge(df,
                      base[[KEY_BENCHMARK, time_key]],
                      how='left',
                      on=[KEY_BENCHMARK],
                      suffixes=('', '_slowdown_base'))
        key_base = f'{time_key}_slowdown_base'
        df.loc[df[time_key] > 0, KEY_TIME_SLOWDOWN] = \
            df[time_key] / df[key_base]
        df[KEY_TIME_SLOWDOWN] = df[KEY_TIME_SLOWDOWN].round(3)
        del (df[key_base])

    df[KEY_UNSOLVED] = 0
    df.loc[(df[KEY_SAT] == 0) & (df[KEY_UNSAT] == 0), [KEY_UNSOLVED]] = 1

    return df


def group_results(df):
    global g_args

    # Set index as (benchmark, config)
    if not g_args.grouped:
        df = df.set_index([KEY_BENCHMARK, KEY_CONFIG]).sort_index()
        return df

    # Options -g, -G, -t

    prefix_len = get_common_path_prefix_len(df)

    # Group by directory for totals
    groupby_cols = [KEY_BENCHMARK, KEY_CONFIG]
    if g_args.totals:
        groupby_cols = [KEY_CONFIG]
    # Group by top-level directory
    elif g_args.grouped_top:
        df[KEY_BENCHMARK] = \
            df[KEY_BENCHMARK].str[prefix_len:].str.split(pat='/', n=1).str[0]
    # Group by lowest subdirectory
    else:
        df[KEY_BENCHMARK] = \
            df[KEY_BENCHMARK].str[prefix_len:].str.split(
                pat='/').str[:-1].str.join('/')

    df = df.groupby(groupby_cols).agg(KEY_AGGS)

    # Determine status for grouped results.
    # Group is status error/disagreement if at least one error/disagreement
    # has been detected. It's timeout/memout if all instances in the group
    # ran out of time/memory. Otherwise, the status is ok.
    df[KEY_STATUS] = STATUS_OK
    df.loc[df[KEY_ERROR] > 1, KEY_STATUS] = STATUS_ERR
    df.loc[df[KEY_DISAGR] > 0, KEY_STATUS] = STATUS_DIS
    df.loc[df[KEY_MEMOUT] == df[KEY_RESULT], KEY_STATUS] = STATUS_MEM
    df.loc[df[KEY_TIMEOUT] == df[KEY_RESULT], KEY_STATUS] = STATUS_TIME

    return df


def print_results(df):

    if df.empty:
        print('Dataframe is empty. Nothing to print.')
        sys.exit(0)

    # Determine default columns based on results (incremental vs. non-incremental)
    if not g_args.columns:
        is_incremental = df[KEY_INCREMENTAL].any()
        g_args.columns = [KEY_STATUS, KEY_RESULT]
        if g_args.grouped:
            g_args.columns.extend([
                KEY_SOLVED, KEY_SAT, KEY_UNSAT, KEY_BEST, KEY_TIMEOUT,
                KEY_MEMOUT, KEY_ERROR, KEY_UNIQ, KEY_DISAGR
            ])
        elif is_incremental:
            g_args.columns.extend([KEY_SOLVED, KEY_SAT, KEY_UNSAT, KEY_BEST])
            g_args.columns.remove(KEY_RESULT)
        else:
            g_args.columns.append(KEY_EXIT_CODE)
        g_args.columns.extend([KEY_TIME_CPU, KEY_MEMORY])

    # Select only columns in g_args.columns
    df = df[g_args.columns]

    # Sort totals by solved, time_cpu if possible
    if g_args.totals:
        sort_keys = []
        sort_asc = []
        if KEY_SOLVED in g_args.columns:
            sort_keys.append(KEY_SOLVED)
            sort_asc.append(False)
        if KEY_TIME_CPU in g_args.columns:
            sort_keys.append(KEY_TIME_CPU)
            sort_asc.append(True)

        if sort_keys:
            df = df.sort_values(by=sort_keys, ascending=sort_asc)

    if g_args.grouped:
        df.rename(columns = {KEY_RESULT: 'total'}, inplace = True)

    if g_args.swap:
        # unstack KEY_CONFIG
        df = df.unstack()
        # swap KEY_CONFIG with COLUMNS
        df = df.swaplevel(0, 1, 1)
        # stack COLUMNS
        df = df.stack()

    if g_args.side_by_side:
        df = df.unstack(level=1)

    with pd.option_context('display.max_columns', None, 'display.max_rows',
                           None, 'display.width', None,
                           'display.max_colwidth', 250,
                           'display.float_format', '{:.1f}'.format):
        if g_args.html:
            print(df.to_html())
        elif g_args.csv:
            print(df.to_csv(), end='')
        elif g_args.latex:
            print(df.to_latex())
        else:
            print(df)


def summarize_errors(df):

    df_error = df[df[KEY_ERROR] == 1]
    errors = {}
    for index, row in df_error.iterrows():
        with open(row[KEY_OUTPUT_LOG]) as output_log:
            lines = output_log.readlines()
            idx = 0
            for i, line in enumerate(lines):
                if line.startswith('----------'):
                    idx = i + 1
                    break
            for i, line in enumerate(lines[idx:]):
                line = line.strip()
                if not line:
                    continue
                if line not in ('sat', 'unsat', 'unknown'):
                    idx += i
                    break
            error_msg = ''.join(lines[idx:])

            if error_msg not in errors:
                errors[error_msg] = []

            errors[error_msg].append(row[KEY_BENCHMARK])

    print('Detected Errors:')
    for i, (error_msg, errors) in enumerate(errors.items()):
        print('\nError #{}:'.format(i + 1))
        print('\n{}'.format(error_msg))
        print('Files:\n  {}'.format('\n  '.join(errors)))


def print_time_stats(what, start):
    global g_args
    if g_args.verbose:
        print('{}: {:.3f}s'.format(what, time.time() - start))


def prepare_data(args=None):
    # Parse options, set defaults
    parse_and_check_arguments(args)

    # Read data from log files or cache files
    start = time.time()
    if g_args.starexec_csv:
        df = read_starexec_csv(g_args.starexec_csv)
    else:
        df = read_data()
    print_time_stats('extract', start)

    df = prefilter_results(df)

    # Process and compute data
    start = time.time()
    df = process_data(df)
    print_time_stats('process', start)

    df = filter_query(df)

    # Filter results based on given options
    start = time.time()
    df = filter_results(df)
    print_time_stats('filter', start)

    if not g_args.summarize_errors:
        # Group results by (benchmark, config)
        start = time.time()
        df = group_results(df)
        print_time_stats('group', start)

    return df


def main():
    global g_args

    df = prepare_data(None)
    if g_args.summarize_errors:
        summarize_errors(df)
    else:
        print_results(df)


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        sys.exit('Interrupted')
    except CmprException as e:
        sys.exit(str(e))
    except BrokenPipeError:
        pass
    sys.exit(0)
