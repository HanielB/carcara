#!/usr/bin/env python3

from cmpr import ResultParser,RESULT_UNSAT,RESULT_SAT,ValueParser, register_output_parser, main, prepare_data, print_results
import ast, re


class CarcaraResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b'valid': RESULT_UNSAT,
            b'holey': RESULT_UNSAT,
            b'invalid': RESULT_SAT
        })

class CarcaraHoleyResultParser(ValueParser):
    def key(self):
        return 'holey'

    def match(self, line):
        return line.startswith(b'holey')

    def extract(self, line):
        return 1

class CheckTimeParser(ValueParser):
    def key(self):
        return "check_time"

    def match(self, line):
        return line.startswith(b'checking:')

    def extract(self, line):
        # get the time (i.e., what is before "+-")
        time = \
          str(line.decode("unicode_escape")).split(":")[1].strip().split(r'±')[0][:-2]
        # get the suffix to the number. It can be either "s", "ms", "Âµs", or
        # "ns". With that we compute the unit, since the extracted time must be
        # in seconds
        match = re.search(r'\D+$',time)
        assert match
        match = match.group()
        unit = 1000000000 if match == r'ns' else 1000000 if time[-3:] == r'Âµs' else 1000 if time[-3:] == r'ms' else 1
        # convert time into float (after removing the suffix)
        time = float(time[:-(len(match))])
        return time/unit

register_output_parser(CarcaraResultParser())
register_output_parser(CarcaraHoleyResultParser(), "count")
register_output_parser(CheckTimeParser(), sum)

df = prepare_data(None)

print_results(df)
