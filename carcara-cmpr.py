#!/usr/bin/env python3

from cmpr import ResultParser,RESULT_UNSAT,RESULT_SAT,ValueParser, register_output_parser, main, prepare_data, print_results
import ast


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
        return float(str(line.decode("unicode_escape")).split(":")[1].split(r'µ')[0][:-1].strip())/1000

register_output_parser(CarcaraResultParser())
register_output_parser(CarcaraHoleyResultParser(), "count")
register_output_parser(CheckTimeParser(), sum)

df = prepare_data(None)

# df = df[df["valid"] == 1]
# df = df[df["holey"] == 1]
# df = df[df["invalid"] == 1]

print_results(df)
