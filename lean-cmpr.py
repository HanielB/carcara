#!/usr/bin/env python3

from cmpr import ResultParser,RESULT_UNSAT,RESULT_SAT,ValueParser, register_output_parser, main, prepare_data, print_results
import ast, re


class LeanResultParser(ResultParser):
    def __init__(self):
        ResultParser.__init__(self)
        self.results.update({
            b'valid': RESULT_UNSAT,
            b'invalid': RESULT_SAT
        })
register_output_parser(LeanResultParser())

df = prepare_data(None)

print_results(df)
