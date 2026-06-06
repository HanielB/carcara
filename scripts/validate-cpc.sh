#!/bin/bash
#
# Validates Carcara's CPC proof checking against the cvc5 regression tests.
#
# For each regression test in the AUFNIRA fragment that cvc5 finds unsat, this script generates a
# CPC proof with cvc5 (using `--proof-print-conclusion`, which is required for Carcara to be able
# to check CPC proofs), and then checks it with `carcara check --proof-format cpc`.
#
# Usage: scripts/validate-cpc.sh [REGRESSION-DIR ...]
#
# Environment variables:
#   CVC5     path to the cvc5 binary           (default: ~/cvc5/prod/bin/cvc5)
#   CARCARA  path to the carcara binary        (default: target/release/carcara, falling back
#                                               to target/debug/carcara)
#   RARE     path to the RARE rules file       (default: rewrites.eo)
#   OUT      working directory for the results (default: a fresh temporary directory)
#   TIMEOUT  timeout in seconds for each cvc5/carcara call (default: 30)

set -u

CVC5=${CVC5:-~/cvc5/prod/bin/cvc5}
if [ -z "${CARCARA:-}" ]; then
    if [ -x target/release/carcara ]; then CARCARA=target/release/carcara
    else CARCARA=target/debug/carcara; fi
fi
RARE=${RARE:-rewrites.eo}
OUT=${OUT:-$(mktemp -d /tmp/validate-cpc.XXXXXX)}
TIMEOUT=${TIMEOUT:-30}

if [ $# -eq 0 ]; then
    set -- ~/cvc5/test/regress/cli/regress0
fi

# The logics in the AUFNIRA fragment (no bitvectors, strings, datatypes, etc.)
LOGICS='QF_UF|UF|QF_LIA|QF_LRA|QF_UFLIA|QF_UFLRA|QF_IDL|QF_RDL|LIA|LRA|UFLIA|UFLRA|AUFLIA|AUFLIRA|AUFNIRA|QF_AUFLIA|QF_ALIA|QF_AX|QF_NIA|QF_NRA|NIA|NRA|QF_UFNIA|QF_UFNRA|UFNIA|UFNRA|QF_UFIDL|ALIA'

valid=0; holey=0; invalid=0; skipped=0
> "$OUT/invalid.txt"
> "$OUT/holey.txt"

for dir in "$@"; do
    for f in $(grep -lrE "set-logic ($LOGICS)\)" "$dir" --include="*.smt2" | sort); do
        # Skip tests with multiple check-sats or incremental features
        [ "$(grep -c check-sat "$f")" != "1" ] && continue
        grep -qE "\(push|\(pop|\(reset|\(get-" "$f" && continue

        base=$(basename "$f" .smt2)
        problem="$OUT/$base.smt2"
        proof="$OUT/$base.cpc"
        grep -v "^;" "$f" > "$problem"

        result=$(timeout "$TIMEOUT" "$CVC5" --dump-proofs --proof-print-conclusion "$problem" 2>/dev/null)
        if [ "$(echo "$result" | head -1)" != "unsat" ]; then
            skipped=$((skipped+1))
            rm -f "$problem"
            continue
        fi
        echo "$result" | tail -n +2 > "$proof"

        result=$(timeout "$TIMEOUT" "$CARCARA" check --proof-format cpc --allow-int-real-subtyping \
            --rare-file "$RARE" "$proof" "$problem" 2> "$OUT/$base.err" | tail -1)
        case "$result" in
            valid) valid=$((valid+1)); rm -f "$OUT/$base.err" ;;
            holey) holey=$((holey+1)); echo "$f" >> "$OUT/holey.txt" ;;
            *) invalid=$((invalid+1))
               echo "$f: $(grep -m1 ERROR "$OUT/$base.err" | head -c 200)" >> "$OUT/invalid.txt" ;;
        esac
    done
done

echo "valid: $valid"
echo "valid with holes: $holey"
echo "invalid: $invalid"
echo "skipped (cvc5 did not return unsat in time): $skipped"
echo "details in $OUT"
