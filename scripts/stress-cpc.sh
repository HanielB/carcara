#!/bin/bash
#
# Differential stress test for Carcara's CPC proof checking.
#
# For each benchmark, cvc5 produces two CPC proofs of the same problem: one with step
# conclusions (which Carcara requires) and one without (which Ethos, the reference CPC checker,
# expects). Both checkers run on their proof, and the verdicts are compared. The interesting
# outcomes are the disagreements:
#
#   - Ethos accepts and Carcara rejects: Carcara is incomplete on that proof, or its
#     translation is wrong (reported as CARCARA-REJECTS);
#   - Carcara accepts and Ethos rejects: a possible unsoundness (reported as ETHOS-REJECTS);
#   - Carcara crashes, hangs or runs out of memory (reported as CARCARA-CRASH).
#
# Proofs neither checker accepts, and benchmarks cvc5 does not prove in time, are counted and
# ignored. A "holey" Carcara verdict is treated as acceptance, as is an "incomplete" one from
# Ethos: both mean the proof checks except for steps the solver itself trusts.
#
# Usage: scripts/stress-cpc.sh [BENCHMARK-DIR ...]
#
# Environment variables:
#   CVC5     path to the cvc5 binary       (default: ~/cvc5/prod/bin/cvc5)
#   CARCARA  path to the carcara binary    (default: target/release/carcara)
#   ETHOS    path to the ethos binary      (default: ~/exp/pfcmp/ethos-src/build-static/src/ethos)
#   SIGS     the CPC signature directory   (default: ~/cvc5/proofs/eo/cpc)
#   RARE     the RARE rules file           (default: ~/carcara/rewrites.eo)
#   OUT      working directory             (default: a fresh temporary directory)
#   TIMEOUT  timeout in seconds per call   (default: 30)
#   MEMLIMIT address-space limit in MB     (default: 8000)

set -u

CVC5=${CVC5:-~/cvc5/prod/bin/cvc5}
CARCARA=${CARCARA:-target/release/carcara}
ETHOS=${ETHOS:-~/exp/pfcmp/ethos-src/build-static/src/ethos}
SIGS=${SIGS:-~/cvc5/proofs/eo/cpc}
RARE=${RARE:-~/carcara/rewrites.eo}
OUT=${OUT:-$(mktemp -d /tmp/stress-cpc.XXXXXX)}
TIMEOUT=${TIMEOUT:-30}
MEMLIMIT=${MEMLIMIT:-8000}

mkdir -p "$OUT"
> "$OUT/disagreements.txt"
> "$OUT/summary.txt"

agree=0; unproved=0; both_reject=0; carcara_rejects=0; ethos_rejects=0; crashes=0

for dir in "$@"; do
    for f in $(find "$dir" -name '*.smt2' | sort); do
        # Skip problems with multiple queries or incremental commands
        [ "$(grep -c check-sat "$f")" != "1" ] && continue
        grep -qE "\(push|\(pop|\(reset|\(get-" "$f" && continue

        base=$(basename "$f" .smt2)
        problem="$OUT/$base.smt2"
        grep -v "^;" "$f" > "$problem"

        result=$(timeout "$TIMEOUT" "$CVC5" --dump-proofs --proof-print-conclusion \
            "$problem" 2>/dev/null | head -1)
        if [ "$result" != unsat ]; then
            unproved=$((unproved+1)); rm -f "$problem"; continue
        fi
        timeout "$TIMEOUT" "$CVC5" --dump-proofs --proof-print-conclusion "$problem" \
            2>/dev/null | tail -n +2 > "$OUT/$base.cpc"
        # Ethos checks the conclusion-free proof, prefixed by the signature includes, as
        # cvc5's contrib/get-ethos-checker builds it
        {
            echo "(include \"$SIGS/Cpc.eo\")"
            echo "(include \"$SIGS/expert/CpcExpert.eo\")"
            timeout "$TIMEOUT" "$CVC5" --dump-proofs "$problem" 2>/dev/null | tail -n +3 | head -n -1
        } > "$OUT/$base.eo"

        ( ulimit -v $((MEMLIMIT * 1000)); timeout "$TIMEOUT" "$CARCARA" check \
            --proof-format cpc --allow-int-real-subtyping --rare-file "$RARE" \
            "$OUT/$base.cpc" "$problem" > "$OUT/$base.cout" 2> "$OUT/$base.cerr" )
        crc=$?
        cver=$(tail -1 "$OUT/$base.cout" 2>/dev/null)

        ( ulimit -v $((MEMLIMIT * 1000)); timeout "$TIMEOUT" "$ETHOS" \
            --require-proof-of-false "$OUT/$base.eo" > "$OUT/$base.eout" 2>&1 )
        erc=$?
        ever=$(grep -m1 -E '^(correct|incomplete)$' "$OUT/$base.eout")

        c_ok=0; e_ok=0
        case "$cver" in valid|holey) c_ok=1 ;; esac
        [ -n "$ever" ] && e_ok=1

        # A crash is any exit that is not a clean verdict and not a timeout or memory-out
        if [ "$c_ok" = 0 ] && [ "$crc" != 124 ] && [ "$crc" != 137 ] \
            && grep -qE 'panicked|fatal runtime|core dumped' "$OUT/$base.cerr"; then
            crashes=$((crashes+1))
            echo "CARCARA-CRASH $f: $(grep -m1 -E 'panicked|fatal runtime' "$OUT/$base.cerr" | head -c 150)" \
                >> "$OUT/disagreements.txt"
        elif [ "$c_ok" = 1 ] && [ "$e_ok" = 1 ]; then
            agree=$((agree+1)); rm -f "$OUT/$base.cerr" "$OUT/$base.eout"
        elif [ "$c_ok" = 0 ] && [ "$e_ok" = 1 ]; then
            carcara_rejects=$((carcara_rejects+1))
            echo "CARCARA-REJECTS $f: [$cver rc=$crc] $(grep -m1 -a error "$OUT/$base.cerr" | head -c 150)" \
                >> "$OUT/disagreements.txt"
        elif [ "$c_ok" = 1 ] && [ "$e_ok" = 0 ]; then
            ethos_rejects=$((ethos_rejects+1))
            echo "ETHOS-REJECTS $f: [carcara $cver] $(head -c 150 "$OUT/$base.eout")" \
                >> "$OUT/disagreements.txt"
        else
            both_reject=$((both_reject+1))
        fi
    done
done

{
    echo "both accept:             $agree"
    echo "only ethos accepts:      $carcara_rejects"
    echo "only carcara accepts:    $ethos_rejects"
    echo "carcara crashes:         $crashes"
    echo "both reject:             $both_reject"
    echo "unproved by cvc5:        $unproved"
    echo "details in $OUT"
} | tee "$OUT/summary.txt"
