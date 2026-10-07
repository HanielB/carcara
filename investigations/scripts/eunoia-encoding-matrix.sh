#!/bin/bash
# eunoia-encoding-matrix.sh <name> <carcara> <signature-dir> [translate flags...]
#
# Translates every case's elab.alethe (with its problem.smt2) to Eunoia and checks it with
# Ethos, as run-eunoia.sh's elab arm does: cvc5 proofs with --expand-let-bindings, veriT
# proofs without. Prints one "<solver>.<bench> <verdict>" line per case to $OUT/<name>.txt
# and keeps the .eo files and Ethos outputs under $OUT/<name>/.
#
#   CASES  file listing work directories (each with elab.alethe and problem.smt2), e.g. the
#          <run>/{cvc5,verit}/work/*/ directories of ~/exp/alethe-eunoia/local/<run>
#   RARE   RARE database passed to carcara
#   ETHOS  Ethos executable (default: ethos)
#   OUT    output directory (default: ./matrix)
#
# Each tool runs under a 6 GB address-space cap and a 180 s limit.
name=$1 carcara=$2 sig=$3; shift 3
: "${CASES:?}" "${RARE:?}"
ETHOS=${ETHOS:-ethos}
OUT=${OUT:-./matrix}
out=$OUT/$name; mkdir -p "$out"
while read -r d; do
  b=$(basename "$d"); solver=$(basename "$(dirname "$(dirname "$d")")")
  let=""; [ "$solver" = cvc5 ] && let=--expand-let-bindings
  ( ulimit -v 6000000; ulimit -s unlimited; ulimit -c 0
    timeout -k 5 180 "$carcara" translate eunoia --eunoia-mech "$sig" --rare-file "$RARE" $let "$@" \
      "$d/elab.alethe" "$d/problem.smt2" > "$out/$solver.$b.eo" 2> "$out/$solver.$b.tr.err" ); trc=$?
  if [ $trc -ne 0 ]; then echo "$solver.$b translate-error"; continue; fi
  ( ulimit -v 6000000; ulimit -s unlimited; ulimit -c 0
    timeout -k 5 180 "$ETHOS" "$out/$solver.$b.eo" > "$out/$solver.$b.ethos.out" 2>&1 ); erc=$?
  v=$(grep -m1 -xE 'correct|incomplete|incorrect' "$out/$solver.$b.ethos.out")
  [ $erc -ne 0 ] && v="ethos-error"
  echo "$solver.$b ${v:-no-verdict}"
done < "$CASES" > "$out.txt"
echo "$name: $(awk '{print $2}' "$out.txt" | sort | uniq -c | tr '\n' ' ')"
