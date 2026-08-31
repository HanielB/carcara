# Investigations

| Date | Note | Branch | Status |
|------|------|--------|--------|
| 2026-08-30 | [Alethe BV proofs: cvc5 production + carcara checking](2026-08-30-alethe-bv-eval.md) | parsing-subst-fixes (+ cvc5 alethebv) | regressions 55/55 valid; QF_BV sample 133/133 valid |
| 2026-08-31 | [Carcara performance on the alethe-bv corpus](2026-08-31-carcara-bv-perf.md) | bv-fixes | cluster run 24204 valid / 0 holey; hotspots: let expansion (parsing), rare_rewrite matching, ac_simp/poly_simp caching |
