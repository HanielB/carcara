# Reduction graph

The current state of the classification as a graph: nodes are rules (families collapsed, with
counts), grouped by concern category; an edge points from a rule to the rules its reduction
targets. Border color and style encode the reducibility level — **core** (blue, bold),
**reducible** (green), **expensive** (yellow, dashed), **aggressive** (violet, dotted),
**removal** (red, double border) — and proposals (`la_mult_pos_pos`, `equiv_intro`, `or_intro`;
the `bind` generalization is noted on the `bind` node) are marked by a dashed border or a
"(proposed)" note. Edge styles mirror the levels: solid = a reduction meeting R1–R4, dashed = an
expensive scheme, dotted = an aggressive scheme or a fallback route.

Ubiquitous glue targets are omitted to keep the graph readable: nearly every reduction also uses
`resolution`, `subproof`, and iff-introduction (`equiv_intro`, or its `equiv_neg1/2` derivation),
so those edges are drawn only where they are the distinctive target.

The graph is **interactive**: click a node to jump to its reduction row or worked example in the
[classification](./classification.md) (collapsible examples open automatically when targeted),
and hover a node for a one-line summary of its reduction.

{{#include reduction-graph.svg}}

The source is [`reduction-graph.dot`](./reduction-graph.dot) — node `URL`/`tooltip` attributes
carry the links. Regenerate with `dot -Tsvg reduction-graph.dot -o reduction-graph.svg`, then
strip the XML prolog and replace the fixed `width`/`height` with
`style="width:100%;height:auto"` and join the opening `<svg …>` tag onto a single line (a multi-line tag is not a CommonMark HTML block) so the SVG can be inlined responsively (the
`{{#include}}` above inlines it, which is what makes the links clickable — an `<img>` embed would
swallow them).
