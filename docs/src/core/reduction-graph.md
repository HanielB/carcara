# Reduction graph

The current state of the classification as a graph, read **hierarchically**: the outermost
boxes are the ladder tiers — **reducible** (green, stage 1), **rw+simp** (violet, stage 2, the
rewrite vocabulary), and **core** (blue) — and each tier is subdivided by the logical concern
categories (structural, clausal, binder, equality & rewriting, arithmetic, bitvector). The
**expensive** rules (`poly_simp`, `aci_simp`, `bind`; yellow dashed) sit *inside the core box*:
they are expandable — the last rung of the ladder removes every corpus instance — but in
practice the idea is not to expand them, so they are core in everything but pedigree; their
expansion edges are labeled as unused. `aci_simp` is grouped with the structural rules — what
it checks is term-structure normalization (associativity, commutativity, identities,
idempotence), not an equational theory. An edge points from a rule to the rules its reduction
targets, so every arrow flows into (or within) the core box. Two markers sit outside the
stages: **variant** (grey dashed) for `eq_transitive`/`eq_congruent`, which Carcara checks with
the same functions as `trans`/`cong` and therefore neither counts nor eliminates, and **oracle**
(red, double border) for the one rule no reduction reaches, `lia_generic`, kept with the legacy
group. Proposed-but-unadopted extensions (`equiv_intro`, `or_intro`; the `bind` generalization
is noted on the `bind` node) are marked by a dashed border or a "(proposed)" note. Edge styles
mirror the levels.

Ubiquitous glue targets are omitted to keep the graph readable: nearly every reduction also uses
`resolution`, `subproof`, and iff-introduction (`equiv_intro`, or its `equiv_neg1/2` derivation),
so those edges are drawn only where they are the distinctive target.

The graph is **interactive**: drag nodes to rearrange, scroll to zoom (horizontal scroll — or
shift+scroll — pans sideways), drag the background to pan; click a node to jump to its reduction row or worked example in the
[classification](./classification.md) (collapsible examples open automatically when targeted);
hover a node to see the rule as phrased in the Alethe specification.

<style>
#redgraph { width: 100%; height: 78vh; border: 1px solid var(--table-border-color, #ccc); border-radius: 6px; position: relative; }
#redgraph-tip { display: none; position: absolute; z-index: 20; max-width: 460px; padding: 6px 9px; font-size: 0.78em; line-height: 1.4; white-space: pre-line; background: var(--bg); color: var(--fg); border: 1px solid var(--table-border-color, #ccc); border-radius: 5px; box-shadow: 0 2px 8px rgba(0,0,0,0.15); pointer-events: none; }
#redgraph-controls { margin-bottom: 6px; }
#redgraph-controls button { font-size: 0.85em; padding: 3px 10px; margin-right: 6px; cursor: pointer; background: var(--bg); color: var(--fg); border: 1px solid var(--table-border-color, #ccc); border-radius: 4px; }
</style>

<div id="redgraph-controls"><button id="redgraph-fit">Fit</button><button id="redgraph-reset">Reset layout</button></div>
<div id="redgraph"></div>
<script src="cytoscape.min.js"></script>
<script src="reduction-graph-data.js"></script>
<script src="reduction-graph-init.js"></script>

The source of truth is [`reduction-graph.dot`](./reduction-graph.dot) — clusters, levels, node
`URL`/`tooltip` attributes (the tooltips carry the abstract rule statements), and edges. After
editing it, regenerate the data with `python3 gen-graph-data.py` (in `docs/src/core/`), which
parses the attributes and takes the initial node positions from `dot -Tplain`. The rendering is
[Cytoscape.js](https://js.cytoscape.org/), vendored at `cytoscape.min.js` so the book stays
self-contained.
