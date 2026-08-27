# Reduction graph

The current state of the classification as a graph: nodes are rules (families collapsed, with
counts), grouped by concern category; an edge points from a rule to the rules its reduction
targets. Border color and style encode the level, which is also the *elimination stage* the rule
belongs to — **reducible** (green, removed first), **rare/simplify** (violet dotted, the rewrite
vocabulary, removed second), **expensive** (yellow dashed, `poly_simp`, `aci_simp` and `sko_ex`,
removed last), and **core** (blue, bold, what is left). Two further markers sit outside the
stages: **variant** (grey dashed) for `eq_transitive`/`eq_congruent`, which Carcara checks with
the same functions as `trans`/`cong` and therefore neither counts nor eliminates, and **oracle**
(red, double border) for the one rule no reduction reaches, `lia_generic`. Proposed-but-unadopted
extensions (`equiv_intro`, `or_intro`; the `bind` generalization is noted on the `bind` node) are
marked by a dashed border or a "(proposed)" note. Edge styles mirror the levels.

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
