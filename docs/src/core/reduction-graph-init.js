// Interactive reduction graph: cytoscape.js over the data generated from
// reduction-graph.dot. Drag nodes, wheel-zoom, drag the background to pan,
// click a node to jump to its classification entry, hover for the rule
// statement as phrased in the Alethe specification.
(function () {
  var PALETTES = {
    light: {
      core: "#2a78d6", reducible: "#1baf7a", expensive: "#eda100",
      aggressive: "#4a3aa7", removal: "#e34948",
      nodeBg: "#ffffff", text: "#0b0b0b", clusterBg: "#f7f6f3",
      clusterBorder: "#d8d6cf", edge: "#8a887f", edgeText: "#52514e"
    },
    dark: {
      core: "#3987e5", reducible: "#199e70", expensive: "#c98500",
      aggressive: "#9085e9", removal: "#e66767",
      nodeBg: "#1f1f1e", text: "#f0f0ef", clusterBg: "#232322",
      clusterBorder: "#3c3b39", edge: "#8a887f", edgeText: "#a5a49b"
    }
  };
  var DARK_THEMES = ["coal", "navy", "ayu"];

  function currentPalette() {
    var cls = document.documentElement.className || "";
    var dark = DARK_THEMES.some(function (t) { return cls.indexOf(t) >= 0; });
    return dark ? PALETTES.dark : PALETTES.light;
  }

  function init() {
    var container = document.getElementById("redgraph");
    if (!container || typeof cytoscape === "undefined" || !window.REDGRAPH) { return; }
    var data = window.REDGRAPH;

    var elements = [];
    data.clusters.forEach(function (c) {
      elements.push({ data: { id: c.id, label: c.label, isCluster: true } });
    });
    var home = {};
    data.nodes.forEach(function (n) {
      home[n.id] = { x: n.x, y: n.y };
      elements.push({
        data: {
          id: n.id, parent: n.parent, label: n.label, level: n.level,
          borderStyle: n.borderStyle, url: n.url, tooltip: n.tooltip,
          w: Math.max(n.w, 40), h: Math.max(n.h, 24)
        },
        position: { x: n.x, y: n.y }
      });
    });
    data.edges.forEach(function (e, i) {
      elements.push({
        data: { id: "e" + i, source: e.source, target: e.target,
                style: e.style, elabel: e.label }
      });
    });

    function styleFor(p) {
      return [
        { selector: "node", style: {
            "shape": "round-rectangle",
            "background-color": p.nodeBg,
            "border-width": 2,
            "width": "data(w)", "height": "data(h)",
            "label": "data(label)",
            "text-wrap": "wrap", "text-max-width": "130px",
            "text-valign": "center", "text-halign": "center",
            "font-size": "11px", "font-family": "sans-serif",
            "color": p.text
        }},
        { selector: "node[level='core']",       style: { "border-color": p.core, "border-width": 3 } },
        { selector: "node[level='reducible']",  style: { "border-color": p.reducible } },
        { selector: "node[level='expensive']",  style: { "border-color": p.expensive } },
        { selector: "node[level='aggressive']", style: { "border-color": p.aggressive } },
        { selector: "node[level='removal']",    style: { "border-color": p.removal } },
        { selector: "node[borderStyle='dashed']", style: { "border-style": "dashed" } },
        { selector: "node[borderStyle='dotted']", style: { "border-style": "dotted" } },
        { selector: "node[borderStyle='double']", style: { "border-style": "double", "border-width": 4 } },
        { selector: ":parent", style: {
            "background-color": p.clusterBg, "background-opacity": 0.6,
            "border-color": p.clusterBorder, "border-width": 1,
            "shape": "round-rectangle", "padding": "18px",
            "label": "data(label)",
            "text-valign": "top", "text-halign": "center",
            "font-size": "14px", "font-weight": "bold", "color": p.text
        }},
        { selector: "edge", style: {
            "curve-style": "bezier",
            "width": 1.2, "line-color": p.edge,
            "target-arrow-shape": "triangle", "target-arrow-color": p.edge,
            "arrow-scale": 0.8,
            "label": "data(elabel)", "font-size": "9px", "color": p.edgeText,
            "text-background-color": p.nodeBg, "text-background-opacity": 0.8,
            "text-background-padding": "1px"
        }},
        { selector: "edge[style='dashed']", style: { "line-style": "dashed" } },
        { selector: "edge[style='dotted']", style: { "line-style": "dotted" } }
      ];
    }

    var cy = cytoscape({
      container: container,
      elements: elements,
      style: styleFor(currentPalette()),
      layout: { name: "preset" },
      minZoom: 0.1, maxZoom: 4, wheelSensitivity: 0.3
    });
    cy.fit(undefined, 20);

    // horizontal wheel (or shift+wheel) pans sideways; vertical wheel keeps zooming
    container.addEventListener("wheel", function (e) {
      var scale = e.deltaMode === 1 ? 16 : 1;   // line-mode deltas (Firefox)
      var dx = e.deltaX * scale, dy = e.deltaY * scale;
      var horizontal = Math.abs(dx) > Math.abs(dy) || e.shiftKey;
      if (!horizontal) { return; }              // fall through to cytoscape's zoom
      e.preventDefault();
      e.stopPropagation();
      cy.panBy({ x: -(Math.abs(dx) > Math.abs(dy) ? dx : dy), y: 0 });
    }, { capture: true, passive: false });

    // theme switching
    new MutationObserver(function () {
      cy.style(styleFor(currentPalette()));
    }).observe(document.documentElement, { attributes: true, attributeFilter: ["class"] });

    // click-through to the classification
    cy.on("tap", "node[url]", function (ev) {
      window.location.href = ev.target.data("url");
    });

    // hover card with the abstract rule statement
    var tip = document.createElement("div");
    tip.id = "redgraph-tip";
    container.appendChild(tip);
    cy.on("mouseover", "node[tooltip]", function (ev) {
      var n = ev.target;
      if (n.data("isCluster")) { return; }
      tip.textContent = n.data("tooltip");
      tip.style.display = "block";
      container.style.cursor = "pointer";
      var rp = n.renderedPosition();
      var x = rp.x + 16, y = rp.y + 16;
      var box = container.getBoundingClientRect();
      tip.style.left = Math.min(x, box.width - tip.offsetWidth - 8) + "px";
      tip.style.top = Math.min(y, box.height - tip.offsetHeight - 8) + "px";
    });
    cy.on("mouseout drag pan zoom", function () {
      tip.style.display = "none";
      container.style.cursor = "default";
    });

    // controls
    document.getElementById("redgraph-fit").addEventListener("click", function () {
      cy.fit(undefined, 20);
    });
    document.getElementById("redgraph-reset").addEventListener("click", function () {
      cy.nodes().forEach(function (n) {
        if (home[n.id()]) { n.position(home[n.id()]); }
      });
      cy.fit(undefined, 20);
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
