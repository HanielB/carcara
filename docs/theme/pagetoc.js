// Floating per-page table of contents ("On this page"), shown on wide screens.
// Header carries a position counter; a vertical track shows reading progress
// with a marker aligned to the active heading.
(function () {
  function pad(n) { return (n < 10 ? "0" : "") + n; }

  function init() {
    var main = document.querySelector("main");
    if (!main) { return; }
    var headings = main.querySelectorAll("h2, h3");
    if (headings.length < 2) { return; }

    var toc = document.createElement("nav");
    toc.className = "pagetoc";

    var header = document.createElement("div");
    header.className = "pagetoc-header";
    var title = document.createElement("span");
    title.className = "pagetoc-title";
    title.textContent = "On this page";
    var count = document.createElement("span");
    count.className = "pagetoc-count";
    header.appendChild(title);
    header.appendChild(count);
    toc.appendChild(header);

    var body = document.createElement("div");
    body.className = "pagetoc-body";
    var track = document.createElement("span");
    track.className = "pagetoc-track";
    var progress = document.createElement("span");
    progress.className = "pagetoc-progress";
    var marker = document.createElement("span");
    marker.className = "pagetoc-marker";
    track.appendChild(progress);
    track.appendChild(marker);
    body.appendChild(track);

    var list = document.createElement("ul");
    list.className = "pagetoc-list";
    var items = [];
    headings.forEach(function (h) {
      if (!h.id) { return; }
      var li = document.createElement("li");
      li.className = "pagetoc-" + h.tagName.toLowerCase();
      var a = document.createElement("a");
      a.href = "#" + h.id;
      a.textContent = h.textContent;
      li.appendChild(a);
      list.appendChild(li);
      items.push({ heading: h, link: a, item: li });
    });
    if (items.length < 2) { return; }
    body.appendChild(list);
    toc.appendChild(body);
    document.body.appendChild(toc);

    count.textContent = pad(1) + " / " + pad(items.length);

    var active = null;
    function update() {
      var current = items[0];
      var index = 0;
      for (var i = 0; i < items.length; i++) {
        if (items[i].heading.getBoundingClientRect().top <= 120) {
          current = items[i];
          index = i;
        }
      }
      if (active !== current) {
        if (active) { active.link.classList.remove("active"); }
        current.link.classList.add("active");
        active = current;
        count.textContent = pad(index + 1) + " / " + pad(items.length);
      }
      // progress fill + marker aligned with the active entry
      var y = current.item.offsetTop + current.item.offsetHeight / 2;
      progress.style.height = y + "px";
      marker.style.top = (y - 3) + "px";
    }
    var CARD_WIDTH = 220;
    function position() {
      if (window.innerWidth < 1080) { toc.style.display = "none"; return; }
      var rect = main.getBoundingClientRect();
      var sidebar = document.getElementById("sidebar");
      var sidebarRight = 0;
      if (sidebar) {
        var sr = sidebar.getBoundingClientRect();
        if (sr.right > 0) { sidebarRight = sr.right; }
      }
      var left = rect.left - CARD_WIDTH - 16;
      if (left < sidebarRight + 4) { toc.style.display = "none"; return; }
      toc.style.display = "block";
      toc.style.left = left + "px";
    }
    function onchange() { position(); update(); }
    document.addEventListener("scroll", onchange, { passive: true });
    window.addEventListener("resize", onchange, { passive: true });
    if (typeof ResizeObserver !== "undefined") {
      new ResizeObserver(onchange).observe(main);
    }
    onchange();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
