/* Extend the standard leanblueprint graphs without replacing their renderer. */
(function () {
    "use strict";

    const graph = document.getElementById("graph");
    if (!graph) return; // This extra script is also loaded on chapter pages.

    function openNode(label) {
        const modal = document.getElementById(label + "_modal");
        if (!modal) return;
        // Match the upstream graph's popup visibility rules, using DOM IDs so
        // punctuation in Blueprint labels does not need CSS-selector escaping.
        $("#statements > div").hide();
        $(".thm").hide();
        $(modal).show().children().show().children().show();
        $("#statements").show();
        modal.querySelector(".dep-modal-content").scrollTop = 0;
        modal.querySelector(".dep-closebtn").focus({preventScroll: true});
    }

    function populateNeighbours() {
        const neighbours = new Map();
        graph.querySelectorAll(".node").forEach(node => {
            const label = node.querySelector("title").textContent.trim();
            const shape = node.querySelector("ellipse, polygon, path, rect");
            neighbours.set(label, {
                parents: new Set(), children: new Set(),
                // Preserve hollow nodes and the separate fill/border statuses.
                fill: shape?.getAttribute("fill") || "none",
                stroke: shape?.getAttribute("stroke") || "black",
            });
        });
        // Read the rendered edges, not the source \uses: the standard graph
        // removes transitive edges, and sector views omit nodes outside the view.
        graph.querySelectorAll(".edge > title").forEach(title => {
            const [source, target] = title.textContent.trim().split("->");
            if (neighbours.has(source) && neighbours.has(target)) {
                neighbours.get(target).parents.add(source);
                neighbours.get(source).children.add(target);
            }
        });

        function list(title, labels) {
            const column = document.createElement("section");
            const heading = document.createElement("h3");
            heading.textContent = title;
            column.append(heading);
            if (!labels.size) {
                const empty = document.createElement("p");
                empty.textContent = "None in this graph.";
                column.append(empty);
                return column;
            }
            const ul = document.createElement("ul");
            [...labels].sort().forEach(label => {
                const statement = document.getElementById(label);
                const sourceLink = statement.querySelector(".latex_link");
                const link = document.createElement("a");
                link.textContent = label;
                link.href = sourceLink.href;
                link.title = statement.querySelector(".thm_thmheading").textContent.replace(/\s+/g, " ").trim();
                link.addEventListener("click", event => {
                    // Keep open-in-new-tab and other normal link gestures.
                    if (event.button !== 0 || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
                    event.preventDefault();
                    openNode(label);
                });
                const {fill, stroke} = neighbours.get(label);
                const dot = document.createElement("span");
                dot.className = "dep-status-dot";
                dot.style.backgroundColor = fill === "none" ? "transparent" : fill;
                dot.style.borderColor = stroke;
                dot.title = "Same status colours as the graph node (see Legend).";
                dot.setAttribute("aria-hidden", "true");
                const li = document.createElement("li");
                li.append(dot, link);
                ul.append(li);
            });
            column.append(ul);
            return column;
        }

        neighbours.forEach(({parents, children}, label) => {
            const statement = document.getElementById(label);
            if (!statement) return;
            statement.querySelector(".dep-neighbours")?.remove();
            const panel = document.createElement("div");
            panel.className = "dep-neighbours";
            panel.title = "Direct connections shown in this graph (transitive edges are omitted).";
            panel.append(list("Depends on", parents), list("Used by", children));
            statement.append(panel);
        });
    }

    const renderer = d3.select(graph).graphviz();

    function enhanceGraph() {
        // d3-graphviz defaults to a maximum scale of 10. On a large graph
        // fitted to the viewport, that can still leave the labels unreadable.
        // Change the live zoom behavior; the renderer's option setter only
        // applies when that behavior is first created.
        const zoom = renderer.zoomBehavior();
        if (zoom) {
            const [min] = zoom.scaleExtent();
            zoom.scaleExtent([min, Infinity]);
        }
        populateNeighbours();
    }

    // The SVG and its zoom behavior are created asynchronously. A namespaced
    // listener leaves the upstream handlers intact. Also handle late loading.
    renderer.on("end.neighbours", enhanceGraph);
    enhanceGraph();
}());
