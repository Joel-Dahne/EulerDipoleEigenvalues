/* Minimal DOM fixture; runnable in Node or any JavaScript engine.
 * Call testGraphNeighbours with blueprint/src/graph_neighbours.js as a string.
 */
function testGraphNeighbours(source) {
    function assert(condition, message) {
        if (!condition) throw new Error(message);
    }
    const run = new Function("document", "d3", "$", source);
    // Loading the shared extra script on chapter pages must be harmless.
    run({getElementById: () => null});

    class Element {
        constructor(tag) {
            this.tagName = tag;
            this.children = [];
            this.className = "";
            this.textContent = "";
            this.style = {};
            this.listeners = {};
            this.attributes = {};
        }
        append(...children) {
            children.forEach(child => { child.parent = this; this.children.push(child); });
        }
        querySelector(selector) {
            const selectors = selector.split(",").map(part => part.trim());
            for (const child of this.children) {
                if (selectors.some(part => part.startsWith(".")
                    ? child.className.split(" ").includes(part.slice(1))
                    : child.tagName === part)) return child;
                const match = child.querySelector(selector);
                if (match) return match;
            }
            return null;
        }
        remove() {
            this.parent.children = this.parent.children.filter(child => child !== this);
        }
        getAttribute(name) { return this.attributes[name] ?? null; }
        setAttribute(name, value) { this.attributes[name] = value; }
        addEventListener(type, listener) { this.listeners[type] = listener; }
        focus() { this.focused = true; }
    }
    const ids = new Map();
    function element(tag, className = "", id = null) {
        const node = new Element(tag);
        node.className = className;
        if (id) ids.set(id, node);
        return node;
    }
    const graph = element("div", "", "graph");
    const statements = element("div", "", "statements");
    const labels = ["def:root", "lem:a.b", "lem:other", "thm:target"];
    labels.forEach(label => {
        const statement = element("div", "thm", label);
        const heading = element("div", "thm_thmheading");
        heading.textContent = "Lemma  1.2\nExample title";
        const latex = element("a", "latex_link");
        latex.href = "chapter.html#" + label;
        statement.append(heading, latex);
        const content = element("div", "dep-modal-content");
        content.scrollTop = 300;
        content.append(element("button", "dep-closebtn"), statement);
        const modal = element("div", "dep-modal-container", label + "_modal");
        modal.append(content);
        statements.append(modal);
    });
    const document = {
        getElementById: id => ids.get(id) || null,
        createElement: tag => element(tag),
    };
    function jquery(selection) {
        let nodes;
        if (selection === "#statements > div") nodes = statements.children;
        else if (selection === "#statements") nodes = [statements];
        else if (selection === ".thm") nodes = labels.map(label => ids.get(label));
        else nodes = Array.isArray(selection) ? selection : [selection];
        return {
            hide() { nodes.forEach(node => { node.style.display = "none"; }); return this; },
            show() { nodes.forEach(node => { node.style.display = "block"; }); return this; },
            children() { return jquery(nodes.flatMap(node => node.children)); },
        };
    }
    const callbacks = {};
    let rendered = false;
    let zoomExtent = [0.1, 10];
    const zoom = {
        scaleExtent(extent) {
            if (extent === undefined) return zoomExtent;
            zoomExtent = extent;
            return this;
        },
    };
    const d3 = {select: () => ({graphviz: () => ({
        on: (event, callback) => { callbacks[event] = callback; },
        zoomBehavior: () => rendered ? zoom : null,
    })})};
    const edges = [
        "def:root->lem:a.b", "def:root->lem:other",
        "lem:other->thm:target", "lem:a.b->thm:target",
        "lem:a.b->thm:target", // Duplicate edges must not duplicate entries.
        "thm:target->thm:outside", // Sector views must stay inside the view.
    ];
    const colours = [
        ["polygon", "#B0ECA3", "green"], // Definition.
        ["ellipse", "#1CAC78", "green"], // Proof formalized.
        ["ellipse", "#A3D6FF", "blue"], // Statement formalized, proof not formalized.
        ["ellipse", "none", "#FFAA33"], // Hollow unfinished node.
    ];
    const renderedNodes = labels.map((label, index) => {
        const node = element("g", "node");
        const title = element("title");
        title.textContent = label;
        const [tag, fill, stroke] = colours[index];
        const shape = element(tag);
        shape.setAttribute("fill", fill);
        shape.setAttribute("stroke", stroke);
        node.append(title, shape);
        return node;
    });
    graph.querySelectorAll = selector => (rendered
        ? (selector === ".node" ? renderedNodes : edges.map(text => ({textContent: text})))
        : []);
    run(document, d3, jquery);
    assert(!ids.get("def:root").querySelector(".dep-neighbours"), "wait for async SVG");
    assert(callbacks["end.neighbours"], "register a namespaced graph-end callback");
    rendered = true;
    callbacks["end.neighbours"]();
    assert(zoomExtent[0] === 0.1 && zoomExtent[1] === Infinity,
        "remove the zoom-in cap after rendering without changing the zoom-out limit");

    function panel(label) { return ids.get(label).querySelector(".dep-neighbours"); }
    function links(label, column) {
        const list = panel(label).children[column].children[1];
        return list.tagName === "ul" ? list.children.map(li => li.querySelector("a")) : [];
    }
    assert(panel("def:root").children[0].children[0].textContent === "Depends on", "parent heading");
    assert(panel("def:root").children[1].children[0].textContent === "Used by", "child heading");
    assert(links("def:root", 0).length === 0, "root has no parents");
    assert(panel("def:root").children[0].children[1].textContent === "None in this graph.", "empty message");
    assert(links("def:root", 1).map(link => link.textContent).join() === "lem:a.b,lem:other", "sorted children");
    assert(links("thm:target", 0).map(link => link.textContent).join() === "lem:a.b,lem:other", "sorted deduplicated parents");
    assert(links("thm:target", 1).length === 0, "exclude neighbours outside sector");

    function dot(label, column, index = 0) {
        return panel(label).children[column].children[1].children[index].querySelector(".dep-status-dot");
    }
    assert(dot("thm:target", 0).style.backgroundColor === "#1CAC78", "copy proof fill colour");
    assert(dot("thm:target", 0).style.borderColor === "green", "copy proof border colour");
    assert(dot("thm:target", 0, 1).style.backgroundColor === "#A3D6FF", "copy statement-only fill colour");
    assert(dot("thm:target", 0, 1).style.borderColor === "blue", "preserve separate border status");
    assert(dot("lem:a.b", 0).style.backgroundColor === "#B0ECA3", "copy polygon definition colour");
    assert(dot("lem:a.b", 1).style.backgroundColor === "transparent", "keep hollow nodes hollow");
    assert(dot("lem:a.b", 1).style.borderColor === "#FFAA33", "copy unfinished border colour");
    assert(dot("thm:target", 0).getAttribute("aria-hidden") === "true", "decorative dot is hidden from screen readers");

    const link = links("thm:target", 0)[0];
    assert(link.href === "chapter.html#lem:a.b", "real chapter-link fallback");
    assert(link.title === "Lemma 1.2 Example title", "human-readable tooltip");
    let prevented = false;
    link.listeners.click({button: 0, ctrlKey: true, preventDefault() { prevented = true; }});
    assert(!prevented, "preserve modified link clicks");
    link.listeners.click({button: 0, preventDefault() { prevented = true; }});
    assert(prevented, "normal click opens a popup instead of navigating away");
    assert(ids.get("lem:a.b_modal").style.display === "block", "open neighbour modal using punctuation-safe ID");
    assert(ids.get("thm:target_modal").style.display === "none", "hide previous modal");
    assert(ids.get("lem:a.b").style.display === "block", "show neighbour statement");
    assert(statements.style.display === "block", "show popup wrapper");
    assert(ids.get("lem:a.b_modal").querySelector(".dep-modal-content").scrollTop === 0, "reset scroll");
    assert(ids.get("lem:a.b_modal").querySelector(".dep-closebtn").focused, "move keyboard focus to new popup");

    renderedNodes[1].querySelector("ellipse").setAttribute("fill", "#9CEC8B");
    callbacks["end.neighbours"]();
    assert(dot("thm:target", 0).style.backgroundColor === "#9CEC8B", "refresh colours after rerender");
    zoomExtent = [0.2, 10];
    run(document, d3, jquery); // Also support a graph rendered before script loading.
    assert(zoomExtent[0] === 0.2 && zoomExtent[1] === Infinity,
        "remove an already-rendered graph's zoom-in cap and preserve its minimum");
    assert(labels.every(label => ids.get(label).children.filter(child => child.className === "dep-neighbours").length === 1), "rerender does not duplicate panels");
    return "Graph neighbour DOM tests passed";
}
