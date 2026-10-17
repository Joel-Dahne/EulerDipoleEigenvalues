# Tasks for the Lean project and its blueprint.
# Run `just` to list the available recipes.

default:
    @just --list

# Start shared Lean MCP server for Pi sessions/workers (keep running; localhost only).
lean-mcp:
    lean-lsp-mcp --transport streamable-http --host 127.0.0.1 --port 8765 --lean-project-path "$PWD"

# Build the Lean project
build:
    lake build

# Output in Manuscript/build. `just manuscript eigenvalues` builds the original manuscript.
# Build the reworked manuscript PDF and rebuild it whenever the source changes
manuscript file="manuscript":
    cd Manuscript && latexmk -pvc -pdf -pdflatex=xelatex -output-directory=build {{file}}.tex

# Build the blueprint website, including full and three sector dependency graphs
web:
    # With a Nix-installed plasTeX, the copied static files are read-only, which
    # makes rebuilds fail when they overwrite them.
    [ ! -d blueprint/web ] || chmod -R u+w blueprint/web
    leanblueprint web
    python3 scripts/blueprint_subgraph.py thm:ee-exclusion
    python3 scripts/blueprint_subgraph.py thm:dd-exclusion
    python3 scripts/blueprint_subgraph.py thm:mixed-exclusion

# Needs `just web` first; writes blueprint/web/dep_graph_<labels>.html.
# Dependency graph restricted to the given nodes and everything they depend on
graph +labels:
    python3 scripts/blueprint_subgraph.py {{labels}}

# Build the blueprint PDF (blueprint/print/print.pdf)
pdf:
    leanblueprint pdf

# Serve the built website at http://localhost:8000 (needs only python3)
serve:
    python3 -m http.server -d blueprint/web 8000

# Build the website and serve it
view: web serve

# Build both versions of the blueprint
blueprint: pdf web

# Check that every \lean{...} name in the blueprint exists (needs checkdecls in the lakefile)
checkdecls: build web
    leanblueprint checkdecls

# Remove generated blueprint files
clean:
    rm -rf blueprint/web blueprint/print
