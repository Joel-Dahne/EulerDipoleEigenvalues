# Tasks for the Lean project and its blueprint.
# Run `just` to list the available recipes.

default:
    @just --list

# Build the Lean project
build:
    lake build

# Build the manuscript PDF (Manuscript/build/eigenvalues.pdf) and rebuild it whenever the source changes
manuscript:
    cd Manuscript && latexmk -pvc -pdf -pdflatex=xelatex -output-directory=build eigenvalues.tex

# Build the blueprint website (blueprint/web), including the dependency graph
web:
    # With a Nix-installed plasTeX, the copied static files are read-only, which
    # makes rebuilds fail when they overwrite them.
    [ ! -d blueprint/web ] || chmod -R u+w blueprint/web
    leanblueprint web

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
