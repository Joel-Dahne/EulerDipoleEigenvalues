# Tasks for the Lean project and its blueprint.
# Run `just` to list the available recipes.

default:
    @just --list

# Build the Lean project
build:
    lake build

# Names may omit the `NoEmbeddedEigenvalues.` prefix; `--all` lists every admission.
# List the declarations with `sorry` (and project axioms) that Lean declarations depend on
sorries +args="main":
    lake -q build --log-level=error
    lake env lean --run scripts/SorryDeps.lean {{args}}

# Unsandboxed stand-in for `lake comparator` (Lean v4.35); reads `comparator.json` (~2 min).
# Check that `Solution.lean` proves the statements of `Challenge.lean`, and list admissions
challenge:
    lake -q build --log-level=error Challenge Solution
    lake env lean --run scripts/CheckChallenge.lean

# Output in Manuscript/build. `just manuscript eigenvalues` builds the original manuscript.
# Build the reworked manuscript PDF and rebuild it whenever the source changes
manuscript file="manuscript":
    cd Manuscript && latexmk -pvc -pdf -pdflatex=xelatex -output-directory=build {{file}}.tex

# Check blueprint labels, references and dependency cycles (Python 3 only)
check-blueprint:
    python3 scripts/check_blueprint.py

# Run regression tests for blueprint checking, status reporting and web build output
test-blueprint:
    python3 -m unittest discover -s scripts/tests -p 'test_*.py'

# Generate the source-only sector status report (no Lean or web build needed)
status-blueprint:
    python3 scripts/blueprint_status.py --output docs/status/generated.md

# Build the blueprint website quietly (use `just web --verbose` for full output)
web verbose="":
    #!/usr/bin/env bash
    set -euo pipefail
    case {{quote(verbose)}} in
        '') verbose=false ;;
        --verbose|-v) verbose=true ;;
        *) echo 'Usage: just web [--verbose|-v]' >&2; exit 2 ;;
    esac
    log=$(mktemp "${TMPDIR:-/tmp}/blueprint-web.XXXXXX")
    status=0
    if "$verbose"; then
        just --justfile {{quote(justfile())}} _web 2>&1 | tee "$log" || status=$?
    else
        just --justfile {{quote(justfile())}} _web >"$log" 2>&1 || status=$?
    fi
    if [ "$status" -ne 0 ]; then
        if ! "$verbose"; then tail -n 60 "$log" >&2; fi
        printf 'Web build failed. Full log: %s\n' "$log" >&2
        exit "$status"
    fi
    printf 'Web build passed (website, sector graphs, status report).\nLog: %s\n' "$log"

[private]
_web: check-blueprint
    # With a Nix-installed plasTeX, the copied static files are read-only, which
    # makes rebuilds fail when they overwrite them.
    [ ! -d blueprint/web ] || chmod -R u+w blueprint/web
    leanblueprint web
    python3 scripts/blueprint_subgraph.py thm:ee-exclusion
    python3 scripts/blueprint_subgraph.py thm:dd-exclusion
    python3 scripts/blueprint_subgraph.py thm:mixed-exclusion
    python3 scripts/blueprint_status.py --output docs/status/generated.md

# Needs `just web` first; writes blueprint/web/dep_graph_<labels>.html.
# Dependency graph restricted to the given nodes and everything they depend on
graph +labels:
    python3 scripts/blueprint_subgraph.py {{labels}}

# Build the blueprint PDF (blueprint/print/print.pdf)
pdf: check-blueprint
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
    rm -f docs/status/generated.md
