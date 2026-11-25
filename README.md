# No nonzero embedded eigenvalues for the linearized Euler dipole

This Lean development proves that the two-dimensional Euler equation
linearized around the dipole on the flat torus has no eigenvalue `iλ` for
nonzero real `λ`. The theorem is about the linearized operator on complex
`L²`, not nonlinear stability or the absence of a zero eigenvalue.

[Challenge.lean](Challenge.lean) is the statement to audit. Besides the main
theorem (`thm:main` in the blueprint), the five compared auxiliary theorems
identify the Fourier characters, compute their classical transport
derivatives, show that the mean-zero inverse Laplacian exists and is unique,
verify weak transport on characters, and exhibit a nonzero eigenfunction
with eigenvalue zero. The intentional placeholders in the Challenge are proved in
[Solution.lean](Solution.lean). [Comparator's configuration](comparator.json)
lists all six declarations and permits only the three standard Lean axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

## Source and scope

The source is Joel Dahne and Hao Jia's
[unpublished working manuscript](Manuscript/eigenvalues.tex), specifically
the theorem labelled `Intm6`. It was largely AI-generated and is preserved
as a historical reference, not as a checked proof or a paper intended for
publication in its present form.

The Lean development retains the reduction to four symmetry sectors and
the use of virial identities. The [blueprint](blueprint/README.md) documents
the proof actually formalized, including the regularity and boundary-limit
arguments and the exact-arithmetic sign certificates. It records differences
from the manuscript where they arise. The Challenge's weak Fourier formulation
uses transport of the vorticity plus stream; the blueprint identifies the
domain with the vorticity transport domain using `lem:L0-stream`.

## Build and check

With the pinned Lean toolchain available through [Elan](https://github.com/leanprover/elan):

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

A clean build can take a while. On a memory-constrained machine, start with
`LEAN_NUM_THREADS=2 lake build`. Comparator needs a supported sandbox and
more resources than a routine Lean check; use a larger machine for the full
run. The [local checks](STATUS.md#review-and-verification) are useful for
quicker feedback but do not replace Comparator.

To read the blueprint, follow the [local build guide](blueprint/README.md#building)
for HTML and PDF. See [docs/architecture.md](docs/architecture.md) for the
module map and [certificate generators](docs/architecture.md#source-checks-and-verification-tools).

## License

The original material in this repository, including the Lean code, scripts,
blueprint, and manuscript, is licensed under the [MIT License](LICENSE).
The [adapted agent skills](.agents/skills/ATTRIBUTION.md) retain their upstream
CC BY 4.0 terms.
