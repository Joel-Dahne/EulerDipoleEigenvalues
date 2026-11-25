# Absence of nonzero embedded eigenvalues for the linearized two-dimensional Euler equation around the symmetric dipole

In [*Dynamics of the linearized two-dimensional Euler equation around the
symmetric dipole*][companion-paper], Theorem 1.2 proves inviscid damping and vorticity depletion
under the assumption that the linearized operator has no nonzero embedded
eigenvalues. This repository proves that spectral assumption in Lean. It does
not formalize the damping or depletion estimates.

<!-- TODO: Replace ARXIV_ID with the companion paper's arXiv ID. -->
[companion-paper]: https://arxiv.org/abs/ARXIV_ID

## Background

We originally planned to leave the spectral exclusion as an assumption in
the paper. Numerical computations of the spectrum and simulations of the
long-time linearized flow gave us convincing evidence for it, but neither
constituted a proof. Shortly after GPT-6 Astra was released, we asked it to
prove the exclusion, and it produced a candidate proof. Ruling out
embedded eigenvalues is a spectral problem, and the argument uses different
tools from those used to prove the paper's damping and depletion estimates.
Rather than add a long, separate argument to the paper, we decided to
formalize the spectral result in Lean.

We kept the largely AI-generated [working manuscript](Manuscript/eigenvalues.tex)
unchanged as a historical record of the original argument (theorem `Intm6`).
The Lean development is not a line-by-line translation: some steps needed
extra hypotheses or estimates, and others were replaced. The blueprint
records what changed.

## AI-assisted formalization

This was our first experience formalizing a proof, and our workflow evolved
as we learned Lean. We used AI agents extensively to break the argument
into lemmas and to write and revise Lean proofs. The blueprint became the
map for that work: it tracked dependencies, linked lemmas to Lean, and
recorded gaps or changes to the original argument.

[AGENTS.md](AGENTS.md) records the instructions we developed for the agents,
from how to work through a blueprint lemma to how to report a gap in the
manuscript. The repository also includes the [Lean language-server setup
for Pi](docs/tooling/pi.md) and [guides for recurring Lean tasks](.agents/skills/README.md)
adapted from Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills).
See the [attribution notice](.agents/skills/ATTRIBUTION.md) for the source
revision and details of the adaptations.

The full Git history is preserved, so readers can see how both the proof
and the workflow evolved from the first commits.

We used a $20/month subscription for the Pi work over roughly two months.
Saved Pi sessions on the main development machine record about 2.07 billion
model tokens, or 76.5 million excluding repeated reads of cached input.
See [`formalization.yaml`](formalization.yaml) for the breakdown and scope.

## Main statement

On the square torus $\mathbb{T}^2=(\mathbb{R}/2\pi\mathbb{Z})^2$, the
symmetric dipole has stream function $\cos x+\cos y$. Write
$L_0=\sin y\,\partial_x-\sin x\,\partial_y$ for transport by its velocity
field. The linearized vorticity operator is $L=L_0(1+\Delta^{-1})$, where
$\Delta^{-1}$ is the mean-zero inverse Laplacian.

The theorem (`thm:main` in the blueprint) says that if $\lambda$ is real
and nonzero and a mean-zero $\omega\in L^2(\mathbb{T}^2;\mathbb{C})$ satisfies

$$
L_0(\omega+\Delta^{-1}\omega)=i\lambda\omega,
$$

then $\omega=0$. The equation is tested weakly against Fourier characters.
The Lean development proves that $L_0\Delta^{-1}\omega\in L^2$ (`lem:L0-stream`),
so requiring $L_0(\omega+\Delta^{-1}\omega)\in L^2$ gives the same domain
as requiring $L_0\omega\in L^2$ (`lem:reduction`). The restriction
$\lambda\ne0$ is essential: zero is an eigenvalue.

## Challenge and verification

[Challenge.lean](Challenge.lean) is the file to audit. It imports only
Mathlib and states the main theorem alongside five checks: the formula
for the Fourier characters, their classical transport derivatives,
existence and uniqueness of the mean-zero inverse Laplacian, agreement
of weak and classical transport on characters, and an example at
eigenvalue zero. Its placeholders are intentional; [Solution.lean](Solution.lean)
proves all six statements without admissions.

Lake Comparator checks that the statements agree, that the proofs use no
axioms beyond those permitted in [comparator.json](comparator.json)
(`propext`, `Classical.choice`, and `Quot.sound`), and that Lean's own
kernel and the independent Nanoda checker accept the solution.

To verify the solution locally, use [Elan](https://github.com/leanprover/elan)
with the pinned Lean toolchain and run these commands from the repository root:

```sh
lake exe cache get
lake build
lake comparator
```

A full Comparator run passed on a machine with 32 GB of RAM.

## Approach of the proof

Two reflection symmetries split the eigenvalue equation into four parity
sectors. A rotation exchanges the two mixed sectors, so only three cases
need separate proofs. In each case a virial identity uses the commutator
of transport with a first-order differential operator. The identities are
first used away from the separatrix, the boundary between the flow cells.
Transport and regularity estimates justify taking limits there. The resulting
bulk and boundary sign estimates force the eigenfunction to vanish.
Some of the coefficient inequalities are proved using exact-arithmetic
certificates: a Python script searches for bounds and subdivisions, and
Lean verifies the resulting inequalities and checks that the boxes cover
the required region.

The [blueprint](blueprint/README.md) gives the details and records where
the Lean proof departs from the working manuscript. Its
[local build guide](blueprint/README.md#building) covers HTML and PDF.
The [architecture guide](docs/architecture.md) describes the module layout
and the [certificate generators](docs/architecture.md#source-checks-and-verification-tools).

## License

The original material in this repository, including the Lean code, scripts,
blueprint, and manuscript, is licensed under the [MIT License](LICENSE).
The [adapted agent skills](.agents/skills/ATTRIBUTION.md) retain their upstream
CC BY 4.0 terms.
