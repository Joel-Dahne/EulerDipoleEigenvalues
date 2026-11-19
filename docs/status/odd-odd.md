# Odd–odd status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#odd-odd)
· [Blueprint chapter](../../blueprint/src/chapters/odd_odd.tex)

Odd–odd exclusion (`thm:dd-exclusion`) is assembled in
[OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean) with no admission of
its own. The geometry, odd–odd, and separatrix transport chapters have no
unfinished nodes on this route. The exclusion still depends on admitted
prerequisites.

The minimal quotient domain (`cor:dd-exclusion-domain`) is admission-free.
The stronger bundled quotient domain is not needed.

The remaining admission is the sign proof for the bulk potential bound
(`cert:dd-residual`). The identity linking the residual table to the actual
differential expression is proved in
[`Certificates/OddOdd.lean`](../../NoEmbeddedEigenvalues/Certificates/OddOdd.lean).
See [shared certificate work](shared.md#shared-certificate-work).

Corrected-boundary nonnegativity and the bulk gradient bound are admission-free.
Use the generated report and graph for the exact prerequisite list.
