# Odd–odd status

[Project status](../../STATUS.md) · [Local status report](../../blueprint/README.md#generated-status-report)
· [Blueprint chapter](../../blueprint/src/chapters/odd_odd.tex)

Odd–odd exclusion (`thm:dd-exclusion`) is transitively admission-free. The
assembly is in [OddOdd.lean](../../EulerDipoleEigenvalues/OddOdd/Conclusion/OddOdd.lean).

The minimal quotient domain (`cor:dd-exclusion-domain`) is admission-free.
The stronger bundled quotient domain is not needed.

The bulk potential bound (`cert:dd-residual`) uses two exact Bernstein
certificates, one for each logarithm endpoint (`cert:dd-residual-lower` and
`cert:dd-residual-upper`). See [shared certificate work](shared.md#shared-certificate-work).

Corrected-boundary nonnegativity and the bulk gradient bound are admission-free.
Use the generated report and graph for the exact prerequisite list.
