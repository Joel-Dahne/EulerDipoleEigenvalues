# Odd–odd status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#odd-odd)
· [Blueprint chapter](../../blueprint/src/chapters/odd_odd.tex)

Odd–odd exclusion (`thm:dd-exclusion`) is assembled in
[OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean) with no admission of
its own. The geometry, odd–odd, and separatrix transport chapters have no
unfinished nodes on this route. The exclusion still depends on admitted
prerequisites.

The remaining work serves two parts of the argument:

- **Quotient existence:** the minimal domain (`cor:dd-exclusion-domain`)
  still depends on weighted elliptic regularity and division for the stream
  H² quotient. The stronger bundled quotient domain is not needed.
- **Bulk potential bound:** the odd–odd residual (`cert:dd-residual`) needs
  both the operator identity and the sign proof. See
  [shared certificate work](shared.md#shared-certificate-work).

Corrected-boundary nonnegativity and the bulk gradient bound are admission-free.
Use the generated report and graph for the exact prerequisite list.
