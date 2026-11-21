# Shared infrastructure status

[Project status](../../STATUS.md) · [Generated report](generated.md) ·
[Module map](../architecture.md)

## Reuse across sectors

The odd–odd route through
[Transport near the separatrix](../../blueprint/src/chapters/transport.tex)
is complete. The transport gains, cellwise H¹ from weighted forcing
(`lem:weighted-transport-h1`), and cylinder inversion
(`lem:cylinder-inverse`) are available for reuse. This does not establish
the mixed saddle jet or quotient domain; see [Mixed](mixed.md).

## Shared certificate work

The general Bernstein criterion (`lem:bernstein-positivity`) and logarithm
tools (`lem:log-bounds`, `lem:affine-in-log`) are proved in
[`Certificates/`](../../NoEmbeddedEigenvalues/Certificates/). The
[certificate chapter](../../blueprint/src/chapters/certificates.tex) separates
operator identities from sign claims. For both odd–odd endpoints
(`cert:dd-residual-lower`, `cert:dd-residual-upper`), Lean checks the
polynomial identities and the coefficient signs. The independent
[SymPy script](../../scripts/verify_dd_residual.py) reproduces the manuscript
data but is not used as evidence by Lean. See the
[digest notes](../../blueprint/src/chapters/notes.tex).

For the mixed sector, Lean checks `cert:robin` on five intervals and
`cert:odd-a` on six boxes. The latter uses `lem:bernstein-separable` to
check and reuse intermediate first-axis coefficient tables. The
[generator](../../scripts/verify_mixed_odd_a.py) reproduces the integer data
but is not used as proof evidence. For `cert:odd-b`, the power tables,
center value, logarithm reduction, and `cert:odd-b-small` are checked.
In `cert:odd-b-strips`, the two endpoints on each strip share a dyadic tree.
Lean checks the root power conversion once and verifies each scaled integer
midpoint split against its parent. The independent
[search script](../../scripts/verify_mixed_odd_b.py) produces the certificate
data; the Lean proof does not trust the script.
