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

No exact certificate backend has been selected. The original verification
scripts and their output are not in the repository. The
[certificate chapter](../../blueprint/src/chapters/certificates.tex) separates
the operator identities from the sign claims; if using Bernstein subdivision,
both the polynomialization and the exact coefficient checks must be justified.
See the [digest notes](../../blueprint/src/chapters/notes.tex).
