# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` is stated with an admitted proof. The blueprint review
has derived the weighted annular/truncated virial and its boundary signs;
these derivations are not yet in Lean. The full sector argument and its
regularity prerequisites have not been verified.

## Main priority when work resumes

Continue with the separatrix limit in `prop:dd-virial`: prove the weighted
quotient gradient traces and corner-tail estimates, then match the cutoff
finite parts to the edge forms. Review the quotient-domain hypotheses before
using them for this limit.

The annular L² identity transfers directly from the established unweighted
virial by multiplication by `s = Ψ`; no new weighted mollifier or global
quotient-domain theorem is needed there. The local Green identity yields
the manuscript's boundary integral, with `n = ∇s/√r` pointing inward.
The center boundary vanishes along a coarea-selected sequence using only
the original inverse-Laplacian regularity. See `lem:dd-weighted-first`
through `lem:dd-truncated-virial`.

Other inputs needing review include the quotient domain and saddle regularity,
the Picone/current argument, the weighted Poincaré inequality, and constants in
the corrected boundary estimate. The shared transport gains remain tentative;
unlike mixed, this sector uses only the existing ±1 rotation characters.
See [shared infrastructure](shared.md). Exact certificate verification is also pending.
The detailed questions live in the blueprint's digest notes.

The finite-part calculation retains the elliptic period formula and sharp
asymptotics. Both Hölder and finite-p embeddings remain dependencies of the
less-settled quotient argument pending review; do not remove them merely
because even–even does not need both.

## Where to work

- [Odd–odd blueprint](../../blueprint/src/chapters/odd_odd.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
