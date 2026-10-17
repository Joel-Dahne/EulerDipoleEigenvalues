# Status

A short entry point, not a progress log. Read the relevant topic page before
working; update current priorities and blockers rather than appending history.

## Current phase

The first-pass review of the even–even blueprint is complete. No next proof
implementation has been selected. Candidate tasks are in the topic pages;
the review is not a complete independent audit of the mathematics.

## Overall state

- The Fourier/L² foundations and algebraic symmetry/sector reductions are
  formalized.
- The even–even exclusion has an assembly proof from admitted analytic inputs.
  Odd–odd and mixed exclusion proofs remain admitted.
- The main theorem is assembled from the sector exclusions; it is not yet an
  admission-free proof. A completed blueprint proof may still cite admissions.
- The reworked manuscript has its introduction through the main theorem;
  later sections remain placeholders.

## Topic pages

- [Even–even](docs/status/even-even.md): assembly, remaining routes and priorities.
- [Odd–odd](docs/status/odd-odd.md): unresolved weighted argument.
- [Mixed](docs/status/mixed.md): regularity, flux and coercivity route.
- [Shared infrastructure](docs/status/shared.md): analytic backlog, reusable
  foundations and cross-project tasks.

## Working constraints and references

**Proof-worker delegation remains paused at the user's request. Do not launch
workers unless the user asks to resume the experiment.** Operational details
are in [the tooling notes](docs/tooling/pi.md).

[AGENTS.md](AGENTS.md) gives the workflow and module layout. Node-by-node
formalization status belongs in the blueprint; mathematical gaps and corrections
belong in its [digest notes](blueprint/src/chapters/notes.tex). History is in Git.
Graph counts are deliberately not duplicated in these hand-maintained summaries.

## Validation baseline

The last recorded full Lean build passed, with the admitted inputs described
above. This documentation-only reorganization did not rerun Lean.
