# Statement and interface checklist

Read only as far as needed for the requested scope. A focused review need not
claim to audit an entire dependency closure.

## 1. Reconstruct the claim

Record the blueprint label, Lean declaration, relevant source locations,
agreed corrections, and any scope limitation. Write the intended premises,
conclusion, domains, and constant dependencies independently of the proof.

If the blueprint and manuscript disagree, identify the adopted correction or
ask the author. Do not silently select the version that is easier to prove.

## 2. Classify logical inputs

Expand project-owned structures, Prop aliases, and typeclasses enough to see
their logical content. For each mathematical input, identify whether it is:

- an intended premise;
- typing or standing data already part of the setup;
- an explicitly agreed correction/generalization;
- a proof obligation now being assumed;
- unclear and requiring review.

A proof obligation in a generic helper can be legitimate. It is not an
additional premise of the advertised endpoint merely because another theorem
could produce it: check that the endpoint actually applies that producer.

Check explicit and implicit binders, section variables, instance parameters,
and assumptions indexed by proof-carrying data. An unused source premise is
not automatically an error; investigate before proposing its removal.

## 3. Compare strength and scope

- Is the conclusion the whole blueprint claim, or only one assertion within it?
- Are universal and existential quantifiers in the correct order?
- Does a constant remain uniform in every parameter excluded from its allowed
  dependency set? Do several split statements require the same witness?
- Are local/global, pointwise/a.e., and classical/weak assertions distinguished?
- Are domains, open/closed endpoints, weights, normal directions, and scaling
  factors correct?
- Are parity, rotation character, mean-zero, and orthogonality hypotheses the
  intended ones?
- Does a stronger/generalized Lean statement have an explicit specialization
  that recovers the advertised result?

## 4. Inspect semantic definitions

Check the actual carriers, measures, Fourier normalizations, derivatives,
quotient construction, Sobolev tier, and trace representatives as applicable.

An a.e. class cannot be evaluated on an exceptional orbit or curve without
the relevant representative or trace bridge. A local finite norm is not a
global one. A formula involving a totalized inverse or integral needs its
intended interpretation checked.

Do not reject legitimate totalization or classical choice mechanically. Check
that the definition denotes the intended object on the domain used, and that
the required characterization and well-definedness are proved or explicitly
listed as obligations. A fallback chosen merely to conceal a missing
construction is not a resolution.

## 5. Check applications and evidence

For each interface under review, record where every nontrivial premise comes
from. Check matching witnesses, representatives, exceptional sets, constants,
domains, and normalization. Imports or blueprint edges alone do not prove
compatibility.

Distinguish four kinds of evidence:

- source comparison supports statement fidelity;
- successful Lean applications support interface compatibility;
- a local proof without `sorry` may still depend on admissions;
- a transitive admission/axiom check supports only its stated trust claim.

Blueprint markers are not an automatic Lean declaration, semantic, or axiom
audit. The project's Challenge checker compares statements and reports axioms;
it does not sandbox compilation or replay every proof in an independent kernel.

## Suggested report

- **Target:** blueprint title/label and exact Lean names.
- **Fidelity:** matches / mismatch / unresolved; explain the substantive inputs.
- **Compatibility:** exact applications checked, or explicitly not checked.
- **Proof status:** statement only / conditional assembly / local proof /
  transitive admission-freedom checked; name remaining inputs when known.
- **Evidence:** files inspected, checks and outputs, skipped checks.
- **Findings:** precise discrepancy, mathematical consequence, suggested next
  action, and whether author agreement is needed.

Keep a verified derivation, a numerical sanity check, and an informal argument
clearly distinguished. Do not label a theorem proved solely because its
statement matches the intended mathematics.
