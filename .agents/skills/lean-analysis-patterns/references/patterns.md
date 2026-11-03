# Analysis patterns

Use only the sections relevant to the current obstruction. Theorem names are
search seeds, not promises about signatures in the pinned Mathlib.

## Representatives and carriers

Distinguish raw functions, a.e. equivalence classes, and chosen continuous or ACL
representatives. An a.e. identity does not determine values on a curve or an
exceptional orbit. Trace statements need the relevant trace theorem and
representative identification.

For `Lp.ext`, first obtain the pointwise or a.e. identity of representatives,
then use extensionality. Avoid one large simplifier call across quotient
coercions, `toLp`, and integrals. If a continuous representative is needed,
prove its a.e. agreement separately before evaluating it pointwise.

Use bundled `Lp` when completeness, inner products, or continuous linear maps
drive the argument. Use raw functions with `MemLp`/`eLpNorm` when local
formulas or weak derivatives dominate. Package the crossing where both
representations are already available.

Do not switch `EuclideanSpace ℝ (Fin d)` to `Fin d → ℝ` merely to simplify
elaboration: the latter's default norm is the sup norm, not the Euclidean norm.
Likewise, coordinate changes must transport measures and all derivative
indices, not only function values.

## Integrability and restricted measures

Carry genuine finiteness data such as `MemLp` or `Integrable`. Since
`ENNReal.toReal ∞ = 0`, an upper bound on `(eLpNorm f p μ).toReal` alone
does not prove that the underlying norm is finite.

A Bochner integral is totalized too. Its formal value alone is not evidence
that the intended analytic integral exists. Prove integrability before using
identities whose mathematical meaning requires it.

Restrict a `MemLp` fact to the desired domain first. For transport across a
rescaled or pushed-forward measure, prove the measure identity and its
finiteness conditions separately; do not hide both in a broad `simpa`.

For a bounded coefficient times an L² function, first prove the product is L².
For a quadratic integrand, combine the two L² factors by Hölder or the
inner-product integrability API. For finite arrays or matrices, entrywise
`Integrable.eval` and `eval_integral` can avoid rebuilding integration theory.

## Approximation and limits

Identify the topology actually needed by the consumer:

- L² convergence for bounded-coefficient product integrals;
- Sobolev convergence when derivatives enter;
- a trace theorem or stronger topology for boundary values.

Bounded continuous density in Lp is not smooth density in H² and supplies no
derivative or trace convergence by itself.

For bounded-coefficient quadratic forms, separate the difference of products
into two terms and control each by L² estimates. This can avoid pointwise
domination or smooth-density arguments when the consumer needs only integral
convergence.

If an a.e. subsequence is genuinely needed, search for
`tendstoInMeasure_of_tendsto_eLpNorm` and
`TendstoInMeasure.exists_seq_tendsto_ae`. Do not introduce a subsequence when
the desired conclusion already follows from strong norm convergence.

For an Lp density step, search for
`MemLp.exists_boundedContinuous_eLpNorm_sub_le`, checking exponent and measure
hypotheses. Prove the result for the approximants and bound both approximation
errors in the exact norm used by the target.

## Scalar algebra

Keep `Real.exp`, `Real.log`, `Real.rpow`, norms, and integrals opaque during
algebraic closure. Extract an equality or inequality over abstract real
variables, prove it with explicit sign/nonzero hypotheses, then substitute.

Prefer a short `calc` when facts are already available. Use `linarith only`
with a small input set; use `nlinarith` when the required nonlinear combination
warrants it, not as a blanket closer. Use targeted `field_simp` for a small
identity, then rewrite the main expression. Do not mechanically replace every
successful automation call.

For sums, reindexing, and telescoping, prove the exact finite identity first;
apply norm or absolute-value inequalities afterward. For real powers, handle
zero bases and zero exponents with their actual side conditions.

## Locality, constants, and interfaces

State the allowed dependence of each constant before constructing it.
`∀ x, ∃ C, P x C` does not supply `∃ C, ∀ x, P x C`. Inspect implicit
parameters and data bundles as well as explicit binders.

Keep local estimates distinct from their globalization. Check covering,
uniformity, overlap compatibility, and summability; the existence of local
witnesses alone does not produce a global finite norm.

Separate regularity, the algebraic differential identity, and integration or
boundary passage. A theorem for supplied quotient/trace data can be useful,
but the existence and compatibility of those data remain separate obligations.
