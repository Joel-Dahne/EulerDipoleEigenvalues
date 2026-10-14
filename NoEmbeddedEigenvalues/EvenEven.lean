import NoEmbeddedEigenvalues.Sectors

/-!
# Even–even exclusion

The top-level statement of blueprint `thm:ee-exclusion`.
The analytic sector argument is not yet formalized.
-/

namespace NoEmbeddedEigenvalues

/-- An eigenfunction even under both separatrix reflections vanishes
at every nonzero real spectral parameter. Proof pending. -/
theorem even_even_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true true ω) : ω = 0 := by
  sorry

end NoEmbeddedEigenvalues
