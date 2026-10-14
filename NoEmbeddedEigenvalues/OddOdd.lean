import NoEmbeddedEigenvalues.Sectors

/-!
# Odd–odd exclusion

The top-level statement of blueprint `thm:dd-exclusion`.
In particular, the renormalized virial identity remains an unresolved
mathematical and formalization gap; this statement does not resolve it.
-/

namespace NoEmbeddedEigenvalues

/-- An eigenfunction odd under both separatrix reflections vanishes
at every nonzero real spectral parameter. Proof pending. -/
theorem odd_odd_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false false ω) : ω = 0 := by
  sorry

end NoEmbeddedEigenvalues
