import NoEmbeddedEigenvalues.Sectors

/-!
# Mixed exclusion

The top-level statement of blueprint `thm:mixed-exclusion`, with its
analytic proof pending. The opposite mixed sector follows by quarter rotation.
-/

namespace NoEmbeddedEigenvalues

/-- An eigenfunction odd under S₁ and even under S₂ vanishes
at every nonzero real spectral parameter. Proof pending. -/
theorem mixed_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false true ω) : ω = 0 := by
  sorry

/-- The other mixed sector is excluded by rotating to the admitted mixed result. -/
theorem mixed_other_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true false ω) : ω = 0 := by
  apply rotate.injective
  rw [map_zero]
  exact mixed_exclusion lam hlam (rotate ω) hω.rotate hsector.rotate

end NoEmbeddedEigenvalues
