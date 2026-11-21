module

public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.CharacterExclusion

/-! # Even–even sector exclusion -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- An eigenfunction even under both separatrix reflections vanishes at every nonzero
    real spectral parameter, with no admitted dependencies. -/
theorem even_even_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true true ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, even_even_character_exclusion hlam hep hsp hkp,
    even_even_character_exclusion hlam hem hsm hkm, add_zero]

end NoEmbeddedEigenvalues
