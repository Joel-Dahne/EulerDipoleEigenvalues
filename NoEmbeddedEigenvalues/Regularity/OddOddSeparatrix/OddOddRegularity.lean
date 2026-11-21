module

public import NoEmbeddedEigenvalues.Regularity.SaddleEstimates.OddOddSaddle
public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddLogarithmic
public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddCellGradient
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.PeriodicWeightedGradient
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeightedElliptic
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.SaddleTaylorJet

/-! # Weighted gradient across an odd–odd cell collar -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Weak gradient with the extra saddle weight (`prop:dd-weighted-gradient`). -/
theorem dd_weighted_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        HasWeakPartialOn U j (liftL2 ω) (D j) ∧
        MemSobolevLocOn 0 U (fun p ↦ D j p / (saddleDist p : ℂ)) := by
  obtain ⟨U, hU, hsep, D, hD⟩ := dd_separatrix_weak_gradient hlam hω hs
  obtain ⟨b, hb, _, E, hE⟩ := dd_cell_weighted_gradient hlam hω hs
  obtain ⟨W, hW, hWsep, hWD⟩ := weighted_gradient_neighbourhood_of_cell hs
    (mul_pos (by norm_num : (0 : ℝ) < 2) hb) hU hsep
    (fun j ↦ (hD j).1) (fun j ↦ (hD j).2.1) ⟨E, hE⟩
  exact ⟨W, hW, hWsep, D, hWD⟩

end NoEmbeddedEigenvalues
