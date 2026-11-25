module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedNumeratorAssembly
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.FirstBulkBoundaryBounds

/-! # Weighted numerator estimates

The original data definitions are reexported from `WeightedNumeratorData`.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Weighted numerator regularity with the quantitative bounds used downstream
(`lem:weighted-numerator-estimates`). No rotation character is needed here. -/
theorem weighted_numerator_estimates {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (_hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 U g D)
    (hf : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D [j] p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ Nonempty (WeightedQuarterNumeratorData lam U g D h₀) := by
  have hU := hp.isOrbitUnion.1
  have hgs := hp.memSobolevOn.congr_ae_on hU.measurableSet
    ((ae_restrict_iff' hU.measurableSet).1 hfg)
  have hgrad (j : Fin 2) : MemSobolevOn 1 U (D [j]) := by
    have hj : HasWeakPartialOn U j g (D [j]) := by
      simpa only [hD.1] using hD.2 [] (by simp) j
    exact hj.memSobolevOn hU hgs
  obtain ⟨d, K, hd, hK, hbd⟩ := quarter_first_bulk_boundary_sq_le hU hcell hgrad
  exact hp.weighted_numerator_data_of_boundary_bound hcell hg hfg hD hf hDf hd hK
    (hbd.mono fun _ hh ↦ hh lam)

end NoEmbeddedEigenvalues
