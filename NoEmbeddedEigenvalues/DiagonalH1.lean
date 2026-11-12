import NoEmbeddedEigenvalues.DiagonalACL
import NoEmbeddedEigenvalues.AffineJets
import NoEmbeddedEigenvalues.WeightedTraces

/-!
# Ordinary H¹ in the diagonal trace charts

Blueprint: `lem:diagonal-h1-pullback`.

The diagonal map has absolute determinant two, not one. Its actual L²
pullback and the sum/difference weak chain rules supply ordinary H¹.
The other trace chart swaps the two parameter coordinates.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

theorem continuous_diagonalTraceChart (j : Fin 2) : Continuous (diagonalTraceChart j) := by
  fin_cases j
  · exact diagInv.continuous.comp continuous_swap
  · exact diagInv.continuous

theorem isOpenMap_diagonalTraceChart (j : Fin 2) : IsOpenMap (diagonalTraceChart j) := by
  fin_cases j
  · exact diagInv.toHomeomorph.isOpenMap.comp (Homeomorph.prodComm ℝ ℝ).isOpenMap
  · exact diagInv.toHomeomorph.isOpenMap

/-- The diagonal map preserves null sets in the direction needed for raw lifts. -/
theorem quasiMeasurePreserving_diagonalTraceChart (j : Fin 2) :
    Measure.QuasiMeasurePreserving (diagonalTraceChart j) volume volume := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hd : (diagInv.toContinuousLinearMap).det ≠ 0 := by
    change LinearMap.det (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0
    rw [det_diagInvLinear]
    norm_num
  have h := Measure.ContinuousLinearMap.quasiMeasurePreserving volume
    diagInv.toContinuousLinearMap hd
  fin_cases j
  · have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      rw [Measure.volume_eq_prod]
      exact Measure.measurePreserving_swap
    exact h.comp hs.quasiMeasurePreserving
  · exact h

/-- The specified Cartesian weak derivatives give both diagonal derivatives. -/
theorem MemSobolevOn.comp_diagInv {V : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevOn 1 V F) (hV : IsOpen V) :
    MemSobolevOn 1 (diagInv ⁻¹' V) (F ∘ diagInv) := by
  obtain ⟨Dx, hx, hDx⟩ := hF.2 0
  obtain ⟨Dy, hy, hDy⟩ := hF.2 1
  refine ⟨memLp_comp_diagInv hV.measurableSet hF.1, fun j ↦ ?_⟩
  fin_cases j
  · exact ⟨(fun p ↦ Dx p + Dy p) ∘ diagInv, hx.comp_diagInv_fst hV hy,
      memLp_comp_diagInv hV.measurableSet (hDx.add hDy)⟩
  · exact ⟨(fun p ↦ Dx p - Dy p) ∘ diagInv, hx.comp_diagInv_snd hV hy,
      memLp_comp_diagInv hV.measurableSet (hDx.sub hDy)⟩

/-- Ordinary H¹ pulls back to either actual diagonal trace chart. -/
theorem MemSobolevOn.comp_diagonalTraceChart {V : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevOn 1 V F) (hV : IsOpen V) (j : Fin 2) :
    MemSobolevOn 1 (diagonalTraceChart j ⁻¹' V) (F ∘ diagonalTraceChart j) := by
  have h := hF.comp_diagInv hV
  fin_cases j
  · let A := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    have hm : MeasurePreserving (planeAffine A 0) volume volume := by
      have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
        rw [Measure.volume_eq_prod]
        exact Measure.measurePreserving_swap
      convert hs using 1
      funext q
      simp [planeAffine_apply, A]
    have hs := h.comp_planeAffine A 0 hm (hV.preimage diagInv.continuous)
    simpa [Set.preimage, planeAffine_apply, A, diagonalTraceChart, Function.comp_def] using hs
  · exact h

end NoEmbeddedEigenvalues
