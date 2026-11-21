import NoEmbeddedEigenvalues.Transport.WeightedForcing.SaddleQuadraticRay
import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddLogSaddle

/-!
# Canonical logarithmic endpoint-ray bounds

Blueprint: `lem:dd-log-ray-bounds`.

The original saddle coefficient and canonical remainder gradients are used in
both strong Cartesian H¹ quotients. Their rectangle traces absorb the weaker
ray weights. The continuous value trace is identified pointwise; gradient traces
remain canonical transverse ACL traces, not raw ray evaluations.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Weighted value and canonical gradient traces on each actual rotated endpoint
ray, from the saddle jet alone. The radius may depend on the ray. -/
theorem dd_log_ray_bounds {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (k : Fin 4) (side : Bool) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
        contStream ω (rotatedQuarterEndpointRay k side r) /
          (Real.rpow r (3 / 2) : ℂ)) 2 (volume.restrict (Ioo 0 δ)) ∧
      ∀ j : Fin 2, MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
        interiorChartTrace (rotatedQuarterEndpointChart k side) (streamJet2 ω [j]) r /
          (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 δ)) := by
  let c := rotatedQuarterEndpointRay k side 0
  let C := rotatedQuarterEndpointChart k side
  obtain ⟨R, hR, a, hval, hgrad⟩ := dd_saddle_ray_quotients_h1 hlam hω hs c
    (quarterRayCenter_mem_saddleSet k side)
  let δ := min (R / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδ1 : δ < 1 := by linarith
  have hδR : 2 * δ < R := by
    have h := min_le_left (R / 4) (1 / 2)
    dsimp [δ]
    linarith
  have hval' : MemSobolevOn 1 (localDisk c R)
      (fun p ↦ (contStream ω p - saddleQuadratic c a p) / (localRadius c p ^ 3 : ℂ)) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_ofNat, Complex.ofReal_pow] using hval
  have hrv := (hval'.logarithmic_quarterRay_trace hδ hδ1.le hδR
    (t := 3 / 2) (by norm_num) k side).2
  have hraw : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      (contStream ω (rotatedQuarterEndpointRay k side r) -
        saddleQuadratic c a (rotatedQuarterEndpointRay k side r)) /
          (Real.rpow r (3 / 2) : ℂ)) 2 (volume.restrict (Ioo 0 δ)) := by
    apply hrv.ae_eq
    apply Eventually.of_forall
    intro r
    have hc : Continuous (fun t : ℝ ↦ contStream ω (C (r, t)) -
        saddleQuadratic c a (C (r, t))) :=
      ((continuous_contStream ω).sub (continuous_saddleQuadratic c a)).comp
        ((continuous_rotatedQuarterEndpointChart k side).comp
          (continuous_const.prodMk continuous_id))
    dsimp only [interiorChartTrace]
    rw [interiorSectionTrace_of_continuous hc]
    simp only [C, quarterRayChart_zero]
  refine ⟨δ, hδ, hδ1, ?_, fun j ↦ ?_⟩
  · apply (hraw.add (saddleQuadratic_log_quarterRay_value hδ1.le k side a)).ae_eq
    exact Eventually.of_forall fun r ↦ by
      simp only [Pi.add_apply]
      dsimp only [c]
      ring
  · have hg : MemSobolevOn 1 (localDisk c R) (fun p ↦
        (streamJet2 ω [j] p - classicalComplexJet [j] (saddleQuadratic c a) p) /
          (localRadius c p ^ 2 : ℂ)) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_two, Complex.ofReal_pow] using hgrad j
    obtain ⟨hgerm, hlp⟩ := hg.logarithmic_quarterRay_trace hδ hδ1.le hδR
      (t := 1 / 2) (by norm_num) k side
    have hr : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
        interiorChartTrace C (fun p ↦ streamJet2 ω [j] p -
          classicalComplexJet [j] (saddleQuadratic c a) p) r /
            (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 δ)) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using hlp
    apply (hr.add (saddleQuadratic_log_quarterRay_gradient hδ1.le k side a j)).ae_eq
    filter_upwards [hgerm] with r hgr
    have hc : Continuous (fun t : ℝ ↦
        classicalComplexJet [j] (saddleQuadratic c a) (C (r, t))) :=
      (continuous_first_saddleQuadratic c a j).comp
        ((continuous_rotatedQuarterEndpointChart k side).comp
          (continuous_const.prodMk continuous_id))
    have he := interiorSectionTrace_eq_sub_add hgr hc
    simp only [Pi.add_apply]
    dsimp only [interiorChartTrace] at he ⊢
    rw [he]
    simp only [C, quarterRayChart_zero]
    dsimp only [c]
    ring

end NoEmbeddedEigenvalues
