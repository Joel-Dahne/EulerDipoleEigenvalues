import NoEmbeddedEigenvalues.QuarterRayCharts
import NoEmbeddedEigenvalues.LogarithmicRadialMass

/-!
# Subcritical logarithmic ray traces from Cartesian radial quotients

Blueprint: `lem:quarter-ray-radial-trace`.

An H¹ radial quotient has an actual L² Cartesian trace. Multiplication by the
continuous integer radius power identifies the trace of the unweighted function.
A positive residual power absorbs the radial logarithm.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- A Cartesian radial quotient fixes both the unweighted trace germ and its
subcritical logarithmic norm. No arbitrary gradient values on the ray are used. -/
theorem MemSobolevOn.logarithmic_quarterRay_trace {R δ t : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 2 * δ < R) (ht : t < n)
    (k : Fin 4) (side : Bool) {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevOn 1 (localDisk (rotatedQuarterEndpointRay k side 0) R)
      (fun p ↦ F p / (localRadius (rotatedQuarterEndpointRay k side 0) p ^ n : ℂ))) :
    (∀ᵐ r ∂volume.restrict (Ioo 0 δ),
      HasContinuousSectionGerm (fun s ↦ F (rotatedQuarterEndpointChart k side (r, s)))) ∧
    MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      interiorChartTrace (rotatedQuarterEndpointChart k side) F r /
      (Real.rpow r t : ℂ)) 2 (volume.restrict (Ioo 0 δ)) := by
  let c := rotatedQuarterEndpointRay k side 0
  let C := rotatedQuarterEndpointChart k side
  let Q := fun p ↦ F p / (localRadius c p ^ n : ℂ)
  have hU : IsOpen (localDisk c R) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hsub := quarterRayRectangle_subset_disk hδ hR k side
  have hQ : MemSobolevOn 1 (Ioo 0 δ ×ˢ Ioo (-δ) δ) (fun q ↦ Q (C q)) := by
    apply (hF.comp_quarterRayChart hU k side).mono
    exact (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans
      (image_subset_iff.mp hsub)
  obtain ⟨htrace, hT⟩ := hQ.hasInteriorChartTrace hδ (neg_neg_of_pos hδ) hδ
  have he : ∀ᵐ r ∂volume.restrict (Ioo 0 δ),
      HasContinuousSectionGerm (fun s ↦ F (C (r, s))) ∧
      interiorChartTrace C F r = (r : ℂ) ^ n * interiorChartTrace C Q r := by
    filter_upwards [htrace.ae_hasContinuousSectionGerm (neg_neg_of_pos hδ) hδ,
      ae_restrict_mem measurableSet_Ioo] with r hr hrI
    have hc : Continuous (fun s : ℝ ↦ (localRadius c (C (r, s)) ^ n : ℂ)) := by
      apply Continuous.pow
      apply Complex.continuous_ofReal.comp
      apply Continuous.comp (show Continuous (localRadius c) by unfold localRadius; fun_prop)
      exact (continuous_rotatedQuarterEndpointChart k side).comp
        (continuous_const.prodMk continuous_id)
    have hfun : (fun s ↦ F (C (r, s))) =
        (fun s ↦ (localRadius c (C (r, s)) ^ n : ℂ) * Q (C (r, s))) := by
      funext s
      have hp : 0 < localRadius c (C (r, s)) := by
        rw [localRadius_quarterRayChart]
        apply Real.sqrt_pos.mpr
        dsimp
        nlinarith only [sq_pos_of_pos hrI.1, sq_nonneg s]
      dsimp [Q]
      field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
    refine ⟨hfun.symm ▸ hr.mul_continuous hc, ?_⟩
    change interiorSectionTrace _ = _
    calc
      _ = interiorSectionTrace (fun s ↦
          (localRadius c (C (r, s)) ^ n : ℂ) * Q (C (r, s))) :=
        congrArg interiorSectionTrace hfun
      _ = _ := by
        rw [interiorSectionTrace_mul_continuous hr hc]
        simp only [C, c, quarterRayChart_zero, localRadius_quarterEndpointRay,
          abs_of_pos hrI.1, interiorChartTrace]
  refine ⟨he.mono fun _ h ↦ h.1, ?_⟩
  apply (memLp_logRadius_nat_mul_div hδ1 ht hT).ae_eq
  filter_upwards [he] with r hr
  rw [hr.2]
  ring

end NoEmbeddedEigenvalues
