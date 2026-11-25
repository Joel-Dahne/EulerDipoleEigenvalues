module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWeakGluing

/-! # Weighted normal-section estimates for the mixed vorticity trace -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Set MeasureTheory Filter

private theorem HasIntervalH1.cut_left {w r : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 0 w F D) (hr : r ≤ w) : HasIntervalH1 0 r F D := by
  have hμ := Measure.restrict_mono_set volume (Ioo_subset_Ioo_right hr : Ioo 0 r ⊆ Ioo 0 w)
  exact ⟨h.memLp_value.mono_measure hμ, h.memLp_derivative.mono_measure hμ,
    fun a b ha hab hb ↦ h.locally_absolutelyContinuous a b ha hab (hb.trans_le hr),
    h.hasDerivAt_ae.mono fun _ hx hm ↦ hx (Ioo_subset_Ioo_right hr hm)⟩

/-- Restrict a transverse ACL section to a normal interval of length `δ k`.
After dividing by `k`, the trace bound uses only `F/k` and the unweighted
normal derivative on the full section. -/
theorem HasIntervalH1.left_trace_div_weight_sq_le {w δ k : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 0 w F D) (hδ : 0 < δ) (hk : 0 < k) (hw : δ * k ≤ w) :
    ‖intervalH1Extension 0 w F D 0 / (Real.sqrt k : ℂ)‖ ^ 2 ≤
      (2 / δ) * (∫ u in Ioo 0 w, ‖F u / (k : ℂ)‖ ^ 2) +
        2 * δ * ∫ u in Ioo 0 w, ‖D u‖ ^ 2 := by
  have hpos := mul_pos hδ hk
  have hw0 := hpos.trans_le hw
  have hcut := h.cut_left hw
  have he := hcut.extension_unique hpos
    ((h.continuousOn_extension hw0).mono (Icc_subset_Icc_right hw))
    (fun _ hu ↦ h.extension_eq hw0 (Ioo_subset_Ioo_right hw hu)) (left_mem_Icc.mpr hpos.le)
  have hle := hcut.extension_sq_le hpos (left_mem_Icc.mpr hpos.le)
  rw [← he, sub_zero] at hle
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt hk.le]
  have hFi := h.memLp_value.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hDi := h.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hsub : Ioo 0 (δ * k) ≤ᵐ[volume] Ioo 0 w :=
    Eventually.of_forall (Ioo_subset_Ioo_right hw)
  have hFle := setIntegral_mono_set hFi (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub
  have hDle := setIntegral_mono_set hDi (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub
  calc
    _ ≤ ((2 / (δ * k)) * (∫ u in Ioo 0 w, ‖F u‖ ^ 2) +
          2 * (δ * k) * ∫ u in Ioo 0 w, ‖D u‖ ^ 2) / k :=
      div_le_div_of_nonneg_right (hle.trans (add_le_add
        (mul_le_mul_of_nonneg_left hFle (by positivity))
        (mul_le_mul_of_nonneg_left hDle (by positivity)))) hk.le
    _ = _ := by
      have hF : (∫ u in Ioo 0 w, ‖F u / (k : ℂ)‖ ^ 2) =
          (k ^ 2)⁻¹ * ∫ u in Ioo 0 w, ‖F u‖ ^ 2 := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun u ↦ by
          dsimp only
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, div_pow,
            div_eq_mul_inv, mul_comm]
      rw [hF]
      field_simp

/-- A canonical left-normal trace has finite mass with weight `1/k` provided
`F/k` is square integrable and a strip of width `δ*k` fits on each section. -/
theorem HasTransverseH1Trace.left_memLp_div_sqrt {a b w δ : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ} {k : ℝ → ℝ}
    (h : HasTransverseH1Trace a b 0 w 0 chart F T)
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 (F ∘ chart) D)
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hF : MemLp (fun q ↦ F (chart q) / (k q.1 : ℂ)) 2
      (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hδ : 0 < δ) (hk : Measurable k) (hk0 : ∀ a' ∈ Ioo a b, 0 < k a')
    (hkw : ∀ a' ∈ Ioo a b, δ * k a' ≤ w) :
    MemLp (fun a' ↦ T a' / (Real.sqrt (k a') : ℂ)) 2 (volume.restrict (Ioo a b)) := by
  let I := Ioo a b
  let J := Ioo (0 : ℝ) w
  let A (q : ℝ × ℝ) := ‖F (chart q) / (k q.1 : ℂ)‖ ^ 2
  let B (q : ℝ × ℝ) := ‖D q‖ ^ 2
  let μ := volume.restrict I
  let ν := volume.restrict J
  obtain ⟨G, hGm, hGF, hGL, hGD, hT⟩ := h.with_weak_snd hd hD
  have hA : Integrable A (μ.prod ν) := by
    rw [Measure.prod_restrict I J, ← Measure.volume_eq_prod]
    exact hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hB : Integrable B (μ.prod ν) := by
    rw [Measure.prod_restrict I J, ← Measure.volume_eq_prod]
    exact hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hGF' : ∀ᵐ s ∂μ, ∀ᵐ u ∂ν, G (s,u) = F (chart (s,u)) := by
    refine Measure.ae_ae_of_ae_prod (p := fun q ↦ G q = F (chart q)) ?_
    rw [Measure.prod_restrict I J, ← Measure.volume_eq_prod]
    exact hGF
  have hTL := ((hGD.l2_trace h.2.1 hGm hGL hD 0 h.2.2.1).1).ae_eq hT.symm
  have hsqrt := Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hk)
  have hm := hTL.aestronglyMeasurable.div₀ hsqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  refine (((hA.integral_prod_left).const_mul (2 / δ)).add
    ((hB.integral_prod_left).const_mul (2 * δ))).mono' (hm.norm.pow 2) ?_
  filter_upwards [hT, hGF', hGD.ae_hasIntervalH1 hGL hD,
    ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with s hs hsf hsl hsI
  simp only [Pi.div_apply, Pi.add_apply, Function.comp_apply]
  rw [hs, Real.norm_of_nonneg (sq_nonneg _)]
  have hle := hsl.left_trace_div_weight_sq_le hδ (hk0 s hsI) (hkw s hsI)
  have he : (∫ u in J, ‖G (s, u) / (k s : ℂ)‖ ^ 2) = ∫ u in J, A (s, u) :=
    integral_congr_ae (hsf.mono fun u hu ↦ by simp only [A, hu])
  rw [he] at hle
  exact hle

end EulerDipoleEigenvalues
