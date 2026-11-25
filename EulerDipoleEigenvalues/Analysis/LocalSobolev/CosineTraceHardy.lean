module

public import EulerDipoleEigenvalues.Analysis.Inequalities.IntervalHardy
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWeakGluing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Cosine division with zero canonical traces -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Real
open scoped ENNReal

/-- The normal cosine is comparable to the distance to the near endpoint
on each half of the interval. Apply the primitive Hardy bound from that
endpoint, using its canonical zero value. -/
theorem HasIntervalH1.lintegral_div_cos_sq {F D : ℝ → ℂ}
    (hf : HasIntervalH1 (-(π / 2)) (π / 2) F D)
    (hl : intervalH1Extension (-(π / 2)) (π / 2) F D (-(π / 2)) = 0)
    (hr : intervalH1Extension (-(π / 2)) (π / 2) F D (π / 2) = 0) :
    (∫⁻ x in Ioo (-(π / 2)) (π / 2), ENNReal.ofReal (‖F x‖ ^ 2 / cos x ^ 2)) ≤
      (2 * (ENNReal.ofReal ((π / 2) ^ 2) * 4)) *
      ∫⁻ x in Ioo (-(π / 2)) (π / 2), ENNReal.ofReal (‖D x‖ ^ 2) := by
  let c := π / 2
  let I := Ioo (-c) c
  let H := fun x ↦ ENNReal.ofReal (‖F x‖ ^ 2 / cos x ^ 2)
  let E := intervalZeroExtension (-c) c D
  let M := ∫⁻ x in I, ENNReal.ofReal (‖D x‖ ^ 2)
  let C := ENNReal.ofReal (c ^ 2)
  have hc : 0 < c := half_pos pi_pos
  have hc' : -c < c := by linarith
  have hi : Integrable E := integrable_intervalZeroExtension hf.memLp_derivative
  have hM : (∫⁻ x, ENNReal.ofReal (‖E x‖ ^ 2)) = M := by
    dsimp only [M, I]
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ I <;> simp [E, I, intervalZeroExtension, hx]
  have hind (P : ℝ → ℝ) (hP : MeasurePreserving P volume volume) (hEmb : MeasurableEmbedding P) :
      (∫⁻ t in Ioo 0 c, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, E (P s)‖ ^ 2 / t ^ 2)) ≤
        4 * M := by
    refine (lintegral_mono_set (Ioo_subset_Ioi_self : Ioo 0 c ⊆ Ioi 0)).trans ?_
    refine (lintegral_sq_primitive_div_sq_le_of_integrable
      (hP.integrable_comp_of_integrable hi)).trans ?_
    gcongr
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_eq ?_
    exact (hP.lintegral_comp_emb hEmb (fun x ↦ ENNReal.ofReal (‖E x‖ ^ 2))).trans hM
  have hsin (t : ℝ) (ht : t ∈ Ioo 0 c) (z : ℂ) :
      ENNReal.ofReal (‖z‖ ^ 2 / sin t ^ 2) ≤ C * ENNReal.ofReal (‖z‖ ^ 2 / t ^ 2) := by
    have hs : 0 < sin t :=
      sin_pos_of_pos_of_lt_pi ht.1 (by dsimp [c] at ht; linarith [ht.2, pi_pos])
    have hst := mul_le_mul_of_nonneg_left (mul_le_sin ht.1.le ht.2.le) hc.le
    have htc : t ≤ c * sin t := by
      convert hst using 1
      dsimp [c]
      field_simp
    have hq := (sq_le_sq₀ ht.1.le (by positivity : 0 ≤ c * sin t)).2 htc
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ht.1)).2
    rw [mul_pow] at hq
    nlinarith only [mul_le_mul_of_nonneg_left hq (sq_nonneg ‖z‖)]
  have hleft : (∫⁻ x in Ioo (-c) 0, H x) ≤ C * (4 * M) := by
    rw [← setLIntegral_Ioo_comp_add_right H (-c) (-c) 0, sub_self, zero_sub, neg_neg]
    refine (setLIntegral_mono' measurableSet_Ioo (f := fun t ↦ _)
      (g := fun t ↦ C * ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, E (s + -c)‖ ^ 2 / t ^ 2))
      fun t ht ↦ ?_).trans ?_
    · have hm : t + -c ∈ I := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hp : (∫ s in (0 : ℝ)..t, E (s + -c)) = F (t + -c) := by
        rw [intervalIntegral.integral_comp_add_right, zero_add,
          intervalIntegral_intervalZeroExtension D ⟨le_rfl, hc'.le⟩ (Ioo_subset_Icc_self hm),
          hf.integral_eq_extension_sub hc' ⟨le_rfl, hc'.le⟩ (Ioo_subset_Icc_self hm),
          hl, sub_zero, hf.extension_eq hc' hm]
      rw [hp]
      simpa only [H, ← sub_eq_add_neg, c, cos_sub_pi_div_two] using hsin t ht (F (t + -c))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact hind _ (measurePreserving_add_right volume (-c))
        (Homeomorph.addRight (-c)).measurableEmbedding
  have hright : (∫⁻ x in Ioo 0 c, H x) ≤ C * (4 * M) := by
    rw [← setLIntegral_Ioo_comp_sub_left H c 0 c, sub_self, sub_zero]
    refine (setLIntegral_mono' measurableSet_Ioo (f := fun t ↦ _)
      (g := fun t ↦ C * ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, E (c - s)‖ ^ 2 / t ^ 2))
      fun t ht ↦ ?_).trans ?_
    · have hm : c - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hp : (∫ s in (0 : ℝ)..t, E (c - s)) = - F (c - t) := by
        rw [intervalIntegral.integral_comp_sub_left, sub_zero,
          intervalIntegral_intervalZeroExtension D (Ioo_subset_Icc_self hm) ⟨hc'.le, le_rfl⟩,
          hf.integral_eq_extension_sub hc' (Ioo_subset_Icc_self hm) ⟨hc'.le, le_rfl⟩,
          hr, zero_sub, hf.extension_eq hc' hm]
      rw [hp, norm_neg]
      simpa only [H, c, cos_pi_div_two_sub] using hsin t ht (F (c - t))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact hind _ (Measure.measurePreserving_sub_left volume c)
        (Homeomorph.subLeft c).measurableEmbedding
  have hu : Ioo (-c) 0 ∪ Ioo 0 c = I \ {0} := by
    ext x
    simp only [mem_union, mem_Ioo, Set.mem_sdiff, mem_singleton_iff, I]
    constructor
    · rintro (hx | hx) <;>
        exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, by linarith [hx.1, hx.2]⟩
    · rintro ⟨hx, hx0⟩
      rcases lt_or_gt_of_ne hx0 with hp | hp
      · exact Or.inl ⟨hx.1, hp⟩
      · exact Or.inr ⟨hp, hx.2⟩
  change (∫⁻ x in I, H x) ≤ (2 * (C * 4)) * M
  calc
    _ = ∫⁻ x in Ioo (-c) 0 ∪ Ioo 0 c, H x := by
      rw [hu, Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton _))]
    _ ≤ _ := (lintegral_union_le H _ _).trans
      ((add_le_add hleft hright).trans_eq (by rw [← two_mul]; ac_rfl))

/-- An absolutely continuous complex trace with zero endpoint values and an
`L²` derivative remains square integrable after division by the cosine. -/
theorem memLp_div_cos_of_ac {F : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval F (-(π / 2)) (π / 2))
    (hD : MemLp (deriv F) 2 (volume.restrict (Ioo (-(π / 2)) (π / 2))))
    (hl : F (-(π / 2)) = 0) (hr : F (π / 2) = 0) :
    MemLp (fun x ↦ F x / (cos x : ℂ)) 2 (volume.restrict (Ioo (-(π / 2)) (π / 2))) := by
  have hab : -(π / 2) < π / 2 := by linarith [pi_pos]
  let I := Ioo (-(π / 2)) (π / 2)
  have hc : ContinuousOn F (Icc (-(π / 2)) (π / 2)) := by
    simpa only [uIcc_of_le hab.le] using hf.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hm := (hc.mono Ioo_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  have hF : MemLp F 2 (volume.restrict I) :=
    MemLp.of_bound hm M ((ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦
      hM t (Ioo_subset_Icc_self ht))
  have hjet : HasIntervalH1 (-(π / 2)) (π / 2) F (deriv F) := by
    refine ⟨hF, hD, ?_, ?_⟩
    · intro a b ha hab' hb
      apply hf.mono
      rw [uIcc_of_le hab.le, uIcc_of_le hab']
      exact Icc_subset_Icc ha.le hb.le
    · filter_upwards [hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht h
      exact (ht (Icc_subset_uIcc (Ioo_subset_Icc_self h))).hasDerivAt
  have he (t : ℝ) (ht : t ∈ Icc (-(π / 2)) (π / 2)) :
      intervalH1Extension (-(π / 2)) (π / 2) F (deriv F) t = F t :=
    (hjet.extension_unique hab hc (fun _ _ ↦ rfl) ht).symm
  have hfin := (hjet.lintegral_div_cos_sq
    ((he _ ⟨le_rfl, hab.le⟩).trans hl) ((he _ ⟨hab.le, le_rfl⟩).trans hr)).trans_lt
      (ENNReal.mul_lt_top (by finiteness) (hD.integrable_norm_pow (by decide)).lintegral_lt_top)
  have hm' : AEStronglyMeasurable (fun x ↦ F x / (cos x : ℂ)) (volume.restrict I) :=
    hm.mul ((Complex.continuous_ofReal.comp continuous_cos).measurable.inv.aestronglyMeasurable)
      |>.congr (.of_forall fun x ↦ (div_eq_mul_inv _ _).symm)
  apply (memLp_two_iff_integrable_sq_norm hm').2
  refine ⟨hm'.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun t ↦ sq_nonneg _)]
  simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs] using hfin

/-- Two zero endpoint traces give square-integrability after division by the
normal cosine. This uses only the inward rectangle, not a reflected extension. -/
theorem HasTransverseH1Trace.memLp_div_cos_snd {l r : ℝ} {F D : ℝ × ℝ → ℂ}
    (hl : HasTransverseH1Trace l r (-(π / 2)) (π / 2) (-(π / 2)) id F (fun _ ↦ 0))
    (hr : HasTransverseH1Trace l r (-(π / 2)) (π / 2) (π / 2) id F (fun _ ↦ 0))
    (hD : HasWeakPartialOn (Ioo l r ×ˢ Ioo (-(π / 2)) (π / 2)) 1 F D)
    (hL : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo (-(π / 2)) (π / 2)))) :
    MemLp (fun p ↦ F p / (cos p.2 : ℂ)) 2
      (volume.restrict (Ioo l r ×ˢ Ioo (-(π / 2)) (π / 2))) := by
  let I := Ioo l r
  let J := Ioo (-(π / 2)) (π / 2)
  have h : -(π / 2) < π / 2 := by linarith [pi_pos]
  obtain ⟨G, hGm, hGF, hGL, hGD, hleft⟩ :=
    hl.with_weak_snd (by simpa only [Function.comp_id] using hD) hL
  obtain ⟨H, _, hHF, hHL, hHD, hright⟩ :=
    hr.with_weak_snd (by simpa only [Function.comp_id] using hD) hL
  have he := hGD.ae_trace_independent h hHD hGF hHF hGL hHL hL hL
  let C := 2 * (ENNReal.ofReal ((π / 2) ^ 2) * 4)
  have hbound : ∀ᵐ a ∂volume.restrict I,
      (∫⁻ b in J, ENNReal.ofReal (‖G (a, b)‖ ^ 2 / cos b ^ 2)) ≤
      C * ∫⁻ b in J, ENNReal.ofReal (‖D (a, b)‖ ^ 2) := by
    filter_upwards [hGD.ae_hasIntervalH1 hGL hL, he, hleft, hright] with a ha he hl hr
    apply ha.lintegral_div_cos_sq hl.symm
    exact (he (π / 2) ⟨h.le, le_rfl⟩).trans hr.symm
  have hfin : (∫⁻ p in I ×ˢ J, ENNReal.ofReal (‖G p‖ ^ 2 / cos p.2 ^ 2)) < ∞ := by
    have he : (∫⁻ p in I ×ˢ J, ENNReal.ofReal (‖G p‖ ^ 2 / cos p.2 ^ 2)) ≤
        C * ∫⁻ p in I ×ˢ J, ENNReal.ofReal (‖D p‖ ^ 2) := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
      rw [setLIntegral_prod _ (by
        rw [← Measure.volume_eq_prod]
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          (hL.aestronglyMeasurable.aemeasurable.norm.pow_const 2))]
      rw [← lintegral_const_mul' _ _ (by dsimp [C]; finiteness)]
      exact lintegral_mono_ae hbound
    exact he.trans_lt (ENNReal.mul_lt_top (by dsimp [C]; finiteness)
      (hL.integrable_norm_pow (by decide) |>.lintegral_lt_top))
  have hdiv : MemLp (fun p ↦ G p / (cos p.2 : ℂ)) 2 (volume.restrict (I ×ˢ J)) := by
    have hm : Measurable (fun p ↦ G p / (cos p.2 : ℂ)) := by fun_prop
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p ↦ sq_nonneg _)]
    simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs] using hfin
  exact hdiv.ae_eq (hGF.mono fun p hp ↦ congrArg (fun z ↦ z / (cos p.2 : ℂ)) hp)

end EulerDipoleEigenvalues
