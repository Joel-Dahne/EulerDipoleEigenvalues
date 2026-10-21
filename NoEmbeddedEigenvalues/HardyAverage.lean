import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The L² Hardy averaging inequality

Blueprint: `lem:hardy-average`.

Nonnegative-integral infrastructure for the direct fractional trace estimate,
including its two height-averaging kernels.
Weighted Cauchy–Schwarz and dilation give the constant four, without an
integration-by-parts argument at the singular endpoint.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped ENNReal

/-- Cauchy–Schwarz, squared, for nonnegative integrals, including infinite values. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff]) hf hg
  have hh := pow_le_pow_left₀ zero_le h 2
  have hs (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [ENNReal.rpow_two, mul_pow, hs, Pi.mul_apply] using hh

/-- The weight in the dilation proof of Hardy's inequality has integral two. -/
theorem lintegral_inv_sqrt_unit :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ)))) = 2 := by
  have hi : IntegrableOn (fun s : ℝ ↦ s ^ (-(1 / 2 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(1 / 2 : ℝ))).1.mono_set
      Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs ↦ Real.rpow_nonneg hs.1.le _))]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
  norm_num

/-- Dilation on the positive half-line, in nonnegative-integral form. -/
theorem lintegral_Ioi_comp_mul {f : ℝ → ℝ≥0∞} (hf : Measurable f) {s : ℝ} (hs : 0 < s) :
    (∫⁻ r in Ioi 0, f (r * s)) = ENNReal.ofReal s⁻¹ * ∫⁻ r in Ioi 0, f r := by
  have he : (Ioi 0).indicator (fun r ↦ f (r * s)) =
      fun r ↦ (Ioi 0).indicator f (r * s) := by
    funext r
    by_cases hr : 0 < r
    · simp [hr, mul_pos hr hs]
    · have hn : ¬ 0 < r * s := by nlinarith
      simp [hr, hn]
  rw [← lintegral_indicator measurableSet_Ioi, he,
    ← lintegral_map (hf.indicator measurableSet_Ioi)
      (show Measurable (fun r : ℝ ↦ r * s) from measurable_id.mul_const s),
    Real.map_volume_mul_right hs.ne', lintegral_smul_measure,
    lintegral_indicator measurableSet_Ioi, abs_of_pos (inv_pos.mpr hs)]
  rfl

/-- Weighted Cauchy–Schwarz on the unit interval, with the integrable weight
`s^(-1/2)`. No finiteness assumption on `f` is needed. -/
theorem lintegral_unit_sq_le_weighted {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo 0 1, f s) ^ 2 ≤
      2 * ∫⁻ s in Ioo 0 1, ENNReal.ofReal s ^ (1 / 2 : ℝ) * f s ^ 2 := by
  let u := fun s ↦ ENNReal.ofReal s ^ (1 / 4 : ℝ) * f s
  let v := fun s ↦ ENNReal.ofReal s ^ (-(1 / 4 : ℝ))
  have hu : Measurable u := by fun_prop
  have hv : Measurable v := by fun_prop
  have h := lintegral_mul_sq_le hu.aemeasurable hv.aemeasurable
    (μ := volume.restrict (Ioo 0 1))
  have huv : (∫⁻ s in Ioo 0 1, u s * v s) = ∫⁻ s in Ioo 0 1, f s := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    change (ENNReal.ofReal s ^ (1 / 4 : ℝ) * f s) *
      ENNReal.ofReal s ^ (-(1 / 4 : ℝ)) = f s
    rw [mul_right_comm, ← ENNReal.rpow_add _ _
      (ENNReal.ofReal_ne_zero_iff.2 hs.1) ENNReal.ofReal_ne_top]
    norm_num
  have hu2 : ∀ s, u s ^ 2 = ENNReal.ofReal s ^ (1 / 2 : ℝ) * f s ^ 2 := by
    intro s
    simp only [u, mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hv2 : (∫⁻ s in Ioo 0 1, v s ^ 2) = 2 := by
    calc
      _ = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro s hs
        simp only [v, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        rw [show -(1 / 4 : ℝ) * 2 = -(1 / 2 : ℝ) by norm_num,
          ENNReal.ofReal_rpow_of_pos hs.1]
      _ = 2 := lintegral_inv_sqrt_unit
  rw [huv, hv2] at h
  simpa only [hu2, mul_comm] using h

/-- Hardy's averaging inequality on the positive half-line. -/
theorem lintegral_hardy_average_sq_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r in Ioi 0, (∫⁻ s in Ioo 0 1, f (r * s)) ^ 2) ≤
      4 * ∫⁻ r in Ioi 0, f r ^ 2 := by
  calc
    _ ≤ ∫⁻ r in Ioi 0, 2 * ∫⁻ s in Ioo 0 1,
        ENNReal.ofReal s ^ (1 / 2 : ℝ) * f (r * s) ^ 2 := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro r _
      exact lintegral_unit_sq_le_weighted (hf.comp (measurable_const.mul measurable_id))
    _ = 2 * ∫⁻ s in Ioo 0 1, ∫⁻ r in Ioi 0,
        ENNReal.ofReal s ^ (1 / 2 : ℝ) * f (r * s) ^ 2 := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_lintegral_swap]
      fun_prop
    _ = 2 * ∫⁻ s in Ioo 0 1, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ∫⁻ r in Ioi 0, f r ^ 2 := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioi_comp_mul (hf.pow_const 2) hs.1,
        ← mul_assoc, ENNReal.ofReal_rpow_of_pos hs.1,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
      congr 2
      rw [← Real.rpow_neg_one s, ← Real.rpow_add hs.1]
      norm_num
    _ = 4 * ∫⁻ r in Ioi 0, f r ^ 2 := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_inv_sqrt_unit]
      ring

/-- A normalized integral on `(0,r)` is its unit-interval dilation average. -/
theorem lintegral_unit_comp_mul {f : ℝ → ℝ≥0∞} (hf : Measurable f) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioo 0 1, f (r * s)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ t in Ioo 0 r, f t := by
  have h := lintegral_Ioi_comp_mul
    (hf.indicator (measurableSet_Ioo (a := 0) (b := r))) hr
  have he : (Ioi 0).indicator (fun s ↦ (Ioo 0 r).indicator f (s * r)) =
      (Ioo 0 1).indicator (fun s ↦ f (r * s)) := by
    funext s
    by_cases hs0 : 0 < s
    · by_cases hs1 : s < 1
      · have hsr : s * r ∈ Ioo 0 r := ⟨mul_pos hs0 hr, by nlinarith⟩
        rw [indicator_of_mem (s := Ioi 0) hs0, indicator_of_mem hsr,
          indicator_of_mem (show s ∈ Ioo 0 1 from ⟨hs0, hs1⟩), mul_comm]
      · have hsr : s * r ∉ Ioo 0 r := by intro h; nlinarith [h.2]
        simp [hs0, hs1, hsr]
    · simp [hs0]
  have he2 : (Ioi 0).indicator ((Ioo 0 r).indicator f) = (Ioo 0 r).indicator f := by
    rw [indicator_indicator, inter_eq_right.2 (fun s hs ↦ hs.1)]
  rw [← lintegral_indicator measurableSet_Ioi, he, lintegral_indicator measurableSet_Ioo,
    ← lintegral_indicator measurableSet_Ioi, he2, lintegral_indicator measurableSet_Ioo] at h
  exact h

/-- Hardy's inequality in normalized primitive form, with constant four. -/
theorem lintegral_hardy_sq_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r in Ioi 0, (ENNReal.ofReal r⁻¹ * ∫⁻ s in Ioo 0 r, f s) ^ 2) ≤
      4 * ∫⁻ r in Ioi 0, f r ^ 2 := by
  calc
    _ = ∫⁻ r in Ioi 0, (∫⁻ s in Ioo 0 1, f (r * s)) ^ 2 := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [lintegral_unit_comp_mul hf hr]
    _ ≤ _ := lintegral_hardy_average_sq_le hf

/-- The complex integral primitive version of Hardy's inequality. -/
theorem lintegral_sq_primitive_div_sq_le {D : ℝ → ℂ} (hD : Measurable D) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (‖∫ t in (0 : ℝ)..r, D t‖ ^ 2 / r ^ 2)) ≤
      4 * ∫⁻ r in Ioi 0, ENNReal.ofReal (‖D r‖ ^ 2) := by
  calc
    _ ≤ ∫⁻ r in Ioi 0, (ENNReal.ofReal r⁻¹ *
        ∫⁻ t in Ioo 0 r, ENNReal.ofReal ‖D t‖) ^ 2 := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro r hr
      rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]
      have hi := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioo 0 r)) D
      simp only [← ofReal_norm] at hi
      have hreal : ‖∫ t in Ioo 0 r, D t‖ ^ 2 / r ^ 2 =
          (r⁻¹ * ‖∫ t in Ioo 0 r, D t‖) ^ 2 := by ring
      rw [hreal, ENNReal.ofReal_pow (mul_nonneg (inv_nonneg.2 hr.le) (norm_nonneg _)),
        ENNReal.ofReal_mul (inv_nonneg.2 hr.le)]
      gcongr
    _ ≤ 4 * ∫⁻ r in Ioi 0, (ENNReal.ofReal ‖D r‖) ^ 2 :=
      lintegral_hardy_sq_le (ENNReal.measurable_ofReal.comp hD.norm)
    _ = _ := by simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- The primitive Hardy inequality is insensitive to null-set changes. -/
theorem lintegral_sq_primitive_div_sq_le_of_integrable {D : ℝ → ℂ} (hD : Integrable D) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (‖∫ t in (0 : ℝ)..r, D t‖ ^ 2 / r ^ 2)) ≤
      4 * ∫⁻ r in Ioi 0, ENNReal.ofReal (‖D r‖ ^ 2) := by
  let M := hD.aestronglyMeasurable.mk D
  have hM : Measurable M := hD.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : D =ᵐ[volume] M := hD.aestronglyMeasurable.ae_eq_mk
  have hi : ∀ r, (∫ t in (0 : ℝ)..r, D t) = ∫ t in (0 : ℝ)..r, M t :=
    fun r ↦ intervalIntegral.integral_congr_ae (he.mono (fun _ ht _ ↦ ht))
  simp_rw [hi]
  refine (lintegral_sq_primitive_div_sq_le hM).trans_eq ?_
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with r hr
  rw [hr]

/-- Dilation of the inverse-square weighted nonnegative integral. -/
theorem lintegral_Ioi_inv_sq_comp_mul {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ r in Ioi 0, (ENNReal.ofReal r⁻¹) ^ 2 * f (r * c)) =
      ENNReal.ofReal c * ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * f t := by
  have hfac : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ =
      ENNReal.ofReal c * ENNReal.ofReal (r * c)⁻¹ := by
    intro r hr
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  calc
    _ = ∫⁻ r in Ioi 0, (ENNReal.ofReal c) ^ 2 *
        ((ENNReal.ofReal (r * c)⁻¹) ^ 2 * f (r * c)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hfac r hr, mul_pow, mul_assoc]
    _ = (ENNReal.ofReal c) ^ 2 * (ENNReal.ofReal c⁻¹ *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * f t) := by
      rw [lintegral_const_mul _ (by fun_prop),
        lintegral_Ioi_comp_mul
          (f := fun t ↦ (ENNReal.ofReal t⁻¹) ^ 2 * f t) (by fun_prop) hc]
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_mul (sq_nonneg c)]
      have he : c ^ 2 * c⁻¹ = c := by field_simp
      rw [he]

/-- Averaging heights between one and two times the separation costs at most
`1/c` in the unweighted integral. -/
theorem lintegral_band_average_le {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ r in Ioi 0, ∫⁻ s in Ioo (1 : ℝ) 2, f (r * c * s)) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ t in Ioi 0, f t := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ = ∫⁻ s in Ioo (1 : ℝ) 2, ENNReal.ofReal (c * s)⁻¹ * ∫⁻ t in Ioi 0, f t := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      simp_rw [mul_assoc]
      exact lintegral_Ioi_comp_mul hf (mul_pos hc (by linarith [hs.1]))
    _ ≤ ∫⁻ _ in Ioo (1 : ℝ) 2, ENNReal.ofReal c⁻¹ * ∫⁻ t in Ioi 0, f t := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro s hs
      gcongr
      nlinarith [hs.1]
    _ = _ := by norm_num [Real.volume_Ioo]

/-- The same averaging with inverse-square weights costs `3c/2`. -/
theorem lintegral_band_average_inv_sq {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ r in Ioi 0, ∫⁻ s in Ioo (1 : ℝ) 2,
      (ENNReal.ofReal r⁻¹) ^ 2 * f (r * c * s)) =
      ENNReal.ofReal (3 / 2 * c) *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * f t := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ = ∫⁻ s in Ioo (1 : ℝ) 2, ENNReal.ofReal (c * s) *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * f t := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      simp_rw [mul_assoc]
      exact lintegral_Ioi_inv_sq_comp_mul hf (mul_pos hc (by linarith [hs.1]))
    _ = (∫⁻ s in Ioo (1 : ℝ) 2, ENNReal.ofReal (c * s)) *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * f t := by
      rw [lintegral_mul_const _ (by fun_prop)]
    _ = _ := by
      congr 1
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun s : ℝ ↦ c * s)
        (μ := volume.restrict (Ioo 1 2))
        (show IntegrableOn (fun s : ℝ ↦ c * s) (Ioo 1 2) volume from
          (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self)
        ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs ↦
          mul_nonneg hc.le (by linarith [hs.1])))]
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), integral_id]
      congr 1
      ring

end NoEmbeddedEigenvalues
