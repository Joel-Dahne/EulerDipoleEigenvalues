import NoEmbeddedEigenvalues.DampedTransportEnergy

/-!
# Saddle-weighted canonical endpoint energy

Blueprint: `lem:transport-saddle-endpoint-energy`.

Exponential distance comparison converts the dissipative interval estimate to
inverse-square-distance mass. The forcing enters only through its actual
weighted L² norm; no pointwise forcing envelope is used. Endpoint values belong
to the specified ACL unknown, not a raw spatial representative.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- Exponentially comparable saddle distance converts canonical endpoint
energy to genuine inverse-square-distance L² mass. -/
theorem transport_saddle_endpoint_energy {L c C lam A : ℝ} {d : ℝ → ℝ}
    {W F : ℝ → ℂ} (hL : 0 ≤ L) (hc : 0 < c)
    (hdm : Measurable d)
    (hlo : ∀ t ∈ Icc (-L) L, c * exp (-|t|) ≤ d t)
    (hhi : ∀ t ∈ Icc (-L) L, d t ≤ C * exp (-|t|))
    (hW : ∀ a b, AbsolutelyContinuousOnInterval W a b)
    (hF : MemLp (fun t ↦ F t / (d t : ℂ) ^ 2) 2
      (volume.restrict (Icc (-L) L)))
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t)
    (hleft : ‖W (-L)‖ ≤ A) (hright : ‖W L‖ ≤ A) :
    MemLp (fun t ↦ W t / (d t : ℂ) ^ 2) 2 (volume.restrict (Icc (-L) L)) ∧
      (∫ t in Icc (-L) L, ‖W t / (d t : ℂ) ^ 2‖ ^ 2) ≤
        exp (4 * L) * A ^ 2 / c ^ 4 + C ^ 4 / (4 * c ^ 4) *
          ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2 := by
  have hd0 (t : ℝ) (ht : t ∈ Icc (-L) L) : 0 < d t :=
    (mul_pos hc (exp_pos _)).trans_le (hlo t ht)
  have he (t : ℝ) : exp (4 * |t|) * exp (-|t|) ^ 4 = 1 := by
    rw [← exp_nat_mul, ← exp_add]
    convert exp_zero using 1
    congr 1
    push_cast
    ring
  have hdl (t : ℝ) (ht : t ∈ Icc (-L) L) :
      c ^ 4 ≤ exp (4 * |t|) * d t ^ 4 := by
    have hb := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ c * exp (-|t|)) (hlo t ht) 4)
      (exp_pos (4 * |t|)).le
    simpa only [mul_pow, mul_left_comm (exp (4 * |t|)), ← mul_assoc, he, one_mul, mul_one]
      using hb
  have hdu (t : ℝ) (ht : t ∈ Icc (-L) L) :
      exp (4 * |t|) * d t ^ 4 ≤ C ^ 4 := by
    have hb := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hd0 t ht).le (hhi t ht) 4) (exp_pos (4 * |t|)).le
    simpa only [mul_pow, mul_left_comm (exp (4 * |t|)), ← mul_assoc, he, one_mul, mul_one]
      using hb
  have hn (H : ℝ → ℂ) (t : ℝ) (ht : t ∈ Icc (-L) L) :
      ‖H t / (d t : ℂ) ^ 2‖ ^ 2 = ‖H t‖ ^ 2 / d t ^ 4 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hd0 t ht), div_pow]
    ring
  have hFn (t : ℝ) (ht : t ∈ Icc (-L) L) :
      exp (4 * |t|) * ‖F t‖ ^ 2 ≤ C ^ 4 * ‖F t / (d t : ℂ) ^ 2‖ ^ 2 := by
    rw [hn F t ht]
    have hb := (le_div_iff₀ (pow_pos (hd0 t ht) 4)).2 (hdu t ht)
    convert mul_le_mul_of_nonneg_right hb (sq_nonneg ‖F t‖) using 1
    ring
  have hdcm : Measurable (fun t ↦ (d t : ℂ) ^ 2) :=
    (Complex.measurable_ofReal.comp hdm).pow_const 2
  have hFm : AEStronglyMeasurable F (volume.restrict (Icc (-L) L)) := by
    apply (hF.aestronglyMeasurable.mul hdcm.aestronglyMeasurable).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hd0 t ht).ne'))
  have hEm : AEStronglyMeasurable (fun t ↦ (exp (2 * |t|) : ℂ) * F t)
      (volume.restrict (Icc (-L) L)) :=
    (show Measurable (fun t : ℝ ↦ (exp (2 * |t|) : ℂ)) from by
      fun_prop).aestronglyMeasurable.mul hFm
  have hEn (t : ℝ) : ‖(exp (2 * |t|) : ℂ) * F t‖ ^ 2 =
      exp (4 * |t|) * ‖F t‖ ^ 2 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    rw [← exp_nat_mul]
    congr 2
    push_cast
    ring
  have hEF : MemLp (fun t ↦ (exp (2 * |t|) : ℂ) * F t) 2
      (volume.restrict (Icc (-L) L)) := by
    apply (memLp_two_iff_integrable_sq_norm hEm).2
    apply ((hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (C ^ 4)).mono'
      (hEm.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change |‖(exp (2 * |t|) : ℂ) * F t‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), hEn]
    exact hFn t ht
  obtain ⟨hi, hb⟩ := transport_weighted_endpoint_energy hL (by norm_num : (0 : ℝ) < 2)
    hW hEF hd hleft hright
  norm_num at hi hb
  have hWm : AEStronglyMeasurable W (volume.restrict (Icc (-L) L)) :=
    ((hW (-L) L).continuousOn.mono
      (by rw [uIcc_of_le (by linarith : -L ≤ L)])).aestronglyMeasurable measurableSet_Icc
  have hQm := hWm.div₀ hdcm.aestronglyMeasurable
  have hQle : ∀ᵐ t ∂(volume.restrict (Icc (-L) L)),
      ‖W t / (d t : ℂ) ^ 2‖ ^ 2 ≤ (1 / c ^ 4) * (exp (4 * |t|) * ‖W t‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hn W t ht]
    have hb : 1 / d t ^ 4 ≤ exp (4 * |t|) / c ^ 4 :=
      (div_le_div_iff₀ (pow_pos (hd0 t ht) 4) (pow_pos hc 4)).2
        (by simpa using hdl t ht)
    convert mul_le_mul_of_nonneg_right hb (sq_nonneg ‖W t‖) using 1 <;> ring
  have hQi : IntegrableOn (fun t ↦ ‖W t / (d t : ℂ) ^ 2‖ ^ 2) (Icc (-L) L) := by
    apply (hi.const_mul (1 / c ^ 4)).mono' (hQm.norm.pow 2)
    filter_upwards [hQle] with t ht
    change |‖W t / (d t : ℂ) ^ 2‖ ^ 2| ≤ _
    rwa [abs_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hQm).2 hQi, ?_⟩
  have hFi := hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hEFi : IntegrableOn (fun t ↦ exp (4 * |t|) * ‖F t‖ ^ 2) (Icc (-L) L) := by
    apply (hEF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    exact Eventually.of_forall hEn
  have hFI := integral_mono_ae hEFi (hFi.const_mul (C ^ 4))
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hFn t ht)
  rw [integral_const_mul] at hFI
  have hQI := integral_mono_ae hQi (hi.const_mul (1 / c ^ 4)) hQle
  rw [integral_const_mul] at hQI
  have hTotal : (∫ t in Icc (-L) L, exp (4 * |t|) * ‖W t‖ ^ 2) ≤
      exp (4 * L) * A ^ 2 +
        (C ^ 4 * ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2) / 4 := by
    have hs := hb.trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right hFI (by norm_num : (0 : ℝ) ≤ 4)))
    convert hs using 1
    ring
  calc _ ≤ (1 / c ^ 4) * (exp (4 * L) * A ^ 2 +
        (C ^ 4 * ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2) / 4) :=
      hQI.trans (mul_le_mul_of_nonneg_left hTotal (by positivity))
    _ = _ := by ring

/-- The corresponding fiber mass bound for the reconstructed field
`v = -(λ W + F)`. This is an identity of the canonical reconstruction;
transfer to a raw spatial representative is a separate a.e. step. -/
theorem transport_saddle_vorticity_energy {L c C lam A : ℝ} {d : ℝ → ℝ}
    {W F : ℝ → ℂ} (hL : 0 ≤ L) (hc : 0 < c)
    (hdm : Measurable d)
    (hlo : ∀ t ∈ Icc (-L) L, c * exp (-|t|) ≤ d t)
    (hhi : ∀ t ∈ Icc (-L) L, d t ≤ C * exp (-|t|))
    (hW : ∀ a b, AbsolutelyContinuousOnInterval W a b)
    (hF : MemLp (fun t ↦ F t / (d t : ℂ) ^ 2) 2
      (volume.restrict (Icc (-L) L)))
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t)
    (hleft : ‖W (-L)‖ ≤ A) (hright : ‖W L‖ ≤ A) :
    MemLp (fun t ↦ -((lam : ℂ) * W t + F t) / (d t : ℂ) ^ 2) 2
      (volume.restrict (Icc (-L) L)) ∧
      (∫ t in Icc (-L) L, ‖-((lam : ℂ) * W t + F t) / (d t : ℂ) ^ 2‖ ^ 2) ≤
        (2 * lam ^ 2 * exp (4 * L) / c ^ 4) * A ^ 2 +
        (lam ^ 2 * C ^ 4 / (2 * c ^ 4) + 2) *
          ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2 := by
  obtain ⟨hZ, hb⟩ := transport_saddle_endpoint_energy hL hc hdm hlo hhi hW hF hd hleft hright
  have hv : MemLp (fun t ↦ -((lam : ℂ) * W t + F t) / (d t : ℂ) ^ 2) 2
      (volume.restrict (Icc (-L) L)) := by
    convert ((hZ.const_mul (lam : ℂ)).add hF).neg using 1
    funext t
    simp only [Pi.neg_apply, Pi.add_apply]
    ring
  have hzi := hZ.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hfi := hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hvi := hv.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hpoint (t : ℝ) : ‖-((lam : ℂ) * W t + F t) / (d t : ℂ) ^ 2‖ ^ 2 ≤
      2 * lam ^ 2 * ‖W t / (d t : ℂ) ^ 2‖ ^ 2 +
        2 * ‖F t / (d t : ℂ) ^ 2‖ ^ 2 := by
    rw [neg_div, norm_neg, add_div, mul_div_assoc]
    have hn := norm_add_le ((lam : ℂ) * (W t / (d t : ℂ) ^ 2)) (F t / (d t : ℂ) ^ 2)
    have hs := sq_nonneg
      (‖(lam : ℂ) * (W t / (d t : ℂ) ^ 2)‖ - ‖F t / (d t : ℂ) ^ 2‖)
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hs hsq
    nlinarith [sq_abs lam]
  have hbound := integral_mono_ae hvi ((hzi.const_mul (2 * lam ^ 2)).add (hfi.const_mul 2))
    (Eventually.of_forall hpoint)
  dsimp only [Pi.add_apply] at hbound
  rw [integral_add (hzi.const_mul (2 * lam ^ 2)) (hfi.const_mul 2),
    integral_const_mul, integral_const_mul] at hbound
  refine ⟨hv, ?_⟩
  calc _ ≤ 2 * lam ^ 2 * (exp (4 * L) * A ^ 2 / c ^ 4 + C ^ 4 / (4 * c ^ 4) *
        ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2) +
        2 * ∫ t in Icc (-L) L, ‖F t / (d t : ℂ) ^ 2‖ ^ 2 :=
      hbound.trans (add_le_add
        (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * lam ^ 2)) le_rfl)
    _ = _ := by ring

end NoEmbeddedEigenvalues
