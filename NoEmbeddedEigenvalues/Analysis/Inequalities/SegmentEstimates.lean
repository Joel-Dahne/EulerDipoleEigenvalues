import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Estimates along segments

Blueprint: `lem:segment-estimate`, `lem:hyperbola-estimate`.

For a function `G(a, b)` that is absolutely continuous in `b` along almost every line
`a = const`, the fundamental theorem of calculus and Cauchy–Schwarz on the segment between
`b₀` and `β(a)` bound `|G(a, β(a)) - G(a, b₀)|²` by `|β(a) - b₀| ∫ |∂_b G(a, ·)|²`. This
controls restrictions to curves `b = β(a)` near the line `b = b₀` (the middle part of the
level traces at the separatrix) and, with `β(u) = h/u` and the weight `1/u`, the corner tails
(the hyperbola estimate). All estimates are lower integrals, so no integrability is assumed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped ENNReal

/-- One segment: if `f` is absolutely continuous on `[c, d]` with derivative `f'` a.e., then
    `|f(d) - f(c)|² ≤ (d - c) ∫_c^d |f'|²`. -/
theorem ofReal_norm_sub_sq_le {f f' : ℝ → ℂ} (hf' : Measurable f') {c d : ℝ} (hcd : c ≤ d)
    (hac : AbsolutelyContinuousOnInterval f c d)
    (hder : ∀ᵐ x ∂(volume.restrict (Ioo c d)), HasDerivAt f (f' x) x) :
    ENNReal.ofReal (‖f d - f c‖ ^ 2) ≤
      ENNReal.ofReal (d - c) * ∫⁻ x in Ioo c d, ENNReal.ofReal (‖f' x‖ ^ 2) := by
  rcases hcd.eq_or_lt with heq | hlt
  · simp [heq]
  by_cases hfin : ∫⁻ x in Ioo c d, ENNReal.ofReal (‖f' x‖ ^ 2) = ⊤
  · rw [hfin, ENNReal.mul_top (by simpa using hlt)]
    exact le_top
  have hint2 : Integrable (fun x ↦ ‖f' x‖ ^ 2) (volume.restrict (Ioo c d)) := by
    refine ⟨(hf'.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ by positivity)]
    exact lt_top_iff_ne_top.2 hfin
  have hL2 : MemLp f' 2 (volume.restrict (Ioo c d)) :=
    (memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).2 hint2
  have hL1 : IntegrableOn f' (Ioo c d) := hL2.integrable (by norm_num)
  have hII : IntervalIntegrable f' volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le).2 hL1
  have hFTC : (∫ x in c..d, f' x) = f d - f c := by
    refine complex_integral_eq_sub_of_ac hac hII ?_
    have h0 : ∀ᵐ v : ℝ, v ≠ c := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ v : ℝ, v ≠ d := by simp [ae_iff, measure_singleton]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hder, h0, h1] with v hv hv0 hv1 hvc
    rw [uIcc_of_le hlt.le] at hvc
    exact hv ⟨lt_of_le_of_ne hvc.1 (Ne.symm hv0), lt_of_le_of_ne hvc.2 hv1⟩
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioo c d))
    Real.HolderConjugate.two_two (f := fun _ ↦ (1 : ℝ)) (g := fun v ↦ ‖f' v‖)
    (Eventually.of_forall fun _ ↦ zero_le_one)
    (Eventually.of_forall fun v ↦ norm_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact memLp_const 1)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hf'.norm.aestronglyMeasurable).2 hint2)
  have hvol : (volume.restrict (Ioo c d)).real univ = d - c := by
    simp [Measure.real, Real.volume_Ioo, hlt.le]
  simp only [one_mul, Real.rpow_two, ← Real.sqrt_eq_rpow, integral_const,
    hvol, one_pow, smul_eq_mul, mul_one] at hCS
  have hI0 : 0 ≤ ∫ v in Ioo c d, ‖f' v‖ ^ 2 := integral_nonneg fun v ↦ by positivity
  have hnorm : ‖f d - f c‖ ≤ √(d - c) * √(∫ v in Ioo c d, ‖f' v‖ ^ 2) := by
    rw [← hFTC, intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo]
    exact (norm_integral_le_integral_norm _).trans hCS
  have hsq : ‖f d - f c‖ ^ 2 ≤ (d - c) * ∫ v in Ioo c d, ‖f' v‖ ^ 2 := by
    calc ‖f d - f c‖ ^ 2 ≤ (√(d - c) * √(∫ v in Ioo c d, ‖f' v‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hI0]
  calc ENNReal.ofReal (‖f d - f c‖ ^ 2)
      ≤ ENNReal.ofReal ((d - c) * ∫ v in Ioo c d, ‖f' v‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = _ := by
        rw [ENNReal.ofReal_mul (by linarith),
          ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun v ↦ by positivity)]

/-- The segment estimate on almost every line (`lem:segment-estimate`): if `b ↦ G(a, b)` is
    locally absolutely continuous on `(b₁, b₂)` with derivative `G_b` for almost every `a ∈ I`,
    and `b₀, β(a)` lie in `(b₁, b₂)`, then for almost every `a ∈ I`
    `|G(a, β(a)) - G(a, b₀)|² w(a) ≤ w(a) |β(a) - b₀| ∫_{b₁}^{b₂} |G_b(a, b)|² db`. The right
    side is measurable in `a` even when `G` is not. -/
theorem ae_segment_le {G Gb : ℝ × ℝ → ℂ} (hGb : Measurable Gb) {I : Set ℝ}
    (hI : MeasurableSet I) {b₁ b₂ b₀ : ℝ} {β w : ℝ → ℝ} (hb₀ : b₀ ∈ Ioo b₁ b₂)
    (hβ : ∀ a ∈ I, β a ∈ Ioo b₁ b₂) (hw : ∀ a ∈ I, 0 ≤ w a)
    (hG : ∀ᵐ a ∂(volume.restrict I),
      (∀ c d, b₁ < c → c ≤ d → d < b₂ → AbsolutelyContinuousOnInterval (fun b ↦ G (a, b)) c d) ∧
        ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)), HasDerivAt (fun b ↦ G (a, b)) (Gb (a, b)) b) :
    ∀ᵐ a ∂(volume.restrict I), ENNReal.ofReal (‖G (a, β a) - G (a, b₀)‖ ^ 2 * w a) ≤
      ENNReal.ofReal (w a * |β a - b₀|) * ∫⁻ b in Ioo b₁ b₂, ENNReal.ofReal (‖Gb (a, b)‖ ^ 2) := by
  filter_upwards [hG, ae_restrict_mem hI] with a ⟨hac, hder⟩ ha
  have hβa := hβ a ha
  have hm : Measurable fun b ↦ Gb (a, b) := hGb.comp (measurable_const.prodMk measurable_id)
  -- The segment between `b₀` and `β a`, in increasing order.
  set c := min b₀ (β a) with hcdef
  set d := max b₀ (β a) with hddef
  have hc : b₁ < c := lt_min hb₀.1 hβa.1
  have hd : d < b₂ := max_lt hb₀.2 hβa.2
  have hcd : c ≤ d := min_le_max
  have hseg := ofReal_norm_sub_sq_le hm hcd (hac c d hc hcd hd)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hc.le hd.le) hder)
  have hdc : d - c = |β a - b₀| := by
    rw [hcdef, hddef]
    rcases le_total b₀ (β a) with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (by linarith)]
      ring
  have hnorm : ‖G (a, β a) - G (a, b₀)‖ = ‖G (a, d) - G (a, c)‖ := by
    rw [hcdef, hddef]
    rcases le_total b₀ (β a) with h | h
    · rw [max_eq_right h, min_eq_left h]
    · rw [max_eq_left h, min_eq_right h, norm_sub_rev]
  calc ENNReal.ofReal (‖G (a, β a) - G (a, b₀)‖ ^ 2 * w a)
      = ENNReal.ofReal (w a) * ENNReal.ofReal (‖G (a, d) - G (a, c)‖ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), hnorm, mul_comm]
    _ ≤ ENNReal.ofReal (w a) * (ENNReal.ofReal |β a - b₀| *
          ∫⁻ b in Ioo b₁ b₂, ENNReal.ofReal (‖Gb (a, b)‖ ^ 2)) := by
        refine mul_le_mul' le_rfl (hseg.trans ?_)
        rw [hdc]
        exact mul_le_mul' le_rfl (lintegral_mono_set (Ioo_subset_Ioo hc.le hd.le))
    _ = _ := by rw [ENNReal.ofReal_mul (hw a ha), mul_assoc]

/-- The segment estimate (`lem:segment-estimate`), integrated over `a ∈ I`:
    `∫_I |G(a, β(a)) - G(a, b₀)|² w(a) da ≤ ∫_I w(a) |β(a) - b₀| ∫_{b₁}^{b₂} |G_b(a, b)|² db da`. -/
theorem lintegral_segment_le {G Gb : ℝ × ℝ → ℂ} (hGb : Measurable Gb) {I : Set ℝ}
    (hI : MeasurableSet I) {b₁ b₂ b₀ : ℝ} {β w : ℝ → ℝ} (hb₀ : b₀ ∈ Ioo b₁ b₂)
    (hβ : ∀ a ∈ I, β a ∈ Ioo b₁ b₂) (hw : ∀ a ∈ I, 0 ≤ w a)
    (hG : ∀ᵐ a ∂(volume.restrict I),
      (∀ c d, b₁ < c → c ≤ d → d < b₂ → AbsolutelyContinuousOnInterval (fun b ↦ G (a, b)) c d) ∧
        ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)), HasDerivAt (fun b ↦ G (a, b)) (Gb (a, b)) b) :
    ∫⁻ a in I, ENNReal.ofReal (‖G (a, β a) - G (a, b₀)‖ ^ 2 * w a) ≤
      ∫⁻ a in I, ENNReal.ofReal (w a * |β a - b₀|) *
        ∫⁻ b in Ioo b₁ b₂, ENNReal.ofReal (‖Gb (a, b)‖ ^ 2) :=
  lintegral_mono_ae (ae_segment_le hGb hI hb₀ hβ hw hG)

/-- The hyperbola estimate (`lem:hyperbola-estimate`): if `v ↦ F(u, v)` is absolutely
    continuous on `[0, u₀]` with derivative `F_v` for almost every `u`, then on the
    half-hyperbola `v = h/u`, `√h ≤ u ≤ u₀`,
    `∫ |F(u, h/u) - F(u, 0)|² du/u ≤ ∫_{(0,u₀)²} |F_v|²`. Each vertical segment has length
    `h/u`, and Cauchy–Schwarz gives the factor `h/u² ≤ 1`. -/
theorem lintegral_hyperbola_le {F Fv : ℝ × ℝ → ℂ} (hFv : Measurable Fv) {u₀ h : ℝ}
    (hh : 0 < h) (hu : √h ≤ u₀)
    (hF : ∀ᵐ u ∂(volume.restrict (Ioo 0 u₀)),
      AbsolutelyContinuousOnInterval (fun v ↦ F (u, v)) 0 u₀ ∧
        ∀ᵐ v ∂(volume.restrict (Ioo 0 u₀)), HasDerivAt (fun v ↦ F (u, v)) (Fv (u, v)) v) :
    ∫⁻ u in Ioo (√h) u₀, ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u) ≤
      ∫⁻ p in Ioo 0 u₀ ×ˢ Ioo 0 u₀, ENNReal.ofReal (‖Fv p‖ ^ 2) := by
  have hsq : 0 < √h := Real.sqrt_pos.2 hh
  have hsub : Ioo (√h) u₀ ⊆ Ioo 0 u₀ := Ioo_subset_Ioo_left hsq.le
  -- The pointwise bound on almost every vertical segment.
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioo (√h) u₀)),
      ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u) ≤
        ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hF,
      ae_restrict_mem measurableSet_Ioo] with u hFu hum
    obtain ⟨hac, hder⟩ := hFu
    have hu0 : 0 < u := hsq.trans hum.1
    set c := h / u with hc_def
    have hc0 : 0 < c := div_pos hh hu0
    have hsh : √h * √h = h := Real.mul_self_sqrt hh.le
    have hcs : c ≤ √h := by
      rw [hc_def, div_le_iff₀ hu0]
      nlinarith [hum.1]
    have hcu : c ≤ u₀ := hcs.trans hu
    have hcu1 : c / u ≤ 1 := by
      rw [div_le_one hu0]
      exact hcs.trans hum.1.le
    have hmono : ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) ≤
        ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
      lintegral_mono_set (Ioo_subset_Ioo_right hcu)
    by_cases hfin : ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) = ⊤
    · rw [hfin, top_le_iff] at hmono
      rw [hmono]
      exact le_top
    have hmeas : Measurable fun v ↦ Fv (u, v) := hFv.comp (measurable_const.prodMk measurable_id)
    have hint2 : Integrable (fun v ↦ ‖Fv (u, v)‖ ^ 2) (volume.restrict (Ioo 0 c)) := by
      refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ by positivity)]
      exact lt_top_iff_ne_top.2 hfin
    have hL2 : MemLp (fun v ↦ Fv (u, v)) 2 (volume.restrict (Ioo 0 c)) :=
      (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 hint2
    have hL1 : IntegrableOn (fun v ↦ Fv (u, v)) (Ioo 0 c) := hL2.integrable (by norm_num)
    have hII : IntervalIntegrable (fun v ↦ Fv (u, v)) volume 0 c :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hc0.le).2 hL1
    -- The fundamental theorem of calculus on `[0, c]`.
    have hFTC : (∫ v in (0 : ℝ)..c, Fv (u, v)) = F (u, c) - F (u, 0) := by
      refine complex_integral_eq_sub_of_ac (hac.mono ?_) hII ?_
      · rw [uIcc_of_le hc0.le, uIcc_of_le (hc0.le.trans hcu)]
        exact Icc_subset_Icc le_rfl hcu
      · have h0 : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
        have h1 : ∀ᵐ v : ℝ, v ≠ u₀ := by simp [ae_iff, measure_singleton]
        filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hder, h0, h1] with v hv hv0 hv1 hvc
        rw [uIcc_of_le hc0.le] at hvc
        exact hv ⟨lt_of_le_of_ne hvc.1 (Ne.symm hv0),
          lt_of_le_of_ne (hvc.2.trans hcu) hv1⟩
    -- Cauchy–Schwarz on the segment.
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioo 0 c))
      Real.HolderConjugate.two_two (f := fun _ ↦ (1 : ℝ)) (g := fun v ↦ ‖Fv (u, v)‖)
      (Eventually.of_forall fun _ ↦ zero_le_one)
      (Eventually.of_forall fun v ↦ norm_nonneg _)
      (by rw [ENNReal.ofReal_ofNat]; exact memLp_const 1)
      (by rw [ENNReal.ofReal_ofNat]
          exact (memLp_two_iff_integrable_sq hmeas.norm.aestronglyMeasurable).2 hint2)
    have hvol : (volume.restrict (Ioo 0 c)).real univ = c := by
      simp [Measure.real, Real.volume_Ioo, hc0.le]
    simp only [one_mul, Real.rpow_two, ← Real.sqrt_eq_rpow, integral_const,
      hvol, one_pow, smul_eq_mul, mul_one] at hCS
    have hnorm : ‖F (u, c) - F (u, 0)‖ ≤ √c * √(∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) := by
      rw [← hFTC, intervalIntegral.integral_of_le hc0.le, integral_Ioc_eq_integral_Ioo]
      exact (norm_integral_le_integral_norm _).trans hCS
    have hI0 : 0 ≤ ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := integral_nonneg fun v ↦ by positivity
    have hsq' : ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
      calc ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ (√c * √(∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hI0]
    have hdiv : ‖F (u, c) - F (u, 0)‖ ^ 2 / u ≤ ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
      rw [div_le_iff₀ hu0]
      calc ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := hsq'
        _ = (c / u) * (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) * u := by field_simp
        _ ≤ 1 * (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) * u := by gcongr
        _ = _ := by ring
    calc ENNReal.ofReal (‖F (u, c) - F (u, 0)‖ ^ 2 / u)
        ≤ ENNReal.ofReal (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) := ENNReal.ofReal_le_ofReal hdiv
      _ = ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun v ↦ by positivity)
      _ ≤ _ := hmono
  have hFm : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (‖Fv p‖ ^ 2) := by fun_prop
  calc ∫⁻ u in Ioo (√h) u₀, ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u)
      ≤ ∫⁻ u in Ioo (√h) u₀, ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
        lintegral_mono_ae hpt
    _ ≤ ∫⁻ u in Ioo 0 u₀, ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
        lintegral_mono_set hsub
    _ = ∫⁻ p in Ioo 0 u₀ ×ˢ Ioo 0 u₀, ENNReal.ofReal (‖Fv p‖ ^ 2) := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hFm.aemeasurable]

end NoEmbeddedEigenvalues
