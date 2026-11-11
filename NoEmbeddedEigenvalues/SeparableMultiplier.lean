import NoEmbeddedEigenvalues.TraceH2

/-!
# Integrable coordinate weights on H¹ rectangles

Blueprint: `lem:coordinate-weight-multiplier`.

The interval H¹ supremum estimate bounds a weighted section by its unweighted
value and derivative energies. Fubini supplies an integrable product majorant.
Only the coordinate weight, not the Sobolev function, must be globally measurable.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- An integrable nonnegative weight in the transverse coordinate is an H¹-to-L²
multiplier. The constant is explicit in the interval length and weight mass. -/
theorem HasWeakPartialOn.sqrt_weight_snd {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F D : ℝ × ℝ → ℂ} {w : ℝ → ℝ} (mw : Measurable w) (hw : ∀ t, 0 ≤ w t)
    (iw : IntegrableOn w (Ioo c d))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d))) :
    MemLp (fun p ↦ (Real.sqrt (w p.2) : ℂ) * F p) 2
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) ∧
    (∫ p in Ioo a b ×ˢ Ioo c d, w p.2 * ‖F p‖ ^ 2) ≤
      (∫ t in Ioo c d, w t) *
        ((2 / (d - c)) * (∫ p in Ioo a b ×ˢ Ioo c d, ‖F p‖ ^ 2) +
          2 * (d - c) * ∫ p in Ioo a b ×ˢ Ioo c d, ‖D p‖ ^ 2) := by
  let I := Ioo a b
  let J := Ioo c d
  let μ := volume.restrict I
  let ν := volume.restrict J
  have he : μ.prod ν = volume.restrict (I ×ˢ J) := by
    simp only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod]
  obtain ⟨G, mG, hGF, hACL, hrows, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) hcd hF hD
  have hG := hF.ae_eq hGF.symm
  have iG : Integrable (fun p ↦ ‖G p‖ ^ 2) (μ.prod ν) := by
    rw [he]
    exact hG.integrable_norm_pow (by norm_num)
  have iD : Integrable (fun p ↦ ‖D p‖ ^ 2) (μ.prod ν) := by
    rw [he]
    exact hD.integrable_norm_pow (by norm_num)
  let H := fun s ↦ (2 / (d - c)) * (∫ t, ‖G (s, t)‖ ^ 2 ∂ν) +
    2 * (d - c) * ∫ t, ‖D (s, t)‖ ^ 2 ∂ν
  have iH : Integrable H μ :=
    (iG.integral_prod_left.const_mul _).add (iD.integral_prod_left.const_mul _)
  have iHw : Integrable (fun p : ℝ × ℝ ↦ H p.1 * w p.2) (μ.prod ν) := iH.mul_prod iw
  have hbound : ∀ᵐ p ∂(μ.prod ν), ‖G p‖ ^ 2 ≤ H p.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrows,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)] with p hp hpJ
    have hh := hp.extension_sq_le hcd (Ioo_subset_Icc_self hpJ)
    rwa [hp.extension_eq hcd hpJ] at hh
  have hmajor : ∀ᵐ p ∂(μ.prod ν), ‖w p.2 * ‖G p‖ ^ 2‖ ≤ H p.1 * w p.2 := by
    filter_upwards [hbound] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw _) (sq_nonneg _)), mul_comm]
    exact mul_le_mul_of_nonneg_right hp (hw _)
  have iWG : Integrable (fun p ↦ w p.2 * ‖G p‖ ^ 2) (μ.prod ν) :=
    iHw.mono' ((mw.comp measurable_snd).mul (mG.norm.pow_const 2)).aestronglyMeasurable hmajor
  have hWG : MemLp (fun p ↦ (Real.sqrt (w p.2) : ℂ) * G p) 2
      (volume.restrict (I ×ˢ J)) := by
    apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
    rw [← he]
    convert iWG using 1
    funext p
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw _)]
  have hWF : MemLp (fun p ↦ (Real.sqrt (w p.2) : ℂ) * F p) 2
      (volume.restrict (I ×ˢ J)) := by
    apply hWG.ae_eq
    filter_upwards [hGF] with p hp
    rw [hp]
  refine ⟨hWF, ?_⟩
  have iWF : Integrable (fun p ↦ w p.2 * ‖F p‖ ^ 2) (μ.prod ν) := by
    apply iWG.congr
    rw [he]
    filter_upwards [hGF] with p hp
    rw [hp]
  have hineq := integral_mono_ae iWG iHw (hmajor.mono fun p hp ↦ (le_abs_self _).trans hp)
  have hiH : (∫ s, H s ∂μ) =
      (2 / (d - c)) * (∫ p in I ×ˢ J, ‖F p‖ ^ 2) +
        2 * (d - c) * ∫ p in I ×ˢ J, ‖D p‖ ^ 2 := by
    rw [integral_add (iG.integral_prod_left.const_mul _) (iD.integral_prod_left.const_mul _),
      integral_const_mul, integral_const_mul, ← integral_prod _ iG, ← integral_prod _ iD, he]
    congr 2
    apply integral_congr_ae
    filter_upwards [hGF] with p hp
    rw [hp]
  have hprod := integral_prod_mul (μ := μ) (ν := ν) H w
  rw [hprod, hiH, mul_comm] at hineq
  convert hineq using 1
  rw [← he]
  apply integral_congr_ae
  rw [he]
  filter_upwards [hGF] with p hp
  rw [hp]

/-- The same estimate for a weight in the first coordinate. -/
theorem HasWeakPartialOn.sqrt_weight_fst {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F D : ℝ × ℝ → ℂ} {w : ℝ → ℝ} (mw : Measurable w) (hw : ∀ t, 0 ≤ w t)
    (iw : IntegrableOn w (Ioo a b))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d))) :
    MemLp (fun p ↦ (Real.sqrt (w p.1) : ℂ) * F p) 2
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) ∧
    (∫ p in Ioo a b ×ˢ Ioo c d, w p.1 * ‖F p‖ ^ 2) ≤
      (∫ t in Ioo a b, w t) *
        ((2 / (b - a)) * (∫ p in Ioo a b ×ˢ Ioo c d, ‖F p‖ ^ 2) +
          2 * (b - a) * ∫ p in Ioo a b ×ˢ Ioo c d, ‖D p‖ ^ 2) := by
  have hU : IsOpen (Ioo a b ×ˢ Ioo c d) := isOpen_Ioo.prod isOpen_Ioo
  have hs : Prod.swap ⁻¹' (Ioo a b ×ˢ Ioo c d) = Ioo c d ×ˢ Ioo a b := by
    ext p; simp
  have hd' := hd.comp_swap_fst hU
  have hF' := memLp_comp_swap hU.measurableSet hF
  have hD' := memLp_comp_swap hU.measurableSet hD
  rw [hs] at hd' hF' hD'
  obtain ⟨hL, hE⟩ := hd'.sqrt_weight_snd hcd hab mw hw iw hF' hD'
  have hbck := memLp_comp_swap (measurableSet_Ioo.prod measurableSet_Ioo) hL
  have hs' : Prod.swap ⁻¹' (Ioo c d ×ˢ Ioo a b) = Ioo a b ×ˢ Ioo c d := by
    ext p; simp
  rw [hs'] at hbck
  refine ⟨hbck, ?_⟩
  rw [Measure.volume_eq_prod] at hE ⊢
  simpa only [← setIntegral_prod_swap (Ioo c d) (Ioo a b), Function.comp_apply,
    Prod.fst_swap, Prod.snd_swap, Prod.swap_swap] using hE

/-- Three genuine square-integrable products dominate a weight bounded by their
sum. This separates weight comparison from the coordinate slicing argument. -/
theorem memLp_sqrt_weight_of_le_sum {μ : Measure (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    {W u v : ℝ × ℝ → ℝ} (mW : Measurable W)
    (hW : ∀ p, 0 ≤ W p) (hu : ∀ p, 0 ≤ u p) (hv : ∀ p, 0 ≤ v p)
    (hbound : ∀ p, W p ≤ 1 + u p + v p)
    (hF : MemLp F 2 μ)
    (hFu : MemLp (fun p ↦ (Real.sqrt (u p) : ℂ) * F p) 2 μ)
    (hFv : MemLp (fun p ↦ (Real.sqrt (v p) : ℂ) * F p) 2 μ) :
    MemLp (fun p ↦ (Real.sqrt (W p) : ℂ) * F p) 2 μ := by
  have hn {w : ℝ × ℝ → ℝ} (hw : ∀ p, 0 ≤ w p) (p : ℝ × ℝ) :
      ‖(Real.sqrt (w p) : ℂ) * F p‖ ^ 2 = w p * ‖F p‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw _)]
  have iF := hF.integrable_norm_pow (by norm_num)
  have iFu := hFu.integrable_norm_pow (by norm_num)
  have iFv := hFv.integrable_norm_pow (by norm_num)
  simp_rw [hn hu] at iFu
  simp_rw [hn hv] at iFv
  have imajor := (iF.add iFu).add iFv
  have mWF : AEStronglyMeasurable (fun p ↦ (Real.sqrt (W p) : ℂ) * F p) μ :=
    (Complex.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp mW)).aestronglyMeasurable.mul
        hF.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm mWF).2
  apply imajor.mono' (mWF.norm.pow 2)
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Pi.pow_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hn hW]
  nlinarith [mul_le_mul_of_nonneg_right (hbound p) (sq_nonneg ‖F p‖)]

end NoEmbeddedEigenvalues
