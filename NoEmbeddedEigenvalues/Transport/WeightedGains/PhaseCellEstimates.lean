module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorFactor
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalLinearHardy
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalSecondHardy
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1Multipliers

/-!
# Uniform complete-cell division estimates

Blueprint: `lem:phase-cell-estimates`.

First divide the numerator by its linear zero. Multiply this H¹ quotient by the
smooth inverse linear divisor factor. The two Hardy bounds and the uniform
factor estimates give the value and derivative energies; level comparability
converts the second-derivative energy to the required `h²`-weighted energy.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

private theorem norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hs := (sq_le_sq₀ (norm_nonneg (x + y))
    (add_nonneg (norm_nonneg x) (norm_nonneg y))).2 (norm_add_le x y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Uniform complete-cell estimates (`lem:phase-cell-estimates`). The endpoints have
phase distance π from the central resonance. Constants are uniform over all cells,
numerators and four quarter characters; they may depend on lam. -/
theorem phase_cell_estimates {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 ∧
      ∀ (κ : ℂ), κ ^ 4 = 1 → ∀ (a z b : ℝ),
        0 < a → a < z → z < b → b < h₀ → quarterDivisor lam κ z = 0 →
        |quarterPhase lam a - quarterPhase lam z| = Real.pi →
        |quarterPhase lam b - quarterPhase lam z| = Real.pi →
        ∀ N N₁ N₂ : ℝ → ℂ, HasIntervalH2 a b N N₁ N₂ → N z = 0 →
          ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 a b Q Q₁ ∧
            (∀ h ∈ Ioo a b, quarterDivisor lam κ h * Q h = N h) ∧
            MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo a b)) ∧
            (∫ h in Ioo a b, ‖Q h / (h : ℂ)‖ ^ 2) ≤
              K * (∫ h in Ioo a b, ‖N₁ h‖ ^ 2) ∧
            (∫ h in Ioo a b, ‖Q₁ h‖ ^ 2) ≤
              K * (∫ h in Ioo a b, ‖N₁ h‖ ^ 2 + h ^ 2 * ‖N₂ h‖ ^ 2) := by
  obtain ⟨B, H, r, hB, hH, hr, hr1, hfactor⟩ := quarterDivisor_inverse_factor hlam
  obtain ⟨J, hJ, hsecond⟩ := interval_h2_div_sub
  let K := 8 * B ^ 4 + 16 * H ^ 2 + 2 * B ^ 4 * J + 1
  refine ⟨K, r, by dsimp [K]; positivity, hr, hr1, ?_⟩
  intro κ _ a z b ha haz hzb hbr hz hleft hright N N₁ N₂ hN hzero
  have hab : a < b := haz.trans hzb
  have hz0 : 0 < z := ha.trans haz
  have hzc : z ∈ Icc a b := ⟨haz.le, hzb.le⟩
  have hNz : intervalH1Extension a b N N₁ z = 0 := by
    rw [hN.1.extension_eq hab ⟨haz, hzb⟩, hzero]
  obtain ⟨U, U₁, hU, hNU, hUE⟩ := hsecond a b z N N₁ N₂ hab hzc hN hNz
  have hUV := hN.1.integral_sq_linear_quotient_le ⟨haz, hzb⟩ hzero hU.memLp_value hNU
  obtain ⟨R, R₁, hR, hdR, hDR, hRb⟩ := hfactor κ a z b ha haz hzb hbr hz hleft hright
  let Q := fun h ↦ R h * U h
  let Q₁ := fun h ↦ R₁ h * U h + R h * U₁ h
  have hQ : HasIntervalH1 a b Q Q₁ := hU.mul_smooth hR
    (fun h hh ↦ hdR h (Ioo_subset_Icc_self hh))
    (fun h hh ↦ (hRb h (Ioo_subset_Icc_self hh)).2.2.1)
    (fun h hh ↦ (hRb h (Ioo_subset_Icc_self hh)).2.2.2)
  have hpos (h : ℝ) (hh : h ∈ Ioo a b) : 0 < h := ha.trans hh.1
  have hzBh (h : ℝ) (hh : h ∈ Ioo a b) : z ≤ B * h := by
    simpa only [mul_comm] using
      (div_le_iff₀ hB).1 (hRb h (Ioo_subset_Icc_self hh)).1
  have hQhb (h : ℝ) (hh : h ∈ Ioo a b) :
      ‖Q h / (h : ℂ)‖ ≤ B ^ 2 * ‖U h‖ := by
    dsimp only [Q]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos h hh)]
    apply (div_le_iff₀ (hpos h hh)).2
    have hm := mul_le_mul_of_nonneg_right
      (hRb h (Ioo_subset_Icc_self hh)).2.2.1 (norm_nonneg (U h))
    have hz' := mul_le_mul_of_nonneg_left (hzBh h hh)
      (mul_nonneg hB.le (norm_nonneg (U h)))
    nlinarith
  have hQhL : MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo a b)) := by
    apply hU.memLp_value.of_le_mul (c := B ^ 2)
      (hQ.memLp_value.aestronglyMeasurable.div₀ (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact hQhb h hh
  have hUs := hU.memLp_value.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hU₁s := hU.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hN₁s := hN.1.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hN₂s := hN.2.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hW : IntegrableOn (fun h ↦ h ^ 2 * ‖N₂ h‖ ^ 2) (Ioo a b) := by
    apply hN₂s.bdd_mul (c := b ^ 2) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact (sq_le_sq₀ (hpos h hh).le (ha.trans hab).le).2 hh.2.le
  have hweighted : z ^ 2 * (∫ h in Ioo a b, ‖N₂ h‖ ^ 2) ≤
      B ^ 2 * ∫ h in Ioo a b, h ^ 2 * ‖N₂ h‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (hN₂s.const_mul _) (hW.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hs := (sq_le_sq₀ hz0.le (mul_nonneg hB.le (hpos h hh).le)).2 (hzBh h hh)
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖N₂ h‖)]
  have hUweighted : z ^ 2 * (∫ h in Ioo a b, ‖U₁ h‖ ^ 2) ≤
      J * B ^ 2 * ∫ h in Ioo a b, h ^ 2 * ‖N₂ h‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hUE (sq_nonneg z)
    have hm' := mul_le_mul_of_nonneg_left hweighted hJ.le
    nlinarith
  have hQv : (∫ h in Ioo a b, ‖Q h / (h : ℂ)‖ ^ 2) ≤
      B ^ 4 * ∫ h in Ioo a b, ‖U h‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      (hQhL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) (hUs.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg B) (norm_nonneg _))).2
      (hQhb h hh)
    nlinarith
  have hQd : (∫ h in Ioo a b, ‖Q₁ h‖ ^ 2) ≤
      2 * (H ^ 2 * (∫ h in Ioo a b, ‖U h‖ ^ 2) +
        (B * z) ^ 2 * ∫ h in Ioo a b, ‖U₁ h‖ ^ 2) := by
    have hi := ((hUs.const_mul (H ^ 2)).add (hU₁s.const_mul ((B * z) ^ 2))).const_mul 2
    have hm : (∫ h in Ioo a b, ‖Q₁ h‖ ^ 2) ≤
        ∫ h in Ioo a b, 2 * (H ^ 2 * ‖U h‖ ^ 2 + (B * z) ^ 2 * ‖U₁ h‖ ^ 2) := by
      apply integral_mono_ae
        (hQ.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      have hsR := (sq_le_sq₀ (norm_nonneg (R h)) (mul_nonneg hB.le hz0.le)).2
        (hRb h (Ioo_subset_Icc_self hh)).2.2.1
      have hsR₁ := (sq_le_sq₀ (norm_nonneg (R₁ h)) hH.le).2
        (hRb h (Ioo_subset_Icc_self hh)).2.2.2
      have hs := norm_add_sq_le_two (R₁ h * U h) (R h * U₁ h)
      simp only [norm_mul, mul_pow] at hs
      change ‖R₁ h * U h + R h * U₁ h‖ ^ 2 ≤
        2 * (H ^ 2 * ‖U h‖ ^ 2 + (B * z) ^ 2 * ‖U₁ h‖ ^ 2)
      nlinarith [mul_le_mul_of_nonneg_right hsR₁ (sq_nonneg ‖U h‖),
        mul_le_mul_of_nonneg_right hsR (sq_nonneg ‖U₁ h‖)]
    convert hm using 1
    rw [integral_const_mul, integral_add (hUs.const_mul _) (hU₁s.const_mul _),
      integral_const_mul, integral_const_mul]
  refine ⟨Q, Q₁, hQ, ?_, hQhL, ?_, ?_⟩
  · intro h hh
    dsimp only [Q]
    rw [← mul_assoc, hDR h (Ioo_subset_Icc_self hh)]
    exact (hNU h hh).symm
  · have hm := mul_le_mul_of_nonneg_left hUV (pow_nonneg hB.le 4)
    have hI : 0 ≤ ∫ h in Ioo a b, ‖N₁ h‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
    have hK : 8 * B ^ 4 ≤ K := by
      dsimp [K]
      nlinarith [mul_nonneg (pow_nonneg hB.le 4) hJ.le]
    exact hQv.trans (hm.trans (by nlinarith [mul_le_mul_of_nonneg_right hK hI]))
  · rw [integral_add hN₁s hW]
    have hI₁ : 0 ≤ ∫ h in Ioo a b, ‖N₁ h‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
    have hI₂ : 0 ≤ ∫ h in Ioo a b, h ^ 2 * ‖N₂ h‖ ^ 2 :=
      integral_nonneg fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hK₁ : 16 * H ^ 2 ≤ K := by
      dsimp [K]
      nlinarith [pow_nonneg hB.le 4, mul_nonneg (pow_nonneg hB.le 4) hJ.le]
    have hK₂ : 2 * B ^ 4 * J ≤ K := by
      dsimp [K]
      nlinarith [pow_nonneg hB.le 4]
    have hm := mul_le_mul_of_nonneg_left hUV (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (sq_nonneg H))
    have hm' := mul_le_mul_of_nonneg_left hUweighted
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg B))
    nlinarith [mul_le_mul_of_nonneg_right hK₁ hI₁,
      mul_le_mul_of_nonneg_right hK₂ hI₂]

end NoEmbeddedEigenvalues
