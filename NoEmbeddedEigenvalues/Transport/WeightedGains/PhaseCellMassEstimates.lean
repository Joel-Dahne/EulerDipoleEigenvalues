module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorFactor
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalLinearHardy

/-!
# First-derivative mass estimates on complete phase cells

Blueprint: `lem:phase-cell-mass-estimates`.

Interior Hardy supplies genuine L² division by the linear zero using only H¹
numerator data. The inverse divisor factor and cell comparability convert this
into the energy of the ordinary quotient divided by √h. Values at a resonance
are immaterial; no H² numerator or derivative of the quotient is required.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Uniform first-derivative mass estimates, with no second numerator jet. -/
theorem phase_cell_mass_estimates {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ r < 1 ∧
      ∀ (κ : ℂ) (a z b : ℝ), 0 < a → a < z → z < b → b < r →
        quarterDivisor lam κ z = 0 →
        |quarterPhase lam a - quarterPhase lam z| = Real.pi →
        |quarterPhase lam b - quarterPhase lam z| = Real.pi →
        ∀ N N₁ : ℝ → ℂ, HasIntervalH1 a b N N₁ → N z = 0 →
          MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (√h : ℂ)) 2
            (volume.restrict (Ioo a b)) ∧
          (∫ h in Ioo a b, ‖(N h / quarterDivisor lam κ h) / (√h : ℂ)‖ ^ 2) ≤
            K * ∫ h in Ioo a b, h * ‖N₁ h‖ ^ 2 := by
  obtain ⟨B, H, r, hB, _, hr, hr1, hfactor⟩ := quarterDivisor_inverse_factor hlam
  refine ⟨8 * B ^ 6, r, by positivity, hr, hr1, ?_⟩
  intro κ a z b ha haz hzb hbr hz hleft hright N N₁ hN hzero
  have hab : a < b := haz.trans hzb
  have hb : 0 < b := ha.trans hab
  let U := fun h ↦ N h / ((h - z : ℝ) : ℂ)
  have hUm : AEStronglyMeasurable U (volume.restrict (Ioo a b)) :=
    hN.memLp_value.aestronglyMeasurable.div₀ (by fun_prop)
  have hNU (h : ℝ) (_hh : h ∈ Ioo a b) : N h = ((h - z : ℝ) : ℂ) * U h := by
    by_cases he : h = z
    · subst h; simp [hzero]
    · dsimp only [U]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _
        (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr he))]
  obtain ⟨hU, hUE⟩ := hN.hardy_interior ⟨haz, hzb⟩ hzero hUm hNU
  obtain ⟨R, R₁, hR, _, hDR, hRb⟩ := hfactor κ a z b ha haz hzb hbr hz hleft hright
  let Q := fun h ↦ R h * U h
  have hQm : AEStronglyMeasurable Q (volume.restrict (Ioo a b)) :=
    ((hR.continuousOn.mono Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo).mul hUm
  have hpos (h : ℝ) (hh : h ∈ Ioo a b) : 0 < h := ha.trans hh.1
  have hzBh (h : ℝ) (hh : h ∈ Ioo a b) : z ≤ B * h := by
    simpa only [mul_comm] using
      (div_le_iff₀ hB).1 (hRb h (Ioo_subset_Icc_self hh)).1
  have hQb (h : ℝ) (hh : h ∈ Ioo a b) : ‖Q h‖ ≤ B ^ 2 * h * ‖U h‖ := by
    dsimp only [Q]
    rw [norm_mul]
    have hm := mul_le_mul_of_nonneg_right
      (hRb h (Ioo_subset_Icc_self hh)).2.2.1 (norm_nonneg (U h))
    have hm' := mul_le_mul_of_nonneg_left (hzBh h hh)
      (mul_nonneg hB.le (norm_nonneg (U h)))
    nlinarith
  have hQs (h : ℝ) (hh : h ∈ Ioo a b) :
      ‖Q h / (√h : ℂ)‖ ≤ B ^ 2 * √h * ‖U h‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (hpos h hh))).2
    apply (hQb h hh).trans_eq
    calc B ^ 2 * h * ‖U h‖ = B ^ 2 * (√h) ^ 2 * ‖U h‖ := by
           rw [Real.sq_sqrt (hpos h hh).le]
         _ = _ := by ring
  have hQs' (h : ℝ) (hh : h ∈ Ioo a b) :
      ‖Q h / (√h : ℂ)‖ ≤ (B ^ 2 * √b) * ‖U h‖ := by
    apply (hQs h hh).trans
    gcongr
    exact hh.2.le
  have hQL : MemLp (fun h ↦ Q h / (√h : ℂ)) 2 (volume.restrict (Ioo a b)) := by
    apply hU.of_le_mul (c := B ^ 2 * √b) (hQm.div₀ (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact hQs' h hh
  have hUs := hU.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hNs := hN.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hW : IntegrableOn (fun h ↦ h * ‖N₁ h‖ ^ 2) (Ioo a b) := by
    apply hNs.bdd_mul (c := b) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [Real.norm_eq_abs, abs_of_pos (hpos h hh)]
    exact hh.2.le
  have hweighted : b * (∫ h in Ioo a b, ‖N₁ h‖ ^ 2) ≤
      B ^ 2 * ∫ h in Ioo a b, h * ‖N₁ h‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (hNs.const_mul _) (hW.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hbz := (hRb b ⟨hab.le, le_rfl⟩).2.1
    have hbBh : b ≤ B ^ 2 * h := by nlinarith [hzBh h hh]
    nlinarith [mul_le_mul_of_nonneg_right hbBh (sq_nonneg ‖N₁ h‖)]
  have hcoef : (B ^ 2 * √b) ^ 2 = B ^ 4 * b := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hb.le]
  have hQE : (∫ h in Ioo a b, ‖Q h / (√h : ℂ)‖ ^ 2) ≤
      B ^ 4 * b * ∫ h in Ioo a b, ‖U h‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hQL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (hUs.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hQs' h hh)
    rw [mul_pow, hcoef] at hs
    exact hs
  have heq : (fun h ↦ Q h / (√h : ℂ)) =ᵐ[volume.restrict (Ioo a b)]
      (fun h ↦ (N h / quarterDivisor lam κ h) / (√h : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne z), ae_restrict_mem measurableSet_Ioo]
      with h hn hh
    have hne : ((h - z : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hn)
    have hD : quarterDivisor lam κ h ≠ 0 := by
      intro he
      have hc := hDR h (Ioo_subset_Icc_self hh)
      rw [he, zero_mul] at hc
      exact hne hc.symm
    congr 1
    apply (eq_div_iff hD).2
    dsimp only [Q]
    rw [mul_right_comm, mul_comm (R h) (quarterDivisor lam κ h),
      hDR h (Ioo_subset_Icc_self hh), ← hNU h hh]
  refine ⟨hQL.ae_eq heq, ?_⟩
  have hIe := integral_congr_ae (heq.fun_comp (fun v : ℂ ↦ ‖v‖ ^ 2))
  dsimp only [Function.comp_def] at hIe
  rw [← hIe]
  have hm := mul_le_mul_of_nonneg_left hUE (mul_nonneg (pow_nonneg hB.le 4) hb.le)
  have hm' := mul_le_mul_of_nonneg_left hweighted
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (pow_nonneg hB.le 4))
  nlinarith

end NoEmbeddedEigenvalues
