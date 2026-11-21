module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorFactor
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalLinearHardy
public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterPhaseCells
public import NoEmbeddedEigenvalues.Analysis.Inequalities.CountableCellEnergy
public import NoEmbeddedEigenvalues.Transport.WeightedGains.DescendingIntervalPartition

/-!
# Second mass division using only the first numerator derivative

Blueprint: `lem:phase-cell-second-mass-estimates`,
`lem:phase-cell-second-mass-division`.

On a complete cell, write D R = h-z and U=N/(h-z). Interior Hardy
establishes actual L² membership of U. The bound |R|/h ≤ B² then controls
(N/D)/h by U, with uniform energy 8 B⁴ ∫|N₁|². Summing the cells needs
only local H¹, resonant cancellation and global L² of N₁, not a second
numerator derivative, a derivative of the quotient or a trace at zero.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Uniform complete-cell second mass from one numerator derivative. -/
theorem phase_cell_second_mass_estimates {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ r < 1 ∧
      ∀ (κ : ℂ) (a z b : ℝ), 0 < a → a < z → z < b → b < r →
        quarterDivisor lam κ z = 0 →
        |quarterPhase lam a - quarterPhase lam z| = Real.pi →
        |quarterPhase lam b - quarterPhase lam z| = Real.pi →
        ∀ N N₁ : ℝ → ℂ, HasIntervalH1 a b N N₁ → N z = 0 →
          MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (h : ℂ)) 2
            (volume.restrict (Ioo a b)) ∧
          (∫ h in Ioo a b, ‖(N h / quarterDivisor lam κ h) / (h : ℂ)‖ ^ 2) ≤
            K * ∫ h in Ioo a b, ‖N₁ h‖ ^ 2 := by
  obtain ⟨B, H, r, hB, _, hr, hr1, hfactor⟩ := quarterDivisor_inverse_factor hlam
  refine ⟨8 * B ^ 4, r, by positivity, hr, hr1, ?_⟩
  intro κ a z b ha haz hzb hbr hz hleft hright N N₁ hN hzero
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
  have hQb (h : ℝ) (hh : h ∈ Ioo a b) : ‖Q h / (h : ℂ)‖ ≤ B ^ 2 * ‖U h‖ := by
    have hpos : 0 < h := ha.trans hh.1
    have hzBh : z ≤ B * h := by
      simpa only [mul_comm] using
        (div_le_iff₀ hB).1 (hRb h (Ioo_subset_Icc_self hh)).1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).2
    dsimp only [Q]
    rw [norm_mul]
    have hm := mul_le_mul_of_nonneg_right
      (hRb h (Ioo_subset_Icc_self hh)).2.2.1 (norm_nonneg (U h))
    have hm' := mul_le_mul_of_nonneg_left hzBh
      (mul_nonneg hB.le (norm_nonneg (U h)))
    nlinarith
  have hQL : MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo a b)) := by
    apply hU.of_le_mul (c := B ^ 2) (hQm.div₀ (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact hQb h hh
  have hQE : (∫ h in Ioo a b, ‖Q h / (h : ℂ)‖ ^ 2) ≤
      B ^ 4 * ∫ h in Ioo a b, ‖U h‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hQL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      ((hU.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hQb h hh)
    simpa only [mul_pow, ← pow_mul] using hs
  have heq : (fun h ↦ Q h / (h : ℂ)) =ᵐ[volume.restrict (Ioo a b)]
      (fun h ↦ (N h / quarterDivisor lam κ h) / (h : ℂ)) := by
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
  exact hQE.trans ((mul_le_mul_of_nonneg_left hUE (pow_nonneg hB.le 4)).trans_eq (by ring))

/-- Global second mass division from local H¹ and a genuine L² first derivative.
The ordinary quotient suffices; no quotient derivative or trace is asserted. -/
theorem phase_cell_second_mass_division {lam : ℝ} (hlam : lam ≠ 0)
    {κ : ℂ} (hκ : κ ^ 4 = 1) {h₀ : ℝ} (hh₀ : 0 < h₀) {N N₁ : ℝ → ℂ}
    (hN : HasIntervalH1Loc 0 h₀ N N₁)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hN₁ : MemLp N₁ 2 (volume.restrict (Ioo 0 h₀))) :
    ∃ η : ℝ, 0 < η ∧ η < h₀ ∧ IsPhaseCellEndpoint lam κ η ∧
      MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (h : ℂ)) 2
        (volume.restrict (Ioo 0 η)) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 η)), quarterDivisor lam κ h ≠ 0 := by
  obtain ⟨K, r, hK, hr, _, hest⟩ := phase_cell_second_mass_estimates hlam
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_ae_quarterDivisor_ne_zero hlam hκ (lt_min hh₀ hr)
  obtain ⟨e, z, he, het, hep, hzp⟩ := exists_complete_phase_cells hlam hκ hρ
  let s := fun n ↦ Ioo (e (n + 1)) (e n)
  have heh₀ (n : ℕ) : e n < h₀ := ((hep n).2.1.trans hρr).trans_le (min_le_left _ _)
  have her (n : ℕ) : e n < r := ((hep n).2.1.trans hρr).trans_le (min_le_right _ _)
  have hsubc (n : ℕ) : s n ⊆ Ioo 0 h₀ := fun x hx ↦
    ⟨(hep (n + 1)).1.trans hx.1, hx.2.trans (heh₀ n)⟩
  have hsub : (⋃ n, s n) ⊆ Ioo 0 h₀ := iUnion_subset hsubc
  have hcell (n : ℕ) := hest κ (e (n + 1)) (z n) (e n)
    (hep (n + 1)).1 (hzp n).1 (hzp n).2.1 (her n) (hzp n).2.2.1
    (hzp n).2.2.2.1 (hzp n).2.2.2.2 N N₁
    (hN _ _ (hep (n + 1)).1 (he (Nat.lt_succ_self n)) (heh₀ n))
    (hzero (z n) ⟨(hep (n + 1)).1.trans (hzp n).1,
      (hzp n).2.1.trans (heh₀ n)⟩ (hzp n).2.2.1)
  have hE : IntegrableOn (fun h ↦ ‖N₁ h‖ ^ 2) (Ioo 0 h₀) :=
    hN₁.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hQL : MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (h : ℂ)) 2
      (volume.restrict (⋃ n, s n)) :=
    memLp_two_of_cell_energy (fun _ ↦ measurableSet_Ioo)
      (descending_cells_disjoint he) hK.le (hE.mono_set hsub)
      (fun _ _ ↦ sq_nonneg _) (fun n ↦ (hcell n).1) (fun n ↦ (hcell n).2)
  refine ⟨e 0, (hep 0).1, heh₀ 0, (hep 0).2.2.1, ?_, ?_⟩
  · rwa [Measure.restrict_congr_set
      (descending_cells_ae_cover he (fun n ↦ (hep n).1) het)] at hQL
  · exact ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl (hep 0).2.1.le) hne

end NoEmbeddedEigenvalues
