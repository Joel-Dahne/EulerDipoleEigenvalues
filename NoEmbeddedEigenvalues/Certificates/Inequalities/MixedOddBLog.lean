import NoEmbeddedEigenvalues.Certificates.Tools.Logarithm
import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBAlgebra

/-!
# Logarithm reduction for the mixed odd-in-b sign

The small strip uses the signs of `-B` and `A-6B` directly. On every other
dyadic strip the two logarithm endpoints reduce to polynomial inequalities.
-/

namespace NoEmbeddedEigenvalues

open Set

noncomputable section

private def smallNegB (i : Fin 9) (j : Fin 8) : ℚ := -mixedOddBBPower i j

private def smallA (i : Fin 11) (j : Fin 9) : ℚ :=
  mixedOddBAPower i j - 6 * if hi : i.val < 9 then
    if hj : j.val < 8 then mixedOddBBPower ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0

private theorem smallNegB_eq (h k : ℝ) :
    certificatePolynomial smallNegB h k = -mixedOddBB h k := by
  rw [mixed_odd_b_b_table]
  simp [certificatePolynomial, Fin.sum_univ_succ, smallNegB, mixedOddBBPower, mixedOddBBInt]
  ring

private theorem smallA_eq (h k : ℝ) :
    certificatePolynomial smallA h k = mixedOddBA h k - 6 * mixedOddBB h k := by
  rw [mixed_odd_b_a_table, mixed_odd_b_b_table]
  simp [certificatePolynomial, Fin.sum_univ_succ, smallA,
    mixedOddBAPower, mixedOddBAInt, mixedOddBBPower, mixedOddBBInt]
  ring

private theorem smallNegB_coeff :
    ∀ i j, 0 ≤ certificateBoxCoeff smallNegB 0 (1 / 1024) 0 1 i j := by decide +kernel

private theorem smallA_coeff :
    ∀ i j, 0 ≤ certificateBoxCoeff smallA 0 (1 / 1024) 0 1 i j := by decide +kernel

private theorem small_log {h : ℝ} (hh : 0 < h) (hs : h ≤ 1 / 1024) : Real.log h ≤ -6 := by
  have hL : (3 / 5 : ℚ) ≤ certificateLogTwoLower := by decide +kernel
  have hL' : (3 / 5 : ℝ) ≤ (certificateLogTwoLower : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hL
  have hp := Real.log_le_log hh hs
  rw [show (1 / 1024 : ℝ) = (2 : ℝ)⁻¹ ^ (10 : ℕ) by norm_num,
    Real.log_pow, Real.log_inv] at hp
  norm_num only [Nat.cast_ofNat] at hp
  linarith [certificate_log_two_bounds.1]

/-- The whole small-`h` strip is certified by two direct Bernstein checks. -/
theorem mixed_odd_b_small_strip {h k : ℝ} (hh : h ∈ Ioc (0 : ℝ) (1 / 1024))
    (hk : k ∈ Icc (0 : ℝ) 1) : 0 ≤ mixedOddBResidual (h, k) := by
  have hH : h ∈ Icc (0 : ℝ) (1 / 1024) := ⟨hh.1.le, hh.2⟩
  have ha := certificate_bernstein_nonneg smallA (by norm_num) (by norm_num) smallA_coeff
    (by norm_num; exact hH) (by norm_num; exact hk)
  have hb := certificate_bernstein_nonneg smallNegB (by norm_num) (by norm_num) smallNegB_coeff
    (by norm_num; exact hH) (by norm_num; exact hk)
  rw [smallA_eq] at ha
  rw [smallNegB_eq] at hb
  have hsum : 0 ≤ mixedOddBCleared h k (Real.log h) := by
    rw [mixed_odd_b_cleared_affine]
    have h := add_nonneg ha (mul_nonneg hb (sub_nonneg.mpr (small_log hh.1 hh.2)))
    linarith only [h]
  have hs : 0 < h + k := add_pos_of_pos_of_nonneg hh.1 hk.1
  have hr : 0 < 2 - h ^ 2 - k ^ 2 := by
    have h1 : h < 1 := hh.2.trans_lt (by norm_num)
    linarith [pow_lt_one₀ hh.1.le h1 (n := 2) (by decide),
      pow_le_one₀ hk.1 hk.2 (n := 2)]
  rw [mixed_odd_b_clear h k hh.1 hs.ne' hr.ne'] at hsum
  exact nonneg_of_mul_nonneg_right hsum (by positivity)

/-- On the logarithm strip, use the rescaled coordinate `z ∈ [0,1]`. -/
def mixedOddBStripH (j : ℕ) (z : ℝ) : ℝ := (1 / 2 : ℝ) ^ j * (1 - z / 2)

/-- The lower endpoint expression, multiplied by the positive `h` to clear
the Taylor remainder denominator. -/
def mixedOddBStripLower (j : ℕ) (z k : ℝ) : ℝ :=
  let h := mixedOddBStripH j z
  h * mixedOddBCleared h k (-(j : ℝ) * (certificateLogTwoUpper : ℝ) +
    certificateLogTaylor (z / 2)) -
    (1 / 2 : ℝ) ^ j * mixedOddBB h k * (z / 2) ^ 15 / 15

/-- The upper endpoint expression is polynomial without the factor `h`. -/
def mixedOddBStripUpper (j : ℕ) (z k : ℝ) : ℝ :=
  mixedOddBCleared (mixedOddBStripH j z) k
    (-(j : ℝ) * (certificateLogTwoLower : ℝ) + certificateLogTaylor (z / 2))

/-- Both endpoint checks on a strip suffice, even when the coefficient of
the logarithm changes sign. The exceptional center is checked separately. -/
theorem mixed_odd_b_of_strip_endpoints {j : ℕ} {z k : ℝ} (hz : z ∈ Icc (0 : ℝ) 1)
    (hk : k ∈ Icc (0 : ℝ) 1) (hl : 0 ≤ mixedOddBStripLower j z k)
    (hu : 0 ≤ mixedOddBStripUpper j z k) :
    0 ≤ mixedOddBResidual (mixedOddBStripH j z, k) := by
  let h := mixedOddBStripH j z
  have hz' : z / 2 ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hn : 0 < 1 - z / 2 := by linarith [hz'.2]
  have hh : 0 < h := mul_pos (by positivity) hn
  have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hh₁ : h ≤ 1 := by
    calc
      h ≤ 1 * (1 - z / 2) := mul_le_mul_of_nonneg_right hp hn.le
      _ ≤ 1 := by linarith [hz'.1]
  by_cases hr : 2 - h ^ 2 - k ^ 2 = 0
  · have eh : h = 1 := by
      by_contra! hn'
      have hlt : h < 1 := lt_of_le_of_ne hh₁ hn'
      linarith [pow_lt_one₀ hh.le hlt (n := 2) (by decide), pow_le_one₀ hk.1 hk.2 (n := 2)]
    have ek : k = 1 := by
      by_contra! hn'
      have hlt := lt_of_le_of_ne hk.2 hn'
      linarith [pow_lt_one₀ hk.1 hlt (n := 2) (by decide), pow_le_one₀ hh.le hh₁ (n := 2)]
    change 0 ≤ mixedOddBResidual (h, k)
    rw [eh, ek, mixed_odd_b_residual_center]
    norm_num
  have hhsq := pow_le_one₀ hh.le hh₁ (n := 2)
  have hksq := pow_le_one₀ hk.1 hk.2 (n := 2)
  have hr' : 0 < 2 - h ^ 2 - k ^ 2 :=
    lt_of_le_of_ne (by linarith only [hhsq, hksq]) (Ne.symm hr)
  let lo := -(j : ℝ) * (certificateLogTwoUpper : ℝ) + certificateLogTaylor (z / 2) -
    (z / 2) ^ 15 / (15 * (1 - z / 2))
  let hi := -(j : ℝ) * (certificateLogTwoLower : ℝ) + certificateLogTaylor (z / 2)
  have hlog : Real.log h = -(j : ℝ) * Real.log 2 + Real.log (1 - z / 2) := by
    unfold h mixedOddBStripH
    rw [Real.log_mul (by positivity : (1 / 2 : ℝ) ^ j ≠ 0) hn.ne',
      Real.log_pow, one_div, Real.log_inv]
    ring
  obtain ⟨htl, htu⟩ := certificate_log_one_sub_bounds hz'
  obtain ⟨h2l, h2u⟩ := certificate_log_two_bounds
  have hI : Real.log h ∈ Icc lo hi := by
    rw [hlog]
    have hl := mul_le_mul_of_nonneg_left h2u (Nat.cast_nonneg (α := ℝ) j)
    have hu := mul_le_mul_of_nonneg_left h2l (Nat.cast_nonneg (α := ℝ) j)
    exact ⟨by dsimp [lo]; linarith only [hl, htl], by dsimp [hi]; linarith only [hu, htu]⟩
  have hE : h * mixedOddBCleared h k lo = mixedOddBStripLower j z k := by
    unfold mixedOddBStripLower lo
    change h * mixedOddBCleared h k _ = h * mixedOddBCleared h k _ - _
    rw [mixed_odd_b_cleared_affine, mixed_odd_b_cleared_affine]
    generalize ht : 1 - z / 2 = t at hn ⊢
    have hh' : h = (1 / 2 : ℝ) ^ j * t := by rw [← ht]; rfl
    have hs' : mixedOddBStripH j z = h := rfl
    rw [hs', hh']
    field_simp [hn.ne']
    ring
  have hLo : 0 ≤ mixedOddBA h k + mixedOddBB h k * lo := by
    have hb := nonneg_of_mul_nonneg_right (hE ▸ hl : 0 ≤ h * mixedOddBCleared h k lo) hh
    rwa [mixed_odd_b_cleared_affine] at hb
  have hHi : 0 ≤ mixedOddBA h k + mixedOddBB h k * hi := by
    change 0 ≤ mixedOddBCleared h k hi at hu
    rwa [mixed_odd_b_cleared_affine] at hu
  have hP := certificate_affine_in_log hI hLo hHi
  rw [← mixed_odd_b_cleared_affine,
    mixed_odd_b_clear h k hh (add_pos_of_pos_of_nonneg hh hk.1).ne' hr] at hP
  exact nonneg_of_mul_nonneg_right hP (mul_pos (mul_pos (by norm_num)
    (pow_pos (add_pos_of_pos_of_nonneg hh hk.1) _)) hr')

private theorem dyadic_cover (n : ℕ) {h : ℝ} (hlo : (1 / 2 : ℝ) ^ n < h) (hhi : h ≤ 1) :
    ∃ j < n, h ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) := by
  induction n with
  | zero =>
    rw [pow_zero] at hlo
    exact False.elim ((not_lt_of_ge hhi) hlo)
  | succ n ih =>
    rcases le_or_gt h ((1 / 2 : ℝ) ^ n) with ht | ht
    · exact ⟨n, Nat.lt_succ_self n, hlo.le, ht⟩
    · obtain ⟨j, hj, hbox⟩ := ih ht
      exact ⟨j, Nat.lt_succ_of_lt hj, hbox⟩

/-- Sign on the full rectangle from the twenty polynomial endpoint inequalities. -/
theorem mixed_odd_b_residual_nonneg_of_strips
    (hstrips : ∀ j < 10, ∀ z k : ℝ, z ∈ Icc 0 1 → k ∈ Icc 0 1 →
      0 ≤ mixedOddBStripLower j z k ∧ 0 ≤ mixedOddBStripUpper j z k)
    {h k : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) (hk : k ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedOddBResidual (h, k) := by
  rcases le_or_gt h (1 / 1024) with hsmall | hlarge
  · exact mixed_odd_b_small_strip ⟨hh.1, hsmall⟩ hk
  have hlo : (1 / 2 : ℝ) ^ (10 : ℕ) < h := by norm_num at hlarge ⊢; exact hlarge
  obtain ⟨j, hj, hbox⟩ := dyadic_cover 10 hlo hh.2
  let p : ℝ := (1 / 2) ^ j
  let z := 2 * (1 - h / p)
  have hp : 0 < p := by dsimp [p]; positivity
  have hdp : h / p ≤ 1 := (div_le_one hp).2 hbox.2
  have hdp' : 1 / 2 ≤ h / p := by
    apply (le_div_iff₀ hp).2
    rw [mul_comm, ← pow_succ]
    exact hbox.1
  have hz : z ∈ Icc 0 1 :=
    ⟨by dsimp [z]; linarith only [hdp], by dsimp [z]; linarith only [hdp']⟩
  have he : mixedOddBStripH j z = h := by
    change p * (1 - 2 * (1 - h / p) / 2) = h
    field_simp [hp.ne']
    ring
  obtain ⟨hl, hu⟩ := hstrips j hj z k hz hk
  rw [← he]
  exact mixed_odd_b_of_strip_endpoints hz hk hl hu

end

end NoEmbeddedEigenvalues
