module

public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBAlgebra

/-!
# Odd-in-b corner certificate

Bound the potential from below before clearing denominators. On the corner box,
a shifted power-basis estimate suffices for the reduced numerator.
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Set

private def cornerLower {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ) : ℚ :=
  ∑ i, ∑ j, if i = 0 ∧ j = 0 then a i j else
    min 0 (a i j) * (1 / 16 : ℚ) ^ i.val * (1 / 16 : ℚ) ^ j.val

private theorem cornerLower_le {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ)
    {x y : ℝ} (hx : x ∈ Icc 0 (1 / 16)) (hy : y ∈ Icc 0 (1 / 16)) :
    (cornerLower a : ℝ) ≤ certificatePolynomial a x y := by
  unfold cornerLower certificatePolynomial
  push_cast
  apply Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    simp
  · simp only [hij, ite_false, Rat.cast_mul, Rat.cast_min, Rat.cast_zero, Rat.cast_pow,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    have hxi := pow_le_pow_left₀ hx.1 hx.2 i.val
    have hyj := pow_le_pow_left₀ hy.1 hy.2 j.val
    calc
      min 0 (a i j : ℝ) * (1 / 16) ^ i.val * (1 / 16) ^ j.val ≤
          min 0 (a i j : ℝ) * x ^ i.val * y ^ j.val := by
        rw [mul_assoc, mul_assoc]
        apply mul_le_mul_of_nonpos_left _ (min_le_left _ _)
        exact mul_le_mul hxi hyj (pow_nonneg hy.1 _) (by positivity)
      _ ≤ (a i j : ℝ) * x ^ i.val * y ^ j.val := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right (0 : ℝ) _) (pow_nonneg hx.1 _))
          (pow_nonneg hy.1 _)

private theorem cornerA_bound : (2600000 : ℚ) ≤ cornerLower mixedOddBCornerA := by
  decide +kernel

private theorem cornerNegB_bound : (-19000000 : ℚ) ≤
    cornerLower (fun i j ↦ -mixedOddBCornerB i j) := by
  decide +kernel

private theorem cornerNum_nonneg {h k : ℝ} (hh : h ∈ Icc (15 / 16) 1)
    (hk : k ∈ Icc (15 / 16) 1) : 0 ≤ mixedOddBCornerNum h k (Real.log h) := by
  let x := 1 - h
  let y := 1 - k
  have hx : x ∈ Icc 0 (1 / 16) := ⟨by dsimp [x]; linarith [hh.2],
    by dsimp [x]; linarith [hh.1]⟩
  have hy : y ∈ Icc 0 (1 / 16) := ⟨by dsimp [y]; linarith [hk.2],
    by dsimp [y]; linarith [hk.1]⟩
  have ha : 2600000 ≤ certificatePolynomial mixedOddBCornerA x y :=
    (show (2600000 : ℝ) ≤ (cornerLower mixedOddBCornerA : ℝ) by exact_mod_cast cornerA_bound).trans
      (cornerLower_le _ hx hy)
  have hb₀ : -19000000 ≤ certificatePolynomial (fun i j ↦ -mixedOddBCornerB i j) x y :=
    (show (-19000000 : ℝ) ≤ (cornerLower (fun i j ↦ -mixedOddBCornerB i j) : ℝ) by
      exact_mod_cast cornerNegB_bound).trans (cornerLower_le _ hx hy)
  have hb : certificatePolynomial mixedOddBCornerB x y ≤ 19000000 := by
    simpa only [certificatePolynomial, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib,
      neg_le_neg_iff] using hb₀
  have hpos : 0 < h := (by norm_num : (0 : ℝ) < 15 / 16).trans_le hh.1
  have hlo : -(1 / 15) ≤ Real.log h := by
    have hinv := inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 15 / 16) |>.2 hh.1
    have h := Real.one_sub_inv_le_log_of_pos hpos
    norm_num at hinv
    linarith only [h, hinv]
  have hhi : Real.log h ≤ 0 := Real.log_nonpos hpos.le hh.2
  have hm := mul_le_mul_of_nonpos_right hb hhi
  have he := mixed_odd_b_corner_power x y (Real.log h)
  rw [show 1 - x = h by dsimp [x]; ring, show 1 - y = k by dsimp [y]; ring] at he
  rw [he]
  linarith only [ha, hm, hlo]

/-- `cert:odd-b-corner`: the residual is nonnegative on the closed corner box. -/
theorem mixed_odd_b_residual_corner {h k : ℝ} (hh : h ∈ Icc (15 / 16) 1)
    (hk : k ∈ Icc (15 / 16) 1) : 0 ≤ mixedOddBResidual (h, k) := by
  have hh₀ : 0 < h := (by norm_num : (0 : ℝ) < 15 / 16).trans_le hh.1
  have hk₀ : 0 ≤ k := (by norm_num : (0 : ℝ) ≤ 15 / 16).trans hk.1
  have hs := add_pos_of_pos_of_nonneg hh₀ hk₀
  have hu : 0 ≤ 1 - h ^ 2 := sub_nonneg.mpr (pow_le_one₀ hh₀.le hh.2)
  have hv : 0 ≤ 1 - k ^ 2 := sub_nonneg.mpr (pow_le_one₀ hk₀ hk.2)
  have hr : 0 ≤ 2 - h ^ 2 - k ^ 2 := by linarith only [hu, hv]
  rcases hr.eq_or_lt with hr | hr
  · have hh' : h = 1 := by
      by_contra! hn
      have hsq := pow_lt_one₀ hh₀.le (lt_of_le_of_ne hh.2 hn) (n := 2) two_ne_zero
      linarith only [hr, hv, hsq]
    have hk' : k = 1 := by
      by_contra! hn
      have hsq := pow_lt_one₀ hk₀ (lt_of_le_of_ne hk.2 hn) (n := 2) two_ne_zero
      linarith only [hr, hu, hsq]
    rw [hh', hk', mixed_odd_b_residual_center]
    norm_num
  · have hf : 0 ≤ mixedOddBMultiplier (h, k) :=
      (by norm_num : (0 : ℝ) ≤ 3 / 4).trans
        (mixed_odd_b_multiplier_closed_bounds ⟨⟨hh₀.le, hh.2⟩, ⟨hk₀, hk.2⟩⟩).1
    have hsum : 0 ≤ mixedOddBCleared h k (Real.log h) := by
      rw [mixed_odd_b_corner_clear]
      exact add_nonneg (mul_nonneg hr.le (cornerNum_nonneg hh hk))
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hu) hv) hf)
    rw [mixed_odd_b_clear h k hh₀ hs.ne' hr.ne'] at hsum
    exact nonneg_of_mul_nonneg_right hsum (by positivity)

end NoEmbeddedEigenvalues
