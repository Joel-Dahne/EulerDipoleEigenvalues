import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Rational logarithm bounds for certificates

The remainder estimates compare the tails of the logarithm series to geometric
series, without expanding the finite sums into explicit coefficients.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set

/-- Bound a nonnegative series by its finite prefix plus a geometric tail. -/
private theorem series_bounds {f : ℕ → ℝ} {L q C : ℝ} (hs : HasSum f L)
    (n : ℕ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ht : ∀ k, 0 ≤ f (k + n)) (hb : ∀ k, f (k + n) ≤ C * q ^ k) :
    (∑ k ∈ Finset.range n, f k) ≤ L ∧
      L ≤ (∑ k ∈ Finset.range n, f k) + C / (1 - q) := by
  have hg := summable_geometric_of_lt_one hq hq1
  have htail : Summable (fun k ↦ f (k + n)) :=
    hs.summable.comp_injective (fun a b h ↦ Nat.add_right_cancel h)
  have he := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at he
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact le_add_of_nonneg_right (tsum_nonneg ht)
  · rw [← he]
    apply add_le_add_right
    calc
      (∑' k, f (k + n)) ≤ ∑' k : ℕ, C * q ^ k := htail.tsum_le_tsum hb (hg.mul_left C)
      _ = C / (1 - q) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

/-- Degree-fourteen truncation of `log(1-z)`. -/
def certificateLogTaylor (z : ℝ) : ℝ :=
  -(∑ k ∈ Finset.range 14, z ^ (k + 1) / ((k : ℝ) + 1))

/-- Rational lower bound for `log 2` from the first twenty atanh terms. -/
def certificateLogTwoLower : ℚ :=
  2 * ∑ k ∈ Finset.range 20, (1 / 3 : ℚ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

/-- The corresponding rational upper bound, including its remainder. -/
def certificateLogTwoUpper : ℚ :=
  certificateLogTwoLower + 2 * (1 / 3 : ℚ) ^ 41 / (41 * (1 - (1 / 3 : ℚ) ^ 2))

theorem certificate_log_ratio_bounds {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (r - 2) / r ≤ Real.log (r / 2) ∧
      Real.log (r / 2) ≤ 2 * (r - 2) / (r + 2) + 2 * (r - 2) ^ 3 / (3 * (r + 2) ^ 3) := by
  refine ⟨?_, ?_⟩
  · have h := Real.one_sub_inv_le_log_of_pos (show 0 < r / 2 by positivity)
    convert h using 1
    field_simp [hr.ne']
  · let t := (2 - r) / (r + 2)
    have hd : 0 < r + 2 := by positivity
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hr2) hd.le
    have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
    have hlog : Real.log ((1 + t) / (1 - t)) = -Real.log (r / 2) := by
      rw [← Real.log_inv]
      congr 1
      rw [← one_div, div_eq_div_iff (by linarith) (by positivity)]
      dsimp [t]
      field_simp [hd.ne']
      ring
    have h := Real.sum_range_le_log_div ht ht1 2
    rw [hlog] at h
    norm_num [Finset.sum_range_succ] at h
    have ht' : (r - 2) / (r + 2) = -t := by dsimp [t]; ring
    rw [show 2 * (r - 2) / (r + 2) = 2 * ((r - 2) / (r + 2)) by ring,
      show 2 * (r - 2) ^ 3 / (3 * (r + 2) ^ 3) =
        2 * ((r - 2) / (r + 2)) ^ 3 / 3 by
          rw [div_pow, ← mul_div_assoc 2, div_div, mul_comm _ (3 : ℝ)],
      ht']
    linarith

theorem certificate_log_one_sub_bounds {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 2)) :
    certificateLogTaylor z - z ^ 15 / (15 * (1 - z)) ≤ Real.log (1 - z) ∧
      Real.log (1 - z) ≤ certificateLogTaylor z := by
  have hz1 : z < 1 := hz.2.trans_lt (by norm_num)
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hz.1])
  have h := series_bounds hs 14 hz.1 hz1 (C := z ^ 15 / 15)
    (fun k ↦ div_nonneg (pow_nonneg hz.1 _) (by positivity)) (by
      intro k
      have hk : k + 14 + 1 = 15 + k := by omega
      rw [hk, pow_add]
      have hd : (15 : ℝ) ≤ ((k + 14 : ℕ) : ℝ) + 1 := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ z ^ 15 * z ^ k / 15 :=
          div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hz.1 _) (pow_nonneg hz.1 _))
            (by norm_num) hd
        _ = _ := by ring)
  rw [certificateLogTaylor]
  constructor
  · linarith only [h.2, div_div (z ^ 15) (15 : ℝ) (1 - z)]
  · linarith only [h.1]

theorem certificate_log_two_bounds :
    (certificateLogTwoLower : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (certificateLogTwoUpper : ℝ) := by
  let x : ℝ := 1 / 3
  have hx : 0 ≤ x := by norm_num [x]
  have hx2 : x ^ 2 < 1 := by norm_num [x]
  have hs : HasSum (fun k : ℕ ↦ 2 * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.log 2) := by
    convert Real.hasSum_log_one_add_inv (a := 1) (by norm_num) using 2
    · dsimp [x]
      norm_num
      ring
    · norm_num
  have h := series_bounds hs 20 (sq_nonneg x) hx2 (C := 2 * x ^ 41 / 41)
    (fun k ↦ by positivity) (by
      intro k
      rw [show 2 * (k + 20) + 1 = 41 + 2 * k by omega, pow_add, pow_mul x 2 k]
      have hd : (41 : ℝ) ≤ 2 * ((k + 20 : ℕ) : ℝ) + 1 := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ 2 * (x ^ 41 * (x ^ 2) ^ k) / 41 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
        _ = _ := by ring)
  have hlo : (certificateLogTwoLower : ℝ) =
      ∑ k ∈ Finset.range 20, 2 * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    unfold certificateLogTwoLower
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by dsimp [x]; ring
  refine ⟨hlo ▸ h.1, ?_⟩
  rw [certificateLogTwoUpper]
  push_cast
  rw [hlo]
  change _ ≤ _ + 2 * x ^ 41 / (41 * (1 - x ^ 2))
  rw [← div_div]
  exact h.2

/-- An affine expression is nonnegative between two endpoints at which it is
    nonnegative; there is no sign hypothesis on its slope. -/
theorem certificate_affine_in_log {A B lo hi t : ℝ} (ht : t ∈ Icc lo hi)
    (hlo : 0 ≤ A + B * lo) (hhi : 0 ≤ A + B * hi) : 0 ≤ A + B * t := by
  rcases le_total 0 B with hB | hB
  · exact hlo.trans (add_le_add_right (mul_le_mul_of_nonneg_left ht.1 hB) A)
  · exact hhi.trans (add_le_add_right (mul_le_mul_of_nonpos_left ht.2 hB) A)

end NoEmbeddedEigenvalues
