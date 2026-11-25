module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBAlgebra

/-!
# Real Horner bounds for the mixed odd-in-b certificate

The generated traces prove inequalities against explicit endpoints, not the
result of a computed interval evaluator.
-/

@[expose] public section

namespace EulerDipoleEigenvalues

namespace MixedOddBTrace

open Set Finset

noncomputable def horner : (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, a, x => a 0 + horner n (fun i => a i.succ) x * x

theorem horner_eq (n : ℕ) (a : Fin n → ℝ) (x : ℝ) :
    horner n a x = ∑ i, a i * x ^ i.val := by
  induction n with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, ih, Fin.sum_univ_succ, sum_mul]
    simp [pow_succ, mul_assoc]

def bPadded (i : Fin 9) (j : Fin 9) : ℤ :=
  if hj : j.val < 8 then mixedOddBBInt i ⟨j.val, hj⟩ else 0

private theorem bPadded_castSucc (i : Fin 9) (j : Fin 8) :
    bPadded i j.castSucc = mixedOddBBInt i j := dite_eq_left j.isLt

private theorem bPadded_last (i : Fin 9) : bPadded i (Fin.last 8) = 0 :=
  dite_eq_right (Nat.lt_irrefl 8)

noncomputable def grouped (h k l : ℝ) : ℝ :=
  horner 9 (fun j => horner 11 (fun i => (mixedOddBAInt i j : ℝ)) h +
    horner 9 (fun i => (bPadded i j : ℝ)) h * l) k

theorem grouped_eq (h k l : ℝ) : grouped h k l = mixedOddBCleared h k l := by
  rw [mixed_odd_b_cleared_affine, mixed_odd_b_a_table, mixed_odd_b_b_table]
  simp only [grouped, horner_eq, certificatePolynomial, mixedOddBAPower, mixedOddBBPower,
    Rat.cast_intCast, add_mul, sum_add_distrib, sum_mul]
  congr 1
  · rw [sum_comm]
  · rw [Fin.sum_univ_castSucc]
    simp only [bPadded_castSucc, bPadded_last, Fin.val_castSucc, Int.cast_zero,
      zero_mul, sum_const_zero, add_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring

-- Each trace step checks just two rounded bounds for `s + x*y`. The
-- sign of each endpoint of `x` determines which endpoint of `y` to use.
theorem realHornerStep {a b c d e f lo hi s x y : ℝ}
    (hs : s ∈ Icc e f) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (hc : 0 ≤ c)
    (hlo : lo ≤ e + (if a < 0 then a * d else a * c))
    (hhi : f + (if 0 ≤ b then b * d else b * c) ≤ hi) :
    s + x * y ∈ Icc lo hi := by
  have hy₀ := hc.trans hy.1
  constructor
  · apply hlo.trans
    apply add_le_add hs.1
    split
    · rename_i ha
      exact (mul_le_mul_of_nonpos_left hy.2 ha.le).trans (mul_le_mul_of_nonneg_right hx.1 hy₀)
    · rename_i ha
      exact (mul_le_mul_of_nonneg_left hy.1 (le_of_not_gt ha)).trans
        (mul_le_mul_of_nonneg_right hx.1 hy₀)
  · apply le_trans _ hhi
    apply add_le_add hs.2
    split
    · rename_i hb
      exact (mul_le_mul_of_nonneg_right hx.2 hy₀).trans (mul_le_mul_of_nonneg_left hy.2 hb)
    · rename_i hb
      exact (mul_le_mul_of_nonneg_right hx.2 hy₀).trans
        (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb))

theorem realPoint (x : ℝ) : x ∈ Icc x x := ⟨le_rfl, le_rfl⟩

theorem realNegBounds {a b x : ℝ} (h : x ∈ Icc a b) : -x ∈ Icc (-b) (-a) :=
  ⟨neg_le_neg h.2, neg_le_neg h.1⟩

end MixedOddBTrace

end EulerDipoleEigenvalues
