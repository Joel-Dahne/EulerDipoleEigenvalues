module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Convert

/-! # Centered bounds for mixed odd-in-b Horner traces -/

@[expose] public section

namespace EulerDipoleEigenvalues.MixedOddBTrace

open Finset Set

theorem horner_hasDerivAt {n : ℕ} (a : Fin (n + 1) → ℝ) (x : ℝ) :
    HasDerivAt (horner (n + 1) a)
      (horner n (fun i => (i.val + 1 : ℝ) * a i.succ) x) x := by
  simp only [funext (horner_eq (n + 1) a), horner_eq]
  have hd := HasDerivAt.sum (u := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pow i.val x).const_mul (a i)
  have hf : (∑ i, fun y : ℝ => a i * y ^ i.val) = (fun y => ∑ i, a i * y ^ i.val) := by
    funext y
    exact Finset.sum_apply y Finset.univ (fun (i : Fin (n + 1)) (z : ℝ) => a i * z ^ i.val)
  rw [hf] at hd
  convert hd using 1
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, zero_mul, mul_zero, zero_add,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply sum_congr rfl
  intro i _
  ring

noncomputable def groupedCoeff (h l : ℝ) (j : Fin 9) : ℝ :=
  horner 11 (fun i => (mixedOddBAInt i j : ℝ)) h +
    horner 9 (fun i => (bPadded i j : ℝ)) h * l

noncomputable def groupedDK (h k l : ℝ) : ℝ :=
  horner 8 (fun j => (j.val + 1 : ℝ) * groupedCoeff h l j.succ) k

-- Kept as a separate identity so the generated bound does not differentiate
-- the full polynomial or unfold the mean-value argument.
theorem groupedDK_eq (h k l : ℝ) : groupedDK h k l =
    horner 8 (fun j => (j.val + 1 : ℝ) *
      (horner 11 (fun i => (mixedOddBAInt i j.succ : ℝ)) h +
        horner 9 (fun i => (bPadded i j.succ : ℝ)) h * l)) k := rfl

private theorem cleared_hasDerivAt_k (h k l : ℝ) :
    HasDerivAt (fun x => mixedOddBCleared h x l) (groupedDK h k l) k := by
  simp only [← grouped_eq]
  exact horner_hasDerivAt (groupedCoeff h l) k

/-- With `h` and `l` fixed, transfer the bound at the center in `k` to the box. -/
theorem centeredK {h k l c d m lb D r : ℝ}
    (hk : k ∈ Icc c d) (hm : m ∈ Icc c d)
    (hD : 0 ≤ D) (hr : |k - m| ≤ r)
    (hcenter : lb ≤ mixedOddBCleared h m l)
    (hgrad : ∀ x ∈ Icc c d, |groupedDK h x l| ≤ D) :
    lb - D * r ≤ mixedOddBCleared h k l := by
  have he := (convex_Icc c d).norm_image_sub_le_of_norm_deriv_le
    (f := fun x => mixedOddBCleared h x l)
    (fun x _ => (cleared_hasDerivAt_k h x l).differentiableAt)
    (fun x hx => by
      rw [(cleared_hasDerivAt_k h x l).deriv, Real.norm_eq_abs]
      exact hgrad x hx) hm hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at he
  have hlow := neg_le_of_abs_le (he.trans (mul_le_mul_of_nonneg_left hr hD))
  linarith only [hlow, hcenter]

end EulerDipoleEigenvalues.MixedOddBTrace
