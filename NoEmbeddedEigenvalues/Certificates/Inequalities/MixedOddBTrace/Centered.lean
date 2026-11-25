module

public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBTrace.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Centering along both coordinates for mixed odd-in-b traces -/

@[expose] public section

namespace NoEmbeddedEigenvalues.MixedOddBTrace

open Set

private theorem horner_param_deriv {n : ℕ} {f : Fin n → ℝ → ℝ} {d : Fin n → ℝ}
    {h : ℝ} (hf : ∀ i, HasDerivAt (f i) (d i) h) (k : ℝ) :
    HasDerivAt (fun y => horner n (fun i => f i y) k) (horner n d k) h := by
  induction n with
  | zero => simpa only [horner] using hasDerivAt_const h (0 : ℝ)
  | succ n ih =>
    simpa only [horner] using (hf 0).fun_add ((ih (fun i => hf i.succ)).mul_const k)

noncomputable def groupedDH (h k l : ℝ) : ℝ :=
  horner 9 (fun j =>
    horner 10 (fun i => (i.val + 1 : ℝ) * (mixedOddBAInt i.succ j : ℝ)) h +
    horner 8 (fun i => (i.val + 1 : ℝ) * (bPadded i.succ j : ℝ)) h * l) k

noncomputable def groupedB (h k : ℝ) : ℝ :=
  horner 9 (fun j => horner 9 (fun i => (bPadded i j : ℝ)) h) k

private theorem cleared_hasDerivAt_h {h : ℝ} (hp : 0 < h) (k e : ℝ) :
    HasDerivAt (fun x => mixedOddBCleared x k (Real.log x + e))
      (groupedDH h k (Real.log h + e) + groupedB h k / h) h := by
  simp only [← grouped_eq]
  have hlog := (Real.hasDerivAt_log hp.ne').add_const e
  have hd := horner_param_deriv (n := 9) (fun j =>
      (horner_hasDerivAt (fun i => (mixedOddBAInt i j : ℝ)) h).add
        ((horner_hasDerivAt (fun i => (bPadded i j : ℝ)) h).mul hlog)) k
  convert hd using 1
  · rfl
  · simp only [groupedDH, groupedB, horner_eq, div_eq_mul_inv, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, mul_right_comm, add_assoc]

private theorem centeredAxis {f d : ℝ → ℝ} {a b m x D r : ℝ}
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) (hD : 0 ≤ D) (hr : |x - m| ≤ r)
    (hd : ∀ y ∈ Icc a b, HasDerivAt f (d y) y)
    (hb : ∀ y ∈ Icc a b, |d y| ≤ D) :
    f m - D * r ≤ f x := by
  have he := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hd y hy).differentiableAt)
    (fun y hy => by rw [(hd y hy).deriv, Real.norm_eq_abs]; exact hb y hy) hm hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at he
  have hl := neg_le_of_abs_le (he.trans (mul_le_mul_of_nonneg_left hr hD))
  linarith only [hl]

/-- Keep the logarithm offset fixed while moving first in `h` and then in `k`. -/
theorem centeredHK {a b c d h k m n e lb D E r s : ℝ}
    (ha : 0 < a) (hh : h ∈ Icc a b) (hk : k ∈ Icc c d)
    (hm : m ∈ Icc a b) (hn : n ∈ Icc c d)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hr : |h - m| ≤ r) (hs : |k - n| ≤ s)
    (hc : lb ≤ mixedOddBCleared m n (Real.log m + e))
    (dh : ∀ x ∈ Icc a b,
      |groupedDH x n (Real.log x + e) + groupedB x n / x| ≤ D)
    (dk : ∀ y ∈ Icc c d, |groupedDK h y (Real.log h + e)| ≤ E) :
    lb - D * r - E * s ≤ mixedOddBCleared h k (Real.log h + e) := by
  have h₁ := centeredAxis hm hh hD hr
    (fun x hx => cleared_hasDerivAt_h (ha.trans_le hx.1) n e) dh
  have h₂ := centeredK hk hn hE hs (le_refl (mixedOddBCleared h n (Real.log h + e))) dk
  linarith only [hc, h₁, h₂]

end NoEmbeddedEigenvalues.MixedOddBTrace
