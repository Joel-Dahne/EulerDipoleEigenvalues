module

public import NoEmbeddedEigenvalues.Certificates.Tools.Bernstein

/-!
# Separable box transform

The two stages of the power-to-Bernstein transform are tensor products of
one-variable transforms. The factored form allows a certificate to store and
check an intermediate table after transforming just one variable.
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Finset

def BernsteinSeparableAux.affineWeight {n : ℕ} (a b : ℚ) (i k : Fin (n + 1)) : ℚ :=
  if i.val ≤ k.val then
    (Nat.choose k.val i.val : ℚ) * a ^ (k.val - i.val) * (b - a) ^ i.val else 0

def BernsteinSeparableAux.bernsteinWeight {n : ℕ} (i k : Fin (n + 1)) : ℚ :=
  if k.val ≤ i.val then (Nat.choose i.val k.val : ℚ) / (Nat.choose n k.val : ℚ) else 0

/-- The rational affine and Bernstein transforms along one axis. -/
def certificateAxisBox {n : ℕ} (a b : ℚ) (p : Fin (n + 1) → ℚ) (i : Fin (n + 1)) : ℚ :=
  ∑ k, (∑ l, p l * BernsteinSeparableAux.affineWeight a b k l)
    * BernsteinSeparableAux.bernsteinWeight i k

private theorem certificateAffineCoeff_eq {n m : ℕ}
    (p : Fin (n + 1) → Fin (m + 1) → ℚ) (a b c d : ℚ) (i j) :
    certificateAffineCoeff p a b c d i j =
      ∑ k, ∑ l, p k l * BernsteinSeparableAux.affineWeight a b i k
        * BernsteinSeparableAux.affineWeight c d j l := by
  unfold certificateAffineCoeff
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  by_cases h₁ : i.val ≤ k.val <;> by_cases h₂ : j.val ≤ l.val <;>
    simp only [BernsteinSeparableAux.affineWeight, h₁, h₂, true_and, false_and, and_false,
      ite_true, ite_false,
      mul_zero, zero_mul]
  ring

private theorem certificateBernsteinCoeff_eq {n m : ℕ}
    (p : Fin (n + 1) → Fin (m + 1) → ℚ) (i j) :
    certificateBernsteinCoeff p i j =
      ∑ k, ∑ l, p k l * BernsteinSeparableAux.bernsteinWeight i k
        * BernsteinSeparableAux.bernsteinWeight j l := by
  unfold certificateBernsteinCoeff
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  by_cases h₁ : k.val ≤ i.val <;> by_cases h₂ : l.val ≤ j.val <;>
    simp only [BernsteinSeparableAux.bernsteinWeight, h₁, h₂, true_and, false_and, and_false,
      ite_true, ite_false,
      mul_zero, zero_mul]
  ring

/-- Apply the first-coordinate transform to each column, then the
second-coordinate transform to each row. -/
theorem certificateBoxCoeff_separable {n m : ℕ}
    (p : Fin (n + 1) → Fin (m + 1) → ℚ) (a b c d : ℚ) (i j) :
    certificateBoxCoeff p a b c d i j =
      certificateAxisBox c d (fun l ↦ certificateAxisBox a b (fun k ↦ p k l) i) j := by
  unfold certificateBoxCoeff
  simp only [certificateBernsteinCoeff_eq, certificateAffineCoeff_eq, certificateAxisBox,
    sum_mul]
  -- Exchange the affine sum in the second coordinate with the two first-coordinate sums.
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  conv_lhs =>
    enter [2, k]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro l' _
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro k' _
  ring

end NoEmbeddedEigenvalues
