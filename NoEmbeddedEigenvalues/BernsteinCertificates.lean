import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Statement interfaces for polynomial and logarithmic certificates

A rational array represents power coefficients with specified degree bounds.
Bernstein coefficients are computed from that array, including an explicit affine
pullback for rational boxes. No coefficient table or subdivision tree is assumed.
The basis is Mathlib's `bernsteinPolynomial`.

Strict positivity requires an active positive coefficient: a coefficient's basis
factor must be positive at the point in question. Merely naming a set of possibly
zero coefficients does not specify a geometric exceptional set.

The logarithmic bounds use exact finite sums. These interfaces do not select a
certificate algorithm or assert that any particular coefficient checks have run.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set

/-- Evaluation of a rational power-coefficient array of degree at most `(n,m)`. -/
def certificatePolynomial {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ)
    (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, (a i j : ℝ) * x ^ i.val * y ^ j.val

/-- Bernstein coefficient of the polynomial represented by `a` on the unit square. -/
def certificateBernsteinCoeff {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) : ℚ :=
  ∑ k, ∑ l, if k.val ≤ i.val ∧ l.val ≤ j.val then
    a k l * (Nat.choose i.val k.val : ℚ) / (Nat.choose n k.val : ℚ) *
      (Nat.choose j.val l.val : ℚ) / (Nat.choose m l.val : ℚ) else 0

/-- Power coefficients after `x=x₀+(x₁-x₀)u`, `y=y₀+(y₁-y₀)v`. -/
def certificateAffineCoeff {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ)
    (x₀ x₁ y₀ y₁ : ℚ) (i : Fin (n + 1)) (j : Fin (m + 1)) : ℚ :=
  ∑ k, ∑ l, if i.val ≤ k.val ∧ j.val ≤ l.val then
    a k l * (Nat.choose k.val i.val : ℚ) * x₀ ^ (k.val - i.val) * (x₁ - x₀) ^ i.val *
      (Nat.choose l.val j.val : ℚ) * y₀ ^ (l.val - j.val) * (y₁ - y₀) ^ j.val else 0

/-- Bernstein coefficients on a rational box, tied to the original power array. -/
def certificateBoxCoeff {n m : ℕ} (a : Fin (n + 1) → Fin (m + 1) → ℚ)
    (x₀ x₁ y₀ y₁ : ℚ) : Fin (n + 1) → Fin (m + 1) → ℚ :=
  certificateBernsteinCoeff (certificateAffineCoeff a x₀ x₁ y₀ y₁)

/-- Evaluation of Mathlib's univariate Bernstein basis polynomial. -/
def certificateBernsteinBasis (n i : ℕ) (x : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n i).eval x

/-- The coefficient formula really expands the represented polynomial. -/
theorem certificate_bernstein_expansion {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) (x y : ℝ) :
    certificatePolynomial a x y = ∑ i, ∑ j,
      (certificateBernsteinCoeff a i j : ℝ) *
        certificateBernsteinBasis n i.val x * certificateBernsteinBasis m j.val y := by
  sorry

/-- The box coefficients expand the affine pullback of the same polynomial. -/
theorem certificate_box_expansion {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) (x₀ x₁ y₀ y₁ : ℚ) (u v : ℝ) :
    certificatePolynomial a ((x₀ : ℝ) + (x₁ - x₀ : ℚ) * u)
        ((y₀ : ℝ) + (y₁ - y₀ : ℚ) * v) =
      ∑ i, ∑ j, (certificateBoxCoeff a x₀ x₁ y₀ y₁ i j : ℝ) *
        certificateBernsteinBasis n i.val u * certificateBernsteinBasis m j.val v := by
  sorry

/-- Nonnegative Bernstein coefficients certify nonnegativity on a rational box. -/
theorem certificate_bernstein_nonneg {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) {x₀ x₁ y₀ y₁ : ℚ}
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hb : ∀ i j, 0 ≤ certificateBoxCoeff a x₀ x₁ y₀ y₁ i j)
    {x y : ℝ} (hxp : x ∈ Icc (x₀ : ℝ) (x₁ : ℝ))
    (hyp : y ∈ Icc (y₀ : ℝ) (y₁ : ℝ)) :
    0 ≤ certificatePolynomial a x y := by
  sorry

/-- Precise strict-positivity criterion for a specified set of possibly zero indices.
    The active-basis condition identifies the exceptional boundary faces/corners. -/
theorem certificate_bernstein_pos {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) {x₀ x₁ y₀ y₁ : ℚ}
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (Z : Set (Fin (n + 1) × Fin (m + 1)))
    (hb : ∀ i j, 0 ≤ certificateBoxCoeff a x₀ x₁ y₀ y₁ i j)
    (hpos : ∀ i j, (i, j) ∉ Z → 0 < certificateBoxCoeff a x₀ x₁ y₀ y₁ i j)
    {x y : ℝ} (hxp : x ∈ Icc (x₀ : ℝ) (x₁ : ℝ))
    (hyp : y ∈ Icc (y₀ : ℝ) (y₁ : ℝ))
    (hactive : ∃ i j, (i, j) ∉ Z ∧
      0 < certificateBernsteinBasis n i.val ((x - x₀) / (x₁ - x₀)) *
        certificateBernsteinBasis m j.val ((y - y₀) / (y₁ - y₀))) :
    0 < certificatePolynomial a x y := by
  sorry

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
  sorry

theorem certificate_log_one_sub_bounds {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 2)) :
    certificateLogTaylor z - z ^ 15 / (15 * (1 - z)) ≤ Real.log (1 - z) ∧
      Real.log (1 - z) ≤ certificateLogTaylor z := by
  sorry

theorem certificate_log_two_bounds :
    (certificateLogTwoLower : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (certificateLogTwoUpper : ℝ) := by
  sorry

/-- An affine expression is nonnegative between two endpoints at which it is
    nonnegative; there is no sign hypothesis on its slope. -/
theorem certificate_affine_in_log {A B lo hi t : ℝ} (ht : t ∈ Icc lo hi)
    (hlo : 0 ≤ A + B * lo) (hhi : 0 ≤ A + B * hi) : 0 ≤ A + B * t := by
  sorry

end NoEmbeddedEigenvalues
