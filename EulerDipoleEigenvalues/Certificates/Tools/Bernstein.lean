module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Bernstein certificates

A rational array represents power coefficients with specified degree bounds.
Bernstein coefficients are computed from that array, including an explicit affine
pullback for rational boxes. No coefficient table or subdivision tree is assumed.
The basis is Mathlib's `bernsteinPolynomial`.

Strict positivity requires an active positive coefficient: a coefficient's basis
factor must be positive at the point in question. Merely naming a set of possibly
zero coefficients does not specify a geometric exceptional set.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

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

private theorem basis_eval (n i : ℕ) (x : ℝ) :
    certificateBernsteinBasis n i x = (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) := by
  simp [certificateBernsteinBasis, bernsteinPolynomial]

private def powerToBernstein (n k i : ℕ) : ℝ :=
  if k ≤ i then (i.choose k : ℝ) / (n.choose k : ℝ) else 0

/-- Degree elevation of a monomial is the binomial expansion of
`x^k * (x + (1 - x))^(n-k)`. -/
private theorem power_bernstein {n : ℕ} (k : Fin (n + 1)) (x : ℝ) :
    (∑ i : Fin (n + 1), powerToBernstein n k.val i.val * certificateBernsteinBasis n i.val x)
      = x ^ k.val := by
  have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  have hc : (n.choose k.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    powerToBernstein n k.val i * certificateBernsteinBasis n i x)]
  have hn : n + 1 = k.val + (n - k.val + 1) := by omega
  conv_lhs => arg 1; rw [hn]
  rw [Finset.sum_range_add]
  have hzero : (∑ i ∈ Finset.range k.val,
      powerToBernstein n k.val i * certificateBernsteinBasis n i x) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      simp [powerToBernstein, not_le.mpr (Finset.mem_range.mp hi)]
  rw [hzero, zero_add]
  calc
    _ = ∑ i ∈ Finset.range (n - k.val + 1),
        x ^ k.val * (x ^ i * (1 - x) ^ (n - k.val - i) * ((n - k.val).choose i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : k.val ≤ k.val + i := Nat.le_add_right _ _
      have hchoose : (n.choose (k.val + i) : ℝ) * ((k.val + i).choose k.val : ℝ) =
          (n.choose k.val : ℝ) * ((n - k.val).choose i : ℝ) := by
        exact_mod_cast (by simpa using Nat.choose_mul (n := n) hi)
      rw [powerToBernstein, ite_eq_left hi, basis_eval, pow_add,
        show n - (k.val + i) = n - k.val - i by omega]
      calc
        _ = ((n.choose (k.val + i) : ℝ) * ((k.val + i).choose k.val : ℝ)) /
            (n.choose k.val : ℝ) * (x ^ k.val * x ^ i * (1 - x) ^ (n - k.val - i)) := by ring
        _ = _ := by rw [hchoose, mul_div_cancel_left₀ _ hc]; ring
    _ = _ := by rw [← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]

private def affinePower (a d u : ℝ) (k i : ℕ) : ℝ :=
  if i ≤ k then (k.choose i : ℝ) * a ^ (k - i) * d ^ i * u ^ i else 0

private theorem power_affine {n : ℕ} (k : Fin (n + 1)) (a d u : ℝ) :
    (∑ i : Fin (n + 1), affinePower a d u k.val i.val) = (a + d * u) ^ k.val := by
  rw [Fin.sum_univ_eq_sum_range (affinePower a d u k.val)]
  rw [← Finset.sum_subset (f := affinePower a d u k.val)
    (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))) (fun i _ hi ↦ by
      have hki : ¬ i ≤ k.val := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
      simp [affinePower, hki])]
  rw [add_comm a, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [affinePower, ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), mul_pow]
  ring

/-- Apply a change of basis independently in the two coordinates. -/
private theorem sum_tensor {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (a : K → L → ℝ) (f : K → I → ℝ) (g : L → J → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, a k l * f k i * g l j) =
      ∑ k, ∑ l, a k l * (∑ i, f k i) * (∑ j, g l j) := by
  calc
    _ = ∑ p : I × J, ∑ q : K × L, a q.1 q.2 * f q.1 p.1 * g q.2 p.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : K × L, ∑ p : I × J, a q.1 q.2 * f q.1 p.1 * g q.2 p.2 :=
      Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      have h : a k l * (∑ i, f k i) = ∑ i, a k l * f k i := Finset.mul_sum _ _ _
      rw [h, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ (Finset.mul_sum _ _ _).symm

/-- The coefficient formula really expands the represented polynomial. -/
theorem certificate_bernstein_expansion {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) (x y : ℝ) :
    certificatePolynomial a x y = ∑ i, ∑ j,
      (certificateBernsteinCoeff a i j : ℝ) *
        certificateBernsteinBasis n i.val x * certificateBernsteinBasis m j.val y := by
  unfold certificatePolynomial
  symm
  calc
    _ = ∑ i : Fin (n + 1), ∑ j : Fin (m + 1), ∑ k, ∑ l,
        (a k l : ℝ) * (powerToBernstein n k.val i.val * certificateBernsteinBasis n i.val x) *
          (powerToBernstein m l.val j.val * certificateBernsteinBasis m j.val y) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold certificateBernsteinCoeff
      push_cast
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      unfold powerToBernstein
      by_cases hk : k.val ≤ i.val <;> by_cases hl : l.val ≤ j.val <;>
        simp [hk, hl]
      ring
    _ = _ := by rw [sum_tensor]; simp only [power_bernstein]

private theorem certificate_affine_expansion {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) (x₀ x₁ y₀ y₁ : ℚ) (u v : ℝ) :
    certificatePolynomial (certificateAffineCoeff a x₀ x₁ y₀ y₁) u v =
      certificatePolynomial a ((x₀ : ℝ) + (x₁ - x₀ : ℚ) * u)
        ((y₀ : ℝ) + (y₁ - y₀ : ℚ) * v) := by
  unfold certificatePolynomial
  calc
    _ = ∑ i : Fin (n + 1), ∑ j : Fin (m + 1), ∑ k, ∑ l,
        (a k l : ℝ) * affinePower x₀ (x₁ - x₀ : ℚ) u k.val i.val *
          affinePower y₀ (y₁ - y₀ : ℚ) v l.val j.val := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold certificateAffineCoeff
      push_cast
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      unfold affinePower
      by_cases hk : i.val ≤ k.val <;> by_cases hl : j.val ≤ l.val <;>
        simp [hk, hl, Rat.cast_pow]
      ring
    _ = _ := by rw [sum_tensor]; simp only [power_affine]

/-- The box coefficients expand the affine pullback of the same polynomial. -/
theorem certificate_box_expansion {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) (x₀ x₁ y₀ y₁ : ℚ) (u v : ℝ) :
    certificatePolynomial a ((x₀ : ℝ) + (x₁ - x₀ : ℚ) * u)
        ((y₀ : ℝ) + (y₁ - y₀ : ℚ) * v) =
      ∑ i, ∑ j, (certificateBoxCoeff a x₀ x₁ y₀ y₁ i j : ℝ) *
        certificateBernsteinBasis n i.val u * certificateBernsteinBasis m j.val v := by
  rw [← certificate_affine_expansion, certificate_bernstein_expansion]
  rfl

private theorem normalize_box {a b : ℚ} {x : ℝ} (hab : a < b)
    (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    (x - (a : ℝ)) / ((b : ℝ) - a) ∈ Icc (0 : ℝ) 1 ∧
      (a : ℝ) + (b - a : ℚ) * ((x - (a : ℝ)) / ((b : ℝ) - a)) = x := by
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr (by exact_mod_cast hab)
  refine ⟨⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
    (div_le_one hd).mpr (sub_le_sub_right hx.2 _)⟩, ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ hd.ne']
  ring

private theorem basis_nonneg (n i : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ certificateBernsteinBasis n i x := by
  rw [basis_eval]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

/-- Nonnegative Bernstein coefficients certify nonnegativity on a rational box. -/
theorem certificate_bernstein_nonneg {n m : ℕ}
    (a : Fin (n + 1) → Fin (m + 1) → ℚ) {x₀ x₁ y₀ y₁ : ℚ}
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hb : ∀ i j, 0 ≤ certificateBoxCoeff a x₀ x₁ y₀ y₁ i j)
    {x y : ℝ} (hxp : x ∈ Icc (x₀ : ℝ) (x₁ : ℝ))
    (hyp : y ∈ Icc (y₀ : ℝ) (y₁ : ℝ)) :
    0 ≤ certificatePolynomial a x y := by
  obtain ⟨hu, ex⟩ := normalize_box hx hxp
  obtain ⟨hv, ey⟩ := normalize_box hy hyp
  rw [← ex, ← ey, certificate_box_expansion]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (by exact_mod_cast hb i j) (basis_nonneg n _ hu)) (basis_nonneg m _ hv)

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
  obtain ⟨hu, ex⟩ := normalize_box hx hxp
  obtain ⟨hv, ey⟩ := normalize_box hy hyp
  rw [← ex, ← ey, certificate_box_expansion]
  have hterm (i : Fin (n + 1)) (j : Fin (m + 1)) :
      0 ≤ (certificateBoxCoeff a x₀ x₁ y₀ y₁ i j : ℝ) *
        certificateBernsteinBasis n i.val ((x - x₀) / (x₁ - x₀)) *
        certificateBernsteinBasis m j.val ((y - y₀) / (y₁ - y₀)) :=
    mul_nonneg (mul_nonneg (by exact_mod_cast hb i j) (basis_nonneg n _ hu)) (basis_nonneg m _ hv)
  obtain ⟨i, j, hij, hactive⟩ := hactive
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hterm i j)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ ↦ hterm i j) ⟨j, Finset.mem_univ _, ?_⟩⟩
  rw [mul_assoc]
  exact mul_pos (by exact_mod_cast hpos i j hij) hactive

end EulerDipoleEigenvalues
