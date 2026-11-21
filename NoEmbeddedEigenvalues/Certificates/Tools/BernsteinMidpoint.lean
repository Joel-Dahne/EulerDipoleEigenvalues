module

public import NoEmbeddedEigenvalues.Certificates.Tools.Bernstein
public import Mathlib.Tactic.FieldSimp

/-!
# Scaled integer Bernstein subdivision

Each midpoint child has the same bidegree as its parent. Its coefficients
are multiplied by a positive power of two, so subdivision uses only integer
addition and scaling. A tree check computes a child from its parent, not
from the original power polynomial.
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Finset Set

private def rawBasis (n i : ℕ) (x : ℝ) : ℝ := (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

private theorem rawBasis_eq (n i : ℕ) (x : ℝ) :
    rawBasis n i x = certificateBernsteinBasis n i x := by
  simp [rawBasis, certificateBernsteinBasis, bernsteinPolynomial]

private theorem rawBasis_succ (n i : ℕ) (x : ℝ) (_hi : i ≤ n) :
    rawBasis (n + 1) (i + 1) x = (1 - x) * rawBasis n (i + 1) x + x * rawBasis n i x := by
  rw [rawBasis, Nat.choose_succ_succ, Nat.cast_add]
  unfold rawBasis
  rw [Nat.add_sub_add_right, pow_succ x i]
  by_cases hi' : i + 1 ≤ n
  · rw [show n - i = n - (i + 1) + 1 by omega, pow_succ (1 - x)]
    ring
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi')]
    push_cast
    ring

private theorem rawEval_succ (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    ∑ i ∈ range (n + 2), c i * rawBasis (n + 1) i x =
      (1 - x) * (∑ i ∈ range (n + 1), c i * rawBasis n i x) +
        x * (∑ i ∈ range (n + 1), c (i + 1) * rawBasis n i x) := by
  rw [sum_range_succ' (n := n + 1) (f := fun i ↦ c i * rawBasis (n + 1) i x),
    sum_range_succ' (n := n) (f := fun i ↦ c i * rawBasis n i x)]
  have h₀ : rawBasis (n + 1) 0 x = (1 - x) * rawBasis n 0 x := by
    simp [rawBasis, pow_succ, mul_comm]
  have hn : rawBasis n (n + 1) x = 0 := by
    simp [rawBasis]
  rw [h₀, mul_add]
  have he : (∑ i ∈ range (n + 1), c (i + 1) * rawBasis (n + 1) (i + 1) x) =
      (1 - x) * (∑ i ∈ range n, c (i + 1) * rawBasis n (i + 1) x) +
        x * (∑ i ∈ range (n + 1), c (i + 1) * rawBasis n i x) := by
    have he' : (∑ i ∈ range (n + 1), c (i + 1) * rawBasis n (i + 1) x) =
        ∑ i ∈ range n, c (i + 1) * rawBasis n (i + 1) x := by
      rw [sum_range_succ]
      simp only [hn, mul_zero, add_zero]
    rw [← he']
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [rawBasis_succ n i x (Nat.le_of_lt_succ (mem_range.1 hi))]
    ring
  rw [he]
  ring

noncomputable def BernsteinMidpointAux.axisEval {n : ℕ} (c : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * certificateBernsteinBasis n i.val x

private theorem axisEval_succ {n : ℕ} (c : Fin (n + 2) → ℝ) (x : ℝ) :
    BernsteinMidpointAux.axisEval c x = (1 - x) * BernsteinMidpointAux.axisEval (fun i ↦ c i.castSucc) x +
      x * BernsteinMidpointAux.axisEval (fun i ↦ c i.succ) x := by
  let C (i : ℕ) : ℝ := if hi : i < n + 2 then c ⟨i, hi⟩ else 0
  have hs := rawEval_succ n C x
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range] at hs
  simpa only [BernsteinMidpointAux.axisEval, ← rawBasis_eq, C, dite_eq_left (Fin.isLt _),
    dite_eq_left (Nat.lt_trans (Fin.isLt _) (Nat.lt_succ_self _)),
    dite_eq_left (Nat.succ_lt_succ (Fin.isLt _)), Fin.eta,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] using hs

private theorem axisEval_rev {n : ℕ} (c : Fin (n + 1) → ℝ) (x : ℝ) :
    BernsteinMidpointAux.axisEval (fun i ↦ c i.rev) x = BernsteinMidpointAux.axisEval c (1 - x) := by
  unfold BernsteinMidpointAux.axisEval
  rw [← Equiv.sum_comp (Fin.revPerm : Fin (n + 1) ≃ Fin (n + 1))
    (fun i ↦ c i.rev * certificateBernsteinBasis n i.val x)]
  apply sum_congr rfl
  intro i _
  change c i.rev.rev * certificateBernsteinBasis n i.rev.val x = _
  rw [Fin.rev_rev]
  congr 1
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  simp only [← rawBasis_eq, rawBasis, Fin.val_rev, sub_sub_cancel]
  rw [show n + 1 - (i.val + 1) = n - i.val by omega, Nat.choose_symm hi,
    show n - (n - i.val) = i.val by omega]
  ring

private theorem axisEval_add {n : ℕ} (c d : Fin (n + 1) → ℝ) (x : ℝ) :
    BernsteinMidpointAux.axisEval (fun i ↦ c i + d i) x = BernsteinMidpointAux.axisEval c x + BernsteinMidpointAux.axisEval d x := by
  simp [BernsteinMidpointAux.axisEval, add_mul, sum_add_distrib]

private theorem axisEval_mul {n : ℕ} (c : Fin (n + 1) → ℝ) (a x : ℝ) :
    BernsteinMidpointAux.axisEval (fun i ↦ a * c i) x = a * BernsteinMidpointAux.axisEval c x := by
  simp [BernsteinMidpointAux.axisEval, mul_assoc, mul_sum]

@[simp] private theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def BernsteinMidpointAux.adjacent {n : ℕ} (c : Vector ℤ (n + 2)) : Vector ℤ (n + 1) :=
  Vector.ofFn (fun i ↦ c.get i.castSucc + c.get i.succ)

/-- Left half-interval control points, multiplied by `2^n`. -/
def bernsteinMidLeft : (n : ℕ) → Vector ℤ (n + 1) → Vector ℤ (n + 1)
  | 0, c => c
  | n + 1, c =>
    let cs := bernsteinMidLeft n (BernsteinMidpointAux.adjacent c)
    Vector.ofFn (Fin.cons ((2 : ℤ) ^ (n + 1) * c.get 0) cs.get)

private theorem midLeft_castSucc (n : ℕ) (c : Vector ℤ (n + 2)) (i : Fin (n + 1)) :
    (bernsteinMidLeft (n + 1) c).get i.castSucc =
      2 * (bernsteinMidLeft n (Vector.ofFn fun j ↦ c.get j.castSucc)).get i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
    simp [hi, bernsteinMidLeft]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [bernsteinMidLeft, pow_succ]
      ring
    · have he : (j.succ.castSucc : Fin (n + 3)) = j.castSucc.succ := rfl
      rw [he, bernsteinMidLeft, get_ofFn, Fin.cons_succ]
      nth_rw 2 [bernsteinMidLeft]
      simp only [get_ofFn, Fin.cons_succ]
      rw [ih]
      have he' : (Vector.ofFn fun a ↦ (BernsteinMidpointAux.adjacent c).get a.castSucc) =
          BernsteinMidpointAux.adjacent (Vector.ofFn fun a ↦ c.get a.castSucc) := by
        apply Vector.ext
        intro a ha
        change (Vector.ofFn fun a ↦ (BernsteinMidpointAux.adjacent c).get a.castSucc).get ⟨a, ha⟩ =
          (BernsteinMidpointAux.adjacent (Vector.ofFn fun a ↦ c.get a.castSucc)).get ⟨a, ha⟩
        simp only [BernsteinMidpointAux.adjacent, get_ofFn]
        rfl
      rw [he']

private theorem axisEval_midLeft (n : ℕ) (c : Vector ℤ (n + 1)) (x : ℝ) :
    BernsteinMidpointAux.axisEval (fun i ↦ ((bernsteinMidLeft n c).get i : ℝ)) x =
      (2 : ℝ) ^ n * BernsteinMidpointAux.axisEval (fun i ↦ (c.get i : ℝ)) (x / 2) := by
  induction n with
  | zero => simp [bernsteinMidLeft, BernsteinMidpointAux.axisEval, ← rawBasis_eq, rawBasis]
  | succ n ih =>
    rw [axisEval_succ (n := n)]
    simp only [midLeft_castSucc, Int.cast_mul, Int.cast_ofNat]
    rw [axisEval_mul, ih]
    have he (i : Fin (n + 1)) : (bernsteinMidLeft (n + 1) c).get i.succ =
        (bernsteinMidLeft n (BernsteinMidpointAux.adjacent c)).get i := by
      rw [bernsteinMidLeft, get_ofFn, Fin.cons_succ]
    simp only [he]
    rw [ih]
    simp only [BernsteinMidpointAux.adjacent, get_ofFn, Int.cast_add]
    rw [axisEval_add, axisEval_succ (n := n) (x := x / 2), pow_succ]
    ring

/-- Right half-interval control points, multiplied by `2^n`. -/
def bernsteinMidRight (n : ℕ) (c : Vector ℤ (n + 1)) : Vector ℤ (n + 1) :=
  let cs := bernsteinMidLeft n (Vector.ofFn fun i ↦ c.get i.rev)
  Vector.ofFn fun i ↦ cs.get i.rev

private theorem axisEval_midRight (n : ℕ) (c : Vector ℤ (n + 1)) (x : ℝ) :
    BernsteinMidpointAux.axisEval (fun i ↦ ((bernsteinMidRight n c).get i : ℝ)) x =
      (2 : ℝ) ^ n * BernsteinMidpointAux.axisEval (fun i ↦ (c.get i : ℝ)) ((1 + x) / 2) := by
  simp only [bernsteinMidRight, get_ofFn]
  rw [axisEval_rev (fun i ↦ ((bernsteinMidLeft n (Vector.ofFn fun j ↦ c.get j.rev)).get i : ℝ)),
    axisEval_midLeft]
  simp only [get_ofFn]
  rw [axisEval_rev (fun i ↦ (c.get i : ℝ)), show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]

/-- A rectangular table of integer Bernstein coefficients, stored by rows. -/
abbrev BernsteinIntTable (n m : ℕ) := Vector (Vector ℤ (m + 1)) (n + 1)

/-- Tensor Bernstein evaluation before dividing by the common positive scale. -/
noncomputable def bernsteinIntEval {n m : ℕ} (c : BernsteinIntTable n m) (x y : ℝ) : ℝ :=
  BernsteinMidpointAux.axisEval (fun i ↦ BernsteinMidpointAux.axisEval (fun j ↦ ((c.get i).get j : ℝ)) y) x

def BernsteinMidpointAux.transpose {n m : ℕ} (c : BernsteinIntTable n m) : BernsteinIntTable m n :=
  Vector.ofFn fun j ↦ Vector.ofFn fun i ↦ (c.get i).get j

private theorem eval_transpose {n m : ℕ} (c : BernsteinIntTable n m) (x y : ℝ) :
    bernsteinIntEval (BernsteinMidpointAux.transpose c) y x = bernsteinIntEval c x y := by
  simp only [bernsteinIntEval, BernsteinMidpointAux.axisEval, BernsteinMidpointAux.transpose, get_ofFn, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

def BernsteinMidpointAux.midRow {n m : ℕ} (right : Bool) (c : BernsteinIntTable n m) :
    BernsteinIntTable n m :=
  Vector.ofFn fun i ↦ if right then bernsteinMidRight m (c.get i) else bernsteinMidLeft m (c.get i)

/-- Bisect the given coordinate, keeping a positive integer scale. -/
def bernsteinMidTable {n m : ℕ} (vertical right : Bool) (c : BernsteinIntTable n m) :
    BernsteinIntTable n m :=
  if vertical then BernsteinMidpointAux.midRow right c
  else BernsteinMidpointAux.transpose (BernsteinMidpointAux.midRow right (BernsteinMidpointAux.transpose c))

noncomputable def BernsteinMidpointAux.child (right : Bool) (x : ℝ) : ℝ := if right then (1 + x) / 2 else x / 2

private theorem eval_midRow {n m : ℕ} (right : Bool) (c : BernsteinIntTable n m) (x y : ℝ) :
    bernsteinIntEval (BernsteinMidpointAux.midRow right c) x y =
      (2 : ℝ) ^ m * bernsteinIntEval c x (BernsteinMidpointAux.child right y) := by
  cases right <;>
    simp only [bernsteinIntEval, BernsteinMidpointAux.midRow, BernsteinMidpointAux.child, get_ofFn, Bool.false_eq_true, ite_false, ite_true,
      axisEval_midLeft, axisEval_midRight, axisEval_mul]

/-- The midpoint algorithm is exact up to its positive scale. -/
theorem bernsteinIntEval_midTable {n m : ℕ} (vertical right : Bool)
    (c : BernsteinIntTable n m) (x y : ℝ) :
    bernsteinIntEval (bernsteinMidTable vertical right c) x y =
      if vertical then (2 : ℝ) ^ m * bernsteinIntEval c x (BernsteinMidpointAux.child right y)
      else (2 : ℝ) ^ n * bernsteinIntEval c (BernsteinMidpointAux.child right x) y := by
  cases vertical
  · simp only [bernsteinMidTable, Bool.false_eq_true, ite_false, eval_transpose, eval_midRow]
  · simp only [bernsteinMidTable, ite_true, eval_midRow]

/-- A dyadic subdivision schedule; `true` splits the second coordinate. -/
inductive BernsteinMidTree where
  | leaf
  | split (vertical : Bool) (left right : BernsteinMidTree)

/-- Check only leaf signs, propagating scaled integer tables along the tree.
Use `List.all` for kernel reduction: the module interface hides `Array.all`'s body. -/
def BernsteinMidTree.check {n m : ℕ} (c : BernsteinIntTable n m) : BernsteinMidTree → Bool
  | .leaf => c.toList.all (fun row ↦ row.toList.all (fun v ↦ decide (0 ≤ v)))
  | .split axis l r =>
    l.check (bernsteinMidTable axis false c) && r.check (bernsteinMidTable axis true c)

private theorem halves {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (2 * x ∈ Icc (0 : ℝ) 1 ∧ BernsteinMidpointAux.child false (2 * x) = x) ∨
    (2 * x - 1 ∈ Icc (0 : ℝ) 1 ∧ BernsteinMidpointAux.child true (2 * x - 1) = x) := by
  rcases le_or_gt x (1 / 2) with h | h
  · exact Or.inl ⟨⟨by linarith [hx.1], by linarith⟩, by simp [BernsteinMidpointAux.child]⟩
  · exact Or.inr ⟨⟨by linarith, by linarith [hx.2]⟩, by simp [BernsteinMidpointAux.child]⟩

private theorem leaf_nonneg {n m : ℕ} {c : BernsteinIntTable n m}
    (hc : BernsteinMidTree.leaf.check c = true) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinIntEval c x y := by
  have hc' (i : Fin (n + 1)) (j : Fin (m + 1)) : 0 ≤ (c.get i).get j := by
    simp only [BernsteinMidTree.check, Vector.toList, Array.all_toList,
      Array.all_eq_true, decide_eq_true_eq] at hc
    exact hc _ (by simpa only [Vector.size_toArray, Fin.val_cast] using i.isLt)
      _ (by simpa only [Vector.size_toArray, Fin.val_cast] using j.isLt)
  have hb (d i : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ certificateBernsteinBasis d i t := by
    rw [← rawBasis_eq]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
      (pow_nonneg (sub_nonneg.mpr ht.2) _)
  unfold bernsteinIntEval BernsteinMidpointAux.axisEval
  apply sum_nonneg
  intro i _
  refine mul_nonneg ?_ (hb n _ hx)
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by
    change 0 ≤ (((c.get i).get j : ℤ) : ℝ)
    exact_mod_cast hc' i j) (hb m _ hy)

/-- Passing the exact midpoint checker proves nonnegativity on the closed unit square. -/
theorem BernsteinMidTree.nonneg {n m : ℕ} (t : BernsteinMidTree)
    (c : BernsteinIntTable n m) (hc : t.check c = true)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinIntEval c x y := by
  induction t generalizing c x y with
  | leaf => exact leaf_nonneg hc hx hy
  | split axis l r hl hr =>
    simp only [BernsteinMidTree.check, Bool.and_eq_true] at hc
    cases axis
    · rcases halves hx with ⟨ht, he⟩ | ⟨ht, he⟩
      · have h := hl _ hc.1 ht hy
        simp only [bernsteinIntEval_midTable, Bool.false_eq_true, ite_false, he] at h
        exact nonneg_of_mul_nonneg_right h (by positivity)
      · have h := hr _ hc.2 ht hy
        simp only [bernsteinIntEval_midTable, Bool.false_eq_true, ite_false, he] at h
        exact nonneg_of_mul_nonneg_right h (by positivity)
    · rcases halves hy with ⟨ht, he⟩ | ⟨ht, he⟩
      · have h := hl _ hc.1 hx ht
        simp only [bernsteinIntEval_midTable, ite_true, he] at h
        exact nonneg_of_mul_nonneg_right h (by positivity)
      · have h := hr _ hc.2 hx ht
        simp only [bernsteinIntEval_midTable, ite_true, he] at h
        exact nonneg_of_mul_nonneg_right h (by positivity)

/-- Power evaluation on the same integer storage used for Bernstein tables. -/
noncomputable def bernsteinIntPowerEval {n m : ℕ} (p : BernsteinIntTable n m) (x y : ℝ) : ℝ :=
  certificatePolynomial (fun i j ↦ ((p.get i).get j : ℚ)) x y

def BernsteinMidpointAux.intWeight {n : ℕ} (i k : Fin (n + 1)) : ℤ :=
  (Nat.fast_choose i.val k.val : ℤ) * (k.val.factorial : ℤ) * ((n - k.val).factorial : ℤ)

private theorem intWeight_eq {n : ℕ} (i k : Fin (n + 1)) :
    (BernsteinMidpointAux.intWeight i k : ℚ) =
      (n.factorial : ℚ) * ((i.val.choose k.val : ℚ) / (n.choose k.val : ℚ)) := by
  have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  have he := Nat.choose_mul_factorial_mul_factorial hk
  have hn : (n.choose k.val : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold BernsteinMidpointAux.intWeight
  rw [← Nat.choose_eq_fast_choose]
  push_cast
  field_simp [hn]
  exact_mod_cast (by rw [← he]; ac_rfl :
    i.val.choose k.val * k.val.factorial * (n - k.val).factorial * n.choose k.val =
      i.val.choose k.val * n.factorial)

/-- Integer one-axis Bernstein transform with common scale `n!`. -/
def bernsteinAxisFromPower {n : ℕ} (c : Vector ℤ (n + 1)) : Vector ℤ (n + 1) :=
  Vector.ofFn fun i ↦ ∑ k, c.get k * BernsteinMidpointAux.intWeight i k

private theorem get_fromPower {n : ℕ} (c : Vector ℤ (n + 1)) (i : Fin (n + 1)) :
    (bernsteinAxisFromPower c).get i = ∑ k, c.get k * BernsteinMidpointAux.intWeight i k := by
  simp only [bernsteinAxisFromPower, get_ofFn]

/-- Convert a power table to Bernstein coefficients scaled by `n! m!`. -/
def bernsteinIntFromPower {n m : ℕ} (p : BernsteinIntTable n m) : BernsteinIntTable n m :=
  let rows := p.map bernsteinAxisFromPower
  BernsteinMidpointAux.transpose ((BernsteinMidpointAux.transpose rows).map bernsteinAxisFromPower)

private theorem fromPower_coeff {n m : ℕ} (p : BernsteinIntTable n m)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    ((bernsteinIntFromPower p).get i |>.get j : ℚ) =
      (n.factorial : ℚ) * (m.factorial : ℚ) *
        certificateBernsteinCoeff (fun k l ↦ ((p.get k).get l : ℚ)) i j := by
  simp only [bernsteinIntFromPower, BernsteinMidpointAux.transpose, get_ofFn]
  have get_map {α β : Type} {n : ℕ} (f : α → β) (v : Vector α n) (k : Fin n) :
      (v.map f).get k = f (v.get k) := Vector.getElem_map f k.isLt
  simp only [get_map, get_fromPower, get_ofFn]
  push_cast
  simp only [intWeight_eq, certificateBernsteinCoeff, mul_sum, sum_mul]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  by_cases hk : k.val ≤ i.val <;> by_cases hl : l.val ≤ j.val
  · simp only [hk, hl, and_self, ite_true]
    ring
  · simp [hk, hl, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hl)]
  · simp [hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
  · simp [hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

/-- The integer root table evaluates to the original polynomial times its
positive common scale. -/
theorem bernsteinIntFromPower_eval {n m : ℕ} (p : BernsteinIntTable n m) (x y : ℝ) :
    bernsteinIntEval (bernsteinIntFromPower p) x y =
      ((n.factorial : ℝ) * m.factorial) * bernsteinIntPowerEval p x y := by
  unfold bernsteinIntPowerEval
  rw [certificate_bernstein_expansion]
  simp only [bernsteinIntEval, BernsteinMidpointAux.axisEval, mul_sum, sum_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (fromPower_coeff p i j)
  push_cast at h
  rw [h]
  ring

/-- Prove positivity of the power polynomial by the integer subdivision check. -/
theorem BernsteinMidTree.power_nonneg {n m : ℕ} (t : BernsteinMidTree)
    (p : BernsteinIntTable n m) (hc : t.check (bernsteinIntFromPower p) = true)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinIntPowerEval p x y := by
  have h := t.nonneg _ hc hx hy
  rw [bernsteinIntFromPower_eval] at h
  exact nonneg_of_mul_nonneg_right h (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
    (Nat.cast_pos.mpr (Nat.factorial_pos _)))

private theorem vector_ext_get {α : Type*} {n : ℕ} {v w : Vector α n}
    (h : ∀ i, v.get i = w.get i) : v = w := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

private theorem table_ext_get {n m : ℕ} {p q : BernsteinIntTable n m}
    (h : ∀ i j, (p.get i).get j = (q.get i).get j) : p = q :=
  vector_ext_get fun i ↦ vector_ext_get (h i)

/-- Check a stored intermediate and root table one axis at a time. -/
theorem bernsteinIntFromPower_eq {n m : ℕ} {p middle root : BernsteinIntTable n m}
    (hrow : ∀ i j, (bernsteinAxisFromPower (p.get i)).get j = (middle.get i).get j)
    (hcol : ∀ i j, (bernsteinAxisFromPower (Vector.ofFn fun k : Fin (n + 1) ↦
        (middle.get k).get j)).get i = (root.get i).get j) :
    bernsteinIntFromPower p = root := by
  have he : p.map bernsteinAxisFromPower = middle := by
    apply table_ext_get
    intro i j
    have h : (p.map bernsteinAxisFromPower).get i =
        bernsteinAxisFromPower (p.get i) := Vector.getElem_map _ i.isLt
    rw [h, hrow]
  unfold bernsteinIntFromPower
  rw [he]
  apply table_ext_get
  intro i j
  have h : ((BernsteinMidpointAux.transpose middle).map bernsteinAxisFromPower).get j =
      bernsteinAxisFromPower ((BernsteinMidpointAux.transpose middle).get j) := Vector.getElem_map _ j.isLt
  simp only [BernsteinMidpointAux.transpose, get_ofFn] at h ⊢
  rw [h]
  exact hcol i j

-- The literal child tables act as evaluation checkpoints. Their identities
-- are checked locally, so the kernel never expands a deep chain of splits
-- when checking a coefficient at the bottom of a tree.
/-- Combine the leaf checks of two verified midpoint children. -/
theorem BernsteinMidTree.check_split {n m : ℕ} {axis : Bool} {t u : BernsteinMidTree}
    {p l r : BernsteinIntTable n m}
    (hl : ∀ i j, ((bernsteinMidTable axis false p).get i).get j = (l.get i).get j)
    (hr : ∀ i j, ((bernsteinMidTable axis true p).get i).get j = (r.get i).get j)
    (hc₁ : t.check l = true) (hc₂ : u.check r = true) :
    (BernsteinMidTree.split axis t u).check p = true := by
  rw [check, table_ext_get hl, table_ext_get hr, hc₁, hc₂]
  rfl

end NoEmbeddedEigenvalues
