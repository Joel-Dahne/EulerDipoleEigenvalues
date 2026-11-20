import NoEmbeddedEigenvalues.VirialAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Explicit mixed-sector comparison data

The matrix and operator use `(a,b)` coordinates, while the multipliers use
`(h,k) = (cos a, cos b)`. The potential is `V`, not the manuscript's `U=-V`.
The off-diagonal entry is `c sin a sin b`, not just `c`.

Real division supplies values at singular points but not boundary derivative
traces. In particular `F_u` has direction-dependent first derivatives at
`(h,k)=(0,0)`. Robin identities there must use the continuous extension from
`h>0`, rather than coordinate derivatives of the totalized function at zero.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set
open scoped ContDiff

/-- Open diagonal-coordinate cell. -/
def mixedOpenCell : Set (ℝ × ℝ) :=
  Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2)

/-- The open comparison quarter in `(a,b)` coordinates. -/
def mixedQuarterCell : Set (ℝ × ℝ) :=
  Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Ioo (0 : ℝ) (Real.pi / 2)

/-- The diagonal matrix entry as a rational function of `(h,k)`. -/
def mixedD (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + 2 * p.1 * (1 - p.1 ^ 2) / (p.1 + p.2)

/-- The factor multiplying `sin a sin b` in the off-diagonal entry. -/
def mixedC (p : ℝ × ℝ) : ℝ := 2 * p.1 ^ 2 / (p.1 + p.2) ^ 2

/-- Potential in `(h,k)`. At `(1,1)` the final quotient is totalized to its
    continuous value zero on the geometric quadrant. -/
def mixedV (p : ℝ × ℝ) : ℝ :=
  -p.1 ^ 2 * (2 - p.1 ^ 2 - p.2 ^ 2) / (p.1 + p.2) ^ 2 +
    2 * p.1 * (1 - p.1 ^ 2) / (p.1 + p.2) -
    2 * (1 - p.1 ^ 2) ^ 2 / (2 - p.1 ^ 2 - p.2 ^ 2)

/-- Diagonal entries of the matrix in `(a,b)`. -/
def mixedComparisonDiagonal (p : ℝ × ℝ) : ℝ := mixedD (Real.cos p.1, Real.cos p.2)

/-- Off-diagonal entry in `(a,b)`. -/
def mixedComparisonOffDiagonal (p : ℝ × ℝ) : ℝ :=
  mixedC (Real.cos p.1, Real.cos p.2) * Real.sin p.1 * Real.sin p.2

/-- Potential in `(a,b)`. -/
def mixedComparisonPotential (p : ℝ × ℝ) : ℝ := mixedV (Real.cos p.1, Real.cos p.2)

/-- The actual classical comparison operator `-div(G∇) + V`, not a polynomial
    supplied independently of the coefficient definitions. -/
def mixedComparisonOperator (z : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -(partialX (fun q ↦ mixedComparisonDiagonal q * partialX z q +
      mixedComparisonOffDiagonal q * partialY z q) p +
    partialY (fun q ↦ mixedComparisonOffDiagonal q * partialX z q +
      mixedComparisonDiagonal q * partialY z q) p) + mixedComparisonPotential p * z p

private theorem mixed_cos_pos {p : ℝ × ℝ} (hp : p ∈ mixedOpenCell) :
    0 < Real.cos p.1 ∧ 0 < Real.cos p.2 :=
  ⟨Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hp.1),
    Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hp.2)⟩

/-- Bounded coefficient claims separated from their definitions. -/
theorem mixed_comparison_coefficient_bounds {p : ℝ × ℝ} (hp : p ∈ mixedOpenCell) :
    0 ≤ -mixedComparisonPotential p ∧ -mixedComparisonPotential p ≤ 4 ∧
      mixedComparisonDiagonal p ≤ 3 ∧ |mixedComparisonOffDiagonal p| ≤ 2 := by
  obtain ⟨hh, hk⟩ := mixed_cos_pos hp
  let h := Real.cos p.1
  let k := Real.cos p.2
  let r := 2 - h ^ 2 - k ^ 2
  let u := 1 - h ^ 2
  have hs : 0 < h + k := add_pos hh hk
  have hhs : h ^ 2 ≤ 1 := by nlinarith only [Real.sin_sq_add_cos_sq p.1, sq_nonneg (Real.sin p.1)]
  have hks : k ^ 2 ≤ 1 := by nlinarith only [Real.sin_sq_add_cos_sq p.2, sq_nonneg (Real.sin p.2)]
  have hu : 0 ≤ u := sub_nonneg.mpr hhs
  have hur : u ≤ r := by dsimp [u, r]; linarith
  have hr : 0 ≤ r := hu.trans hur
  have hr₂ : r ≤ 2 := by dsimp [r]; nlinarith
  have hd : h ^ 2 ≤ (h + k) ^ 2 :=
    pow_le_pow_left₀ hh.le (le_add_of_nonneg_right hk.le) _
  have hh' : h ≤ h + k := le_add_of_nonneg_right hk.le
  have hhu : h * u ≤ h + k := by
    have hu₁ : u ≤ 1 := by dsimp [u]; nlinarith
    exact (mul_le_of_le_one_right hh.le hu₁).trans hh'
  have hj : |Real.sin p.1 * Real.sin p.2| ≤ 1 := by
    rw [abs_mul]
    have ha (x : ℝ) : |Real.sin x| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
    exact (mul_le_of_le_one_right (abs_nonneg _) (ha _)).trans (ha _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 ≤ -(-h ^ 2 * r / (h + k) ^ 2 + 2 * h * u / (h + k) - 2 * u ^ 2 / r)
    rcases hr.eq_or_lt with hr₀ | hrp
    · have hu₀ : u = 0 := le_antisymm (hur.trans hr₀.ge) hu
      rw [← hr₀, hu₀]
      simp
    · have hn : 0 ≤ ((h * r - u * (h + k)) ^ 2 + (u * (h + k)) ^ 2) /
          ((h + k) ^ 2 * r) := by positivity
      convert hn using 1
      field_simp
      ring
  · change -(-h ^ 2 * r / (h + k) ^ 2 + 2 * h * u / (h + k) - 2 * u ^ 2 / r) ≤ 4
    have h₁ : h ^ 2 * r / (h + k) ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      exact (mul_le_mul_of_nonneg_right hd hr).trans
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr₂ (sq_nonneg (h + k)))
    have h₂ : u ^ 2 / r ≤ 1 := by
      rcases hr.eq_or_lt with hr₀ | hrp
      · rw [← hr₀, div_zero]; norm_num
      · apply (div_le_iff₀ hrp).mpr
        rw [one_mul]
        have hu₁ : u ≤ 1 := by dsimp [u]; nlinarith
        exact (by simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hu₁ hu :
          u ^ 2 ≤ u).trans hur
    have h₃ : 0 ≤ 2 * h * u / (h + k) := by positivity
    rw [neg_mul, neg_div, mul_div_assoc (2 : ℝ) (u ^ 2) r]
    linarith only [h₁, h₂, h₃]
  · change h ^ 2 + 2 * h * u / (h + k) ≤ 3
    have h₁ : 2 * h * u / (h + k) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
    linarith
  · change |2 * h ^ 2 / (h + k) ^ 2 * Real.sin p.1 * Real.sin p.2| ≤ 2
    rw [mul_assoc, abs_mul, abs_of_nonneg (by positivity)]
    have hi : 2 * h ^ 2 / (h + k) ^ 2 ≤ 2 := (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      (by linarith)
    exact (mul_le_of_le_one_right (by positivity) hj).trans hi

/-- Polynomial part of the odd-in-b multiplier. -/
def mixedOddBPolynomial (h k : ℝ) : ℝ :=
  1 + (4132 * k ^ 2 + 2167 * k ^ 3 - 2011 * h * k -
    7640 * h * k ^ 2 - 226 * h ^ 2 + 3795 * h ^ 2 * k - 834 * h ^ 3) / 10000

/-- The explicit logarithmic multiplier `F_v(h,k)`. -/
def mixedOddBMultiplier (p : ℝ × ℝ) : ℝ :=
  mixedOddBPolynomial p.1 p.2 +
    (808 * p.1 * p.2 + 2505 * p.1 * p.2 ^ 2) / 10000 * Real.log p.1

/-- The logarithmic multiplier is smooth wherever the first coordinate is positive. -/
theorem mixedOddBMultiplier_contDiffAt {n : ℕ∞ω} {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ n mixedOddBMultiplier p := by
  have hlog : ContDiffAt ℝ n (fun q : ℝ × ℝ ↦ Real.log q.1) p :=
    (Real.contDiffAt_log.mpr hp.ne').comp p contDiff_fst.contDiffAt
  unfold mixedOddBMultiplier mixedOddBPolynomial
  fun_prop

private theorem mixedOddBPolynomial_antitone {k : ℝ} (hk : 0 ≤ k) :
    AntitoneOn (fun h ↦ mixedOddBPolynomial h k) (Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · unfold mixedOddBPolynomial
    fun_prop
  · intro h _
    unfold mixedOddBPolynomial
    fun_prop
  · simp only [interior_Icc]
    intro h hh
    have hd : deriv (fun x ↦ mixedOddBPolynomial x k) h =
        (-(2502 * h ^ 2 - 7590 * h * k + 7640 * k ^ 2) - 452 * h - 2011 * k) / 10000 := by
      simp (disch := fun_prop) only [mixedOddBPolynomial, deriv_const_add, deriv_div_const,
        deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_id, deriv_pow_field,
        deriv_const]
      ring
    rw [hd]
    have hquad : 0 ≤ 2502 * h ^ 2 - 7590 * h * k + 7640 * k ^ 2 := by
      nlinarith only [sq_nonneg (5004 * h - 7590 * k), sq_nonneg k]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hh.1]) (by norm_num)

private theorem neg_mul_log_le_three_eighth {h : ℝ} (hh : 0 < h) :
    -(h * Real.log h) ≤ 3 / 8 := by
  have hE : 0 < Real.exp 1 := Real.exp_pos _
  have hp : 0 < h * Real.exp 1 := mul_pos hh hE
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv, Real.log_mul hh.ne' hE.ne', Real.log_exp, mul_inv_rev] at hlog
  have hle := mul_le_mul_of_nonneg_left hlog hh.le
  have heq : h * ((Real.exp 1)⁻¹ * h⁻¹ - 1) = (Real.exp 1)⁻¹ - h := by
    field_simp
  rw [heq] at hle
  have hE' : (Real.exp 1)⁻¹ ≤ 3 / 8 := by
    rw [inv_le_iff_one_le_mul₀ hE]
    linarith only [Real.exp_one_gt_d9]
  linarith only [hle, hE']

private theorem mixedOddBMultiplier_bounds {q : ℝ × ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    (3 / 4 : ℝ) < mixedOddBMultiplier q ∧ mixedOddBMultiplier q < 5 / 3 := by
  let h := q.1
  let k := q.2
  have hh : h ∈ Ioc 0 1 := hq.1
  have hk : k ∈ Icc 0 1 := hq.2
  have han := mixedOddBPolynomial_antitone hk.1
  have h₁ := han (show h ∈ Icc 0 1 from ⟨hh.1.le, hh.2⟩) (by simp) hh.2
  have h₀ := han (show (0 : ℝ) ∈ Icc 0 1 by simp) ⟨hh.1.le, hh.2⟩ hh.1.le
  have hlog : Real.log h ≤ 0 := Real.log_nonpos hh.1.le hh.2
  have hk₀ : 0 ≤ k := hk.1
  have hkl : 0 ≤ (808 * k + 2505 * k ^ 2) / 10000 := by positivity
  have hk₂ : k ^ 2 ≤ 1 := pow_le_one₀ hk₀ hk.2
  have hk₃ : k ^ 3 ≤ 1 := pow_le_one₀ hk₀ hk.2
  have hku : (808 * k + 2505 * k ^ 2) / 10000 ≤ 3313 / 10000 := by linarith [hk.2]
  have hb₁ : 894 / 1000 ≤ mixedOddBPolynomial 1 k := by
    have hquad : 0 ≤ 1784 - 3508 * k + 2167 * k ^ 2 := by
      nlinarith only [sq_nonneg (4334 * k - 3508)]
    unfold mixedOddBPolynomial
    nlinarith only [mul_nonneg hk.1 hquad]
  have hb₀ : mixedOddBPolynomial 0 k ≤ 16299 / 10000 := by
    unfold mixedOddBPolynomial
    linarith only [hk₂, hk₃]
  have hident : mixedOddBMultiplier q = mixedOddBPolynomial h k +
      ((808 * k + 2505 * k ^ 2) / 10000) * (h * Real.log h) := by
    unfold mixedOddBMultiplier
    dsimp [h, k]
    ring
  rw [hident]
  have hlo := mul_le_mul_of_nonneg_left (neg_mul_log_le_three_eighth hh.1) hkl
  have hlo' := mul_le_mul_of_nonneg_right hku (by norm_num : 0 ≤ (3 / 8 : ℝ))
  have hup := mul_nonpos_of_nonneg_of_nonpos hkl (mul_nonpos_of_nonneg_of_nonpos hh.1.le hlog)
  exact ⟨by linarith only [h₁, hb₁, hlo, hlo'], by linarith only [h₀, hb₀, hup]⟩

/-- The odd-in-`b` comparison in actual diagonal coordinates. -/
def mixedOddBComparison (p : ℝ × ℝ) : ℝ :=
  Real.sin p.2 * mixedOddBMultiplier (Real.cos p.1, Real.cos p.2)

/-- Polynomial part of `1000 F_u(h,k)`. -/
def mixedOddAPolynomial (p : ℝ × ℝ) : ℝ :=
  721 * p.2 ^ 2 - 107 * p.2 ^ 3 + 60 * p.2 ^ 4 + 85 * p.2 ^ 6 +
    p.1 * (-519 * p.2 - 64 * p.2 ^ 2 - 26 * p.2 ^ 3 - 400 * p.2 ^ 5) +
    p.1 ^ 2 * (-98 - 79 * p.2 ^ 2 + 890 * p.2 ^ 4) +
    p.1 ^ 3 * (781 - 583 * p.2 - 842 * p.2 ^ 3) +
    p.1 ^ 4 * (-240 + 677 * p.2 + 124 * p.2 ^ 2) +
    p.1 ^ 5 * (-263 + 37 * p.2) + 53 * p.1 ^ 6 - p.1 / 2 - 4 * p.2

/-- The rational exponent `F_u(h,k)`; no exponential is taken in these variables. -/
def mixedOddAExponent (p : ℝ × ℝ) : ℝ :=
  (mixedOddAPolynomial p -
    4 * p.1 ^ 3 / (p.1 + p.2) ^ 2 - 2744 * p.1 ^ 6 / (p.1 + p.2) ^ 4 +
    1033 * p.1 ^ 8 / (p.1 + p.2) ^ 6 + 224 * p.1 ^ 4 / (p.1 + p.2) +
    235 * p.1 ^ 8 / (p.1 + p.2) ^ 5) / 1000

/-- Smoothness away from the vanishing denominator, including the regular Robin side. -/
theorem mixedOddAExponent_contDiffAt {n : ℕ∞ω} {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    ContDiffAt ℝ n mixedOddAExponent p := by
  unfold mixedOddAExponent mixedOddAPolynomial
  fun_prop (disch := positivity)

private theorem compact_partial_bounds {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, |f q| ≤ C ∧ |partialX f q| ≤ C ∧ |partialY f q| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((hf.continuous.abs.add (contDiff_partialX (n := 0) (by simpa using hf)).continuous.abs).add
      (contDiff_partialY (n := 0) (by simpa using hf)).continuous.abs).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun q hq ↦ ?_⟩
  have h := hC q hq
  simp only [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg
    (add_nonneg (add_nonneg (abs_nonneg (f q)) (abs_nonneg (partialX f q)))
      (abs_nonneg (partialY f q)))] at h
  have hm := le_max_left C 0
  exact ⟨by linarith [abs_nonneg (partialX f q), abs_nonneg (partialY f q)],
    by linarith [abs_nonneg (f q), abs_nonneg (partialY f q)],
    by linarith [abs_nonneg (f q), abs_nonneg (partialX f q)]⟩

private abbrev mixedUnitSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private theorem mixed_regularStrip_subset :
    Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ mixedUnitSquare :=
  fun _ hq ↦ ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩

private def mixedRationalTerm (m n : ℕ) (q : ℝ × ℝ) : ℝ :=
  q.1 ^ m / (q.1 + q.2) ^ n

/-- Cancel a power of the larger denominator against the same power of `h`.
This estimate also holds for the totalized value at the corner. -/
private theorem mixedRationalTerm_le_pow {m n : ℕ} (hmn : n ≤ m)
    {q : ℝ × ℝ} (hq : q ∈ mixedUnitSquare) :
    |mixedRationalTerm m n q| ≤ q.1 ^ (m - n) := by
  have hh : 0 ≤ q.1 := hq.1.1
  have hk : 0 ≤ q.2 := hq.2.1
  by_cases hs : 0 < q.1 + q.2
  · rw [mixedRationalTerm, abs_of_nonneg (by positivity), div_le_iff₀ (pow_pos hs _)]
    calc
      q.1 ^ m = q.1 ^ (m - n) * q.1 ^ n := by rw [← pow_add, Nat.sub_add_cancel hmn]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hh (le_add_of_nonneg_right hk) _) (by positivity)
  · have hz : q.1 = 0 := by linarith
    have hkz : q.2 = 0 := by linarith
    rcases n with _ | n
    · simp [mixedRationalTerm, abs_of_nonneg (pow_nonneg hh m)]
    · simp [mixedRationalTerm, hz, hkz]

private theorem mixedRationalTerm_continuousOn {m n : ℕ} (hmn : n < m) :
    ContinuousOn (mixedRationalTerm m n) mixedUnitSquare := by
  intro q hq
  have hh : 0 ≤ q.1 := hq.1.1
  have hk : 0 ≤ q.2 := hq.2.1
  by_cases hs : 0 < q.1 + q.2
  · apply ContinuousAt.continuousWithinAt
    unfold mixedRationalTerm
    fun_prop (disch := positivity)
  · have hzero : q = (0, 0) := Prod.ext (by linarith) (by linarith)
    subst q
    have hv : (mixedRationalTerm m n) (0, 0) = 0 := by
      simp [mixedRationalTerm, Nat.ne_of_gt (Nat.zero_le n |>.trans_lt hmn)]
    rw [ContinuousWithinAt, hv]
    apply squeeze_zero_norm' (a := fun q : ℝ × ℝ ↦ q.1 ^ (m - n))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa only [Real.norm_eq_abs] using mixedRationalTerm_le_pow hmn.le hz
    · have ht : ContinuousWithinAt (fun z : ℝ × ℝ ↦ z.1 ^ (m - n))
          mixedUnitSquare (0, 0) := (continuous_fst.pow _).continuousWithinAt
      simpa only [ContinuousWithinAt, Prod.fst, zero_pow (Nat.sub_ne_zero_of_lt hmn)] using ht

private theorem mixedRationalTerm_partials (m n : ℕ) {q : ℝ × ℝ} (hs : 0 < q.1 + q.2) :
    partialX (mixedRationalTerm m n) q =
      m * mixedRationalTerm (m - 1) n q - n * mixedRationalTerm m (n + 1) q ∧
    partialY (mixedRationalTerm m n) q = -n * mixedRationalTerm m (n + 1) q := by
  have hx : HasDerivAt (fun x : ℝ ↦ x + q.2) 1 q.1 := (hasDerivAt_id q.1).add_const _
  have hy : HasDerivAt (fun y : ℝ ↦ q.1 + y) 1 q.2 := (hasDerivAt_id q.2).const_add _
  have Hx := (((hasDerivAt_id q.1).pow m).div (hx.pow n) (pow_pos hs n).ne').deriv
  have Hy := ((hasDerivAt_const q.2 (q.1 ^ m)).div (hy.pow n) (pow_pos hs n).ne').deriv
  constructor
  · change deriv (fun x ↦ x ^ m / (x + q.2) ^ n) q.1 = _
    change deriv (id ^ m / (fun x : ℝ ↦ x + q.2) ^ n) q.1 = _
    rw [Hx]
    simp only [Pi.pow_apply, id_eq, mul_one, mixedRationalTerm]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ _ n, pow_succ _ (n + 1)]
      field_simp [hs.ne']
  · change deriv (fun y ↦ q.1 ^ m / (q.1 + y) ^ n) q.2 = _
    change deriv ((fun _ : ℝ ↦ q.1 ^ m) / (fun y : ℝ ↦ q.1 + y) ^ n) q.2 = _
    rw [Hy]
    simp only [Pi.pow_apply, zero_mul, zero_sub, mul_one, mixedRationalTerm]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ _ n, pow_succ _ (n + 1)]
      field_simp [hs.ne']

private theorem mixedRationalTerm_bounds {m n : ℕ} (hmn : n < m)
    {q : ℝ × ℝ} (hq : q ∈ mixedUnitSquare) (hs : 0 < q.1 + q.2) :
    |mixedRationalTerm m n q| ≤ 1 ∧ |partialX (mixedRationalTerm m n) q| ≤ m + n ∧
      |partialY (mixedRationalTerm m n) q| ≤ n := by
  have hb (a b : ℕ) (hab : b ≤ a) : |mixedRationalTerm a b q| ≤ 1 :=
    (mixedRationalTerm_le_pow hab hq).trans (pow_le_one₀ hq.1.1 hq.1.2)
  obtain ⟨hx, hy⟩ := mixedRationalTerm_partials m n hs
  refine ⟨hb _ _ hmn.le, ?_, ?_⟩
  · rw [hx]
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul, Nat.abs_cast]
    have h₁ := mul_le_mul_of_nonneg_left (hb (m - 1) n (by omega))
      (Nat.cast_nonneg (α := ℝ) m)
    have h₂ := mul_le_mul_of_nonneg_left (hb m (n + 1) hmn) (Nat.cast_nonneg (α := ℝ) n)
    linarith
  · rw [hy, abs_mul, abs_neg, Nat.abs_cast]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hb m (n + 1) hmn) (Nat.cast_nonneg (α := ℝ) n)

private theorem mixedOddAExponent_eq (q : ℝ × ℝ) :
    mixedOddAExponent q = (mixedOddAPolynomial q -
    4 * mixedRationalTerm 3 2 q - 2744 * mixedRationalTerm 6 4 q +
    1033 * mixedRationalTerm 8 6 q + 224 * mixedRationalTerm 4 1 q +
    235 * mixedRationalTerm 8 5 q) / 1000 := by
  simp only [mixedOddAExponent, mixedRationalTerm, mul_div_assoc, pow_one]

/-- The positive-degree rational terms extend continuously through the corner. -/
theorem mixedOddAExponent_continuousOn :
    ContinuousOn mixedOddAExponent (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  rw [show mixedOddAExponent = _ from funext mixedOddAExponent_eq]
  have hpoly : Continuous mixedOddAPolynomial := by unfold mixedOddAPolynomial; fun_prop
  have h32 := mixedRationalTerm_continuousOn (m := 3) (n := 2) (by decide)
  have h64 := mixedRationalTerm_continuousOn (m := 6) (n := 4) (by decide)
  have h86 := mixedRationalTerm_continuousOn (m := 8) (n := 6) (by decide)
  have h41 := mixedRationalTerm_continuousOn (m := 4) (n := 1) (by decide)
  have h85 := mixedRationalTerm_continuousOn (m := 8) (n := 5) (by decide)
  fun_prop

private theorem mixedOddAExponent_abs_partials_bound {q : ℝ × ℝ} (hq : q ∈ mixedUnitSquare)
    (hs : 0 < q.1 + q.2) (C : ℝ) (hC : 0 ≤ C)
    (hp : |mixedOddAPolynomial q| ≤ C ∧ |partialX mixedOddAPolynomial q| ≤ C ∧
      |partialY mixedOddAPolynomial q| ≤ C) :
    |mixedOddAExponent q| ≤ C + 100 ∧ |partialX mixedOddAExponent q| ≤ C + 100 ∧
      |partialY mixedOddAExponent q| ≤ C + 100 := by
  have h32 := mixedRationalTerm_bounds (m := 3) (n := 2) (by decide) hq hs
  have h64 := mixedRationalTerm_bounds (m := 6) (n := 4) (by decide) hq hs
  have h86 := mixedRationalTerm_bounds (m := 8) (n := 6) (by decide) hq hs
  have h41 := mixedRationalTerm_bounds (m := 4) (n := 1) (by decide) hq hs
  have h85 := mixedRationalTerm_bounds (m := 8) (n := 5) (by decide) hq hs
  have hdiff (m n : ℕ) : DifferentiableAt ℝ (mixedRationalTerm m n) q := by
    unfold mixedRationalTerm
    fun_prop (disch := positivity)
  have hdP : DifferentiableAt ℝ mixedOddAPolynomial q := by unfold mixedOddAPolynomial; fun_prop
  have hx (f : ℝ × ℝ → ℝ) (hf : DifferentiableAt ℝ f q) :
      DifferentiableAt ℝ (fun t : ℝ ↦ f (t, q.2)) q.1 :=
    hf.comp q.1 (by fun_prop)
  have hy (f : ℝ × ℝ → ℝ) (hf : DifferentiableAt ℝ f q) :
      DifferentiableAt ℝ (fun t : ℝ ↦ f (q.1, t)) q.2 :=
    hf.comp q.2 (by fun_prop)
  have H (a b c d e f : ℝ) (ha : |a| ≤ C) (hb : |b| ≤ 5) (hc : |c| ≤ 10)
      (hd : |d| ≤ 14) (he : |e| ≤ 5) (hf : |f| ≤ 13) :
      |(a - 4 * b - 2744 * c + 1033 * d + 224 * e + 235 * f) / 1000| ≤ C + 100 := by
    rw [abs_div, abs_of_nonneg (by norm_num : 0 ≤ (1000 : ℝ)), div_le_iff₀ (by norm_num)]
    rw [abs_le] at *
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [mixedOddAExponent_eq]
    exact H _ _ _ _ _ _ hp.1 (h32.1.trans (by norm_num)) (h64.1.trans (by norm_num))
      (h86.1.trans (by norm_num)) (h41.1.trans (by norm_num)) (h85.1.trans (by norm_num))
  · unfold partialX at *
    simp (disch := first | exact hx _ hdP | exact hx _ (hdiff _ _) | fun_prop)
      only [mixedOddAExponent_eq, deriv_fun_add, deriv_fun_sub, deriv_const_mul_field,
        deriv_div_const]
    exact H _ _ _ _ _ _ hp.2.1 (h32.2.1.trans (by norm_num)) (h64.2.1.trans (by norm_num))
      (h86.2.1.trans (by norm_num)) (h41.2.1.trans (by norm_num)) (h85.2.1.trans (by norm_num))
  · unfold partialY at *
    simp (disch := first | exact hy _ hdP | exact hy _ (hdiff _ _) | fun_prop)
      only [mixedOddAExponent_eq, deriv_fun_add, deriv_fun_sub, deriv_const_mul_field,
        deriv_div_const]
    exact H _ _ _ _ _ _ hp.2.2 (h32.2.2.trans (by norm_num)) (h64.2.2.trans (by norm_num))
      (h86.2.2.trans (by norm_num)) (h41.2.2.trans (by norm_num)) (h85.2.2.trans (by norm_num))

/-- Homogeneity bounds the value and both first derivatives on the whole regular strip. -/
theorem mixed_odd_a_exponent_bounds_regular : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |mixedOddAExponent q| ≤ C ∧ |partialX mixedOddAExponent q| ≤ C ∧
        |partialY mixedOddAExponent q| ≤ C := by
  have hp : ContDiff ℝ 1 mixedOddAPolynomial := by unfold mixedOddAPolynomial; fun_prop
  obtain ⟨C, hC, hb⟩ := compact_partial_bounds hp (isCompact_Icc.prod isCompact_Icc :
    IsCompact mixedUnitSquare)
  exact ⟨C + 100, by positivity, fun q hq ↦
    mixedOddAExponent_abs_partials_bound (mixed_regularStrip_subset hq)
      (add_pos_of_pos_of_nonneg hq.1.1 hq.2.1) C hC (hb q (mixed_regularStrip_subset hq))⟩

/-- The odd-in-`a` comparison in actual diagonal coordinates. -/
def mixedOddAComparison (p : ℝ × ℝ) : ℝ :=
  Real.sin p.1 * Real.exp (mixedOddAExponent (Real.cos p.1, Real.cos p.2))

/-- Homogeneity gives bounded value and first derivatives, not continuity of the
    gradient at the corner. -/
theorem mixed_odd_a_exponent_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      |mixedOddAExponent p| ≤ C ∧ |partialX mixedOddAExponent p| ≤ C ∧
        |partialY mixedOddAExponent p| ≤ C := by
  obtain ⟨C, hC, hb⟩ := mixed_odd_a_exponent_bounds_regular
  exact ⟨C, hC, fun p hp ↦ hb p ⟨⟨hp.1.1, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩⟩

private def mixedOddBLogCoeff (q : ℝ × ℝ) : ℝ := (808 * q.2 + 2505 * q.2 ^ 2) / 10000

private theorem mixedOddBMultiplier_eq (q : ℝ × ℝ) :
    mixedOddBMultiplier q = mixedOddBPolynomial q.1 q.2 +
      mixedOddBLogCoeff q * (q.1 * Real.log q.1) := by
  unfold mixedOddBMultiplier mixedOddBLogCoeff
  ring

/-- The factor `h log h` gives continuity through `h=0`. -/
theorem mixedOddBMultiplier_continuous : Continuous mixedOddBMultiplier := by
  rw [show mixedOddBMultiplier = _ from funext mixedOddBMultiplier_eq]
  have hlog : Continuous (fun q : ℝ × ℝ ↦ q.1 * Real.log q.1) :=
    Real.continuous_mul_log.comp continuous_fst
  unfold mixedOddBPolynomial mixedOddBLogCoeff
  fun_prop

/-- The multiplier stays uniformly positive, including at `h=0`. -/
theorem mixed_odd_b_multiplier_closed_bounds {q : ℝ × ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    (3 / 4 : ℝ) ≤ mixedOddBMultiplier q ∧ mixedOddBMultiplier q ≤ 5 / 3 := by
  rcases hq.1.1.eq_or_lt with hh | hh
  · rw [mixedOddBMultiplier_eq, ← hh]
    have hk₀ : 0 ≤ q.2 := hq.2.1
    have hk₂ : q.2 ^ 2 ≤ 1 := pow_le_one₀ hk₀ hq.2.2
    have hk₃ : q.2 ^ 3 ≤ 1 := pow_le_one₀ hk₀ hq.2.2
    simp only [zero_mul, mul_zero, add_zero, mixedOddBPolynomial, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), sub_zero]
    constructor
    · have : 0 ≤ (4132 * q.2 ^ 2 + 2167 * q.2 ^ 3) / 10000 := by positivity
      linarith
    · linarith
  · obtain ⟨hl, hu⟩ := mixedOddBMultiplier_bounds ⟨⟨hh, hq.1.2⟩, hq.2⟩
    exact ⟨hl.le, hu.le⟩

/-- Bounded smooth coefficients times `h log h` and its derivative
give exactly a logarithmic bound on the regular strip. -/
theorem mixed_odd_b_multiplier_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |partialX mixedOddBMultiplier q| + |partialY mixedOddBMultiplier q| ≤
        C * (1 + |Real.log q.1|) := by
  let P : ℝ × ℝ → ℝ := fun q ↦ mixedOddBPolynomial q.1 q.2
  let L := mixedOddBLogCoeff
  have hp : ContDiff ℝ 1 P := by unfold P mixedOddBPolynomial; fun_prop
  have hl : ContDiff ℝ 1 L := by unfold L mixedOddBLogCoeff; fun_prop
  have hK : IsCompact mixedUnitSquare := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC, hbP⟩ := compact_partial_bounds hp hK
  obtain ⟨D, hD, hbL⟩ := compact_partial_bounds hl hK
  refine ⟨2 * (C + D), by positivity, fun q hq ↦ ?_⟩
  obtain ⟨_, hPx, hPy⟩ := hbP q (mixed_regularStrip_subset hq)
  obtain ⟨hL, _, hLy⟩ := hbL q (mixed_regularStrip_subset hq)
  have hfit : mixedOddBMultiplier = fun p ↦ P p + L p * (p.1 * Real.log p.1) :=
    funext mixedOddBMultiplier_eq
  have hP₀ : DifferentiableAt ℝ (fun t : ℝ ↦ P (t, q.2)) q.1 := by
    unfold P mixedOddBPolynomial
    fun_prop
  have hP₁ : DifferentiableAt ℝ (fun t : ℝ ↦ P (q.1, t)) q.2 := by
    unfold P mixedOddBPolynomial
    fun_prop
  have hL₁ : DifferentiableAt ℝ (fun t : ℝ ↦ L (q.1, t)) q.2 := by
    unfold L mixedOddBLogCoeff
    fun_prop
  have hx : partialX mixedOddBMultiplier q =
      partialX P q + L q * (Real.log q.1 + 1) := by
    rw [hfit]
    exact (hP₀.hasDerivAt.add ((Real.hasDerivAt_mul_log hq.1.1.ne').const_mul (L q))).deriv
  have hy : partialY mixedOddBMultiplier q =
      partialY P q + partialY L q * (q.1 * Real.log q.1) := by
    rw [hfit]
    exact (hP₁.hasDerivAt.add (hL₁.hasDerivAt.mul_const (q.1 * Real.log q.1))).deriv
  have hlog : |q.1 * Real.log q.1| ≤ 1 := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1.1.le
      (Real.log_nonpos hq.1.1.le hq.1.2))]
    exact (neg_mul_log_le_three_eighth hq.1.1).trans (by norm_num)
  rw [hx, hy]
  have hx' : |partialX P q + L q * (Real.log q.1 + 1)| ≤ C + D * (1 + |Real.log q.1|) := by
    refine (abs_add_le _ _).trans (add_le_add hPx ?_)
    rw [abs_mul]
    apply mul_le_mul hL _ (abs_nonneg _) hD
    simpa only [abs_one, add_comm |Real.log q.1| 1] using abs_add_le (Real.log q.1) 1
  have hy' : |partialY P q + partialY L q * (q.1 * Real.log q.1)| ≤ C + D := by
    refine (abs_add_le _ _).trans (add_le_add hPy ?_)
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hLy hlog (abs_nonneg _) hD
  have hC' := mul_nonneg hC (abs_nonneg (Real.log q.1))
  have hD' := mul_nonneg hD (abs_nonneg (Real.log q.1))
  nlinarith only [hx', hy', hC', hD']

/-- Determinant of the second-order matrix, with its positive expansion on the
open cell. The positive diagonal and determinant give positive definiteness. -/
theorem mixed_comparison_matrix_positive {q : ℝ × ℝ} (hq : q ∈ mixedOpenCell) :
    let h := Real.cos q.1
    let k := Real.cos q.2
    let d := mixedComparisonDiagonal q
    let j := mixedComparisonOffDiagonal q
    0 < d ∧ 0 < d ^ 2 - j ^ 2 ∧
    d ^ 2 - j ^ 2 = h ^ 2 / (h + k) ^ 4 *
      (h ^ 6 + 4 * h * (2 - h ^ 2) * k + (4 + 8 * h ^ 2 - 6 * h ^ 4) * k ^ 2 +
        4 * h * k ^ 3 + h ^ 2 * k ^ 4) := by
  obtain ⟨hh, hk⟩ := mixed_cos_pos hq
  let h := Real.cos q.1
  let k := Real.cos q.2
  have hp : 0 < h + k := add_pos hh hk
  have hh₂ : h ^ 2 ≤ 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq q.1, sq_nonneg (Real.sin q.1)]
  have hd : 0 < mixedComparisonDiagonal q := by
    change 0 < h ^ 2 + 2 * h * (1 - h ^ 2) / (h + k)
    exact add_pos_of_pos_of_nonneg (by positivity)
      (div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hh₂)) hp.le)
  let B := h ^ 6 + 4 * h * (2 - h ^ 2) * k + (4 + 8 * h ^ 2 - 6 * h ^ 4) * k ^ 2 +
    4 * h * k ^ 3 + h ^ 2 * k ^ 4
  have he : mixedComparisonDiagonal q ^ 2 - mixedComparisonOffDiagonal q ^ 2 =
      h ^ 2 / (h + k) ^ 4 * B := by
    change (h ^ 2 + 2 * h * (1 - h ^ 2) / (h + k)) ^ 2 -
      (2 * h ^ 2 / (h + k) ^ 2 * Real.sin q.1 * Real.sin q.2) ^ 2 =
      h ^ 2 / (h + k) ^ 4 * B
    rw [mul_pow, mul_pow, show Real.sin q.1 ^ 2 = 1 - h ^ 2 by
      linarith [Real.sin_sq_add_cos_sq q.1], show Real.sin q.2 ^ 2 = 1 - k ^ 2 by
      linarith [Real.sin_sq_add_cos_sq q.2]]
    dsimp only [B]
    field_simp
    ring
  have h₁ : 0 ≤ 2 - h ^ 2 := by linarith
  have h₂ : 0 ≤ 4 + 8 * h ^ 2 - 6 * h ^ 4 := by
    nlinarith only [sq_nonneg h, mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh₂)]
  exact ⟨hd, by rw [he]; dsimp only [B]; positivity, he⟩

/-- The Robin numerator at `(h,0)` for a multiplier `ρ`.
The first term is `3hρ` for odd-in-a comparisons and `hρ` for odd-in-b. -/
def mixedRobinNumerator (oddA : Bool) (ρ : ℝ × ℝ → ℝ) (h : ℝ) : ℝ :=
  (if oddA then 3 else 1) * h * ρ (h, 0) -
    2 * (1 - h ^ 2) * partialX ρ (h, 0) - (2 - h ^ 2) * partialY ρ (h, 0)

/-- The multiplier bounds and boundary inequality for the odd-in-b comparison.
All derivatives on the Robin side are taken at `h>0`. -/
theorem mixed_odd_b_multiplier_robin :
    (∀ q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) < mixedOddBMultiplier q ∧ mixedOddBMultiplier q < 5 / 3) ∧
    ∀ h ∈ Ioc (0 : ℝ) 1,
      1789 / 2500 * h ≤ mixedRobinNumerator false mixedOddBMultiplier h := by
  refine ⟨fun _ hq ↦ mixedOddBMultiplier_bounds hq, ?_⟩
  intro h hh
  have hv (x : ℝ) : mixedOddBMultiplier (x, 0) =
      1 + (-226 * x ^ 2 - 834 * x ^ 3) / 10000 := by
    simp [mixedOddBMultiplier, mixedOddBPolynomial]
  have hx : partialX mixedOddBMultiplier (h, 0) = (-452 * h - 2502 * h ^ 2) / 10000 := by
    change deriv (fun x ↦ mixedOddBMultiplier (x, 0)) h = _
    simp (disch := fun_prop) only [hv, deriv_const_add, deriv_div_const, deriv_fun_sub,
      deriv_const_mul_field, deriv_pow_field]
    ring
  have hy : partialY mixedOddBMultiplier (h, 0) =
      (-2011 * h + 3795 * h ^ 2 + 808 * h * Real.log h) / 10000 := by
    change deriv (fun k ↦ mixedOddBMultiplier (h, k)) 0 = _
    simp (disch := fun_prop) only [mixedOddBMultiplier, mixedOddBPolynomial, deriv_fun_add,
      deriv_div_const, deriv_fun_sub, deriv_const_mul_field, deriv_const_mul_id,
      deriv_pow_field, deriv_mul_const_field, deriv_const]
    ring
  have he : mixedRobinNumerator false mixedOddBMultiplier h = h *
      ((14926 - 2586 * h - 3141 * h ^ 2 - 2043 * h ^ 3) / 10000 -
        (808 / 10000) * (2 - h ^ 2) * Real.log h) := by
    simp only [mixedRobinNumerator, Bool.false_eq_true, ite_false, hv, hx, hy]
    ring
  rw [he, mul_comm (1789 / 2500 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ hh.1.le
  have h₂ : h ^ 2 ≤ 1 := pow_le_one₀ hh.1.le hh.2
  have h₃ : h ^ 3 ≤ 1 := pow_le_one₀ hh.1.le hh.2
  have hlog := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (808 / 10000 : ℝ) * (2 - h ^ 2) by linarith only [h₂])
    (Real.log_nonpos hh.1.le hh.2)
  linarith only [hh.2, h₂, h₃, hlog]

end NoEmbeddedEigenvalues
