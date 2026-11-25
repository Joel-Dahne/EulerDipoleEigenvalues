module

public import EulerDipoleEigenvalues.Virial.VirialAlgebra
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # The mixed second-order coefficients and matrix positivity -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

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

end EulerDipoleEigenvalues
