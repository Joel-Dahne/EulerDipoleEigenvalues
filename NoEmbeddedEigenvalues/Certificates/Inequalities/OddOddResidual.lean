module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The explicit Odd–odd residual

This is the two-variable coefficient table for `cert:dd-residual`. It is kept
independent of the differentiated ground state and the certificate checks.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

/-- Integer polynomial A in the odd–odd residual table. -/
def ddResidualA (s r : ℝ) : ℝ :=
  (452 * r ^ 4 - 832 * r ^ 3 + 1024 * r ^ 2) +
    s * (-9 * r ^ 5 + 120 * r ^ 4 + 768 * r ^ 3) +
    s ^ 2 * (148 * r ^ 3 + 1664 * r - 4096) +
    s ^ 3 * (20 * r ^ 4 + 98 * r ^ 3 - 512 * r ^ 2 + 768 * r) +
    s ^ 4 * (-32 * r ^ 2 - 384 * r + 2048) +
    s ^ 5 * (28 * r ^ 3 + 72 * r ^ 2 - 592 * r + 512) +
    s ^ 6 * (-8 * r - 256) + s ^ 7 * (10 * r ^ 2 + 96 * r - 256) +
    s ^ 9 * (r + 32)

/-- Integer polynomial B in the same table. -/
def ddResidualB (s r : ℝ) : ℝ :=
  (1408 * r ^ 3 - 2240 * r ^ 2) + s * (-87 * r ^ 4 + 96 * r ^ 3) +
    s ^ 2 * (528 * r ^ 2 - 512 * r + 1024) + s ^ 3 * (4 * r ^ 3 - 56 * r ^ 2) +
    s ^ 4 * (128 * r - 512) + s ^ 5 * (18 * r ^ 2 + 64 * r - 128) +
    s ^ 6 * 64 + s ^ 7 * (-16 * r + 64) - s ^ 9 * 8

/-- The residual `R₀(s,r) + R₁(s,r) log(r/2)` on its geometric range. -/
def ddResidualExpression (s r : ℝ) : ℝ :=
  s * ddResidualA s r / (384 * r ^ 3) +
    s * ddResidualB s r / (1536 * r ^ 2) * Real.log (r / 2)

/-- The residual's geometric range is the image of these unit-square coordinates. -/
theorem dd_residual_box_coordinates {s r : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hrlo : s * (2 - s) ≤ r) (hrhi : r ≤ 2 - s ^ 2 / 2) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
      2 * x = s ∧ 2 * (1 - x) * (2 * x + (1 - x) * y) = r := by
  let x := s / 2
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by dsimp [x]; positivity, by dsimp [x]; linarith⟩
  have hsx : 2 * x = s := by dsimp [x]; ring
  have hd : 0 < 2 * (1 - x) ^ 2 := mul_pos (by norm_num)
    (pow_pos (sub_pos.mpr (show x < 1 by dsimp [x]; linarith)) _)
  let y := (r - s * (2 - s)) / (2 * (1 - x) ^ 2)
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hrlo) hd.le, (div_le_one hd).mpr ?_⟩
    calc
      r - s * (2 - s) ≤ (2 - s ^ 2 / 2) - s * (2 - s) := sub_le_sub_right hrhi _
      _ = _ := by dsimp [x]; ring
  refine ⟨x, hx, y, hy, hsx, ?_⟩
  calc
    _ = s * (2 - s) + 2 * (1 - x) ^ 2 * y := by rw [← hsx]; ring
    _ = r := by dsimp only [y]; rw [mul_div_cancel₀ _ hd.ne']; ring

end NoEmbeddedEigenvalues
