import NoEmbeddedEigenvalues.Certificates.Bernstein
import NoEmbeddedEigenvalues.Certificates.OddOddResidual
import Mathlib.Data.Fin.VecNotation

/-!
# The lower endpoint polynomial for the Odd–odd residual

Blueprint: `cert:dd-residual-lower`. The integer power table can be reproduced
by `scripts/verify_dd_residual.py`, but Lean checks its evaluation identity and
both sets of Bernstein coefficient signs independently of the script.
The sign checks use kernel reduction of closed rational inequalities. Keeping
them separate from the symbolic identity makes either step easy to profile.
-/

namespace NoEmbeddedEigenvalues

open Set

/-- Power coefficients of `Q_-`, ordered by increasing powers of `x` (rows)
and `y` (columns). -/
private def ddLowerInt : Fin 10 → Fin 7 → ℤ :=
  ![
    ![0, 0, 0, 17152, -33536, 25728, 0],
    ![0, 0, 102912, -302592, 414464, -142368, -3936],
    ![0, 168960, -872960, 2022912, -1441856, 266688, 31488],
    ![63488, -1007616, 4170240, -4856832, 1947840, 1440, -110208],
    ![-481280, 3918848, -6842880, 4149504, 37760, -878208, 220416],
    ![1310720, -3565056, 2396672, 2110464, -3693824, 1759392, -275520],
    ![-117760, -1027072, 5080064, -7847424, 5512896, -1806912, 220416],
    ![-531456, 3363328, -7326720, 7610880, -4089664, 1084512, -110208],
    ![610304, -2586624, 4306944, -3621888, 1619200, -362880, 31488],
    ![-215040, 735232, -1014272, 717824, -273280, 52608, -3936]]

private def ddLowerPower (i : Fin 10) (j : Fin 7) : ℚ := ddLowerInt i j

/-- Clearing the rational lower logarithm bound gives `(1-x)^4 Q_-(x,y)`. -/
private theorem ddLowerPower_identity (x y : ℝ) :
    let s := 2 * x
    let r := 2 * (1 - x) * (2 * x + (1 - x) * y)
    r * (ddResidualA s r + ddResidualB s r * (r - 2) / 4) =
      (1 - x) ^ 4 * certificatePolynomial ddLowerPower x y := by
  dsimp only
  simp [certificatePolynomial, Fin.sum_univ_succ, ddLowerPower, ddLowerInt,
    ddResidualA, ddResidualB]
  ring

private theorem ddLower_left_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddLowerPower 0 (1 / 2) 0 1 i j := by
  decide +kernel

private theorem ddLower_right_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddLowerPower (1 / 2) 1 0 1 i j := by
  decide +kernel

private theorem ddLowerPower_nonneg {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ certificatePolynomial ddLowerPower x y := by
  rcases le_total x (1 / 2) with h | h
  · exact certificate_bernstein_nonneg ddLowerPower (by norm_num) (by norm_num)
      ddLower_left_coeff_nonneg (by norm_num; exact ⟨hx.1, h⟩) (by norm_num; exact hy)
  · exact certificate_bernstein_nonneg ddLowerPower (by norm_num) (by norm_num)
      ddLower_right_coeff_nonneg (by norm_num; exact ⟨h, hx.2⟩) (by norm_num; exact hy)

/-- The odd–odd residual with `log (r/2)` replaced by the lower ratio bound. -/
theorem dd_residual_lower_nonneg {s r : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hrlo : s * (2 - s) ≤ r) (hrhi : r ≤ 2 - s ^ 2 / 2) :
    0 ≤ s * ddResidualA s r / (384 * r ^ 3) +
      s * ddResidualB s r / (1536 * r ^ 2) * ((r - 2) / r) := by
  have hr : 0 < r := (mul_pos hs (sub_pos.mpr hs2)).trans_le hrlo
  obtain ⟨x, hx, y, hy, hsx, hry⟩ := dd_residual_box_coordinates hs hs2 hrlo hrhi
  have hclear := ddLowerPower_identity x y
  dsimp only at hclear
  rw [hry, hsx] at hclear
  have hprod : 0 ≤ r * (ddResidualA s r + ddResidualB s r * (r - 2) / 4) := by
    rw [hclear]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (ddLowerPower_nonneg hx hy)
  calc
    0 ≤ s / (384 * r ^ 4) * (r * (ddResidualA s r + ddResidualB s r * (r - 2) / 4)) :=
      mul_nonneg (by positivity) hprod
    _ = _ := by field_simp [hr.ne']; ring

end NoEmbeddedEigenvalues
