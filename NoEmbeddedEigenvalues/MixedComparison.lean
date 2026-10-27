import NoEmbeddedEigenvalues.VirialAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

/-- Bounded coefficient claims separated from their definitions. -/
theorem mixed_comparison_coefficient_bounds {p : ℝ × ℝ} (hp : p ∈ mixedOpenCell) :
    0 ≤ -mixedComparisonPotential p ∧ -mixedComparisonPotential p ≤ 4 ∧
      mixedComparisonDiagonal p ≤ 3 ∧ |mixedComparisonOffDiagonal p| ≤ 2 := by
  sorry

/-- The explicit logarithmic multiplier `F_v(h,k)`. -/
def mixedOddBMultiplier (p : ℝ × ℝ) : ℝ :=
  1 + (4132 * p.2 ^ 2 + 2167 * p.2 ^ 3 - 2011 * p.1 * p.2 -
    7640 * p.1 * p.2 ^ 2 - 226 * p.1 ^ 2 + 3795 * p.1 ^ 2 * p.2 - 834 * p.1 ^ 3) / 10000 +
    (808 * p.1 * p.2 + 2505 * p.1 * p.2 ^ 2) / 10000 * Real.log p.1

/-- The odd-in-`b` comparison in actual diagonal coordinates. -/
def mixedOddBComparison (p : ℝ × ℝ) : ℝ :=
  Real.sin p.2 * mixedOddBMultiplier (Real.cos p.1, Real.cos p.2)

/-- The rational exponent `F_u(h,k)`; no exponential is taken in these variables. -/
def mixedOddAExponent (p : ℝ × ℝ) : ℝ :=
  (721 * p.2 ^ 2 - 107 * p.2 ^ 3 + 60 * p.2 ^ 4 + 85 * p.2 ^ 6 +
    p.1 * (-519 * p.2 - 64 * p.2 ^ 2 - 26 * p.2 ^ 3 - 400 * p.2 ^ 5) +
    p.1 ^ 2 * (-98 - 79 * p.2 ^ 2 + 890 * p.2 ^ 4) +
    p.1 ^ 3 * (781 - 583 * p.2 - 842 * p.2 ^ 3) +
    p.1 ^ 4 * (-240 + 677 * p.2 + 124 * p.2 ^ 2) +
    p.1 ^ 5 * (-263 + 37 * p.2) + 53 * p.1 ^ 6 - p.1 / 2 - 4 * p.2 -
    4 * p.1 ^ 3 / (p.1 + p.2) ^ 2 - 2744 * p.1 ^ 6 / (p.1 + p.2) ^ 4 +
    1033 * p.1 ^ 8 / (p.1 + p.2) ^ 6 + 224 * p.1 ^ 4 / (p.1 + p.2) +
    235 * p.1 ^ 8 / (p.1 + p.2) ^ 5) / 1000

/-- The odd-in-`a` comparison in actual diagonal coordinates. -/
def mixedOddAComparison (p : ℝ × ℝ) : ℝ :=
  Real.sin p.1 * Real.exp (mixedOddAExponent (Real.cos p.1, Real.cos p.2))

/-- Homogeneity gives bounded value and first derivatives, not continuity of the
    gradient at the corner. -/
theorem mixed_odd_a_exponent_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      |mixedOddAExponent p| ≤ C ∧ |partialX mixedOddAExponent p| ≤ C ∧
        |partialY mixedOddAExponent p| ≤ C := by
  sorry

end NoEmbeddedEigenvalues
