import NoEmbeddedEigenvalues.OddOdd
import NoEmbeddedEigenvalues.MixedComparison

/-!
# Explicit sign statements for the odd–odd and mixed comparisons

The sign claims do not prescribe Bernstein subdivision or any other proof method.
The odd–odd residual is an explicit two-variable expression, with a separate
identity tying the manuscript's integer coefficient table to `ddGroundResidual`.
The mixed residuals are defined by differentiation of the actual comparison
multipliers and likewise have explicit identities with the differential operator.
Thus a coefficient table alone cannot substitute for the operator being bounded.

The Robin polynomial is defined on the closed interval. Its identity with the
rational exponent's derivatives is stated only for `h>0`: the value at zero is
the continuous extension of that expression, not raw corner derivative data.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set

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

/-- The coefficient table represents the actual differentiated ground residual. -/
theorem dd_residual_identity {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) :
    ddGroundResidual p + (5 / 2 : ℝ) * ddWeight p * ddGround p =
      ddResidualExpression (dipoleLift p) (gradSq dipoleLift p) := by
  sorry

/-- Odd–odd residual sign on the full two-variable geometric range. -/
theorem dd_residual_nonneg {s r : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hrlo : s * (2 - s) ≤ r) (hrhi : r ≤ 2 - s ^ 2 / 2) :
    0 ≤ ddResidualExpression s r := by
  sorry

/-- Auxiliary A_F in the odd-in-b differential reduction, in `(h,k)` variables. -/
def mixedOddBFluxA (p : ℝ × ℝ) : ℝ :=
  -mixedD p * partialX mixedOddBMultiplier p + mixedC p *
    (p.2 * mixedOddBMultiplier p - (1 - p.2 ^ 2) * partialY mixedOddBMultiplier p)

/-- Auxiliary B_F in the same reduction. -/
def mixedOddBFluxB (p : ℝ × ℝ) : ℝ :=
  -mixedC p * (1 - p.1 ^ 2) * (1 - p.2 ^ 2) * partialX mixedOddBMultiplier p +
    mixedD p * (p.2 * mixedOddBMultiplier p -
      (1 - p.2 ^ 2) * partialY mixedOddBMultiplier p)

/-- Normalized odd-in-b residual after subtracting `h² F_v/100`. -/
def mixedOddBResidual (p : ℝ × ℝ) : ℝ :=
  -p.1 * mixedOddBFluxA p + (1 - p.1 ^ 2) * partialX mixedOddBFluxA p +
    partialY mixedOddBFluxB p + mixedV p * mixedOddBMultiplier p -
    p.1 ^ 2 * mixedOddBMultiplier p / 100

theorem mixed_odd_b_identity {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    mixedComparisonOperator mixedOddBComparison p -
        (1 / 100 : ℝ) * Real.cos p.1 ^ 2 * mixedOddBComparison p =
      Real.sin p.2 * mixedOddBResidual (Real.cos p.1, Real.cos p.2) := by
  sorry

/-- The normalized residual includes the one-sided boundary values in the rectangle.
    At `(1,1)` the potential uses its specified continuous value. -/
theorem mixed_odd_b_residual_nonneg {h k : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1)
    (hk : k ∈ Icc (0 : ℝ) 1) : 0 ≤ mixedOddBResidual (h, k) := by
  sorry

theorem mixed_odd_b_interior {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    (1 / 100 : ℝ) * Real.cos p.1 ^ 2 * mixedOddBComparison p ≤
      mixedComparisonOperator mixedOddBComparison p := by
  sorry

/-- First-order coefficients in the normalized odd-in-a reduction. -/
def mixedOddACoeffH (p : ℝ × ℝ) : ℝ :=
  3 * p.1 * mixedD p - (1 - p.1 ^ 2) * partialX mixedD p +
    (1 - p.1 ^ 2) * (p.2 * mixedC p - (1 - p.2 ^ 2) * partialY mixedC p)

def mixedOddACoeffK (p : ℝ × ℝ) : ℝ :=
  (1 - p.2 ^ 2) * (-(1 - p.1 ^ 2) * partialX mixedC p +
    3 * p.1 * mixedC p - partialY mixedD p) + p.2 * mixedD p

def mixedOddACoeffZero (p : ℝ × ℝ) : ℝ :=
  mixedD p + p.1 * partialX mixedD p - p.1 * p.2 * mixedC p +
    p.1 * (1 - p.2 ^ 2) * partialY mixedC p + mixedV p

/-- Rational normalized odd-in-a residual; division by the comparison has removed
    the positive exponential before any polynomial denominator clearing. -/
def mixedOddAResidual (p : ℝ × ℝ) : ℝ :=
  mixedOddACoeffZero p + mixedOddACoeffH p * partialX mixedOddAExponent p +
    mixedOddACoeffK p * partialY mixedOddAExponent p -
    mixedD p * ((1 - p.1 ^ 2) *
      (partialX (partialX mixedOddAExponent) p + partialX mixedOddAExponent p ^ 2) +
      (1 - p.2 ^ 2) *
        (partialY (partialY mixedOddAExponent) p + partialY mixedOddAExponent p ^ 2)) -
    2 * mixedC p * (1 - p.1 ^ 2) * (1 - p.2 ^ 2) *
      (partialY (partialX mixedOddAExponent) p +
        partialX mixedOddAExponent p * partialY mixedOddAExponent p) - p.1 ^ 2 / 200

theorem mixed_odd_a_identity {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    mixedComparisonOperator mixedOddAComparison p -
        (1 / 200 : ℝ) * Real.cos p.1 ^ 2 * mixedOddAComparison p =
      mixedOddAComparison p * mixedOddAResidual (Real.cos p.1, Real.cos p.2) := by
  sorry

theorem mixed_odd_a_residual_nonneg {h k : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hk : k ∈ Ioo (0 : ℝ) 1) : 0 ≤ mixedOddAResidual (h, k) := by
  sorry

theorem mixed_odd_a_interior {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    (1 / 200 : ℝ) * Real.cos p.1 ^ 2 * mixedOddAComparison p ≤
      mixedComparisonOperator mixedOddAComparison p := by
  sorry

/-- The exact Robin margin polynomial, including its continuous endpoint value. -/
def mixedRobinPolynomial (h : ℝ) : ℝ :=
  (673 * h ^ 7 - 1953 * h ^ 6 - 3213 * h ^ 5 + 7317 * h ^ 4 +
    109 * h ^ 3 - 4647 * h ^ 2 + 1718 * h + 1) / 1000 - h / 250

/-- The differential identity excludes the corner, where raw partial derivatives
    of the rational exponent do not equal their limits along `k=0`. -/
theorem mixed_robin_identity {h : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) :
    3 * h - 2 * (1 - h ^ 2) * partialX mixedOddAExponent (h, 0) -
        (2 - h ^ 2) * partialY mixedOddAExponent (h, 0) - h / 250 =
      mixedRobinPolynomial h := by
  sorry

theorem mixed_robin_nonneg {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedRobinPolynomial h := by
  sorry

end NoEmbeddedEigenvalues
