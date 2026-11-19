import NoEmbeddedEigenvalues.MixedComparison

/-!
# Mixed comparison certificates

The normalized residuals are defined by differentiation of the comparison
multipliers. Their operator identities are separate from their signs.
The Robin polynomial at zero is the continuous extension of the boundary
expression, not its value computed from raw corner derivatives.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set

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

private theorem cos_mem_unit {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    Real.cos t ∈ Ioo 0 1 := by
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩, ?_⟩
  have h := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show t ∈ Icc 0 Real.pi from ⟨ht.1.le, ht.2.le.trans (half_le_self Real.pi_pos.le)⟩) ht.1
  simpa only [Real.cos_zero] using h

private theorem sin_pos_quarter {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans (half_lt_self Real.pi_pos))

theorem mixed_odd_b_interior {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    (1 / 100 : ℝ) * Real.cos p.1 ^ 2 * mixedOddBComparison p ≤
      mixedComparisonOperator mixedOddBComparison p := by
  rw [← sub_nonneg, mixed_odd_b_identity hp]
  have hh := cos_mem_unit hp.1
  have hk := cos_mem_unit hp.2
  exact mul_nonneg (sin_pos_quarter hp.2).le
    (mixed_odd_b_residual_nonneg ⟨hh.1, hh.2.le⟩ ⟨hk.1.le, hk.2.le⟩)

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
  rw [← sub_nonneg, mixed_odd_a_identity hp]
  have hw : 0 ≤ mixedOddAComparison p :=
    mul_nonneg (sin_pos_quarter hp.1).le (Real.exp_pos _).le
  exact mul_nonneg hw (mixed_odd_a_residual_nonneg (cos_mem_unit hp.1) (cos_mem_unit hp.2))

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
