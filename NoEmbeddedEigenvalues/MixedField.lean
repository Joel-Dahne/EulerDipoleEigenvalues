import NoEmbeddedEigenvalues.MixedComparison
import NoEmbeddedEigenvalues.Cells

/-! # The adapted field in the odd–even mixed sector -/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Set

/-- Cartesian components of the mixed adapted field. -/
def mixedFieldX (p : ℝ × ℝ) : ℝ := tan (p.1 / 2)
def mixedFieldY (p : ℝ × ℝ) : ℝ := tan (p.2 / 2)

/-- Components of the same field in the diagonal chart. -/
def mixedFieldA (q : ℝ × ℝ) : ℝ := sin q.1 / (cos q.1 + cos q.2)
def mixedFieldB (q : ℝ × ℝ) : ℝ := sin q.2 / (cos q.1 + cos q.2)

/-- The adapted coefficient in diagonal coordinates. -/
def mixedFieldCoeff (q : ℝ × ℝ) : ℝ :=
  (sin q.1 ^ 2 + sin q.2 ^ 2) / (cos q.1 + cos q.2) ^ 2

/-- The off-diagonal entry of `2 sym DW - f I` in the orthonormal diagonal basis. -/
def mixedFieldMatrixOffDiagonal (q : ℝ × ℝ) : ℝ :=
  2 * sin q.1 * sin q.2 / (cos q.1 + cos q.2) ^ 2

/-- Algebra of the mixed field, including the coordinate change. In Cartesian
coordinates the symmetric Jacobian is diagonal, with the two stated eigenvalues. -/
theorem mixed_field_algebra :
    IsAdaptedOn mixedFieldX mixedFieldY (mixedFieldCoeff ∘ diagCoord) cellSquare ∧
    ∀ p ∈ cellSquare,
      let q := diagCoord p
      mixedFieldA q = (mixedFieldX p + mixedFieldY p) / 2 ∧
      mixedFieldB q = (mixedFieldX p - mixedFieldY p) / 2 ∧
      fieldDeriv mixedFieldX mixedFieldY dipoleLift p = dipoleLift p - 2 ∧
      divergence mixedFieldX mixedFieldY p = mixedFieldCoeff q + 1 ∧
      2 * partialX mixedFieldA q - mixedFieldCoeff q = 1 ∧
      2 * partialY mixedFieldB q - mixedFieldCoeff q = 1 ∧
      partialY mixedFieldA q + partialX mixedFieldB q = mixedFieldMatrixOffDiagonal q ∧
      partialY mixedFieldX p = 0 ∧ partialX mixedFieldY p = 0 ∧
      2 * partialX mixedFieldX p = (cos ((q.1 + q.2) / 2) ^ 2)⁻¹ ∧
      2 * partialY mixedFieldY p = (cos ((q.1 - q.2) / 2) ^ 2)⁻¹ := by
  sorry

end NoEmbeddedEigenvalues
