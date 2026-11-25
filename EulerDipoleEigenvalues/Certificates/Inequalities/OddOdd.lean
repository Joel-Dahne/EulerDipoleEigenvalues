module

public import EulerDipoleEigenvalues.OddOdd.Picone.OddOddGroundResidual
public import EulerDipoleEigenvalues.Certificates.Tools.Logarithm
public import EulerDipoleEigenvalues.Certificates.Inequalities.OddOddLower
public import EulerDipoleEigenvalues.Certificates.Inequalities.OddOddUpper

/-!
# Odd–odd residual certificate

The residual sign follows by affine interpolation between the two rational
logarithm bounds. Their coefficient checks live in `OddOddLower` and
`OddOddUpper`, independently of the identity for the differentiated ground state.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

/-- The coefficient table represents the actual differentiated ground residual. -/
theorem dd_residual_identity {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) :
    ddGroundResidual p + (5 / 2 : ℝ) * ddWeight p * ddGround p =
      ddResidualExpression (dipoleLift p) (gradSq dipoleLift p) := by
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  rw [ddGroundResidual_eq_polynomial hs.ne' hr]
  unfold ddWeight ddGround
  generalize gradSq dipoleLift p = r at hr ⊢
  generalize dipoleLift p = s
  unfold ddGroundResidualPolynomial ddResidualExpression ddResidualA ddResidualB
  -- Keep the logarithm as a single variable in the rational identity.
  generalize Real.log (r / 2) = l
  field_simp [hr]
  ring

/-- Odd–odd residual sign on the full two-variable geometric range. -/
theorem dd_residual_nonneg {s r : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hrlo : s * (2 - s) ≤ r) (hrhi : r ≤ 2 - s ^ 2 / 2) :
    0 ≤ ddResidualExpression s r := by
  have hr : 0 < r := (mul_pos hs (sub_pos.mpr hs2)).trans_le hrlo
  have hr2 : r ≤ 2 := hrhi.trans (sub_le_self _ (by positivity))
  obtain ⟨hlo, hhi⟩ := certificate_log_ratio_bounds hr hr2
  exact certificate_affine_in_log ⟨hlo, hhi⟩
    (dd_residual_lower_nonneg hs hs2 hrlo hrhi) (dd_residual_upper_nonneg hs hs2 hrlo hrhi)

end EulerDipoleEigenvalues
