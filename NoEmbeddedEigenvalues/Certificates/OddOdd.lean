import NoEmbeddedEigenvalues.OddOddGroundResidual

/-!
# Odd–odd residual certificate

The residual sign on the geometric range is separate from the identity tying
the manuscript's integer coefficient table to the differentiated ground state.
-/

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
  sorry

end NoEmbeddedEigenvalues
