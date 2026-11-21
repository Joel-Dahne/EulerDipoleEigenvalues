import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderSynthesis
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderData

/-!
# Pointwise axis parity of trigonometric synthesis

Allowed degrees give the first reflection sign; the cosine/sine choice gives
the second. The identities are pointwise in both cylinder coordinates. Actual
integrability and continuity are supplied separately by the spectral bounds.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Reflection in the second Cartesian axis acts as angular negation. -/
theorem cylinderAngularMode_neg (even : Bool) (m : ℕ) (θ : ℝ) :
    cylinderAngularMode even m (-θ) =
      (if even then (1 : ℂ) else -1) * cylinderAngularMode even m θ := by
  cases even <;> simp [cylinderAngularMode]

/-- The angular half-turn character determined by the two parity signs. -/
theorem AllowedSaddleDegree.neg_one_pow {ε : Fin 2 → Bool} {m : ℕ}
    (hm : AllowedSaddleDegree ε m) :
    (-1 : ℂ) ^ m = paritySign (ε 0) * paritySign (ε 1) := by
  simp only [neg_one_pow_eq_ite, hm.1]
  cases ε 0 <;> cases ε 1 <;> simp [paritySign]

/-- Reflection in the first Cartesian axis uses both allowed degree and basis type. -/
theorem cylinderAngularMode_pi_sub {ε : Fin 2 → Bool} {m : ℕ}
    (hm : AllowedSaddleDegree ε m) (θ : ℝ) :
    cylinderAngularMode (ε 1) m (Real.pi - θ) =
      paritySign (ε 0) * cylinderAngularMode (ε 1) m θ := by
  have hp := hm.neg_one_pow
  cases h1 : ε 1 <;>
    simp only [cylinderAngularMode, Bool.false_eq_true, ite_false, ite_true,
      mul_sub, Real.sin_nat_mul_pi_sub, Real.cos_nat_mul_pi_sub, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one, hp, paritySign,
      h1, ite_false, ite_true] <;> ring

/-- The sine/cosine choice gives actual pointwise angular-negation parity. -/
theorem cylinderSynthesis_neg (even : Bool) (μ : Measure (ℝ × ℕ))
    (V : ℝ × ℕ → ℂ) (t θ : ℝ) :
    cylinderSynthesis even μ V (t, -θ) =
      (if even then (1 : ℂ) else -1) * cylinderSynthesis even μ V (t, θ) := by
  unfold cylinderSynthesis
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p ↦ by
    change Complex.exp _ * cylinderAngularMode even p.2 (-θ) * V p = _
    rw [cylinderAngularMode_neg]
    dsimp only [cylinderSynthesisKernel]
    ring

/-- Allowed support gives actual pointwise first-axis reflection parity. -/
theorem cylinderSynthesis_pi_sub {ε : Fin 2 → Bool} {μ : Measure (ℝ × ℕ)}
    (hM : ∀ᵐ p ∂μ, AllowedSaddleDegree ε p.2) (V : ℝ × ℕ → ℂ) (t θ : ℝ) :
    cylinderSynthesis (ε 1) μ V (t, Real.pi - θ) =
      paritySign (ε 0) * cylinderSynthesis (ε 1) μ V (t, θ) := by
  unfold cylinderSynthesis
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hM] with p hp
  change Complex.exp _ * cylinderAngularMode (ε 1) p.2 (Real.pi - θ) * V p = _
  rw [cylinderAngularMode_pi_sub hp]
  dsimp only [cylinderSynthesisKernel]
  ring

end NoEmbeddedEigenvalues
