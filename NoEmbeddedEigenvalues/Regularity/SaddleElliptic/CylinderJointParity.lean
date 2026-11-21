module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderJointSynthesis
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTrigParity
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderAngularSpectrum

/-!
# Pointwise parity of signed joint inverse synthesis

Negative-mode identities are combined over the countable index before frequency
integration. Allowed support gives the half-turn character. These yield both
reflection identities for the actual integral at every cylinder point.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Frequency-a.e. reflection signs yield pointwise angular reflection of the
actual integral. No representative is restricted to a selected time slice. -/
theorem cylinderJointSynthesis_neg {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) {s : ℂ}
    (hneg : ∀ n : ℤ, (fun ξ ↦ H (ξ, -n)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ s * H (ξ, n)) (t : ℝ) (θ : AddCircle (2 * Real.pi)) :
    cylinderJointSynthesis H (t, -θ) = s * cylinderJointSynthesis H (t, θ) := by
  have hc (n : ℤ) : _root_.fourier n (-θ) = _root_.fourier (-n) θ := by
    simp only [_root_.fourier_apply, smul_neg, neg_smul]
  have hall := ae_all_iff.mpr hneg
  change (∫ p, cylinderJointKernel (t, -θ) p * H p ∂cylinderFourierMeasure) =
    s * ∫ p, cylinderJointKernel (t, θ) p * H p ∂cylinderFourierMeasure
  rw [cylinderFourierMeasure, integral_prod _ (integrable_cylinderJointSynthesis hH (t, -θ)),
    integral_prod _ (integrable_cylinderJointSynthesis hH (t, θ)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hall] with ξ hξ
  calc
    _ = ∫ n : ℤ, Complex.exp (Complex.I * ((t * ξ : ℝ) : ℂ)) *
        _root_.fourier n θ * H (ξ, -n) ∂Measure.count := by
      simpa only [cylinderJointKernel, hc, neg_neg] using integral_neg_eq_self
        (fun n : ℤ ↦ Complex.exp (Complex.I * ((t * ξ : ℝ) : ℂ)) *
          _root_.fourier n θ * H (ξ, -n)) Measure.count
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun n ↦ by
        dsimp only [cylinderJointKernel]
        rw [hξ n]
        ring

/-- Allowed degree supplies the actual half-turn character before integration. -/
theorem cylinderJointSynthesis_half_turn {H : ℝ × ℤ → ℂ} {ε : Fin 2 → Bool}
    (hM : ∀ᵐ p ∂cylinderFourierMeasure,
      ¬AllowedSaddleDegree ε p.2.natAbs → H p = 0)
    (t : ℝ) (θ : AddCircle (2 * Real.pi)) :
    cylinderJointSynthesis H (t, θ + (Real.pi : AddCircle (2 * Real.pi))) =
      (paritySign (ε 0) * paritySign (ε 1)) * cylinderJointSynthesis H (t, θ) := by
  unfold cylinderJointSynthesis
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hM] with p hp
  by_cases hm : AllowedSaddleDegree ε p.2.natAbs
  · have hc : _root_.fourier p.2 (θ + (Real.pi : AddCircle (2 * Real.pi))) =
        _root_.fourier p.2 θ * _root_.fourier p.2 (Real.pi : AddCircle (2 * Real.pi)) := by
      simp only [_root_.fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    dsimp only [cylinderJointKernel]
    rw [hc, cylinderAngularCharacter_pi, hm.neg_one_pow]
    ring
  · rw [hp hm, mul_zero, mul_zero, mul_zero]

/-- The signed integral reconstruction retains both original reflection signs
pointwise, rather than only on a.e. angular slice. -/
theorem cylinderJointSynthesis_parity {H : ℝ × ℤ → ℂ} {ε : Fin 2 → Bool}
    (hH : Integrable H cylinderFourierMeasure)
    (hM : ∀ᵐ p ∂cylinderFourierMeasure,
      ¬AllowedSaddleDegree ε p.2.natAbs → H p = 0)
    (hneg : ∀ n : ℤ, (fun ξ ↦ H (ξ, -n)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ paritySign (ε 1) * H (ξ, n))
    (t : ℝ) (θ : AddCircle (2 * Real.pi)) :
    cylinderJointSynthesis H (t, (Real.pi : AddCircle (2 * Real.pi)) - θ) =
        paritySign (ε 0) * cylinderJointSynthesis H (t, θ) ∧
      cylinderJointSynthesis H (t, -θ) =
        paritySign (ε 1) * cylinderJointSynthesis H (t, θ) := by
  refine ⟨?_, cylinderJointSynthesis_neg hH hneg t θ⟩
  rw [sub_eq_neg_add, cylinderJointSynthesis_half_turn hM,
    cylinderJointSynthesis_neg hH hneg]
  cases ε 1 <;> simp [paritySign]

end NoEmbeddedEigenvalues
