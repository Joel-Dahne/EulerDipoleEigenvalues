module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderJetCandidates
public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderLift
public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.SobolevLocal

/-!
# Weak differentiation of actual integrable cylinder synthesis

The joint kernel has classical derivatives on the entire real-angle plane.
Fubini transports its integration-by-parts identity to actual inverse integrals
when both spectra are integrable. These premises are intended for finite-mass
spectral truncations; no integrability of an untruncated derivative is inferred.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SigmaFinite cylinderFourierMeasure := by
  unfold cylinderFourierMeasure
  infer_instance

theorem cylinderJointKernel_lift (q : ℝ × ℝ) (p : ℝ × ℤ) :
    cylinderJointKernel (logCylinderProjection q) p =
      Complex.exp (Complex.I * ((q.1 * p.1 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((q.2 * (p.2 : ℝ) : ℝ) : ℂ)) := by
  unfold cylinderJointKernel logCylinderProjection
  rw [_root_.fourier_coe_apply]
  congr 2
  push_cast
  field_simp

theorem contDiff_cylinderJointKernel_lift (p : ℝ × ℤ) :
    ContDiff ℝ ∞ (fun q ↦ cylinderJointKernel (logCylinderProjection q) p) := by
  simp only [cylinderJointKernel_lift]
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul contDiff_const))).cexp.mul
      (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_snd.mul contDiff_const))).cexp

theorem coordPartial_cylinderJointKernel_lift (j : Fin 2) (p : ℝ × ℤ) :
    coordPartial j (fun q ↦ cylinderJointKernel (logCylinderProjection q) p) =
      fun q ↦ cylinderDerivativeSymbol j p * cylinderJointKernel (logCylinderProjection q) p := by
  funext q
  fin_cases j
  · change deriv (fun t ↦ cylinderJointKernel (logCylinderProjection (t, q.2)) p) q.1 = _
    change _ = (Complex.I * (p.1 : ℂ)) * cylinderJointKernel (logCylinderProjection q) p
    simp only [cylinderJointKernel_lift]
    have h := (((hasDerivAt_id q.1).mul_const p.1).ofReal_comp.const_mul Complex.I).cexp
    simpa [mul_comm, mul_left_comm, mul_assoc] using (h.mul_const
      (Complex.exp (Complex.I * ((q.2 * (p.2 : ℝ) : ℝ) : ℂ)))).deriv
  · change deriv (fun θ ↦ cylinderJointKernel (logCylinderProjection (q.1, θ)) p) q.2 = _
    change _ = (Complex.I * ((p.2 : ℝ) : ℂ)) *
      cylinderJointKernel (logCylinderProjection q) p
    simp only [cylinderJointKernel_lift]
    have h := (((hasDerivAt_id q.2).mul_const (p.2 : ℝ)).ofReal_comp.const_mul Complex.I).cexp
    simpa [mul_comm, mul_left_comm, mul_assoc] using (h.const_mul
      (Complex.exp (Complex.I * ((q.1 * p.1 : ℝ) : ℂ)))).deriv

private theorem continuous_projection : Continuous logCylinderProjection := by
  unfold logCylinderProjection
  fun_prop

/-- Transfer an integrable planar pairing to its actual signed spectral integral. -/
theorem integral_cylinderJointSynthesis_lift_mul_swap {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) {ψ : ℝ × ℝ → ℂ} (hψ : Integrable ψ) :
    (∫ q, cylinderJointSynthesis H (logCylinderProjection q) * ψ q) =
      ∫ p, H p * (∫ q, cylinderJointKernel (logCylinderProjection q) p * ψ q)
        ∂cylinderFourierMeasure := by
  have hc : Continuous (fun z : (ℝ × ℤ) × (ℝ × ℝ) ↦
      cylinderJointKernel (logCylinderProjection z.2) z.1) :=
    continuous_cylinderJointKernel.comp
      ((continuous_projection.comp continuous_snd).prodMk continuous_fst)
  have hi : Integrable (fun z : (ℝ × ℤ) × (ℝ × ℝ) ↦
      cylinderJointKernel (logCylinderProjection z.2) z.1 * (H z.1 * ψ z.2))
        (cylinderFourierMeasure.prod volume) :=
    (hH.mul_prod hψ).bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ (norm_cylinderJointKernel _ _).le)
  calc
    _ = ∫ q, ∫ p, cylinderJointKernel (logCylinderProjection q) p * (H p * ψ q)
        ∂cylinderFourierMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q ↦ by
        dsimp only
        unfold cylinderJointSynthesis
        rw [← integral_mul_const]
        simp only [mul_assoc]
    _ = ∫ p, (∫ q, cylinderJointKernel (logCylinderProjection q) p * (H p * ψ q))
        ∂cylinderFourierMeasure := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        simp_rw [mul_left_comm (cylinderJointKernel _ _) (H p)]
        exact integral_const_mul _ _

/-- Integrable spectra and their specified first multipliers give weak identities
on the entire real-angle lift, with no strip or seam restriction. -/
theorem cylinderJointSynthesis_hasWeakPartial {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (j : Fin 2)
    (hD : Integrable (fun p ↦ cylinderDerivativeSymbol j p * H p) cylinderFourierMeasure) :
    HasWeakPartialOn univ j (cylinderJointSynthesis H ∘ logCylinderProjection)
      (cylinderJointSynthesis (fun p ↦ cylinderDerivativeSymbol j p * H p) ∘
        logCylinderProjection) := by
  refine ⟨((continuous_cylinderJointSynthesis hH).comp continuous_projection).locallyIntegrable
    |>.locallyIntegrableOn univ,
    ((continuous_cylinderJointSynthesis hD).comp continuous_projection).locallyIntegrable
      |>.locallyIntegrableOn univ, ?_⟩
  intro φ hφ
  have hφi : Integrable φ :=
    hφ.contDiff.continuous.integrable_of_hasCompactSupport hφ.hasCompactSupport
  have hφdi : Integrable (coordPartial j φ) :=
    (hφ.continuous_coordPartial j).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport_coordPartial j)
  simp only [Function.comp_apply]
  rw [integral_cylinderJointSynthesis_lift_mul_swap hH hφdi,
    integral_cylinderJointSynthesis_lift_mul_swap hD hφi, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p ↦ by
    dsimp only
    have hk := integral_mul_coordPartial j
      ((contDiff_cylinderJointKernel_lift p).of_le (by simp))
      (hφ.contDiff.of_le (by simp)) hφ.hasCompactSupport
    rw [coordPartial_cylinderJointKernel_lift] at hk
    rw [hk]
    simp_rw [mul_assoc, integral_const_mul]
    ring

end EulerDipoleEigenvalues
