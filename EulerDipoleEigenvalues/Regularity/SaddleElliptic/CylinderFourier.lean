module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderAngularTransform
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Real-line L² Fourier analysis of cylinder modes

The Fourier transform here is Mathlib's unitary cycle-frequency transform.
Angular frequency is `2 * π` times this real frequency. Mode functions are
first passed to their genuine L² classes; no time L¹ hypothesis is imposed.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The actual angular coefficient in real-line L². -/
def cylinderTimeMode {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (cylinderAngularCoeff_memLp hG n).toLp (cylinderAngularCoeff G n)

/-- The cycle-frequency L² Fourier transform of an actual cylinder coefficient. -/
def cylinderFourierMode {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕 (cylinderTimeMode hG n)

/-- Passing to L² does not change the specified coefficient a.e. -/
theorem cylinderTimeMode_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    cylinderTimeMode hG n =ᵐ[volume] cylinderAngularCoeff G n :=
  (cylinderAngularCoeff_memLp hG n).coeFn_toLp

/-- The inverse transform recovers the original coefficient class. -/
theorem cylinderFourierMode_inverse {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    𝓕⁻ (cylinderFourierMode hG n) = cylinderTimeMode hG n :=
  FourierTransform.fourierInv_fourier_eq _

/-- Squared L² norm is the genuine integral of the squared representative. -/
theorem cylinderRealL2_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h
  · exact L2.integrable_inner f f

/-- Angular Parseval may be integrated: the sum of the real-line mode masses is
finite and equals the full cylinder mass. -/
theorem cylinderTimeMode_hasSum_mass {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    HasSum (fun n : ℤ ↦ ‖cylinderTimeMode hG n‖ ^ 2)
      (∫ q, ‖G q‖ ^ 2 ∂logCylinderMeasure) := by
  have hp := cylinderAngularCoeff_parseval hG
  have hi := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hb : Integrable (fun t ↦ ∑' n : ℤ, ‖cylinderAngularCoeff G n t‖ ^ 2) volume :=
    hi.integral_prod_left.congr (hp.mono fun _ ht ↦ ht.tsum_eq.symm)
  have hs := hasSum_integral_of_dominated_convergence
    (fun n t ↦ ‖cylinderAngularCoeff G n t‖ ^ 2)
    (fun n ↦ (cylinderAngularCoeff_memLp hG n).aestronglyMeasurable.norm.pow 2)
    (fun n ↦ Filter.Eventually.of_forall fun t ↦ by
      simp only [Pi.pow_apply, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg ‖cylinderAngularCoeff G n t‖), le_refl])
    (hp.mono fun _ ht ↦ ht.summable) hb hp
  have hm (n : ℤ) : ‖cylinderTimeMode hG n‖ ^ 2 =
      ∫ t, ‖cylinderAngularCoeff G n t‖ ^ 2 := by
    rw [cylinderRealL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [cylinderTimeMode_ae hG n] with t ht
    rw [ht]
  simpa only [hm, Pi.pow_apply, logCylinderMeasure, ← integral_prod _ hi] using hs

/-- Plancherel in time preserves the sum of the angular mode masses. -/
theorem cylinderFourierMode_hasSum_mass {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    HasSum (fun n : ℤ ↦ ‖cylinderFourierMode hG n‖ ^ 2)
      (∫ q, ‖G q‖ ^ 2 ∂logCylinderMeasure) := by
  simpa only [cylinderFourierMode, Lp.norm_fourier_eq] using cylinderTimeMode_hasSum_mass hG

/-- A scalar relation between actual coefficients passes to their Fourier classes. -/
theorem cylinderFourierMode_smul_of_coeff_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) {m n : ℤ} {c : ℂ}
    (hc : cylinderAngularCoeff G m =ᵐ[volume] fun t ↦ c * cylinderAngularCoeff G n t) :
    cylinderFourierMode hG m = c • cylinderFourierMode hG n := by
  have he : cylinderTimeMode hG m = c • cylinderTimeMode hG n := by
    apply Lp.ext
    filter_upwards [cylinderTimeMode_ae hG m, cylinderTimeMode_ae hG n,
      Lp.coeFn_smul c (cylinderTimeMode hG n), hc] with t hm hn hs ht
    simpa only [hm, hs, Pi.smul_apply, hn, smul_eq_mul] using ht
  simp only [cylinderFourierMode, he, FourierTransform.fourier_smul]

/-- Vanishing of an actual coefficient gives vanishing of its Fourier L² class. -/
theorem cylinderFourierMode_eq_zero {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) {n : ℤ}
    (hn : cylinderAngularCoeff G n =ᵐ[volume] 0) : cylinderFourierMode hG n = 0 := by
  have hz : cylinderTimeMode hG n = 0 := by
    apply Lp.ext
    exact (cylinderTimeMode_ae hG n).trans (hn.trans (Lp.coeFn_zero _ _ _).symm)
  simp [cylinderFourierMode, hz]

end EulerDipoleEigenvalues
