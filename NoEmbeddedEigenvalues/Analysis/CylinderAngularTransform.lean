import NoEmbeddedEigenvalues.Analysis.LogPolarL2

/-!
# Angular analysis of square-integrable cylinder data

Probability-Haar coefficients satisfy Parseval on a.e. angular slice. Each
coefficient is an actual L² function of logarithmic radius, so real-line L²
Fourier analysis can be applied without assuming pointwise integrability in t.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The normalized angular Fourier coefficient as a function of logarithmic radius. -/
def cylinderAngularCoeff (G : ℝ × AddCircle (2 * Real.pi) → ℂ) (n : ℤ) (t : ℝ) : ℂ :=
  _root_.fourierCoeff (fun θ ↦ G (t, θ)) n

/-- Raw L² representatives have genuine Parseval coefficients and finite sum of squares. -/
theorem hasSum_sq_circle_fourierCoeff {f : AddCircle (2 * Real.pi) → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    HasSum (fun n : ℤ ↦ ‖_root_.fourierCoeff f n‖ ^ 2)
      (∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have hs := _root_.hasSum_sq_fourierCoeff (hf.toLp f)
  have hc : ∀ n : ℤ, _root_.fourierCoeff (hf.toLp f) n = _root_.fourierCoeff f n :=
    fun n ↦ congrFun (_root_.fourierCoeff_congr_ae hf.coeFn_toLp) n
  have hi : (∫ θ, ‖hf.toLp f θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  simpa only [hc, hi] using hs

/-- Angular Parseval is used only on a.e. logarithmic-radius slices. -/
theorem cylinderAngularCoeff_parseval {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    ∀ᵐ t : ℝ, HasSum (fun n : ℤ ↦ ‖cylinderAngularCoeff G n t‖ ^ 2)
      (∫ θ, ‖G (t, θ)‖ ^ 2 ∂AddCircle.haarAddCircle) :=
  (memLp_logCylinder_slices hG).mono fun _ ht ↦ hasSum_sq_circle_fourierCoeff ht

/-- Every angular coefficient has actual finite L² mass in logarithmic radius. -/
theorem cylinderAngularCoeff_memLp {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    MemLp (cylinderAngularCoeff G n) 2 volume := by
  have hk : Continuous (fun q : ℝ × AddCircle (2 * Real.pi) ↦ _root_.fourier (-n) q.2) :=
    (_root_.fourier (-n)).continuous.comp continuous_snd
  have hm : AEStronglyMeasurable (cylinderAngularCoeff G n) volume := by
    change AEStronglyMeasurable (fun t ↦ ∫ θ,
      _root_.fourier (-n) θ * G (t, θ) ∂AddCircle.haarAddCircle) volume
    simpa only [Pi.mul_apply] using
      (hk.aestronglyMeasurable.mul hG.aestronglyMeasurable).integral_prod_right'
  have hi := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hi.integral_prod_left.mono' (hm.norm.pow 2)
  filter_upwards [cylinderAngularCoeff_parseval hG] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (ht.summable.le_tsum n (fun _ _ ↦ sq_nonneg _)).trans_eq ht.tsum_eq

end NoEmbeddedEigenvalues
