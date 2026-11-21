import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.LogPolarCoordinates
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite L² mass under logarithmic-polar transport

Multiplication by exp(-t), the square root of the planar Jacobian, sends
planar L² data to actual L² data on the logarithmic cylinder. The circle
measure is probability Haar measure; angular slices are taken only a.e. in t.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Measure

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The square-root-Jacobian pullback of planar data. -/
def logCylinderL2Pullback (f : ℝ × ℝ → ℂ)
    (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  (Real.exp (-q.1) : ℂ) * f (logCylinderPlane q)

/-- Actual finite mass on the real angular chart, before passing to the quotient. -/
theorem memLp_logPolarPlane_scaled {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun q ↦ (Real.exp (-q.1) : ℂ) * f (logPolarPlane q)) 2
      (volume.restrict logPolarStrip) := by
  have hw := hf.comp_measurePreserving measurePreserving_logPolarPlane
  have hi := (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have hj : Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2)) := by
    fun_prop
  have hi' := (integrable_withDensity_iff_integrable_smul' hj
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hi
  have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    quasiMeasurePreserving_logPolarPlane
  have hr : Continuous (fun q : ℝ × ℝ ↦ (Real.exp (-q.1) : ℂ)) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm (hr.aestronglyMeasurable.mul hcomp)).mpr
  apply hi'.congr
  filter_upwards [] with q
  simp only [Pi.mul_apply, Function.comp_apply, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]

/-- Finite planar L² mass gives finite cylinder L² mass, including measurability. -/
theorem memLp_logCylinderL2Pullback {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (logCylinderL2Pullback f) 2 logCylinderMeasure := by
  have hp := measurePreserving_logCylinderProjection
  have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    quasiMeasurePreserving_logCylinderPlane_length
  have hr : Continuous
      (fun q : ℝ × AddCircle (2 * Real.pi) ↦ (Real.exp (-q.1) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (logCylinderL2Pullback f)
      (volume.prod (volume : Measure (AddCircle (2 * Real.pi)))) :=
    hr.aestronglyMeasurable.mul hcomp
  have hm' : AEStronglyMeasurable (logCylinderL2Pullback f)
      (Measure.map logCylinderProjection (volume.restrict logPolarStrip)) := by
    rwa [hp.map_eq]
  have hreal : MemLp (logCylinderL2Pullback f ∘ logCylinderProjection) 2
      (volume.restrict logPolarStrip) := by
    simpa only [Function.comp_def, logCylinderL2Pullback, logCylinderProjection,
      logCylinderPlane_coe] using memLp_logPolarPlane_scaled hf
  have hfull := (memLp_map_measure_iff hm' hp.measurable.aemeasurable).mpr hreal
  rw [hp.map_eq] at hfull
  rw [logCylinderMeasure_eq_smul_length]
  exact hfull.smul_measure (ENNReal.inv_ne_top.mpr (by positivity))

/-- Exact mass identity on the real angular chart, with the area Jacobian. -/
theorem integral_sq_logPolarPlane_scaled {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ q in logPolarStrip, ‖(Real.exp (-q.1) : ℂ) * f (logPolarPlane q)‖ ^ 2) =
      ∫ p, ‖f p‖ ^ 2 := by
  have hp := measurePreserving_logPolarPlane
  have hm : AEStronglyMeasurable (fun p ↦ ‖f p‖ ^ 2)
      (Measure.map logPolarPlane
        ((volume.restrict logPolarStrip).withDensity
          (fun q ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2)))) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable.norm.pow 2
  have hi := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at hi
  have hj : Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2)) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hj
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow] using hi.symm

/-- Exact normalization for probability angular Haar measure. Both square masses
are finite by planar L² and `memLp_logCylinderL2Pullback`. -/
theorem integral_sq_logCylinderL2Pullback {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ q, ‖logCylinderL2Pullback f q‖ ^ 2 ∂logCylinderMeasure) =
      (2 * Real.pi)⁻¹ * ∫ p, ‖f p‖ ^ 2 := by
  have hp := measurePreserving_logCylinderProjection
  have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    quasiMeasurePreserving_logCylinderPlane_length
  have hr : Continuous
      (fun q : ℝ × AddCircle (2 * Real.pi) ↦ (Real.exp (-q.1) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (fun q ↦ ‖logCylinderL2Pullback f q‖ ^ 2)
      (Measure.map logCylinderProjection (volume.restrict logPolarStrip)) := by
    rw [hp.map_eq]
    exact (hr.aestronglyMeasurable.mul hcomp).norm.pow 2
  have hi := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at hi
  have hlen : (∫ q, ‖logCylinderL2Pullback f q‖ ^ 2
      ∂(volume.prod (volume : Measure (AddCircle (2 * Real.pi))))) = ∫ p, ‖f p‖ ^ 2 := by
    calc
      _ = _ := hi
      _ = _ := by
        simpa only [logCylinderL2Pullback, logCylinderProjection, logCylinderPlane_coe]
          using integral_sq_logPolarPlane_scaled hf
  rw [logCylinderMeasure_eq_smul_length, integral_smul_measure, hlen,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]

/-- A.e. angular slices have genuine L² mass. No chosen exceptional circle is used. -/
theorem memLp_logCylinder_slices {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    ∀ᵐ t : ℝ, MemLp (fun θ ↦ G (t, θ)) 2 AddCircle.haarAddCircle := by
  have hi := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hi' := hi.prod_right_ae
  obtain ⟨g, hg, heq⟩ := hG.aestronglyMeasurable
  have hs := ae_ae_of_ae_prod heq
  filter_upwards [hi', hs] with t ht heq_t
  have hm : AEStronglyMeasurable (fun θ ↦ g (t, θ)) AddCircle.haarAddCircle :=
    (hg.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have heq' : (fun θ ↦ G (t, θ)) =ᵐ[AddCircle.haarAddCircle] (fun θ ↦ g (t, θ)) := heq_t
  exact (memLp_two_iff_integrable_sq_norm (hm.congr heq'.symm)).mpr ht

end NoEmbeddedEigenvalues
