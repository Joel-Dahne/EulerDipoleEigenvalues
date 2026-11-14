import NoEmbeddedEigenvalues.Regularity.CylinderForcing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Inverse logarithmic-polar coordinates on the punctured plane

The angle is circle-valued. Thus these coordinates are continuous at every
nonzero point, including both sides of any chosen real-angle seam. The two
round-trips are pointwise; null-set transport is joint in both variables.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Measure Set
open scoped Topology

/-- Circle-valued logarithmic-polar coordinates, totalized at the origin. -/
def logCylinderCoordinates (p : ℝ × ℝ) : ℝ × AddCircle (2 * Real.pi) :=
  (-Real.log (localRadius 0 p), Complex.arg (Complex.equivRealProdCLM.symm p))

theorem localRadius_eq_complex_norm (p : ℝ × ℝ) :
    localRadius 0 p = ‖Complex.equivRealProdCLM.symm p‖ := by
  simp [localRadius, Complex.equivRealProdCLM_symm_apply, Complex.norm_def,
    Complex.normSq_add_mul_I]

theorem localRadius_pos_of_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) :
    0 < localRadius 0 p := by
  rw [localRadius_eq_complex_norm]
  exact norm_pos_iff.mpr (fun h ↦ hp (Complex.equivRealProdCLM.symm.injective
    (by simpa using h)))

@[fun_prop]
theorem measurable_logCylinderCoordinates : Measurable logCylinderCoordinates := by
  apply Measurable.prodMk
  · apply Measurable.neg
    apply Real.measurable_log.comp
    unfold localRadius
    fun_prop
  · exact (AddCircle.continuous_mk' (2 * Real.pi)).measurable.comp
      (Complex.measurable_arg.comp Complex.equivRealProdCLM.symm.continuous.measurable)

theorem continuousAt_logCylinderCoordinates {p : ℝ × ℝ} (hp : p ≠ 0) :
    ContinuousAt logCylinderCoordinates p := by
  have hr : ContinuousAt (localRadius 0) p := by unfold localRadius; fun_prop
  apply ContinuousAt.prodMk
  · exact (Real.continuousAt_log (localRadius_pos_of_ne_zero hp).ne').comp hr |>.neg
  · exact (Complex.continuousAt_arg_coe_angle (fun h ↦ hp
      (Complex.equivRealProdCLM.symm.injective (by simpa using h)))).comp
        Complex.equivRealProdCLM.symm.continuous.continuousAt

/-- The circle-valued inverse recovers every cylinder point, not just a strip. -/
theorem logCylinderCoordinates_plane (q : ℝ × AddCircle (2 * Real.pi)) :
    logCylinderCoordinates (logCylinderPlane q) = q := by
  rcases q with ⟨t, θ⟩
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  apply Prod.ext
  · simp [logCylinderCoordinates, localRadius_logCylinderPlane]
  · change (Complex.arg (Complex.equivRealProdCLM.symm
        (logCylinderPlane (t, (θ : AddCircle (2 * Real.pi))))) : Real.Angle) = θ
    rw [logCylinderPlane_coe]
    have hz : Complex.equivRealProdCLM.symm (logPolarPlane (t, θ)) =
        (Real.exp (-t) : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
      simp [logPolarPlane, Complex.equivRealProdCLM_symm_apply]
      ring
    rw [hz]
    simpa using Complex.arg_mul_cos_add_sin_mul_I_coe_angle (Real.exp_pos (-t))
      (θ : Real.Angle)

/-- The physical inverse is exact at every nonzero point, including seam points. -/
theorem logCylinderPlane_coordinates {p : ℝ × ℝ} (hp : p ≠ 0) :
    logCylinderPlane (logCylinderCoordinates p) = p := by
  rw [logCylinderCoordinates, logCylinderPlane_coe]
  have hr := localRadius_pos_of_ne_zero hp
  simp only [logPolarPlane, neg_neg, Real.exp_log hr]
  rw [localRadius_eq_complex_norm]
  apply Prod.ext
  · exact Complex.norm_mul_cos_arg _
  · exact Complex.norm_mul_sin_arg _

/-- The inverse coordinates transport planar null-set assertions jointly. -/
theorem quasiMeasurePreserving_logCylinderCoordinates :
    QuasiMeasurePreserving logCylinderCoordinates volume logCylinderMeasure := by
  let μ := (volume.restrict logPolarStrip).withDensity
    (fun q : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2))
  have hπ : QuasiMeasurePreserving logCylinderProjection μ
      ((volume : Measure ℝ).prod (volume : Measure (AddCircle (2 * Real.pi)))) :=
    measurePreserving_logCylinderProjection.quasiMeasurePreserving.mono_left
      (withDensity_absolutelyContinuous _ _)
  have hlength : ((volume : Measure ℝ).prod
      (volume : Measure (AddCircle (2 * Real.pi)))).AbsolutelyContinuous logCylinderMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.prod_smul_right]
    exact smul_absolutelyContinuous
  have hc : logCylinderCoordinates ∘ logPolarPlane = logCylinderProjection := by
    funext q
    change logCylinderCoordinates (logPolarPlane (q.1, q.2)) = logCylinderProjection q
    rw [← logCylinderPlane_coe q.1 q.2]
    exact logCylinderCoordinates_plane _
  refine ⟨measurable_logCylinderCoordinates, ?_⟩
  rw [← measurePreserving_logPolarPlane.map_eq,
    Measure.map_map measurable_logCylinderCoordinates continuous_logPolarPlane.measurable, hc]
  exact hπ.absolutelyContinuous.trans hlength

end NoEmbeddedEigenvalues
