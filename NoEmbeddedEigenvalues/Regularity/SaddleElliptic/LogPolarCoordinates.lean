module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint logarithmic-polar measure transport

The real-angle chart is injective on the open angular strip. Its nonzero
Jacobian transports planar a.e. identities jointly, before any angular slicing.
The circle uses probability Haar measure, not angular length measure.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Measure Set

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Logarithmic-polar parametrization with a real angular coordinate. -/
def logPolarPlane (q : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (-q.1) * Real.cos q.2, Real.exp (-q.1) * Real.sin q.2)

/-- One injective angular chart; the omitted seam is null. -/
def logPolarStrip : Set (ℝ × ℝ) := univ ×ˢ Ioo (-Real.pi) Real.pi

theorem measurableSet_logPolarStrip : MeasurableSet logPolarStrip :=
  MeasurableSet.univ.prod measurableSet_Ioo

/-- The exact Cartesian derivative of the logarithmic-polar parametrization. -/
def logPolarDeriv (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![-Real.exp (-q.1) * Real.cos q.2, -Real.exp (-q.1) * Real.sin q.2;
       -Real.exp (-q.1) * Real.sin q.2, Real.exp (-q.1) * Real.cos q.2]).toContinuousLinearMap

@[fun_prop]
theorem continuous_logPolarPlane : Continuous logPolarPlane := by
  unfold logPolarPlane
  fun_prop

theorem hasFDerivAt_logPolarPlane (q : ℝ × ℝ) :
    HasFDerivAt logPolarPlane (logPolarDeriv q) q := by
  have hfst : HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) q := hasFDerivAt_fst
  have hr := (Real.hasDerivAt_exp (-q.1)).comp_hasFDerivAt q hfst.neg
  have hsnd : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ ℝ ℝ) q := hasFDerivAt_snd
  have hc := (Real.hasDerivAt_cos q.2).comp_hasFDerivAt q hsnd
  have hs := (Real.hasDerivAt_sin q.2).comp_hasFDerivAt q hsnd
  unfold logPolarDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (hr.mul hc) (hr.mul hs) using 2 <;>
    simp [smul_smul, add_comm, mul_comm, neg_mul, smul_neg, neg_smul,
      ContinuousLinearMap.snd]

theorem det_logPolarDeriv (q : ℝ × ℝ) :
    (logPolarDeriv q).det = -(Real.exp (-q.1) ^ 2) := by
  unfold logPolarDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  calc
    _ = -(Real.exp (-q.1) ^ 2) * (Real.cos q.2 ^ 2 + Real.sin q.2 ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem logPolarPlane_injOn : InjOn logPolarPlane logPolarStrip := by
  intro x hx y hy hxy
  have hx' : (Real.exp (-x.1), x.2) ∈ polarCoord.target := ⟨Real.exp_pos _, hx.2⟩
  have hy' : (Real.exp (-y.1), y.2) ∈ polarCoord.target := ⟨Real.exp_pos _, hy.2⟩
  have h := polarCoord.symm.injOn hx' hy' hxy
  obtain ⟨ht, hθ⟩ := Prod.mk.inj h
  exact Prod.ext (neg_injective (Real.exp_injective ht)) hθ

theorem image_logPolarPlane_strip : logPolarPlane '' logPolarStrip = polarCoord.source := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : (Real.exp (-q.1), q.2) ∈ polarCoord.target := ⟨Real.exp_pos _, hq.2⟩
    have hout := polarCoord.map_target hq'
    exact hout
  · intro p hp
    have hq := polarCoord.map_source hp
    refine ⟨(-Real.log (polarCoord p).1, (polarCoord p).2), ⟨mem_univ _, hq.2⟩, ?_⟩
    change polarCoord.symm (Real.exp (-(-Real.log (polarCoord p).1)), (polarCoord p).2) = p
    rw [neg_neg, Real.exp_log hq.1]
    exact polarCoord.left_inv hp

/-- The polar area Jacobian is exp(-2t). The omitted planar seam is null. -/
theorem measurePreserving_logPolarPlane :
    MeasurePreserving logPolarPlane
      ((volume.restrict logPolarStrip).withDensity
        (fun q ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2))) volume := by
  refine ⟨continuous_logPolarPlane.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (ℝ × ℝ))
    measurableSet_logPolarStrip.nullMeasurableSet
    (fun q _ ↦ (hasFDerivAt_logPolarPlane q).hasFDerivWithinAt) logPolarPlane_injOn
  simpa only [det_logPolarDeriv, abs_neg, abs_sq,
    image_logPolarPlane_strip, Measure.restrict_congr_set polarCoord_source_ae_eq_univ,
    Measure.restrict_univ] using hm

/-- Joint transport of null sets on the real angular chart. -/
theorem quasiMeasurePreserving_logPolarPlane :
    QuasiMeasurePreserving logPolarPlane (volume.restrict logPolarStrip) volume := by
  have hj : Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2)) := by
    fun_prop
  exact measurePreserving_logPolarPlane.quasiMeasurePreserving.mono_left
    (withDensity_absolutelyContinuous' hj.aemeasurable
      (Filter.Eventually.of_forall fun q ↦ ne_of_gt (ENNReal.ofReal_pos.mpr
        (sq_pos_of_pos (Real.exp_pos _)))))

/-- Logarithmic-cylinder measure with probability angular Haar measure. -/
def logCylinderMeasure : Measure (ℝ × AddCircle (2 * Real.pi)) :=
  volume.prod AddCircle.haarAddCircle

/-- Probability angular measure differs from angular length by the factor 1/(2π). -/
theorem logCylinderMeasure_eq_smul_length :
    logCylinderMeasure = (ENNReal.ofReal (2 * Real.pi))⁻¹ •
      (volume.prod (volume : Measure (AddCircle (2 * Real.pi)))) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.prod_smul_right, smul_smul,
    ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul]
  rfl

/-- The Cartesian point represented by logarithmic radius and circle angle. -/
def logCylinderPlane (q : ℝ × AddCircle (2 * Real.pi)) : ℝ × ℝ :=
  (Real.exp (-q.1) * (_root_.fourier 1 q.2).re,
   Real.exp (-q.1) * (_root_.fourier 1 q.2).im)

private theorem angularUnit_coe (θ : ℝ) :
    _root_.fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi)) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [_root_.fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem logCylinderPlane_coe (t θ : ℝ) :
    logCylinderPlane (t, (θ : AddCircle (2 * Real.pi))) = logPolarPlane (t, θ) := by
  simp only [logCylinderPlane, logPolarPlane, angularUnit_coe,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

@[fun_prop]
theorem continuous_logCylinderPlane : Continuous logCylinderPlane := by
  unfold logCylinderPlane
  fun_prop

/-- Pass from a real angular representative to the angular quotient. -/
def logCylinderProjection (q : ℝ × ℝ) : ℝ × AddCircle (2 * Real.pi) := (q.1, q.2)

/-- Projection of one real angular period has angular length measure. -/
theorem measurePreserving_logCylinderProjection :
    MeasurePreserving logCylinderProjection (volume.restrict logPolarStrip)
      (volume.prod (volume : Measure (AddCircle (2 * Real.pi)))) := by
  have hm := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi))
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he] at hm
  have hs : volume.restrict logPolarStrip =
      (volume : Measure ℝ).prod (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    rw [logPolarStrip, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [hs]
  exact hm

/-- Joint null-set transport with angular length measure. -/
theorem quasiMeasurePreserving_logCylinderPlane_length :
    QuasiMeasurePreserving logCylinderPlane
      (volume.prod (volume : Measure (AddCircle (2 * Real.pi)))) volume := by
  have hp := measurePreserving_logCylinderProjection
  have hc : logCylinderPlane ∘ logCylinderProjection = logPolarPlane := by
    funext q
    exact logCylinderPlane_coe q.1 q.2
  refine ⟨continuous_logCylinderPlane.measurable, ?_⟩
  rw [← hp.map_eq, Measure.map_map continuous_logCylinderPlane.measurable hp.measurable, hc]
  exact quasiMeasurePreserving_logPolarPlane.absolutelyContinuous

/-- Joint transport on the whole logarithmic cylinder. Probability Haar measure
changes only a positive constant, so it preserves the same null sets. -/
theorem quasiMeasurePreserving_logCylinderPlane :
    QuasiMeasurePreserving logCylinderPlane logCylinderMeasure volume := by
  apply quasiMeasurePreserving_logCylinderPlane_length.mono_left
  apply AbsolutelyContinuous.prod AbsolutelyContinuous.rfl
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact absolutelyContinuous_smul (by positivity)

end NoEmbeddedEigenvalues
