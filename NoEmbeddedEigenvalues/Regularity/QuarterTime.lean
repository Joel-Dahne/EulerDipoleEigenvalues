import NoEmbeddedEigenvalues.QuarterTimeDerivative
import NoEmbeddedEigenvalues.CellPeriodization

/-!
# The eigenfunction's weak quarter-time derivative

Blueprint: `def:vorticity-time-derivative`, `lem:eigen-quarter-time`.

The canonical Fourier partial lifts differentiate the continuous stream weakly.
Subtracting their transport equation from the eigenfunction equation gives a
specified transport derivative of the vorticity, and orbitwise ACL testing
identifies its raw pullback as the weak time derivative.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The spatial formula whose pullback is the vorticity time derivative. -/
def vorticityTimeDerivative (lam : ℝ) (ω : L2) (p : ℝ × ℝ) : ℂ :=
  Complex.I * (lam : ℂ) * liftL2 ω p -
    ((Real.sin p.2 : ℂ) * liftL2 (streamPartial 0 ω) p -
      (Real.sin p.1 : ℂ) * liftL2 (streamPartial 1 ω) p)

private theorem measurable_lift (v : L2) : Measurable (liftL2 v) :=
  (Lp.stronglyMeasurable v).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable

theorem measurable_vorticityTimeDerivative (lam : ℝ) (ω : L2) :
    Measurable (vorticityTimeDerivative lam ω) := by
  have hv := measurable_lift ω
  have hx := measurable_lift (streamPartial 0 ω)
  have hy := measurable_lift (streamPartial 1 ω)
  unfold vorticityTimeDerivative
  fun_prop

theorem memLp_vorticityTimeDerivative (lam : ℝ) (ω : L2) :
    MemLp (vorticityTimeDerivative lam ω) 2 (volume.restrict cellSquare) := by
  have hb : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  have hsin (v : L2) (j : Fin 2) :
      MemLp (fun p : ℝ × ℝ ↦ (Real.sin (if j = 0 then p.1 else p.2) : ℂ) * liftL2 v p)
        2 (volume.restrict cellSquare) := by
    have hm : Measurable (fun p : ℝ × ℝ ↦
        (Real.sin (if j = 0 then p.1 else p.2) : ℂ) * liftL2 v p) := by
      have := measurable_lift v
      split_ifs <;> fun_prop
    apply (memLp_liftL2 v hb).of_le_mul (c := 1) hm.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
  exact ((memLp_liftL2 ω hb).const_mul (Complex.I * (lam : ℂ))).sub
    ((hsin (streamPartial 0 ω) 1).sub (hsin (streamPartial 1 ω) 0))

/-- This transport derivative uses only the eigenfunction equation and canonical
Fourier first partials, with no saddle regularity hypothesis. -/
theorem hasWeakL0On_vorticityTimeDerivative {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    HasWeakL0On cellNeighbourhood (liftL2 ω) (vorticityTimeDerivative lam ω) := by
  have hp := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0)
    cellNeighbourhood).congr_left (streamLift_ae_eq_contStream ω)
  have hy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1)
    cellNeighbourhood).congr_left (streamLift_ae_eq_contStream ω)
  have hf := HasWeakPartialOn.hasWeakL0On isOrbitUnion_cellNeighbourhood.1 hx hy
  have hv := hp.hasWeakL0On.sub hf
  have hval : (fun p ↦ (liftL2 ω p + contStream ω p) - contStream ω p) = liftL2 ω := by
    funext p
    ring
  rw [hval] at hv
  apply hv.congr_deriv
  exact Eventually.of_forall fun p ↦ by dsimp [vorticityTimeDerivative]; ring

/-- The actual base-quarter vorticity pullback has its specified weak time
derivative on every strip with cutoff below one. -/
theorem eigenfunction_quarter_time {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {b : ℝ} (hb : b < 1) :
    HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2))
      (fun q ↦ vorticityTimeDerivative lam ω (dipoleOrbit q.1 q.2)) := by
  apply (hasWeakL0On_vorticityTimeDerivative hlam hω).quarter_time hb
    (fun _ hp ↦ closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1.1))
    (measurable_lift ω) (measurable_vorticityTimeDerivative lam ω)
  · exact memLp_liftL2 ω (isBounded_cellNeighbourhood.subset
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood))
  · exact memLp_vorticityTimeDerivative lam ω

end NoEmbeddedEigenvalues
