module

public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.QuarterTime
public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.OddOddQuarter
public import EulerDipoleEigenvalues.Transport.WeightedForcing.SaddleTransportWeights

/-!
# Saddle-weighted time derivatives on the base quarter

Blueprint: `lem:dd-quarter-time`, `lem:dd-base-quarter-weighted-derivatives`.

The weak time identity is independent of odd–odd saddle regularity.
Only its stronger weighted L² bound uses saddle mass and forcing weights.
The same raw spatial vorticity pullback carries both coordinate derivatives.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- The actual odd–odd vorticity time derivative has the squared-distance
weighted L² bound on every base-quarter strip below level one. -/
theorem dd_quarter_time {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {b : ℝ} (hb : b < 1) :
    HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2))
      (fun q ↦ vorticityTimeDerivative lam ω (dipoleOrbit q.1 q.2)) ∧
    MemLp (fun q ↦ vorticityTimeDerivative lam ω (dipoleOrbit q.1 q.2) /
      (saddleDist (dipoleOrbit q.1 q.2) ^ 2 : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  refine ⟨eigenfunction_quarter_time hlam hω hb, ?_⟩
  have hgrad := (dd_weighted_forcing hlam hω hs).2.1
  have hm (v : L2) : Measurable (liftL2 v) :=
    (Lp.stronglyMeasurable v).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have hx := memLp_sin_mul_div_saddleDist_sq (hm (streamPartial 0 ω)) (hgrad 0) 1
  have hy := memLp_sin_mul_div_saddleDist_sq (hm (streamPartial 1 ω)) (hgrad 1) 0
  have hv := (saddle_dd hlam hω hs).1
  have htime : MemLp (fun p ↦ vorticityTimeDerivative lam ω p / (saddleDist p ^ 2 : ℂ))
      2 (volume.restrict cellNeighbourhood) := by
    apply ((hv.const_mul (Complex.I * (lam : ℂ))).sub (hx.sub hy)).ae_eq
    exact Eventually.of_forall fun p ↦ by
      dsimp [vorticityTimeDerivative]
      ring
  have hd : Continuous saddleDist := Metric.continuous_infDist_pt saddleSet
  have hmt := measurable_vorticityTimeDerivative lam ω
  have hmeas : Measurable (fun p ↦
      vorticityTimeDerivative lam ω p / (saddleDist p ^ 2 : ℂ)) := by fun_prop
  exact memLp_comp_quarterOrbitStrip hb.le hmeas
    (htime.mono_measure (Measure.restrict_mono
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood) le_rfl))

/-- Both specified base-quarter derivatives, with the distinct weights needed
for inverse-coordinate reconstruction of the Cartesian gradient. -/
theorem dd_base_quarter_weighted_derivatives {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ H T : ℝ × ℝ → ℂ,
      HasWeakPartialOn (quarterOrbitStrip b) 0
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) H ∧
      HasWeakPartialOn (quarterOrbitStrip b) 1
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) T ∧
      MemLp H 2 (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨b, hb, hbhalf, H, hH, hHl⟩ := dd_quarter_level hlam hω hs hκ
  have htime := dd_quarter_time hlam hω hs (by linarith : b < 1)
  exact ⟨b, hb, hbhalf, H, _, hH, htime.1, hHl, htime.2⟩

end EulerDipoleEigenvalues
