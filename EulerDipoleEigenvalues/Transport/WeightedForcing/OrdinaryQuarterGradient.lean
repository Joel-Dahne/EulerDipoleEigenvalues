module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterGradient
public import EulerDipoleEigenvalues.Transport.WeightedForcing.SecondNumeratorBulk

/-!
# Ordinary physical gradient norms on the supplied quarter collar

The inverse-frame coefficients normalized by distance are bounded on every
collar b < 1/2. The small-level estimates handle h near zero; compactness handles
the rest of the same collar. Thus no shrinkage is needed for ordinary H¹.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- The level variation times distance is bounded on every specified quarter
collar below half level, not merely on an unspecified smaller collar. -/
theorem orbit_level_variation_mul_distance_bound {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2) :
    ∃ C : ℝ, ∀ q ∈ quarterOrbitStrip b,
      ‖deriv (fun h ↦ dipoleOrbit h q.2) q.1‖ * saddleDist (dipoleOrbit q.1 q.2) ≤ C := by
  obtain ⟨C, δ, hδ, _, hV⟩ := deriv_dipoleOrbit_level_le_saddleDist
  let a := min δ b / 2
  have ha : 0 < a := half_pos (lt_min hδ hb)
  have haδ : a ≤ δ := by dsimp [a]; linarith [min_le_left δ b, lt_min hδ hb]
  have hb1 : b < 1 := by linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_eighthPeriod.mono (Icc_subset_Ioo ha hb1))
  let K := Icc a b ×ˢ Icc (-M) M
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hVK : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun h ↦ dipoleOrbit h q.2) q.1) K := by
    intro q hq
    exact (contDiffAt_orbit_level_derivative
      ⟨ha.trans_le hq.1.1, hq.1.2.trans_lt hb1⟩).continuousAt.continuousWithinAt
  have hd : Continuous (fun q : ℝ × ℝ ↦ saddleDist (dipoleOrbit q.1 q.2)) :=
    (Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit
  obtain ⟨E, hE⟩ := hK.exists_bound_of_continuousOn (hVK.norm.mul hd.continuousOn)
  refine ⟨max |C| |E|, fun q hq ↦ ?_⟩
  have hd0 : 0 ≤ saddleDist (dipoleOrbit q.1 q.2) := Metric.infDist_nonneg
  by_cases hh : q.1 < δ
  · by_cases hz : saddleDist (dipoleOrbit q.1 q.2) = 0
    · simp [hz]
    · have h := mul_le_mul_of_nonneg_right
        (hV q.1 ⟨hq.1, hh⟩ q.2 (abs_le.mpr ⟨hq.2.2.1.le, hq.2.2.2.le⟩)).1 hd0
      rw [div_mul_cancel₀ _ hz] at h
      exact h.trans ((le_abs_self C).trans (le_max_left _ _))
  · have hqa : a ≤ q.1 := haδ.trans (le_of_not_gt hh)
    have ht : |q.2| ≤ M := (abs_le.mpr ⟨hq.2.2.1.le, hq.2.2.2.le⟩).trans
      ((le_abs_self _).trans (hM q.1 ⟨hqa, hq.2.1.le⟩))
    exact (le_abs_self _).trans ((hE q ⟨⟨hqa, hq.2.1.le⟩, abs_le.mp ht⟩).trans
      ((le_abs_self E).trans (le_max_right _ _)))

/-- Original weak-quarter weights give actual ordinary Cartesian candidate
norms on that same whole quarter strip. -/
theorem quarterInverseGradient_ordinary_memLp {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2)
    {H T : ℝ × ℝ → ℂ}
    (hH : MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * H q) 2
      (volume.restrict (quarterOrbitStrip b)))
    (hT : MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b))) (j : Fin 2) :
    MemLp (quarterInverseGradient H T j) 2 (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨C, hC⟩ := orbit_level_variation_mul_distance_bound hb hbh
  have hd : Measurable (fun q : ℝ × ℝ ↦ saddleDist (dipoleOrbit q.1 q.2)) :=
    ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit).measurable
  have hA : MemLp (fun q ↦ quarterLevelDual j q /
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) ⊤
      (volume.restrict (quarterOrbitStrip b)) :=
    memLp_top_of_bound ((measurable_quarterLevelDual j).div hd.complex_ofReal).aestronglyMeasurable
      1 (Eventually.of_forall (norm_quarterLevelDual_div_le j))
  have hB : MemLp (fun q ↦ quarterTimeDual j q *
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) ⊤
      (volume.restrict (quarterOrbitStrip b)) := by
    apply memLp_top_of_bound
      ((measurable_quarterTimeDual j).mul hd.complex_ofReal).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ saddleDist (dipoleOrbit q.1 q.2) from Metric.infDist_nonneg)]
    exact (mul_le_mul_of_nonneg_right (norm_quarterTimeDual_le j q)
      Metric.infDist_nonneg).trans (hC q hq)
  apply ((hA.mul hH).add (hB.mul hT)).ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
  have hp := dipoleOrbit_mem_cellSquare hq.1 (by linarith [hq.2.1]) q.2
  have hdpos : 0 < saddleDist (dipoleOrbit q.1 q.2) :=
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1)).trans_le (cos_diag_fst_le_saddleDist _)
  have hdc : (saddleDist (dipoleOrbit q.1 q.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdpos.ne'
  dsimp only [Pi.add_apply, Pi.mul_apply, quarterInverseGradient]
  field_simp

/-- Unweighted inverse candidates transport to actual L² spatial gradients. -/
theorem memLp_quarterSpatialGradient_ordinary {b : ℝ} (hb : b ≤ 1)
    {H T : ℝ × ℝ → ℂ} (j : Fin 2)
    (hG : MemLp (quarterInverseGradient H T j) 2
      (volume.restrict (quarterOrbitStrip b))) :
    MemLp (quarterSpatialGradient H T j) 2 (volume.restrict (quarterImage b)) := by
  exact memLp_two_comp_chart_symm (contDiffOn_quarterChart hb)
    (fun _ hq ↦ det_fderiv_quarterChart hb hq) hG

end EulerDipoleEigenvalues
