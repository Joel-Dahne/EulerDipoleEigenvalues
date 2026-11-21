import NoEmbeddedEigenvalues.Transport.WeightedForcing.OrdinaryQuarterForcing
import NoEmbeddedEigenvalues.Transport.WeightedForcing.SaddleTransportWeights

/-!
# The physical-time derivative of the first fixed-time level contraction

The variational equation gives V_t = DX V. The Hessian coefficients V_j X_i
are bounded because |V| is at most C/d and each velocity component is at most d.
Only the singleton row has a distance weight; ordered Hessian entries need their
standing unweighted L2 norms. The formula and its norm are separate from the
weak differentiation identity.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology

/-- Formal time derivative, with the supplied ordered second entries retained. -/
def quarterForcingLevelTimeDerivative (J : List (Fin 2) → ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) : ℂ :=
  let p := dipoleOrbit q.1 q.2
  let V := deriv (fun h ↦ dipoleOrbit h q.2) q.1
  ((Real.cos p.2 * V.2 : ℝ) : ℂ) * J [0] p -
    ((Real.cos p.1 * V.1 : ℝ) : ℂ) * J [1] p +
    ∑ i : Fin 2, ∑ j : Fin 2,
      ((axisCoord j V * axisCoord i (dipoleVelocity p) : ℝ) : ℂ) * J [i, j] p

/-- Raw L2 first entries suffice for joint a.e. measurability of the level field. -/
theorem aestronglyMeasurable_quarterFirstLevelDerivative {b : ℝ} (hb : b ≤ 1)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hJ : ∀ j : Fin 2, MemLp (J [j]) 2 (volume.restrict cellSquare)) :
    AEStronglyMeasurable (quarterForcingLevelDerivative J)
      (volume.restrict (quarterOrbitStrip b)) := by
  have hV : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun x ↦ dipoleOrbit x q.2) q.1)
      (quarterOrbitStrip b) := fun q hq ↦
    (contDiffAt_orbit_level_derivative ⟨hq.1, hq.2.1.trans_le hb⟩).continuousAt.continuousWithinAt
  have hP (j) := (memLp_comp_quarterOrbitStrip_of_memLp hb (hJ j)).aestronglyMeasurable
  change AEStronglyMeasurable (fun q ↦ _ + _) _
  exact (((Complex.continuous_ofReal.comp_continuousOn hV.fst).aestronglyMeasurable
    (measurableSet_quarterOrbitStrip b)).mul (hP 0)).add
    (((Complex.continuous_ofReal.comp_continuousOn hV.snd).aestronglyMeasurable
      (measurableSet_quarterOrbitStrip b)).mul (hP 1))

/-- Auxiliary singleton entries of DXᵀ D; no weak-jet property is asserted. -/
private def velocityJacobianJet (J : List (Fin 2) → ℝ × ℝ → ℂ)
    (w : List (Fin 2)) (p : ℝ × ℝ) : ℂ :=
  if w = [0] then -(Real.cos p.1 : ℂ) * J [1] p
  else if w = [1] then (Real.cos p.2 : ℂ) * J [0] p else 0

private theorem memLp_cos_mul {μ : Measure (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 μ) {x : ℝ × ℝ → ℝ} (hx : Continuous x) :
    MemLp (fun p ↦ (Real.cos (x p) : ℂ) * F p) 2 μ := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (Real.cos (x p) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (Real.continuous_cos.comp hx)).aestronglyMeasurable
  apply hF.of_le (hm.mul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun p ↦ by
    rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

/-- Both the level contraction and its formal time derivative are genuinely L2
on one smaller quarter strip, under the original singleton weight and standing
unweighted second-jet norms. No logarithmic Hessian norm is assumed. -/
theorem quarter_first_bulk_time_energy {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hJ : ∀ w, w.length ≤ 2 → MemLp (J w) 2 (volume.restrict cellSquare))
    (hDw : ∀ j : Fin 2, MemLp (fun p ↦ J [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare)) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧
      MemLp (quarterForcingLevelDerivative J) 2 (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (quarterForcingLevelTimeDerivative J) 2 (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨C, η, hη, _, hV⟩ := deriv_dipoleOrbit_level_le_saddleDist
  let c := min r η / 2
  have hc : 0 < c := half_pos (lt_min hr hη)
  have hcr : c < r := by dsimp [c]; linarith [min_le_left r η]
  have hcη : c < η := by dsimp [c]; linarith [min_le_right r η]
  have hc1 : c < 1 := hcr.trans hr1
  have hJL (j : Fin 2) := hJ [j] (by simp)
  obtain ⟨b₀, _, hb₀, hb₀c, _, hG, _⟩ := ordinary_quarter_forcing_data hc hc1 hDw
    (aestronglyMeasurable_quarterFirstLevelDerivative hc1.le hJL)
  let K := velocityJacobianJet J
  have hKL (j : Fin 2) : MemLp (K [j]) 2 (volume.restrict cellSquare) := by
    fin_cases j
    · change MemLp (fun p ↦ -(Real.cos p.1 : ℂ) * J [1] p) 2 _
      convert (memLp_cos_mul (hJL 1) continuous_fst).neg using 1
      ext p
      simp only [Pi.neg_apply, neg_mul]
    · change MemLp (fun p ↦ (Real.cos p.2 : ℂ) * J [0] p) 2 _
      exact memLp_cos_mul (hJL 0) continuous_snd
  have hKw (j : Fin 2) : MemLp (fun p ↦ K [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare) := by
    fin_cases j
    · change MemLp (fun p ↦ (-(Real.cos p.1 : ℂ) * J [1] p) /
        (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 _
      convert (memLp_cos_mul (hDw 1) continuous_fst).neg using 1
      ext p
      simp only [Pi.neg_apply, mul_div_assoc, neg_mul, neg_div]
    · change MemLp (fun p ↦ ((Real.cos p.2 : ℂ) * J [0] p) /
        (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 _
      convert memLp_cos_mul (hDw 0) continuous_snd using 1
      ext p
      exact mul_div_assoc _ _ _
  have hb₀1 : b₀ < 1 := hb₀c.trans hc1
  obtain ⟨b, _, hb, hbb₀, _, hGK, _⟩ := ordinary_quarter_forcing_data hb₀ hb₀1 hKw
    (aestronglyMeasurable_quarterFirstLevelDerivative hb₀1.le hKL)
  have hbr : b < r := hbb₀.trans (hb₀c.trans hcr)
  have hbη : b < η := hbb₀.trans (hb₀c.trans hcη)
  have hb1 : b < 1 := hbr.trans hr1
  have hs : quarterOrbitStrip b ⊆ quarterOrbitStrip b₀ :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans hbb₀, hq.2.2⟩
  have hVc : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun x ↦ dipoleOrbit x q.2) q.1)
      (quarterOrbitStrip b) := fun q hq ↦
    (contDiffAt_orbit_level_derivative ⟨hq.1, hq.2.1.trans hb1⟩).continuousAt.continuousWithinAt
  have hXc : Continuous (fun q : ℝ × ℝ ↦ dipoleVelocity (dipoleOrbit q.1 q.2)) := by
    have hc : Continuous dipoleVelocity := by unfold dipoleVelocity; fun_prop
    exact hc.comp continuous_dipoleOrbit
  have haxis (j : Fin 2) {F : ℝ × ℝ → ℝ × ℝ}
      (hF : ContinuousOn F (quarterOrbitStrip b)) :
      ContinuousOn (fun q ↦ axisCoord j (F q)) (quarterOrbitStrip b) := by
    fin_cases j
    · exact hF.fst
    · exact hF.snd
  have hcoef (q : ℝ × ℝ) (hq : q ∈ quarterOrbitStrip b) (i j : Fin 2) :
      |axisCoord j (deriv (fun x ↦ dipoleOrbit x q.2) q.1) *
        axisCoord i (dipoleVelocity (dipoleOrbit q.1 q.2))| ≤ |C| := by
    let d := saddleDist (dipoleOrbit q.1 q.2)
    have hd : 0 ≤ d := Metric.infDist_nonneg
    have hv := (hV q.1 ⟨hq.1, hq.2.1.trans hbη⟩ q.2
      (abs_le.2 ⟨hq.2.2.1.le, hq.2.2.2.le⟩)).1
    have hvj : |axisCoord j (deriv (fun x ↦ dipoleOrbit x q.2) q.1)| ≤ C / d := by
      apply le_trans _ hv
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hx : |axisCoord i (dipoleVelocity (dipoleOrbit q.1 q.2))| ≤ d := by
      fin_cases i
      · simpa [axisCoord, dipoleVelocity] using abs_sin_axis_le_saddleDist (dipoleOrbit q.1 q.2) 1
      · simpa [axisCoord, dipoleVelocity] using abs_sin_axis_le_saddleDist (dipoleOrbit q.1 q.2) 0
    rw [abs_mul]
    by_cases hd0 : d = 0
    · have hx0 : |axisCoord i (dipoleVelocity (dipoleOrbit q.1 q.2))| = 0 :=
        le_antisymm (hd0 ▸ hx) (abs_nonneg _)
      rw [hx0, mul_zero]
      exact abs_nonneg _
    · calc
        _ ≤ (|C| / d) * d := mul_le_mul
          (hvj.trans (div_le_div_of_nonneg_right (le_abs_self C) hd)) hx
          (abs_nonneg _) (by positivity)
        _ = |C| := div_mul_cancel₀ _ hd0
  have hTerm (i j : Fin 2) : MemLp (fun q ↦
      ((axisCoord j (deriv (fun x ↦ dipoleOrbit x q.2) q.1) *
        axisCoord i (dipoleVelocity (dipoleOrbit q.1 q.2)) : ℝ) : ℂ) *
        J [i, j] (dipoleOrbit q.1 q.2)) 2 (volume.restrict (quarterOrbitStrip b)) := by
    have hl := memLp_comp_quarterOrbitStrip_of_memLp hb1.le (hJ [i, j] (by simp))
    have hm : AEStronglyMeasurable (fun q ↦
        ((axisCoord j (deriv (fun x ↦ dipoleOrbit x q.2) q.1) *
          axisCoord i (dipoleVelocity (dipoleOrbit q.1 q.2)) : ℝ) : ℂ))
        (volume.restrict (quarterOrbitStrip b)) :=
      (Complex.continuous_ofReal.comp_continuousOn
        ((haxis j hVc).mul (haxis i hXc.continuousOn))).aestronglyMeasurable
        (measurableSet_quarterOrbitStrip b)
    apply hl.of_le_mul (c := |C|) (hm.mul hl.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcoef q hq i j) (norm_nonneg _)
  have hHess := memLp_finsetSum Finset.univ fun i _ ↦
    memLp_finsetSum Finset.univ fun j _ ↦ hTerm i j
  refine ⟨b, hb, hbr, hG.mono_measure (Measure.restrict_mono_set _ hs), ?_⟩
  apply (hGK.add hHess).ae_eq
  exact Eventually.of_forall fun q ↦ by
    dsimp only [Pi.add_apply, quarterForcingLevelTimeDerivative, quarterForcingLevelDerivative,
      K, velocityJacobianJet]
    simp only [List.cons.injEq, Fin.isValue, ↓reduceIte, one_ne_zero, false_and]
    push_cast
    ring

end NoEmbeddedEigenvalues
