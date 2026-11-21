module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.FirstBulkEndpointEnergy
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.EndpointTangentialTrace

/-!
# Global ordinary second numerator norm from the original weighted forcing

The actual second derivative has three terms: fixed-time second bulk,
first-bulk boundary potential, and differentiated forcing-value flux.
Unit-time-window traces control the middle term without logarithmic Hessian
weights or chart covariance of individual gradient traces. The local ordinary
second identity identifies their sum with the original scalar second derivative.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The distinct first-bulk boundary term in the second moving-endpoint identity
has its required actual h-weighted level norm on one common frequency collar. -/
theorem quarter_first_bulk_boundary_weighted_memLp {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hcell : cellSquare ⊆ U)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ i j, HasWeakPartialOn U i (J [j]) (J [i, j]))
    (hJL : ∀ w, w.length ≤ 2 → MemLp (J w) 2 (volume.restrict U))
    (hDw : ∀ j : Fin 2, MemLp (fun p ↦ J [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∀ μ : ℝ,
      MemLp (fun h : ℝ ↦ (h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ) *
        (quarterFirstBulkTrace μ J (1 / 8) h - quarterFirstBulkTrace μ J (-1 / 8) h)) 2
        (volume.restrict (Ioo 0 b)) := by
  obtain ⟨a, ha, hah, hT⟩ := quarter_first_bulk_endpoint_energy hU hcell hD hJL hDw
  obtain ⟨r, hr, hrh, hK⟩ := quarterEndpointCoefficient_weighted_bounds
  obtain ⟨K, hKpos, hKb⟩ := hK 0
  let b := min a r
  have hb : 0 < b := lt_min ha hr
  have hba : b ≤ a := min_le_left _ _
  have hbr : b ≤ r := min_le_right _ _
  have hbh : b < 1 / 2 := lt_of_le_of_lt hba hah
  have hb1 : b < 1 := by linarith
  have hcoeff : ContinuousOn (fun h : ℝ ↦ (8 : ℂ) *
      ((h : ℂ) * quarterEndpointCoefficient 0 1 h)) (Ioo 0 b) :=
    continuousOn_const.mul ((Complex.continuous_ofReal.continuousOn).mul
      ((contDiffOn_quarterEndpointCoefficient 0 1).continuousOn.mono
        (Ioo_subset_Ioo le_rfl hb1.le)))
  have htop : MemLp (fun h : ℝ ↦ (8 : ℂ) *
      ((h : ℂ) * quarterEndpointCoefficient 0 1 h)) ⊤
      (volume.restrict (Ioo 0 b)) := by
    apply memLp_top_of_bound (hcoeff.aestronglyMeasurable measurableSet_Ioo) (8 * K)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]
    exact mul_le_mul_of_nonneg_left (hKb 1 (Or.inr rfl) h
      ⟨hh.1, hh.2.trans_le hbr⟩).1 (by norm_num)
  have he (h : ℝ) (hh : h ∈ Ioo 0 b) :
      (8 : ℂ) * ((h : ℂ) * quarterEndpointCoefficient 0 1 h) =
        (h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ) := by
    have hd := ((contDiffOn_eighthPeriod.contDiffAt
      (Ioo_mem_nhds hh.1 (hh.2.trans hb1))).differentiableAt (by simp)).hasDerivAt
    have hs : HasDerivAt orbitPeriod (8 * deriv eighthPeriod h) h := by
      change HasDerivAt (fun x : ℝ ↦ 8 * eighthPeriod x) _ _
      exact hd.const_mul (8 : ℝ)
    rw [hs.deriv]
    simp only [quarterEndpointCoefficient, zero_mul, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, mul_one, Complex.ofReal_mul]
    push_cast
    ring
  refine ⟨b, hb, hbh, ?_⟩
  intro μ
  have hTp := (hT μ true).mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hba))
  have hTm := (hT μ false).mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hba))
  apply (htop.mul (hTp.sub hTm)).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  rw [Pi.mul_apply, Pi.sub_apply, he h hh]
  rfl

/-- Global control of the actual ordinary second numerator derivative under the
original weighted forcing inputs (`lem:weighted-numerator-second-norm`).
This is the ordinary scalar derivative, not only the fixed-time bulk term. -/
theorem IsTransportPair.weighted_numerator_second_norm
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ ∀ μ : ℝ,
      MemLp (fun h : ℝ ↦ (h : ℂ) * deriv (deriv (quarterNumerator μ g)) h) 2
        (volume.restrict (Ioo 0 r)) := by
  have hU := hp.isOrbitUnion.1
  obtain ⟨J, hJ, hJD⟩ := hp.memSobolevOn.exists_weakJet_two_with_first hU hD
  have hJL := hp.memSobolevOn.memLp_weakJet hU hJ
  have hDw (j : Fin 2) : MemLp (fun p ↦ J [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare) := by
    simpa only [hJD j] using hDf j
  have hD₁ (j : Fin 2) : HasWeakPartialOn U j f (J [j]) := by
    simpa only [hJD j] using hD j
  have hD₂ (i j : Fin 2) : HasWeakPartialOn U i (J [j]) (J [i, j]) :=
    hJ.2 [j] (by simp) i
  obtain ⟨a, ha, hah, hT⟩ := quarter_first_bulk_boundary_weighted_memLp hU
    (subset_closure.trans hcell) hD₂ hJL hDw
  obtain ⟨b, _, hb, hbh, _, _, hB₂, _⟩ :=
    hp.memSobolevOn.second_numerator_bulk_estimates hU (subset_closure.trans hcell) hJ
  obtain ⟨c, hc, hch, hE₁⟩ :=
    hp.weighted_numerator_endpoint_derivative hcell hg hfg hD₁ hf hDw
  let r := min a (min b c)
  have hr : 0 < r := lt_min ha (lt_min hb hc)
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right a (min b c)).trans (min_le_left _ _)
  have hrc : r ≤ c := (min_le_right a (min b c)).trans (min_le_right _ _)
  have hrh : r < 1 / 2 := lt_of_le_of_lt hra hah
  have hr1 : r < 1 := by linarith
  refine ⟨r, hr, hrh, ?_⟩
  intro μ
  have hA := (hB₂ μ).mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hrb))
  have hB := (hT μ).mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hra))
  have hC := (hE₁ μ).mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hrc))
  have hCandidate : MemLp (fun h : ℝ ↦
      (h : ℂ) * quarterNumeratorSecondDerivative μ g J h) 2
      (volume.restrict (Ioo 0 r)) := by
    apply ((hA.add hB).add hC).ae_eq
    exact Eventually.of_forall fun h ↦ by
      dsimp only [Pi.add_apply, quarterNumeratorSecondDerivative]
      ring
  apply memLp_two_of_local_sq_bound (hCandidate.integrable_norm_pow (by norm_num))
  intro u w hu huw hw
  have he := hp.quarterNumerator_second_derivative_ae hcell hg hfg hJ hu huw hw hr1 μ
  have hew : (fun h : ℝ ↦ (h : ℂ) * deriv (deriv (quarterNumerator μ g)) h)
      =ᵐ[volume.restrict (Ioo u w)]
        (fun h : ℝ ↦ (h : ℂ) * quarterNumeratorSecondDerivative μ g J h) :=
    he.mono fun h hh ↦ congrArg ((h : ℂ) * ·) hh
  exact ⟨(hCandidate.mono_measure
    (Measure.restrict_mono_set _ (Ioo_subset_Ioo hu.le hw.le))).ae_eq hew.symm,
    hew.mono fun h hh ↦ le_of_eq (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hh)⟩

end NoEmbeddedEigenvalues
