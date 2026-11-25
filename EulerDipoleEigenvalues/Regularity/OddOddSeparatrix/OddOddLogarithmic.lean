module

public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.OddOddLogBulk
public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.OddOddLogSaddle
public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.OddOddLogRays
public import EulerDipoleEigenvalues.Transport.WeightedForcing.WeightedNumerators
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.StreamJet
public import EulerDipoleEigenvalues.Transport.WeightedGains.LogarithmicDivision
public import EulerDipoleEigenvalues.Transport.WeightedForcing.LogarithmicNumerators

/-!
# Odd–odd logarithmic forcing and numerator interfaces

The canonical Fourier stream jet fixes the derivative data shared by bulk,
ray and orbit bounds. Periodic lifts have local weighted norms on an open
neighbourhood of the whole lifted separatrix, not a global finite plane norm.
The ordinary bulk terms use the physical logarithmic H¹ multiplier on the fixed
stream jet. The inverse-distance and ray terms require the quadratic saddle data.
The ray estimates use a bounded radial interval and canonical gradient traces.
Numerator summation restricts the existing compatible data, identifies its ray
traces by uniqueness, and combines the weighted bulk and endpoint masses.
Rotation parity is not needed for this summation; its premise is retained in the
export used by the subsequent character-wise phase division.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- Logarithmic bulk and endpoint-ray forcing estimates (`lem:dd-log-forcing`). -/
theorem dd_log_forcing {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      (∀ j : Fin 2, MemSobolevLocOn 0 U (fun p ↦
        (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω [j] p /
          (Real.rpow (saddleDist p) (3 / 2) : ℂ))) ∧
      (∀ w : List (Fin 2), w.length = 1 ∨ w.length = 2 →
        MemSobolevLocOn 0 U (fun p ↦
          (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω w p)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ (k : Fin 4) (side : Bool),
        rotatedQuarterEndpointRay k side '' Icc 0 ρ ⊆ U ∧
        MemLp (fun (r : ℝ) ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
          contStream ω (rotatedQuarterEndpointRay k side r) / (Real.rpow r (3 / 2) : ℂ)) 2
          (volume.restrict (Ioo 0 ρ)) ∧
        ∃ T : Fin 2 → ℝ → ℂ, ∀ j,
          HasQuarterRayTrace U ρ k side (streamJet2 ω [j]) (T j) ∧
          MemLp (fun (r : ℝ) ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * T j r /
            (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 ρ)) := by
  classical
  obtain ⟨V, hV, hVsep, hgrad, hbulk⟩ := dd_log_bulk hlam hω hs
  obtain ⟨W, hW, hWsep, _, _, hH3⟩ := dd_separatrix_h1 hlam hω hs
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hsep : {p | dipoleLift p = 0} ⊆ U := fun p hp ↦ ⟨hVsep hp, hWsep hp⟩
  have hJ (j : Fin 2) : MemSobolevLocOn 1 U (streamJet2 ω [j]) := by
    have h := (streamJet2_weak ω W).memSobolevLocOn hH3 [j] (by simp) (by simp)
    exact h.of_succ.mono inter_subset_right
  have hlocal (i : Fin 4 × Bool) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      rotatedQuarterEndpointRay i.1 i.2 '' Icc 0 δ ⊆ U ∧
      MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
        contStream ω (rotatedQuarterEndpointRay i.1 i.2 r) /
          (Real.rpow r (3 / 2) : ℂ)) 2 (volume.restrict (Ioo 0 δ)) ∧
      ∀ j : Fin 2, MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
        interiorChartTrace (rotatedQuarterEndpointChart i.1 i.2) (streamJet2 ω [j]) r /
          (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 δ)) := by
    obtain ⟨r, hr, hr1, hval, htrace⟩ := dd_log_ray_bounds hlam hω hs i.1 i.2
    have hc : dipoleLift (rotatedQuarterEndpointRay i.1 i.2 0) = 0 := by
      rcases i with ⟨k, side⟩
      fin_cases k <;> cases side <;>
        simp [rotatedQuarterEndpointRay, quarterEndpointRay, rotLift,
          Function.iterate_succ_apply', dipoleLift]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ (hsep hc)
    let δ := min r (ε / 2)
    have hδ : 0 < δ := lt_min hr (half_pos hε)
    have hδr : δ ≤ r := min_le_left _ _
    have hsub : Ioo 0 δ ⊆ Ioo 0 r := Ioo_subset_Ioo_right hδr
    refine ⟨δ, hδ, hδr.trans_lt hr1, ?_,
      hval.mono_measure (Measure.restrict_mono hsub le_rfl),
      fun j ↦ (htrace j).mono_measure (Measure.restrict_mono hsub le_rfl)⟩
    rintro _ ⟨s, hs, rfl⟩
    apply hball
    apply lt_of_le_of_lt (dist_le_localRadius _ _)
    rw [localRadius_quarterEndpointRay, abs_of_nonneg hs.1]
    exact hs.2.trans_lt ((min_le_right r (ε / 2)).trans_lt (by linarith))
  choose r hr hr1 hray hval htrace using hlocal
  let ρ := Finset.univ.inf' Finset.univ_nonempty r
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    rw [Finset.lt_inf'_iff]
    exact fun i _ ↦ hr i
  have hρr (i : Fin 4 × Bool) : ρ ≤ r i := Finset.inf'_le _ (Finset.mem_univ i)
  have hρ1 : ρ < 1 := (hρr (0, false)).trans_lt (hr1 (0, false))
  refine ⟨U, hU, hsep, fun j ↦ (hgrad j).mono inter_subset_left,
    fun w hw ↦ (hbulk w hw).mono inter_subset_left, ρ, hρ, hρ1, fun k side ↦ ?_⟩
  have hsub : Ioo 0 ρ ⊆ Ioo 0 (r (k, side)) := Ioo_subset_Ioo_right (hρr (k, side))
  refine ⟨(image_mono (Icc_subset_Icc le_rfl (hρr (k, side)))).trans (hray (k, side)),
    (hval (k, side)).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun j ↦ interiorChartTrace (rotatedQuarterEndpointChart k side) (streamJet2 ω [j]),
    fun j ↦ ⟨(hJ j).quarterRayTrace ρ k side,
      (htrace (k, side) j).mono_measure (Measure.restrict_mono hsub le_rfl)⟩⟩

/-- Logarithmic numerator estimates with the same canonical jet and compatible
unweighted derivative/trace data (`lem:dd-log-numerators`). -/
theorem dd_log_numerators {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (_hκ : InRotationCharacter κ ω) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧
      ∃ d : WeightedQuarterNumeratorData lam cellNeighbourhood (contStream ω) (streamJet2 ω) h₀,
        IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 (3 / 2) (streamJet2 ω) h)
          (Ioo 0 h₀) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.first h) 2
          (volume.restrict (Ioo 0 h₀)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.halfFirst h) 2
          (volume.restrict (Ioo 0 h₀)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * (h : ℂ) * d.second h) 2
          (volume.restrict (Ioo 0 h₀)) := by
  clear _hκ
  have hp := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hf := dd_weighted_forcing hlam hω hs
  have hcell : cellSquare ⊆ cellNeighbourhood :=
    subset_closure.trans closure_cellSquare_subset_cellNeighbourhood
  obtain ⟨a, ha, hahalf, ⟨d₀⟩⟩ := weighted_numerator_estimates hp isBounded_cellNeighbourhood
    closure_cellSquare_subset_cellNeighbourhood (continuous_contStream ω).continuousOn
    (Filter.Eventually.of_forall fun _ ↦ rfl) (streamJet2_weak ω cellNeighbourhood)
    (hf.1.mono_measure (Measure.restrict_mono hcell le_rfl))
    (fun j ↦ (hf.2.1 j).mono_measure (Measure.restrict_mono hcell le_rfl))
  obtain ⟨U, hU, hsep, hgrad, hbulk, ρ, hρ, _, hrays⟩ := dd_log_forcing hlam hω hs
  obtain ⟨ε, hε, V, hV, hVc, hVU, hcollar⟩ := exists_compact_cell_collar hU hsep
  let r₀ := min d₀.radius ρ
  have hr₀ : 0 < r₀ := lt_min d₀.radius_pos hρ
  let b := min a (min (ε / 2) ((r₀ / 8) ^ 2))
  have hb : 0 < b := lt_min ha (lt_min (half_pos hε) (sq_pos_of_pos (by positivity)))
  have hba : b ≤ a := min_le_left _ _
  have hbε : b ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbr : b ≤ (r₀ / 8) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbhalf : b < 1 / 2 := hba.trans_lt hahalf
  have hb1 : b < 1 := by linarith
  have hsq : Real.sqrt b ≤ r₀ / 8 := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b]
  have hRb : quarterEndpointRadius b < r₀ :=
    (quarterEndpointRadius_le_four_sqrt hb hb1).trans_lt (by linarith)
  let d := d₀.restrict hba
  have hsub : cellSeparatrixStrip (2 * b) ⊆ V := by
    intro p hp
    apply hcollar
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le (by linarith)⟩
  have hK := integrable_log_quarterJetEnergy hb1.le hV.measurableSet hsub
    (D := streamJet2 ω) (k := 1) (s := 3 / 2) (fun w ↦ by
      simpa only [MemSobolevOn, MemSobolevOnWith, List.ofFn_succ, List.ofFn_zero]
        using hgrad (w 0) V hV hVc hVU)
  have hK₁ := integrable_log_quarterJetEnergy hb1.le hV.measurableSet hsub
    (D := streamJet2 ω) (k := 1) (s := 0) (fun w ↦ by
      simpa only [MemSobolevOn, MemSobolevOnWith, Real.rpow_eq_pow, Real.rpow_zero,
        Complex.ofReal_one, div_one] using
        hbulk (List.ofFn w) (Or.inl (by simp)) V hV hVc hVU)
  have hK₂ := integrable_log_quarterJetEnergy hb1.le hV.measurableSet hsub
    (D := streamJet2 ω) (k := 2) (s := 0) (fun w ↦ by
      simpa only [MemSobolevOn, MemSobolevOnWith, Real.rpow_eq_pow, Real.rpow_zero,
        Complex.ofReal_one, div_one] using
        hbulk (List.ofFn w) (Or.inr (by simp)) V hV hVc hVU)
  choose T hT using fun side ↦ (hrays (0 : Fin 4) side).2.2
  have htrace (side : Bool) (j : Fin 2) :
      d.gradientTrace side j =ᵐ[volume.restrict (Ioo 0 r₀)] T side j := by
    apply (d.ray_trace side j).ae_eq isOrbitUnion_cellNeighbourhood.1 hU (hT side j).1
      (min_le_left _ _) (min_le_right _ _)
    rintro _ ⟨r, hr, rfl⟩
    have hrr : r < ρ := hr.2.trans_le (min_le_right _ _)
    have hr1 : r < 1 := (hr.2.trans_le (min_le_left _ _)).trans d₀.radius_lt
    refine ⟨?_, (hrays (0 : Fin 4) side).1 ⟨r, ⟨hr.1.le, hrr.le⟩, rfl⟩⟩
    cases side <;> dsimp [rotatedQuarterEndpointRay, quarterEndpointRay,
      cellNeighbourhood, diagCoord] <;> constructor <;> rw [abs_lt] <;>
      constructor <;> linarith only [hr.1, hr1, Real.pi_gt_three]
  have htraceLp (side : Bool) (j : Fin 2) : MemLp (fun r ↦
      (Real.sqrt (logRadiusWeight r) : ℂ) * d.gradientTrace side j r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 r₀)) := by
    have hl := (hT side j).2.mono_measure (Measure.restrict_mono
      (Ioo_subset_Ioo_right (min_le_right d₀.radius ρ)) le_rfl)
    apply hl.ae_eq
    filter_upwards [htrace side j] with r hr
    rw [hr]
  have hval (side : Bool) := integrable_log_endpoint_value hb1
    (hRb.trans_le (min_le_right _ _)) (d.endpoint_value_lp side)
    ((hrays (0 : Fin 4) side).2.1)
  have hgradient (side : Bool) (j : Fin 2) := integrable_log_endpoint_gradient hb1 hRb
    (d.endpoint_gradient_lp side j) (htraceLp side j)
  have hvalSum : IntegrableOn (fun h ↦ logLevelWeight h *
      quarterEndpointValueEnergy (contStream ω) h) (Ioo 0 b) := by
    unfold quarterEndpointValueEnergy
    simp_rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    exact integrable_finsetSum Finset.univ (fun side _ ↦ hval side)
  have hgradSum : IntegrableOn (fun h ↦ logLevelWeight h *
      quarterEndpointGradientEnergy d.gradientTrace h) (Ioo 0 b) := by
    unfold quarterEndpointGradientEnergy
    simp_rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    exact integrable_finsetSum Finset.univ (fun side _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hgradient side j))
  obtain ⟨hfirst, hhalf, hsecond⟩ := d.log_estimates hb1.le hK hK₁ hK₂ hvalSum hgradSum
  exact ⟨b, hb, hbhalf, d, hK, hfirst, hhalf, hsecond⟩

end EulerDipoleEigenvalues
