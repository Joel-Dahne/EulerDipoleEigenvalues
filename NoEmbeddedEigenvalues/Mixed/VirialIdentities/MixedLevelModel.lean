import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedEdgeDefect
import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.LevelTraces

/-! # The paired corner model on exact regular levels -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real
open scoped Topology

local notation "c" => (π / 2)

/-- The open tangential parameter interval of one quarter of a regular level. -/
def mixedLevelInterval (s : ℝ) : Set ℝ := Ioo (-arccos (√s)) (arccos (√s))

/-- The level frame's signed normal-minus-tangential coefficient for a
gradient in the first diagonal direction, with its sign reversed. -/
def mixedLevelModelWeight (s a : ℝ) : ℝ :=
  let b := quarterHeight s a
  let R := cos a * sin b
  let S := cos b * sin a
  ((R ^ 2 - S ^ 2) / (R ^ 2 + S ^ 2)) * (1 / √(cos a ^ 2 - s ^ 2))

/-- Reflection in the diagonal interchanges the two components of the
level normal, negating the coefficient of the squared model gradient. -/
theorem mixed_level_frame_swap (q : ℝ × ℝ) :
    ((cos q.swap.1 * sin q.swap.2) ^ 2 - (cos q.swap.2 * sin q.swap.1) ^ 2) /
        ((cos q.swap.1 * sin q.swap.2) ^ 2 + (cos q.swap.2 * sin q.swap.1) ^ 2) =
      -(((cos q.1 * sin q.2) ^ 2 - (cos q.2 * sin q.1) ^ 2) /
        ((cos q.1 * sin q.2) ^ 2 + (cos q.2 * sin q.1) ^ 2)) := by
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← neg_div, neg_sub]
  congr 1
  ring

/-- A common level-weight bound, valid on the entire quarter for
`0 < s < 1/2`, without distinguishing the near-axis and corner regions. -/
theorem mixed_quarter_weight_bound {s a : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2))
    (ha : a ∈ mixedLevelInterval s) :
    0 < √(cos a ^ 2 - s ^ 2) ∧ 1 / √(cos a ^ 2 - s ^ 2) ≤ 2 / cos a := by
  have hb := sqrt_lt_cos_of_abs_lt_arccos ⟨hs.1, by linarith [hs.2]⟩
    (abs_lt.mpr ⟨ha.1, ha.2⟩)
  have hc := (sqrt_pos.2 hs.1).trans hb
  have he : s ≤ cos a ^ 2 := by nlinarith [sq_sqrt hs.1.le, sqrt_nonneg s]
  have hf : s ^ 2 ≤ cos a ^ 2 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hs.2.le hs.1.le, he]
  have hr : (cos a / 2) ^ 2 ≤ cos a ^ 2 - s ^ 2 := by nlinarith only [hf, sq_nonneg (cos a)]
  have hh : cos a / 2 ≤ √(cos a ^ 2 - s ^ 2) := by
    simpa only [sqrt_sq (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2))] using sqrt_le_sqrt hr
  refine ⟨(half_pos hc).trans_le hh, ?_⟩
  calc
    _ ≤ 1 / (cos a / 2) := one_div_le_one_div_of_le (half_pos hc) hh
    _ = _ := by ring

/-- The depth of the quarter graph below its edge is bounded by a
constant times the tangential cosine. This pays for the singular time
weight when comparing a section with its canonical trace. -/
theorem mixed_quarter_height_defect_bound {s a : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ mixedLevelInterval s) :
    0 ≤ c - quarterHeight s a ∧ c - quarterHeight s a ≤ c * cos a := by
  have hb := sqrt_lt_cos_of_abs_lt_arccos hs (abs_lt.mpr ⟨ha.1, ha.2⟩)
  have hp := (sqrt_pos.2 hs.1).trans hb
  have hsq : s ≤ cos a ^ 2 := by nlinarith [sq_sqrt hs.1.le, sqrt_nonneg s]
  have hsc : s ≤ cos a := hsq.trans (by nlinarith [cos_le_one a, hp.le])
  obtain ⟨hl, hu⟩ := pi_div_two_sub_quarterHeight_le hs.1.le hp hsc
  exact ⟨hl, hu.trans (mul_le_mul_of_nonneg_left
    ((div_le_iff₀ hp).2 (by simpa only [pow_two] using hsq)) (half_pos pi_pos).le)⟩

/-- The exact level weight, with the paired signs, converges against the
boundary mass defect. Here the common leading mass has already been
combined, so only its integrable defect is multiplied by the singular weight. -/
theorem mixed_level_model_trace_limit {ω : L2} (d : MixedQuotientData ω) :
    Tendsto (fun s ↦ ∫ a in mixedLevelInterval s,
      mixedLevelModelWeight s a * mixedEdgeMassDefect d.phi a)
      (𝓝[>] 0)
      (𝓝 (∫ a in Ioo (-c) c, mixedEdgeMassDefect d.phi a / cos a)) := by
  let I := Ioo (-c) c
  let μ := volume.restrict I
  let f := fun a ↦ mixedEdgeMassDefect d.phi a / cos a
  let F := fun s ↦ (mixedLevelInterval s).indicator
    (fun a ↦ mixedLevelModelWeight s a * mixedEdgeMassDefect d.phi a)
  have hi : Integrable f μ := mixed_edge_mass_defect_integrable d
  have hdom : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hcos (a : ℝ) (ha : a ∈ I) : 0 < cos a := cos_pos_of_mem_Ioo ha
  have hsub {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) : mixedLevelInterval s ⊆ I := by
    have h := arccos_lt_pi_div_two.2 (sqrt_pos.2 hs.1)
    exact Ioo_subset_Ioo (neg_le_neg h.le) h.le
  have hsM (s : ℝ) : MeasurableSet (mixedLevelInterval s) := measurableSet_Ioo
  have hD : AEStronglyMeasurable (mixedEdgeMassDefect d.phi) μ := by
    apply (hi.aestronglyMeasurable.mul ((continuous_cos.aestronglyMeasurable
      (μ := μ)))).congr
    filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a ha
    change (mixedEdgeMassDefect d.phi a / cos a) * cos a = _
    exact div_mul_cancel₀ _ (hcos a ha).ne'
  have hsC (s : ℝ) : Measurable (mixedLevelModelWeight s) := by
    unfold mixedLevelModelWeight quarterHeight
    dsimp
    fun_prop
  have ht : Tendsto (fun s ↦ ∫ a, F s a ∂μ) (𝓝[>] 0) (𝓝 (∫ a, f a ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ 2 * ‖f a‖)
    · exact .of_forall fun s ↦ ((hsC s).aestronglyMeasurable.mul hD).indicator (hsM s)
    · filter_upwards [hdom] with s hs
      filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a ha
      by_cases h : a ∈ mixedLevelInterval s
      · have hfrac (R S : ℝ) : ‖(R ^ 2 - S ^ 2) / (R ^ 2 + S ^ 2)‖ ≤ 1 := by
          by_cases hz : R ^ 2 + S ^ 2 = 0
          · simp [hz]
          have hp : 0 < R ^ 2 + S ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_one hp, abs_le]
          constructor <;> linarith [sq_nonneg R, sq_nonneg S]
        have hw := mixed_quarter_weight_bound hs h
        dsimp only [F]
        rw [indicator_of_mem h, norm_mul, show f a = mixedEdgeMassDefect d.phi a / cos a from rfl,
          norm_div, Real.norm_of_nonneg (hcos a ha).le]
        unfold mixedLevelModelWeight
        rw [norm_mul]
        have hW := mul_le_mul (hfrac (cos a * sin (quarterHeight s a))
          (cos (quarterHeight s a) * sin a)) hw.2 (by positivity) (by norm_num)
        rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / √(cos a ^ 2 - s ^ 2))] at ⊢
        calc
          _ ≤ (1 * (2 / cos a)) * ‖mixedEdgeMassDefect d.phi a‖ :=
            mul_le_mul_of_nonneg_right hW (norm_nonneg _)
          _ = _ := by ring
      · dsimp only [F]
        rw [indicator_of_notMem h, norm_zero]
        positivity
    · exact hi.norm.const_mul 2
    · filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a ha
      have ha' : |a| < c := abs_lt.mpr ⟨ha.1, ha.2⟩
      have H : ContinuousAt (fun s : ℝ ↦ arccos (√s)) 0 :=
        (continuous_arccos.comp continuous_sqrt).continuousAt
      have HH : ∀ᶠ s : ℝ in 𝓝[>] 0, a ∈ mixedLevelInterval s := by
        have h := H.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        have hh : Tendsto (fun s : ℝ ↦ arccos (√s)) (𝓝[>] 0) (𝓝 c) := by
          simpa only [sqrt_zero, arccos_zero] using h
        filter_upwards [hh.eventually (lt_mem_nhds ha')] with s hs
        exact abs_lt.mp hs
      have hc := hcos a ha
      have h : ContinuousAt (fun s ↦ mixedLevelModelWeight s a * mixedEdgeMassDefect d.phi a)
          0 := by
        unfold mixedLevelModelWeight quarterHeight
        dsimp
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.mul
        · apply ContinuousAt.div (by fun_prop) (by fun_prop)
          simp [hc.ne']
        · apply ContinuousAt.div continuousAt_const (by fun_prop)
          simp [sqrt_sq hc.le, hc.ne']
      have h0 : mixedLevelModelWeight 0 a * mixedEdgeMassDefect d.phi a = f a := by
        simp only [mixedLevelModelWeight, quarterHeight, zero_div, arccos_zero,
          sin_pi_div_two, cos_pi_div_two, mul_one, zero_mul, zero_pow (by decide : 2 ≠ 0),
          sub_zero, add_zero, div_self (pow_ne_zero _ hc.ne'), one_mul, sqrt_sq hc.le, f]
        ring
      rw [← h0]
      apply (h.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [HH] with s hs
      exact (indicator_of_mem hs
        (fun a ↦ mixedLevelModelWeight s a * mixedEdgeMassDefect d.phi a)).symm
  apply ht.congr'
  filter_upwards [hdom] with s hs
  dsimp only [F]
  rw [integral_indicator (hsM s), Measure.restrict_restrict (hsM s),
    inter_eq_left.2 (hsub hs)]

end NoEmbeddedEigenvalues
