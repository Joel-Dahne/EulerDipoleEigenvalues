import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedLevelModel
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceWeakGluing

/-!
# Sobolev traces on the moving quarter graphs

An interval H¹ estimate supplies a single square-integrable envelope for
all normal positions. For a field with a second normal derivative, the
same estimate applied to its first normal derivative controls the
increment divided by the tangential cosine.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real
open scoped Topology Interval

local notation "c" => (π / 2)
local notation "Jside" => (Ioo (-c) c)
local notation "νside" => (volume.restrict Jside)
local notation "Plane" => (ℝ × ℝ)

private theorem mixed_interval_ne : -c < c := by linarith [pi_pos]

theorem mixed_quarter_graph_mem {s a : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ mixedLevelInterval s) :
    (a, quarterHeight s a) ∈ Jside ×ˢ Jside ∧ 0 < cos (quarterHeight s a) ∧
      cos (quarterHeight s a) ≤ cos a := by
  have hc := sqrt_lt_cos_of_abs_lt_arccos hs (abs_lt.mpr ⟨ha.1, ha.2⟩)
  have hp := (sqrt_pos.2 hs.1).trans hc
  have hsq : s ≤ cos a ^ 2 := by nlinarith [sq_sqrt hs.1.le, sqrt_nonneg s]
  have hsc : s < cos a := by
    have ht := (sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by simpa using hs.2)
    have hss : s ≤ √s := by
      simpa only [mul_one, ← pow_two, sq_sqrt hs.1.le] using
        mul_le_mul_of_nonneg_left ht.le (sqrt_nonneg s)
    exact hss.trans_lt hc
  have harc := arccos_lt_pi_div_two.2 (sqrt_pos.2 hs.1)
  have ha' : a ∈ Jside := ⟨by linarith [ha.1], ha.2.trans harc⟩
  have hq : s / cos a ∈ Ioo 0 1 := ⟨div_pos hs.1 hp, (div_lt_one hp).2 hsc⟩
  have hb0 : 0 ≤ quarterHeight s a := arccos_nonneg _
  refine ⟨⟨ha', ⟨(neg_lt_zero.mpr (half_pos pi_pos)).trans_le hb0,
    arccos_lt_pi_div_two.2 hq.1⟩⟩, ?_⟩
  rw [quarterHeight, cos_arccos (by linarith [hq.1]) hq.2.le]
  exact ⟨hq.1, (div_le_iff₀ hp).2 (by simpa only [pow_two] using hsq)⟩

/-- Almost-everywhere identities in the open square restrict to almost
every quarter graph. The exceptional set is in the level variable. -/
theorem ae_mixed_quarterGraph_of_ae {P : Plane → Prop}
    (hP : ∀ᵐ q ∂volume.restrict (Jside ×ˢ Jside), P q) :
    ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      ∀ᵐ a ∂volume.restrict (mixedLevelInterval s), P (a, quarterHeight s a) := by
  have h := (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).1 hP
  have hMap : ∀ᵐ p ∂Measure.map diagInv volume,
      diagInv.symm p ∈ Jside ×ˢ Jside → P (diagInv.symm p) :=
    diagInv.toHomeomorph.measurableEmbedding.ae_map_iff.2 (by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph, diagInv.symm_apply_apply] using h)
  rw [map_diagInv_volume, Measure.ae_ennreal_smul_measure_iff
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0)] at hMap
  filter_upwards [ae_quarterGraph_of_ae hMap] with s hs hs'
  filter_upwards [hs hs', ae_restrict_mem (s := mixedLevelInterval s) measurableSet_Ioo]
    with a h a_mem
  simpa only [diagInv.symm_apply_apply] using h (by
    rw [diagInv.symm_apply_apply]
    exact (mixed_quarter_graph_mem hs' a_mem).1)

/-- An L² function on the tangential interval bounds each entire closed
normal H¹ section, uniformly in its evaluation point. -/
theorem HasACLSectionsOn.exists_l2_section_envelope {F D : Plane → ℂ}
    (hF : HasACLSectionsOn Jside Jside F D)
    (hFL : MemLp F 2 (volume.restrict (Jside ×ˢ Jside)))
    (hDL : MemLp D 2 (volume.restrict (Jside ×ˢ Jside))) :
    ∃ M : ℝ → ℝ, MemLp M 2 νside ∧
      ∀ᵐ a ∂νside, ∀ b ∈ Icc (-c) c, ‖aclTrace (-c) c F D b a‖ ≤ M a := by
  let S (Z : Plane → ℂ) (a : ℝ) := ∫ b in Jside, ‖Z (a, b)‖ ^ 2
  have hi (Z : Plane → ℂ) (hZ : MemLp Z 2 (volume.restrict (Jside ×ˢ Jside))) :
      Integrable (S Z) νside := by
    have hZ' : MemLp Z 2 (Measure.prod νside νside) := by
      simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hZ
    exact hZ'.norm.integrable_sq.integral_prod_left
  let B : ℝ → ℝ := fun a ↦ (2 / (c - (-c))) * S F a + 2 * (c - (-c)) * S D a
  have hB : Integrable B νside := (hi F hFL |>.const_mul _).add (hi D hDL |>.const_mul _)
  have hB0 (a : ℝ) : 0 ≤ B a := by
    have hSF : 0 ≤ S F a := integral_nonneg fun b ↦ sq_nonneg _
    have hSD : 0 ≤ S D a := integral_nonneg fun b ↦ sq_nonneg _
    have hπ : 0 < c - (-c) := sub_pos.mpr mixed_interval_ne
    dsimp only [B]
    positivity
  let M := fun a ↦ √(B a)
  have hM : AEStronglyMeasurable M νside := continuous_sqrt.comp_aestronglyMeasurable
    hB.aestronglyMeasurable
  refine ⟨M, (memLp_two_iff_integrable_sq_norm hM).2 ?_, ?_⟩
  · refine hB.congr (Eventually.of_forall fun a ↦ ?_)
    simp only [M, Real.norm_of_nonneg (sqrt_nonneg _), sq_sqrt (hB0 a)]
  · filter_upwards [hF.ae_hasIntervalH1 hFL hDL] with a ha
    intro b hb
    calc
      _ = √(‖aclTrace (-c) c F D b a‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
      _ ≤ M a := sqrt_le_sqrt (ha.extension_sq_le mixed_interval_ne hb)

/-- A Neumann or Dirichlet quotient section differs from its value trace by
at most the normal distance times an L² envelope. This bound uses H¹ of the
normal derivative, not any pointwise gradient at a corner. -/
theorem HasACLSectionsOn.exists_l2_section_increment {F D G E : Plane → ℂ}
    (hF : HasACLSectionsOn Jside Jside F D) (hG : HasACLSectionsOn Jside Jside G E)
    (hFG : D =ᵐ[volume.restrict (Jside ×ˢ Jside)] G)
    (hFL : MemLp F 2 (volume.restrict (Jside ×ˢ Jside)))
    (hGL : MemLp G 2 (volume.restrict (Jside ×ˢ Jside)))
    (hEL : MemLp E 2 (volume.restrict (Jside ×ˢ Jside))) :
    ∃ M : ℝ → ℝ, MemLp M 2 νside ∧
      ∀ᵐ a ∂νside, ∀ b ∈ Jside, ‖F (a, b) - aclTrace (-c) c F D c a‖ ≤ (c - b) * M a := by
  obtain ⟨M, hML, hM⟩ := hG.exists_l2_section_envelope hGL hEL
  have hDL := hGL.ae_eq hFG.symm
  have hFGp : D =ᵐ[Measure.prod νside νside] G := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hFG
  refine ⟨M, hML, ?_⟩
  filter_upwards [hM, hF.ae_hasIntervalH1 hFL hDL, hG.ae_hasIntervalH1 hGL hEL,
    Measure.ae_ae_of_ae_prod hFGp] with a ha hFa hGa hea
  intro b hb
  have hc : c ∈ Icc (-c) c := right_mem_Icc.mpr mixed_interval_ne.le
  have hFTC := hFa.integral_eq_extension_sub mixed_interval_ne (Ioo_subset_Icc_self hb) hc
  rw [hFa.extension_eq mixed_interval_ne hb] at hFTC
  have hh : ∀ᵐ r ∂volume, r ∈ Ι b c → ‖D (a, r)‖ ≤ M a := by
    have h := (ae_restrict_iff' measurableSet_Ioo).1 hea
    have hne : ∀ᵐ r ∂volume, r ∉ ({c} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton c)
    filter_upwards [h, hne] with r hr hrc hm
    rw [uIoc_of_le hb.2.le] at hm
    have hrI : r ∈ Jside := ⟨hb.1.trans hm.1, lt_of_le_of_ne hm.2 hrc⟩
    rw [hr hrI]
    simpa only [aclTrace, hGa.extension_eq mixed_interval_ne hrI] using
      ha r (Ioo_subset_Icc_self hrI)
  rw [norm_sub_rev, ← show (∫ x in b..c, D (a, x)) =
    aclTrace (-c) c F D c a - F (a, b) from hFTC]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb.2.le), mul_comm (M a)] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hh

theorem eventually_mem_mixedLevelInterval {a : ℝ} (ha : a ∈ Jside) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, a ∈ mixedLevelInterval s := by
  have hc : |a| < c := abs_lt.2 ⟨ha.1, ha.2⟩
  have hh : ContinuousAt (fun s : ℝ ↦ arccos (√s)) 0 :=
    (continuous_arccos.comp continuous_sqrt).continuousAt
  have ht : Tendsto (fun s : ℝ ↦ arccos (√s)) (𝓝[>] 0) (𝓝 c) := by
    simpa only [sqrt_zero, arccos_zero] using hh.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  filter_upwards [ht.eventually (lt_mem_nhds hc)] with s hs
  exact abs_lt.mp hs

/-- Quarter graphs converge to the upper edge through the open square
at each fixed tangential coordinate. -/
theorem mixed_quarter_height_tendsto {a : ℝ} (ha : a ∈ Jside) :
    Tendsto (fun s : ℝ ↦ quarterHeight s a) (𝓝[>] 0) (𝓝[Jside] c) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : ContinuousAt (fun s : ℝ ↦ quarterHeight s a) 0 :=
      (continuous_arccos.comp (continuous_id.div_const (cos a))).continuousAt
    simpa only [quarterHeight, zero_div, arccos_zero] using h.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [eventually_mem_mixedLevelInterval ha, (Ioo_mem_nhdsGT zero_lt_one :
      Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with s hs hs'
    exact (mixed_quarter_graph_mem hs' hs).1.2

/-- Put quarter integrals on the fixed tangential interval. Tail bounds are
supplied by the application, so this also works for signed currents. -/
theorem mixed_quarter_dominated_limit {F : ℝ → ℝ → ℝ} {T B : ℝ → ℝ}
    (hFm : ∀ᶠ s in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F s) νside)
    (hB : Integrable B νside)
    (hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ∀ᵐ a ∂νside, a ∈ mixedLevelInterval s → ‖F s a‖ ≤ B a)
    (hpos : 0 ≤ᵐ[νside] B)
    (hlim : ∀ᵐ a ∂νside, Tendsto (fun s ↦ F s a) (𝓝[>] 0) (𝓝 (T a))) :
    Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, F s a) (𝓝[>] 0)
      (𝓝 (∫ a in Jside, T a)) := by
  let W := fun s ↦ (mixedLevelInterval s).indicator (F s)
  have hm (s : ℝ) : MeasurableSet (mixedLevelInterval s) := measurableSet_Ioo
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := νside) (F := W) (f := T) B
    (hFm.mono fun s h ↦ h.indicator (hm s))
    (by
      filter_upwards [hbound] with s hs
      filter_upwards [hs, hpos] with a ha hp
      by_cases h : a ∈ mixedLevelInterval s
      · simpa only [W, indicator_of_mem h] using ha h
      · simpa only [W, indicator_of_notMem h, norm_zero, Pi.zero_apply] using hp)
    hB (by
      filter_upwards [hlim, ae_restrict_mem measurableSet_Ioo] with a ha ha'
      apply ha.congr'
      filter_upwards [eventually_mem_mixedLevelInterval ha'] with s hs
      exact (indicator_of_mem hs (F s)).symm)
  apply hh.congr'
  filter_upwards [(Ioo_mem_nhdsGT zero_lt_one : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with s hs
  have hsub : mixedLevelInterval s ⊆ Jside := fun _ ha ↦ (mixed_quarter_graph_mem hs ha).1.1
  dsimp only [W]
  rw [integral_indicator (hm s), Measure.restrict_restrict (hm s), inter_eq_left.2 hsub]

/-- The signed-model coefficient is uniformly bounded by one, including
at the center where its totalized value is zero. -/
theorem mixed_level_frame_norm_le (R S : ℝ) :
    ‖(R ^ 2 - S ^ 2) / (R ^ 2 + S ^ 2)‖ ≤ 1 := by
  by_cases hz : R ^ 2 + S ^ 2 = 0
  · simp [hz]
  have hp : 0 < R ^ 2 + S ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_one hp, abs_le]
  constructor <;> linarith [sq_nonneg R, sq_nonneg S]

/-- The singular leading energy can be evaluated using the boundary
value of the quotient rather than the moving graph value. For domination
the normal increment supplies one factor of the tangential cosine. At
fixed tangential coordinate the increment vanishes as the level shrinks. -/
theorem mixed_quarter_mass_replacement {F D G E : Plane → ℂ}
    (hF : HasACLSectionsOn Jside Jside F D) (hG : HasACLSectionsOn Jside Jside G E)
    (hFG : D =ᵐ[volume.restrict (Jside ×ˢ Jside)] G)
    (hFm : Measurable F)
    (hFL : MemLp F 2 (volume.restrict (Jside ×ˢ Jside)))
    (hGL : MemLp G 2 (volume.restrict (Jside ×ˢ Jside)))
    (hEL : MemLp E 2 (volume.restrict (Jside ×ˢ Jside))) :
    Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, mixedLevelModelWeight s a *
      (‖F (a, quarterHeight s a)‖ ^ 2 - ‖aclTrace (-c) c F D c a‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have hDL := hGL.ae_eq hFG.symm
  obtain ⟨M, hML, hM⟩ := hF.exists_l2_section_envelope hFL hDL
  obtain ⟨V, hVL, hV⟩ := hF.exists_l2_section_increment hG hFG hFL hGL hEL
  let T := aclTrace (-c) c F D c
  have hc : c ∈ Icc (-c) c := right_mem_Icc.mpr mixed_interval_ne.le
  have hTm := aestronglyMeasurable_aclTrace (I := Jside) mixed_interval_ne hc hFm hDL
  let W := fun s a ↦ mixedLevelModelWeight s a *
    (‖F (a, quarterHeight s a)‖ ^ 2 - ‖T a‖ ^ 2)
  let B := fun a ↦ (4 * c) * (‖M a‖ * ‖V a‖)
  have hB : Integrable B νside := (hML.norm.integrable_mul hVL.norm).const_mul _
  have hpos : 0 ≤ᵐ[νside] B := Eventually.of_forall fun _ ↦ by
    dsimp only [B]
    positivity
  have hsmall : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT (by norm_num)
  have hin (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hWm (s : ℝ) : AEStronglyMeasurable (W s) νside := by
    have hw : Measurable (mixedLevelModelWeight s) := by
      unfold mixedLevelModelWeight quarterHeight
      dsimp
      fun_prop
    have hf : Measurable (fun a ↦ F (a, quarterHeight s a)) := hFm.comp (by
      unfold quarterHeight
      fun_prop)
    exact hw.aestronglyMeasurable.mul ((hf.aestronglyMeasurable.norm.pow 2).sub (hTm.norm.pow 2))
  have hdom : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ∀ᵐ a ∂νside, a ∈ mixedLevelInterval s → ‖W s a‖ ≤ B a := by
    filter_upwards [hsmall] with s hs
    filter_upwards [hM, hV, hF.ae_hasIntervalH1 hFL hDL] with a hma hva hFa
    intro ha
    let b := quarterHeight s a
    have hmem := (mixed_quarter_graph_mem (hin s hs) ha).1
    have hb : b ∈ Jside := hmem.2
    have hA : ‖F (a, b)‖ ≤ ‖M a‖ := le_trans (by
      simpa only [aclTrace, hFa.extension_eq mixed_interval_ne hb] using
        hma b (Ioo_subset_Icc_self hb)) (le_abs_self _)
    have hT : ‖T a‖ ≤ ‖M a‖ := (hma c hc).trans (le_abs_self _)
    have hcos : 0 < cos a := cos_pos_of_mem_Ioo hmem.1
    have hz := mixed_quarter_weight_bound hs ha
    have hw : ‖mixedLevelModelWeight s a‖ ≤ 2 / cos a := by
      unfold mixedLevelModelWeight
      dsimp only
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / √(cos a ^ 2 - s ^ 2))]
      exact (mul_le_mul_of_nonneg_right (mixed_level_frame_norm_le _ _) (by positivity)).trans
        (by rw [one_mul]; exact hz.2)
    have hΔ : ‖F (a, b) - T a‖ ≤ c * cos a * ‖V a‖ :=
      (hva b hb).trans (mul_le_mul (mixed_quarter_height_defect_bound (hin s hs) ha).2
        (le_abs_self _) (by
          have ht := hva b hb
          exact nonneg_of_mul_nonneg_right ((norm_nonneg _).trans ht) (sub_pos.mpr hb.2))
        (mul_nonneg (half_pos pi_pos).le hcos.le))
    have hsq : ‖‖F (a, b)‖ ^ 2 - ‖T a‖ ^ 2‖ ≤
        (c * cos a * ‖V a‖) * (2 * ‖M a‖) := by
      rw [show ‖F (a, b)‖ ^ 2 - ‖T a‖ ^ 2 =
        (‖F (a, b)‖ - ‖T a‖) * (‖F (a, b)‖ + ‖T a‖) by ring, norm_mul,
        Real.norm_of_nonneg (by positivity : 0 ≤ ‖F (a, b)‖ + ‖T a‖)]
      exact mul_le_mul ((abs_norm_sub_norm_le _ _).trans hΔ) (by linarith)
        (by positivity) (by positivity)
    change ‖mixedLevelModelWeight s a * _‖ ≤ B a
    rw [norm_mul]
    calc
      _ ≤ (2 / cos a) * ((c * cos a * ‖V a‖) * (2 * ‖M a‖)) :=
        mul_le_mul hw hsq (norm_nonneg _) (by positivity)
      _ = B a := by dsimp only [B]; field_simp; ring
  have hlim : ∀ᵐ a ∂νside, Tendsto (fun s ↦ W s a) (𝓝[>] 0) (𝓝 ((0 : ℝ → ℝ) a)) := by
    filter_upwards [hF.ae_tendsto_trace mixed_interval_ne hFL hDL,
      ae_restrict_mem measurableSet_Ioo] with a ha ha'
    have ht := (ha c hc).comp (mixed_quarter_height_tendsto ha')
    have hw : ContinuousAt (fun s ↦ mixedLevelModelWeight s a) 0 := by
      have hcos := cos_pos_of_mem_Ioo ha'
      unfold mixedLevelModelWeight quarterHeight
      dsimp only
      apply ContinuousAt.mul
      · apply ContinuousAt.div (by fun_prop) (by fun_prop)
        simp [hcos.ne']
      · apply ContinuousAt.div continuousAt_const (by fun_prop)
        simp [sqrt_sq hcos.le, hcos.ne']
    have he := (hw.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).mul
      ((ht.norm.pow 2).sub_const (‖T a‖ ^ 2))
    simpa only [W, Function.comp_apply, ← show T a = aclTrace (-c) c F D c a from rfl,
      sub_self, mul_zero, Pi.zero_apply] using he
  simpa only [Pi.zero_apply, integral_zero] using
    mixed_quarter_dominated_limit (.of_forall hWm) hB hdom hpos hlim

/-- Once the singular time weight is absorbed by a cosine, every
quadratic remainder on the graph is controlled by a product of two
L² section envelopes. No regularity in the level parameter is needed
for the coefficient, only a uniform bound and a pointwise limit. -/
theorem mixed_quarter_pair_limit_of_graph {F D G E : Plane → ℂ} {K : ℝ → ℝ → ℝ}
    {k : ℝ → ℝ} {C t : ℝ} {b : ℝ → ℝ → ℝ}
    (ht : t ∈ Icc (-c) c) (hbm : ∀ s, Measurable (b s))
    (hbmem : ∀ᶠ s in 𝓝[>] 0, ∀ a ∈ mixedLevelInterval s, b s a ∈ Jside)
    (hbt : ∀ a ∈ Jside, Tendsto (fun s ↦ b s a) (𝓝[>] 0) (𝓝[Jside] t))
    (hF : HasACLSectionsOn Jside Jside F D) (hG : HasACLSectionsOn Jside Jside G E)
    (hFm : Measurable F) (hGm : Measurable G)
    (hFL : MemLp F 2 (volume.restrict (Jside ×ˢ Jside)))
    (hDL : MemLp D 2 (volume.restrict (Jside ×ˢ Jside)))
    (hGL : MemLp G 2 (volume.restrict (Jside ×ˢ Jside)))
    (hEL : MemLp E 2 (volume.restrict (Jside ×ˢ Jside)))
    (hKm : ∀ᶠ s in 𝓝[>] 0, AEStronglyMeasurable (K s) νside)
    (hK : ∀ᶠ s in 𝓝[>] 0, ∀ a ∈ mixedLevelInterval s, ‖K s a‖ ≤ C)
    (hlim : ∀ᵐ a ∂νside, Tendsto (fun s ↦ K s a) (𝓝[>] 0) (𝓝 (k a))) :
    (∀ᶠ s in 𝓝[>] 0, IntegrableOn (fun a ↦ K s a *
      (F (a, b s a) * (starRingEnd ℂ) (G (a, b s a))).re) (mixedLevelInterval s)) ∧
    Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, K s a *
      (F (a, b s a) * (starRingEnd ℂ) (G (a, b s a))).re) (𝓝[>] 0)
      (𝓝 (∫ a in Jside, k a *
        (aclTrace (-c) c F D t a * (starRingEnd ℂ) (aclTrace (-c) c G E t a)).re)) := by
  obtain ⟨M, hML, hM⟩ := hF.exists_l2_section_envelope hFL hDL
  obtain ⟨N, hNL, hN⟩ := hG.exists_l2_section_envelope hGL hEL
  let B := fun a ↦ max C 0 * (‖M a‖ * ‖N a‖)
  let W := fun s a ↦ K s a *
    (F (a, b s a) * (starRingEnd ℂ) (G (a, b s a))).re
  have hS (s : ℝ) : Measurable (fun a ↦ (a, b s a)) := by
    exact measurable_id.prodMk (hbm s)
  have hWm : ∀ᶠ s in 𝓝[>] 0, AEStronglyMeasurable (W s) νside := by
    filter_upwards [hKm] with s h
    have hFG : Measurable (fun a ↦ (F (a, b s a) *
        star (G (a, b s a))).re) :=
      Complex.continuous_re.measurable.comp
        ((hFm.comp (hS s)).mul (Complex.continuous_conj.measurable.comp (hGm.comp (hS s))))
    exact h.mul hFG.aestronglyMeasurable
  have hB : Integrable B νside := (hML.norm.integrable_mul hNL.norm).const_mul (max C 0)
  have hbound : ∀ᶠ s in 𝓝[>] 0,
      ∀ᵐ a ∂νside, a ∈ mixedLevelInterval s → ‖W s a‖ ≤ B a := by
    filter_upwards [hK, hbmem] with s hs hs'
    filter_upwards [hM, hN, hF.ae_hasIntervalH1 hFL hDL, hG.ae_hasIntervalH1 hGL hEL]
      with a hMa hNa hFa hGa
    intro ha
    let z := b s a
    have hb : z ∈ Jside := hs' a ha
    have hMf : ‖F (a, z)‖ ≤ ‖M a‖ := le_trans (by
      simpa only [aclTrace, hFa.extension_eq mixed_interval_ne hb] using
        hMa z (Ioo_subset_Icc_self hb)) (le_abs_self _)
    have hNg : ‖G (a, z)‖ ≤ ‖N a‖ := le_trans (by
      simpa only [aclTrace, hGa.extension_eq mixed_interval_ne hb] using
        hNa z (Ioo_subset_Icc_self hb)) (le_abs_self _)
    change ‖K s a * _‖ ≤ B a
    rw [norm_mul]
    apply mul_le_mul ((hs a ha).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hMf hNg (norm_nonneg _) (norm_nonneg _)
  constructor
  · filter_upwards [hWm, hbound, (Ioo_mem_nhdsGT zero_lt_one : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)]
      with s hsm hsb hs
    have hsub : mixedLevelInterval s ⊆ Jside :=
      fun _ ha ↦ (mixed_quarter_graph_mem hs ha).1.1
    exact (hB.mono_measure (Measure.restrict_mono hsub le_rfl)).mono'
      (hsm.mono_measure (Measure.restrict_mono hsub le_rfl)) (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsb,
          ae_restrict_mem (s := mixedLevelInterval s) measurableSet_Ioo] with a ha hm
        exact ha hm)
  · refine mixed_quarter_dominated_limit hWm hB hbound
      (Eventually.of_forall fun a ↦
        show 0 ≤ B a from mul_nonneg (le_max_right C 0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))) ?_
    filter_upwards [hlim, hF.ae_tendsto_trace mixed_interval_ne hFL hDL,
      hG.ae_tendsto_trace mixed_interval_ne hGL hEL, ae_restrict_mem measurableSet_Ioo]
      with a ha hf hg ham
    have hht := hbt a ham
    have hft := (hf t ht).comp hht
    have hgt := Complex.continuous_conj.continuousAt.tendsto.comp ((hg t ht).comp hht)
    have hr := Complex.continuous_re.continuousAt.tendsto.comp (hft.mul hgt)
    simpa only [W, Function.comp_apply] using ha.mul hr

theorem mixed_quarter_pair_limit {F D G E : Plane → ℂ} {K : ℝ → ℝ → ℝ}
    {k : ℝ → ℝ} {C : ℝ}
    (hF : HasACLSectionsOn Jside Jside F D) (hG : HasACLSectionsOn Jside Jside G E)
    (hFm : Measurable F) (hGm : Measurable G)
    (hFL : MemLp F 2 (volume.restrict (Jside ×ˢ Jside)))
    (hDL : MemLp D 2 (volume.restrict (Jside ×ˢ Jside)))
    (hGL : MemLp G 2 (volume.restrict (Jside ×ˢ Jside)))
    (hEL : MemLp E 2 (volume.restrict (Jside ×ˢ Jside)))
    (hKm : ∀ᶠ s in 𝓝[>] 0, AEStronglyMeasurable (K s) νside)
    (hK : ∀ᶠ s in 𝓝[>] 0, ∀ a ∈ mixedLevelInterval s, ‖K s a‖ ≤ C)
    (hlim : ∀ᵐ a ∂νside, Tendsto (fun s ↦ K s a) (𝓝[>] 0) (𝓝 (k a))) :
    Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, K s a *
      (F (a, quarterHeight s a) * (starRingEnd ℂ) (G (a, quarterHeight s a))).re) (𝓝[>] 0)
      (𝓝 (∫ a in Jside, k a *
        (aclTrace (-c) c F D c a * (starRingEnd ℂ) (aclTrace (-c) c G E c a)).re)) :=
  (mixed_quarter_pair_limit_of_graph
    (right_mem_Icc.mpr mixed_interval_ne.le)
    (fun s ↦ by unfold quarterHeight; fun_prop)
    (by
      filter_upwards [(Ioo_mem_nhdsGT zero_lt_one : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with s hs
      exact fun _ ha ↦ (mixed_quarter_graph_mem hs ha).1.2)
    (fun _ ha ↦ mixed_quarter_height_tendsto ha)
    hF hG hFm hGm hFL hDL hGL hEL hKm hK hlim).2

/-- On each of the two positive sides, the singular signed quadratic
model evaluated on the actual quotient differs from its trace model by
an integral tending to zero outside a null set of levels. -/
theorem mixed_quarter_quotient_mass_replacement {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, mixedLevelModelWeight s a *
        (‖d.phi (traceSideCoords j (a, quarterHeight s a))‖ ^ 2 -
          ‖d.phi (traceSideCoords j (a, c))‖ ^ 2))
        (𝓝[Ioo 0 1 \ N] 0) (𝓝 0) := by
  let U := Jside ×ˢ Jside
  let C := traceSideCoords j
  let n := 1 - j
  let D := d.jet [n] ∘ C
  let E := d.jet [n, n] ∘ C
  let T := fun a ↦ d.phi (C (a, c))
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hcell : mixedOpenCell = U := by simp only [mixedOpenCell, neg_div, U]
  have hpre : Prod.swap ⁻¹' U = U := by
    ext q
    exact and_comm
  have hweak {f e : Plane → ℂ} (h : HasWeakPartialOn U n f e) :
      HasWeakPartialOn U 1 (f ∘ C) (e ∘ C) := by
    fin_cases j
    · exact h
    · exact hpre ▸ h.comp_swap hU
  have hmem {f : Plane → ℂ} (h : MemLp f 2 (volume.restrict U)) :
      MemLp (f ∘ C) 2 (volume.restrict U) := by
    fin_cases j
    · exact h
    · exact hpre ▸ memLp_comp_swap hU.measurableSet h
  have hL := d.h2.memLp_weakJet (hcell.symm ▸ hU) d.weakJet
  have hDL : MemLp D 2 (volume.restrict U) := hmem (hcell ▸ hL [n] (by simp))
  have hEL : MemLp E 2 (volume.restrict U) := hmem (hcell ▸ hL [n, n] (by simp))
  have hD : HasWeakPartialOn U 1 (d.phi ∘ C) D := by
    have hh := d.weakJet.2 [] (by decide) n
    rw [d.weakJet.1] at hh
    exact hweak (hcell ▸ hh)
  have hE : HasWeakPartialOn U 1 (d.jet [n] ∘ C) E :=
    hweak (hcell ▸ d.weakJet.2 [n] (by simp) n)
  have hside : HasTransverseH1Trace (-c) c (-c) c c C d.phi T := by
    simpa only [T, C, cellEdgeNormal, ite_true, neg_div] using
      (mixed_quotient_side_traces d j true).2.2.1
  obtain ⟨F, hFm, hFa, hFL, hFacl, hFt⟩ := hside.with_weak_snd hD hDL
  obtain ⟨G, hGm, hGa, hGacl⟩ := hE.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 mixed_interval_ne) isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 mixed_interval_ne)
  have hl := mixed_quarter_mass_replacement hFacl hGacl hGa.symm hFm hFL
    (hDL.ae_eq hGa.symm) hEL
  have hGraph := ae_mixed_quarterGraph_of_ae hFa
  let N : Set ℝ := {s | ¬(s ∈ Ioo (0 : ℝ) 1 → ∀ᵐ a ∂volume.restrict (mixedLevelInterval s),
    F (a, quarterHeight s a) = (d.phi ∘ C) (a, quarterHeight s a))}
  have hN : volume N = 0 := hGraph
  refine ⟨N, hN, ?_⟩
  have hsub : 𝓝[Ioo 0 1 \ N] (0 : ℝ) ≤ 𝓝[>] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ hs.1.1)
  apply (hl.mono_left hsub).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsF := not_not.mp hs.2 hs.1
  have htsub : mixedLevelInterval s ⊆ Jside :=
    fun _ ha ↦ (mixed_quarter_graph_mem hs.1 ha).1.1
  have hsT := ae_restrict_of_ae_restrict_of_subset htsub hFt
  apply integral_congr_ae
  filter_upwards [hsF, hsT] with a ha ht
  simp only [ha, Function.comp_apply, ← ht]
  rfl

/-- Central oddness and reversal of the symmetric tangential interval
transfer the mass replacement to the two opposite sides. -/
theorem mixed_quarter_all_side_mass_replacement {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ σ : Bool,
      let e : ℝ := if σ then 1 else -1
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, mixedLevelModelWeight s a *
        (‖d.phi (traceSideCoords j (a, e * quarterHeight s a))‖ ^ 2 -
          ‖d.phi (traceSideCoords j (a, e * c))‖ ^ 2))
        (𝓝[Ioo 0 1 \ N] 0) (𝓝 0) := by
  obtain ⟨N, hN, H⟩ := mixed_quarter_quotient_mass_replacement d j
  refine ⟨N, hN, fun σ ↦ ?_⟩
  cases σ
  · simp only [Bool.false_eq_true, ite_false, neg_mul, one_mul]
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hT : 0 ≤ arccos (√s) := arccos_nonneg _
    have hneg (g : ℝ → ℝ) :
        (∫ a in mixedLevelInterval s, g (-a)) = ∫ a in mixedLevelInterval s, g a := by
      have hh : -arccos (√s) ≤ arccos (√s) := by linarith
      unfold mixedLevelInterval
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh,
        intervalIntegral.integral_comp_neg, neg_neg, intervalIntegral.integral_of_le hh,
        integral_Ioc_eq_integral_Ioo]
    rw [← hneg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro a ha
    have ha' : -a ∈ mixedLevelInterval s := ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have hmem := (mixed_quarter_graph_mem hs.1 ha').1
    have hb : c ∈ Icc (-c) c := right_mem_Icc.mpr mixed_interval_ne.le
    have hclosed (x y : ℝ) (hx : x ∈ Icc (-c) c) (hy : y ∈ Icc (-c) c) :
        traceSideCoords j (x, y) ∈ closure mixedOpenCell := by
      rw [mixedOpenCell, neg_div, closure_prod_eq, closure_Ioo mixed_interval_ne.ne]
      fin_cases j
      · exact ⟨hx, hy⟩
      · exact ⟨hy, hx⟩
    have odd (b : ℝ) (hb : b ∈ Icc (-c) c) :
        ‖d.phi (traceSideCoords j (a, -b))‖ = ‖d.phi (traceSideCoords j (-a, b))‖ := by
      have he : traceSideCoords j (a, -b) = -traceSideCoords j (-a, b) := by
        fin_cases j <;> ext <;> simp [traceSideCoords]
      rw [he, d.central_odd _ (hclosed _ _ (Ioo_subset_Icc_self hmem.1) hb), norm_neg]
    have hβ : quarterHeight s (-a) = quarterHeight s a := by simp only [quarterHeight, cos_neg]
    have hw : mixedLevelModelWeight s (-a) = mixedLevelModelWeight s a := by
      simp only [mixedLevelModelWeight, hβ, cos_neg, sin_neg, mul_neg, neg_sq]
    dsimp only
    rw [hw, ← odd c hb]
    have hh := odd (quarterHeight s (-a)) (Ioo_subset_Icc_self hmem.2)
    rw [hβ] at hh ⊢
    rw [hh]
  · simpa only [ite_true, one_mul] using H

/-- The signed normal graph in side coordinates. -/
def mixedQuarterHeight (σ : Bool) (s a : ℝ) : ℝ :=
  if σ then quarterHeight s a else -quarterHeight s a

/-- An exact quarter graph, with the tangential coordinate first before
applying the side chart. -/
def mixedQuarterPoint (j : Fin 2) (σ : Bool) (s a : ℝ) : Plane :=
  traceSideCoords j (a, mixedQuarterHeight σ s a)

private theorem mixed_neg_mem {x : ℝ} (hx : x ∈ Jside) : -x ∈ Jside :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem mixed_quarter_signed_height_mem (σ : Bool) {s a : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ha : a ∈ mixedLevelInterval s) :
    mixedQuarterHeight σ s a ∈ Jside := by
  cases σ
  · exact mixed_neg_mem (mixed_quarter_graph_mem hs ha).1.2
  · exact (mixed_quarter_graph_mem hs ha).1.2

theorem mixed_quarter_signed_height_tendsto (σ : Bool) {a : ℝ} (ha : a ∈ Jside) :
    Tendsto (fun s ↦ mixedQuarterHeight σ s a) (𝓝[>] 0) (𝓝[Jside] (cellEdgeNormal σ)) := by
  have h := mixed_quarter_height_tendsto ha
  cases σ
  · rw [tendsto_nhdsWithin_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · simpa only [mixedQuarterHeight, cellEdgeNormal, Bool.false_eq_true, ite_false, neg_div]
        using h.1.neg
    · exact h.2.mono fun _ hb ↦ mixed_neg_mem hb
  · exact h

/-- The graph a.e. transfer works in either orientation. -/
theorem ae_mixed_quarterGraph_signed_of_ae (σ : Bool) {P : Plane → Prop}
    (hP : ∀ᵐ q ∂volume.restrict (Jside ×ˢ Jside), P q) :
    ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      ∀ᵐ a ∂volume.restrict (mixedLevelInterval s), P (a, mixedQuarterHeight σ s a) := by
  cases σ
  · let M : Plane → Plane := fun q ↦ (q.1, -q.2)
    have hm : MeasurePreserving M volume volume := by
      change MeasurePreserving (Prod.map id Neg.neg) (volume : Measure Plane) volume
      rw [Measure.volume_eq_prod]
      exact (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg volume)
    have hp : ∀ᵐ q ∂volume.restrict (Jside ×ˢ Jside), P (M q) := by
      have h := hm.quasiMeasurePreserving.ae
        ((ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).1 hP)
      refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 ?_
      filter_upwards [h] with q hq hqm
      exact hq ⟨hqm.1, mixed_neg_mem hqm.2⟩
    exact ae_mixed_quarterGraph_of_ae hp
  · exact ae_mixed_quarterGraph_of_ae hP

/-- The three fields appearing in the geometric quadratic forms: the
quotient and its two specified first weak partials. -/
def MixedQuotientData.levelField {ω : L2} (d : MixedQuotientData ω) :
    Option (Fin 2) → Plane → ℂ
  | none => d.phi
  | some i => d.jet [i]

/-- Their canonical traces in the side chart. The normal trace is zero,
and the tangential trace differentiates the continuous edge value. -/
def MixedQuotientData.levelTrace {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool) :
    Option (Fin 2) → ℝ → ℂ
  | none => mixedEdgeValue (1 - j) σ d.phi
  | some i => if i = j then deriv (mixedEdgeValue (1 - j) σ d.phi) else fun _ ↦ 0

private theorem mixed_levelField_acl {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool)
    (i : Option (Fin 2)) :
    ∃ F D : Plane → ℂ, Measurable F ∧
      F =ᵐ[volume.restrict (Jside ×ˢ Jside)] d.levelField i ∘ traceSideCoords j ∧
      MemLp F 2 (volume.restrict (Jside ×ˢ Jside)) ∧
      MemLp D 2 (volume.restrict (Jside ×ˢ Jside)) ∧
      HasACLSectionsOn Jside Jside F D ∧
      d.levelTrace j σ i =ᵐ[νside] aclTrace (-c) c F D (cellEdgeNormal σ) := by
  let U := Jside ×ˢ Jside
  let C := traceSideCoords j
  let n := 1 - j
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hcell : mixedOpenCell = U := by simp only [mixedOpenCell, neg_div, U]
  have hpre : Prod.swap ⁻¹' U = U := by
    ext q
    exact and_comm
  have hweak {f e : Plane → ℂ} (h : HasWeakPartialOn U n f e) :
      HasWeakPartialOn U 1 (f ∘ C) (e ∘ C) := by
    fin_cases j
    · exact h
    · exact hpre ▸ h.comp_swap hU
  have hmem {f : Plane → ℂ} (h : MemLp f 2 (volume.restrict U)) :
      MemLp (f ∘ C) 2 (volume.restrict U) := by
    fin_cases j
    · exact h
    · exact hpre ▸ memLp_comp_swap hU.measurableSet h
  have hC : axisTraceChart n = C := by fin_cases j <;> rfl
  have go {f e : Plane → ℂ} {T : ℝ → ℂ} (h : HasMixedEdgeTrace n σ f T)
      (hw : HasWeakPartialOn mixedOpenCell n f e)
      (hL : MemLp e 2 (volume.restrict mixedOpenCell)) :
      ∃ F : Plane → ℂ, Measurable F ∧ F =ᵐ[volume.restrict U] f ∘ C ∧
        MemLp F 2 (volume.restrict U) ∧ HasACLSectionsOn Jside Jside F (e ∘ C) ∧
        T =ᵐ[νside] aclTrace (-c) c F (e ∘ C) (cellEdgeNormal σ) := by
    unfold HasMixedEdgeTrace at h
    rw [hC, neg_div] at h
    exact h.with_weak_snd (hweak (hcell ▸ hw)) (hmem (hcell ▸ hL))
  have hL := d.h2.memLp_weakJet (hcell.symm ▸ hU) d.weakJet
  cases i with
  | none =>
    have hw : HasWeakPartialOn mixedOpenCell n d.phi (d.jet [n]) := by
      simpa only [d.weakJet.1] using d.weakJet.2 [] (by decide) n
    have hLn := hL [n] (by simp)
    have hside : HasMixedEdgeTrace n σ d.phi (d.levelTrace j σ none) := by
      unfold HasMixedEdgeTrace MixedQuotientData.levelTrace mixedEdgeValue
      change HasTransverseH1Trace _ _ _ _ _ (axisTraceChart n) d.phi
        (fun a ↦ d.phi (axisTraceChart n (a, cellEdgeNormal σ)))
      rw [hC]
      exact (mixed_quotient_side_traces d j σ).2.2.1
    obtain ⟨F, hm, he, hF, hA, hT⟩ := go hside hw hLn
    exact ⟨F, d.jet [n] ∘ C, hm, he, hF, hmem (hcell ▸ hLn), hA, hT⟩
  | some i =>
    have hw := d.weakJet.2 [i] (by simp) n
    have hLi := hL [n, i] (by simp)
    have hside : HasMixedEdgeTrace n σ (d.jet [i]) (d.levelTrace j σ (some i)) := by
      by_cases hi : i = j
      · subst i
        simp only [HasMixedEdgeTrace, MixedQuotientData.levelTrace, ite_true]
        change HasTransverseH1Trace _ _ _ _ _ (axisTraceChart n) (d.jet [j])
          (deriv (fun a ↦ d.phi (axisTraceChart n (a, cellEdgeNormal σ))))
        rw [hC]
        exact (mixed_quotient_side_traces d j σ).2.2.2
      · have hn : i = n := by fin_cases j <;> fin_cases i <;> simp_all [n]
        rw [MixedQuotientData.levelTrace, ite_eq_right hi, hn]
        exact d.normal_zero n σ
    obtain ⟨F, hm, he, hF, hA, hT⟩ := go hside hw hLi
    exact ⟨F, d.jet [n, i] ∘ C, hm, he, hF, hmem (hcell ▸ hLi), hA, hT⟩

/-- Bounded-coefficient quadratic products of the specified weak fields
converge to the canonical products on each of the four sides. The good
level set is independent of the coefficient and of the pair of fields. -/
theorem mixed_quarter_weak_pair_limit {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ (i l : Option (Fin 2)) (K : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (C : ℝ),
      (∀ᶠ s in 𝓝[>] 0, AEStronglyMeasurable (K s) νside) →
      (∀ᶠ s in 𝓝[>] 0, ∀ a ∈ mixedLevelInterval s, ‖K s a‖ ≤ C) →
      (∀ᵐ a ∂νside, Tendsto (fun s ↦ K s a) (𝓝[>] 0) (𝓝 (k a))) →
      let W := fun s a ↦ K s a * (d.levelField i (mixedQuarterPoint j σ s a) *
        (starRingEnd ℂ) (d.levelField l (mixedQuarterPoint j σ s a))).re
      (∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, IntegrableOn (W s) (mixedLevelInterval s)) ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W s a) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 (∫ a in Jside, k a * (d.levelTrace j σ i a *
          (starRingEnd ℂ) (d.levelTrace j σ l a)).re)) := by
  choose F D hm ha hF hD hA hT using fun i ↦ mixed_levelField_acl d j σ i
  have hg (i : Option (Fin 2)) := ae_mixed_quarterGraph_signed_of_ae σ (ha i)
  let P := fun s ↦ s ∈ Ioo (0 : ℝ) 1 → ∀ i, ∀ᵐ a ∂volume.restrict (mixedLevelInterval s),
    F i (a, mixedQuarterHeight σ s a) = d.levelField i (mixedQuarterPoint j σ s a)
  have hp : ∀ᵐ s ∂volume, P s := by
    filter_upwards [ae_all_iff.2 hg] with s hs h i
    exact hs i h
  let N := {s | ¬P s}
  refine ⟨N, hp, fun i l K k C hKm hK hlim ↦ ?_⟩
  have ht : cellEdgeNormal σ ∈ Icc (-c) c := by
    cases σ
    · simpa only [cellEdgeNormal, Bool.false_eq_true, ite_false, neg_div] using
        left_mem_Icc.mpr mixed_interval_ne.le
    · exact right_mem_Icc.mpr mixed_interval_ne.le
  have H := mixed_quarter_pair_limit_of_graph ht
    (fun s ↦ by
      cases σ <;> simp only [mixedQuarterHeight, quarterHeight, Bool.false_eq_true,
        ite_false, ite_true] <;> fun_prop)
    (by
      filter_upwards [(Ioo_mem_nhdsGT zero_lt_one : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with s hs
      exact fun _ ha ↦ mixed_quarter_signed_height_mem σ hs ha)
    (fun _ ha ↦ mixed_quarter_signed_height_tendsto σ ha)
    (hA i) (hA l) (hm i) (hm l) (hF i) (hD i) (hF l) (hD l) hKm hK hlim
  have hf : 𝓝[Ioo 0 1 \ N] (0 : ℝ) ≤ 𝓝[>] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ hs.1.1)
  dsimp only
  have he : ∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0,
      (fun a ↦ K s a * (F i (a, mixedQuarterHeight σ s a) *
        (starRingEnd ℂ) (F l (a, mixedQuarterHeight σ s a))).re)
        =ᵐ[volume.restrict (mixedLevelInterval s)]
      fun a ↦ K s a * (d.levelField i (mixedQuarterPoint j σ s a) *
        (starRingEnd ℂ) (d.levelField l (mixedQuarterPoint j σ s a))).re := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hh : P s := not_not.mp hs.2
    filter_upwards [hh hs.1 i, hh hs.1 l] with a hi hl
    simp only [hi, hl]
  refine ⟨?_, ?_⟩
  · filter_upwards [hf H.1, he] with s hs h
    exact hs.congr h
  · rw [show (∫ a in Jside, k a * (d.levelTrace j σ i a *
        (starRingEnd ℂ) (d.levelTrace j σ l a)).re) =
        ∫ a in Jside, k a * (aclTrace (-c) c (F i) (D i) (cellEdgeNormal σ) a *
          (starRingEnd ℂ) (aclTrace (-c) c (F l) (D l) (cellEdgeNormal σ) a)).re by
      apply integral_congr_ae
      filter_upwards [hT i, hT l] with a hi hl
      simp only [hi, hl]
    ]
    exact (H.2.mono_left hf).congr' (he.mono fun s hs ↦ integral_congr_ae hs)

end NoEmbeddedEigenvalues
