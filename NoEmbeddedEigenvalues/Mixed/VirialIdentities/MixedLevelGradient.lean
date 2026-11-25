module

public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedLevelRemainder
public import NoEmbeddedEigenvalues.EvenEven.NormalVirial.NormalVirial

/-! # Pairing the signed gradient terms on regular levels -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real
open scoped Topology ComplexConjugate

local notation "c" => (π / 2)
local notation "Jside" => (Ioo (-c) c)
local notation "Plane" => (ℝ × ℝ)

private theorem edge_model_integrable {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun a ↦ mixedLevelModelWeight s a * ‖d.phi (mixedQuarterSidePoint j σ a)‖ ^ 2)
      (mixedLevelInterval s) := by
  let I := mixedLevelInterval s
  let μ := volume.restrict I
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have hT := (mixed_quotient_side_traces d j σ).1
  have hC : ContinuousOn (d.phi ∘ mixedQuarterSidePoint j σ) (Icc (-c) c) := by
    have h := hT.continuousOn
    rw [neg_div, uIcc_of_le (by linarith [pi_pos])] at h
    exact h
  obtain ⟨C, hC'⟩ := isCompact_Icc.bddAbove_image hC.norm
  have hsub : I ⊆ Icc (-c) c := fun _ ha ↦ Ioo_subset_Icc_self
    (mixed_quarter_graph_mem hs' ha).1.1
  have hW : Measurable (mixedLevelModelWeight s) := by
    unfold mixedLevelModelWeight quarterHeight
    dsimp
    fun_prop
  have : IsFiniteMeasure μ := ⟨by
    dsimp only [μ, I]
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top⟩
  refine (integrable_const (μ := μ) (2 / √s * (max C 0) ^ 2)).mono'
    (hW.aestronglyMeasurable.mul
      (((hC.mono hsub).aestronglyMeasurable measurableSet_Ioo).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a ha
  have hw := mixed_quarter_weight_bound hs ha
  have hca := sqrt_lt_cos_of_abs_lt_arccos hs' (abs_lt.mpr ⟨ha.1, ha.2⟩)
  have hc : ‖d.phi (mixedQuarterSidePoint j σ a)‖ ≤ max C 0 :=
    (hC' (mem_image_of_mem _ (hsub ha))).trans (le_max_left _ _)
  have hM : ‖mixedLevelModelWeight s a‖ ≤ 2 / √s := by
    change ‖mixedLevelSign (a, quarterHeight s a) * (1 / √(cos a ^ 2 - s ^ 2))‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / √(cos a ^ 2 - s ^ 2))]
    refine (mul_le_mul (mixed_level_frame_norm_le _ _) hw.2 (by positivity) (by norm_num)).trans ?_
    rw [one_mul]
    exact div_le_div_of_nonneg_left (by norm_num) (sqrt_pos.2 hs.1) hca.le
  change ‖mixedLevelModelWeight s a * ‖d.phi (mixedQuarterSidePoint j σ a)‖ ^ 2‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  exact mul_le_mul hM (pow_le_pow_left₀ (norm_nonneg _) hc 2) (sq_nonneg _) (by positivity)

/-- If the actual model masses are integrable on the retained levels,
their signed sum converges to the paired trace defect. This does not
take a limit of any individual mass. -/
theorem mixed_level_actual_mass_limit {ω : L2} (d : MixedQuotientData ω)
    (hI : ∃ N : Set ℝ, volume N = 0 ∧
      ∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, ∀ (j : Fin 2) (σ : Bool),
        IntegrableOn (fun a ↦ mixedLevelModelWeight s a *
          ‖d.phi (mixedQuarterPoint j σ s a)‖ ^ 2) (mixedLevelInterval s)) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun s ↦ ∑ j : Fin 2, ∑ σ : Bool, ∫ a in mixedLevelInterval s,
          (if j = 0 then -1 else 1) *
            (mixedLevelModelWeight s a * ‖d.phi (mixedQuarterPoint j σ s a)‖ ^ 2))
        (𝓝[Ioo 0 1 \ N] 0) (𝓝 (∫ a in Jside, mixedEdgeMassDefect d.phi a / cos a)) := by
  obtain ⟨M, hM, hI⟩ := hI
  choose N hN hL using fun j ↦ mixed_quarter_all_side_mass_replacement d j
  let U := M ∪ ⋃ j, N j
  have hU : volume U = 0 := measure_union_null hM (measure_iUnion_null hN)
  refine ⟨U, hU, ?_⟩
  let 𝓕 := 𝓝[Ioo 0 1 \ U] (0 : ℝ)
  have hf : 𝓕 ≤ 𝓝[>] 0 := nhdsWithin_mono _ (fun _ hs ↦ hs.1.1)
  have fm : 𝓕 ≤ 𝓝[Ioo 0 1 \ M] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun hm ↦ hs.2 (Or.inl hm)⟩)
  have fn (j : Fin 2) : 𝓕 ≤ 𝓝[Ioo 0 1 \ N j] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun hn ↦ hs.2 (Or.inr (mem_iUnion.2 ⟨j, hn⟩))⟩)
  let V := fun j σ s a ↦ mixedLevelModelWeight s a * ‖d.phi (mixedQuarterPoint j σ s a)‖ ^ 2
  let E := fun j σ s a ↦ mixedLevelModelWeight s a * ‖d.phi (mixedQuarterSidePoint j σ a)‖ ^ 2
  let b : Fin 2 → ℝ := fun j ↦ if j = 0 then -1 else 1
  have hl (j : Fin 2) (σ : Bool) :
      Tendsto (fun s ↦ b j * (∫ a in mixedLevelInterval s, V j σ s a - E j σ s a))
        𝓕 (𝓝 0) := by
    have H := ((hL j σ).mono_left (fn j)).const_mul (b j)
    simp only [mul_zero] at H
    apply H.congr
    intro s
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun a ↦ ?_
    cases σ <;> simp only [V, E, mixedQuarterSidePoint, mixedQuarterPoint, mixedQuarterHeight,
      cellEdgeNormal,
      Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul, neg_div, mul_sub]
  have L := tendsto_finsetSum Finset.univ fun j _ ↦ tendsto_finsetSum Finset.univ fun σ _ ↦ hl j σ
  simp only [Finset.sum_const_zero] at L
  have H := (mixed_level_model_trace_limit d).mono_left hf
  have ht := H.add L
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [fm hI, hf (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))] with s hs h
  have hEi (j : Fin 2) (σ : Bool) : IntegrableOn (E j σ s) (mixedLevelInterval s) :=
    edge_model_integrable d j σ h
  have hdef (a : ℝ) : mixedLevelModelWeight s a * mixedEdgeMassDefect d.phi a =
      ∑ j : Fin 2, ∑ σ : Bool, b j * E j σ s a := by
    simp only [Fin.sum_univ_two, Fintype.sum_bool, E, b, mixedEdgeMassDefect, mixedQuarterSidePoint]
    change _ = -1 * (mixedLevelModelWeight s a * ‖d.phi (a, cellEdgeNormal true)‖ ^ 2) +
      -1 * (mixedLevelModelWeight s a * ‖d.phi (a, cellEdgeNormal false)‖ ^ 2) +
      (1 * (mixedLevelModelWeight s a * ‖d.phi (cellEdgeNormal true, a)‖ ^ 2) +
       1 * (mixedLevelModelWeight s a * ‖d.phi (cellEdgeNormal false, a)‖ ^ 2))
    ring
  simp only [hdef]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun σ _ ↦ (hEi j σ).const_mul _)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun σ _ ↦ (hEi j σ).const_mul _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_sub (hs j σ) (hEi j σ), integral_const_mul]
  change b j * _ + b j * (_ - _) = b j * _
  ring

private theorem quarter_gradNorm_ne {s a : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ mixedLevelInterval s) (j : Fin 2) (σ : Bool) :
    gradNorm (diagInv (mixedQuarterPoint j σ s a)) ≠ 0 := by
  let b := quarterHeight s a
  have hh := mixed_quarter_graph_mem hs ha
  have ha' : 0 < cos a := cos_pos_of_mem_Ioo hh.1.1
  have hh' := sqrt_lt_cos_of_abs_lt_arccos hs (abs_lt.mpr ⟨ha.1, ha.2⟩)
  have hss : s ≤ √s := by
    have h := (sqrt_lt' (show (0 : ℝ) < 1 by norm_num)).2 (by simpa using hs.2)
    nlinarith only [sq_sqrt hs.1.le, mul_le_mul_of_nonneg_left h.le (sqrt_nonneg s)]
  have hd : s / cos a < 1 := (div_lt_one ha').2 (hss.trans_lt hh')
  have hc : cos b < 1 := (cos_arccos
    ((by norm_num : (-1 : ℝ) ≤ 0).trans (div_nonneg hs.1.le ha'.le)) hd.le).trans_lt hd
  intro he
  have hz := mixed_level_gradNorm_sq (mixedQuarterPoint j σ s a)
  rw [he] at hz
  have hr : mixedLevelR (mixedQuarterPoint j σ s a) = 0 :=
    by nlinarith [sq_nonneg (mixedLevelS (mixedQuarterPoint j σ s a))]
  have hS : mixedLevelS (mixedQuarterPoint j σ s a) = 0 :=
    by nlinarith [sq_nonneg (mixedLevelR (mixedQuarterPoint j σ s a))]
  have hb : sin b ≠ 0 := by
    intro he
    have hbp : 0 < cos b := hh.2.1
    have hsincos := sin_sq_add_cos_sq b
    rw [he, zero_pow (by decide : 2 ≠ 0), zero_add] at hsincos
    nlinarith only [hsincos, hbp, hc,
      mul_pos (sub_pos.mpr hc) (by linarith : 0 < 1 + cos b)]
  have hp := mul_ne_zero ha'.ne' hb
  fin_cases j <;> cases σ
  · change cos a * sin (-b) = 0 at hr
    rw [sin_neg, mul_neg, neg_eq_zero] at hr
    exact hp hr
  · exact hp hr
  · change cos a * sin (-b) = 0 at hS
    rw [sin_neg, mul_neg, neg_eq_zero] at hS
    exact hp hS
  · exact hp hS

private theorem level_gradient_energy_integrable (ω : L2) :
    IntegrableOn (fun p ↦ ‖streamNormal ω p‖ ^ 2) cellSquare ∧
    IntegrableOn (fun p ↦ ‖streamTangent ω p‖ ^ 2) cellSquare := by
  have hsub : cellSquare ⊆
      Ioc (-2 * π) (2 * π) ×ˢ Ioc (-2 * π) (2 * π) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [pi_pos]
  have hi (g : L2) := (integrableOn_norm_liftL2_sq g).mono_set hsub
  let B := fun p ↦ 2 * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2)
  have hB : IntegrableOn B cellSquare :=
    ((hi (streamPartial 0 ω)).add (hi (streamPartial 1 ω))).const_mul 2
  have hm (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have hX : Measurable (streamLiftX ω) := hm _
  have hY : Measurable (streamLiftY ω) := hm _
  have go (F : Plane → ℂ) (hF : Measurable F)
      (hb : ∀ p, ‖F p‖ ≤ ‖streamLiftX ω p‖ + ‖streamLiftY ω p‖) :
      IntegrableOn (fun p ↦ ‖F p‖ ^ 2) cellSquare := by
    refine hB.mono' (hF.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine (pow_le_pow_left₀ (norm_nonneg _) (hb p) 2).trans ?_
    dsimp only [B]
    nlinarith [sq_nonneg (‖streamLiftX ω p‖ - ‖streamLiftY ω p‖)]
  exact ⟨go _ (by unfold streamNormal normalDeriv gradNorm; fun_prop) (norm_normalDeriv_le _ _),
    go _ (by unfold streamTangent tangentDeriv gradNorm; fun_prop) (norm_tangentDeriv_le _ _)⟩

set_option maxHeartbeats 600000 in
-- Common exceptional sets and the finite-sum integral congruences exceed the default.
/-- The full signed gradient limit pairs the singular masses and sums
the four finite corrections. -/
theorem mixed_level_signed_gradient_limit {ω : L2} (d : MixedQuotientData ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun s ↦ 2 * (levelIntegral s (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
        levelIntegral s (fun p ↦ ‖streamTangent ω p‖ ^ 2))) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 ((∫ a in Jside, mixedEdgeMassDefect d.phi a / cos a) +
          ∑ σ : Bool, ∫ a in Jside, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a)) := by
  let G := fun p ↦ 2 * (‖streamNormal ω p‖ ^ 2 - ‖streamTangent ω p‖ ^ 2)
  let F := fun j σ s a ↦ mixedQuarterTimeWeight s a * G (diagInv (mixedQuarterPoint j σ s a))
  let V := fun j σ s a ↦ mixedLevelModelWeight s a * ‖d.phi (mixedQuarterPoint j σ s a)‖ ^ 2
  let b : Fin 2 → ℝ := fun j ↦ if j = 0 then -1 else 1
  let W := fun j σ s a ↦ mixedLevelCosWeight j σ s a *
    d.levelGradientRemainder (mixedQuarterPoint j σ s a)
  obtain ⟨hn, ht⟩ := level_gradient_energy_integrable ω
  have hg : IntegrableOn G cellSquare := (hn.sub ht).const_mul 2
  let P := fun s ↦ s ∈ Ioo (0 : ℝ) 1 →
    (∀ (j : Fin 2) (σ : Bool), IntegrableOn (F j σ s) (mixedLevelInterval s) ∧
      F j σ s =ᵐ[volume.restrict (mixedLevelInterval s)]
        fun a ↦ b j * V j σ s a + W j σ s a) ∧
    (levelIntegral s G = 2 * (levelIntegral s (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
      levelIntegral s (fun p ↦ ‖streamTangent ω p‖ ^ 2)))
  have hp : ∀ᵐ s ∂volume, P s := by
    filter_upwards [ae_mixedQuarter_integrable hg,
      ae_mixedQuarterPoint_of_ae d.level_signed_gradient_ae,
      (ae_restrict_iff' measurableSet_Ioo).1 (integral_cellSquare_eq hn).1,
      (ae_restrict_iff' measurableSet_Ioo).1 (integral_cellSquare_eq ht).1] with s hi ha hn ht hs
    refine ⟨fun j σ ↦ ⟨hi hs j σ, ?_⟩, ?_⟩
    · filter_upwards [ha hs j σ, ae_restrict_mem (s := mixedLevelInterval s) measurableSet_Ioo]
        with a h hm
      dsimp only [F, G]
      rw [h (quarter_gradNorm_ne hs hm j σ), d.level_gradient_remainder_eq, mul_add]
      dsimp only [V, W, b]
      rw [← mul_assoc, mixed_quarter_signed_weight]
      simp only [mixedLevelCosWeight, mixedQuarterTimeWeight]
      ring
    · simp only [levelIntegral_eq_setIntegral hs.1 hs.2]
      dsimp only [G]
      rw [integral_const_mul, integral_sub (hn hs) (ht hs)]
  choose N hN hI hL using fun j σ ↦ mixed_quarter_gradient_remainder_limit d j σ
  let U := {s | ¬P s} ∪ ⋃ j, ⋃ σ, N j σ
  have hU : volume U = 0 := measure_union_null hp
    (measure_iUnion_null fun j ↦ measure_iUnion_null (hN j))
  let 𝓕 := 𝓝[Ioo 0 1 \ U] (0 : ℝ)
  have hf (j : Fin 2) (σ : Bool) : 𝓕 ≤ 𝓝[Ioo 0 1 \ N j σ] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inr
      (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨σ, h⟩⟩))⟩)
  have hi : ∀ᶠ s in 𝓕, ∀ (j : Fin 2) (σ : Bool),
      IntegrableOn (W j σ s) (mixedLevelInterval s) :=
    eventually_all.2 (fun j ↦ eventually_all.2 (fun σ ↦ hf j σ (hI j σ)))
  have hP : ∀ᶠ s in 𝓕, s ∈ Ioo (0 : ℝ) 1 ∧ P s := by
    filter_upwards [(self_mem_nhdsWithin : Ioo 0 1 \ U ∈ 𝓕)] with s hs
    exact ⟨hs.1, not_not.mp (fun h ↦ hs.2 (Or.inl h))⟩
  have hv : ∀ᶠ s in 𝓕, ∀ (j : Fin 2) (σ : Bool),
      IntegrableOn (V j σ s) (mixedLevelInterval s) := by
    filter_upwards [hi, hP] with s hw ⟨hs, hp⟩ j σ
    obtain ⟨hF, he⟩ := (hp hs).1 j σ
    refine (((hF.sub (hw j σ)).const_mul (b j)).congr ?_)
    filter_upwards [he] with a ha
    change b j * (F j σ s a - W j σ s a) = V j σ s a
    rw [ha]
    dsimp only [b]
    split_ifs <;> ring
  obtain ⟨M, hM, hm⟩ := mixed_level_actual_mass_limit d ⟨U, hU, hv⟩
  refine ⟨U ∪ M, measure_union_null hU hM, ?_⟩
  let 𝓖 := 𝓝[Ioo 0 1 \ (U ∪ M)] (0 : ℝ)
  have hgu : 𝓖 ≤ 𝓕 := nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inl h)⟩)
  have hgm : 𝓖 ≤ 𝓝[Ioo 0 1 \ M] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inr h)⟩)
  have hl := tendsto_finsetSum Finset.univ fun j _ ↦
    tendsto_finsetSum Finset.univ fun σ _ ↦ (hL j σ).mono_left (hgu.trans (hf j σ))
  have hl' : (∑ j : Fin 2, ∑ σ : Bool,
      if j = 0 then ∫ a in Jside, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a else 0) =
      ∑ σ : Bool, ∫ a in Jside, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a := by
    rw [Fin.sum_univ_two]
    simp
  rw [hl'] at hl
  apply ((hm.mono_left hgm).add hl).congr'
  filter_upwards [hgu hi, hgu hv, hgu hP] with s hw hv ⟨hs, hp⟩
  rw [← (hp hs).2, mixed_levelIntegral_eq_signed_quarters hs G (fun j σ ↦ ((hp hs).1 j σ).1)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ ↦ ?_)
  rw [← integral_add ((hv j σ).const_mul (b j)) (hw j σ)]
  exact integral_congr_ae (((hp hs).1 j σ).2.symm)

end NoEmbeddedEigenvalues
