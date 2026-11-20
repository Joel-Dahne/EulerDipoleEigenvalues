import NoEmbeddedEigenvalues.MixedLevelOrbit
import NoEmbeddedEigenvalues.MixedLevelDensity
import NoEmbeddedEigenvalues.MixedRellich
import NoEmbeddedEigenvalues.WeightedBoundary

/-! # The finite remainder terms on mixed quarter graphs -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real
open scoped Topology ComplexConjugate ENNReal

local notation "c" => (π / 2)
local notation "Jside" => (Ioo (-c) c)
local notation "νside" => (volume.restrict Jside)
local notation "Plane" => (ℝ × ℝ)

/-- A point on the side of a signed quarter, in its straight parameter. -/
def mixedQuarterSidePoint (j : Fin 2) (σ : Bool) (a : ℝ) : Plane :=
  traceSideCoords j (a, cellEdgeNormal σ)

/-- The regular time weight multiplied by the Dirichlet cosine. -/
def mixedLevelCosWeight (j : Fin 2) (σ : Bool) (s a : ℝ) : ℝ :=
  cos (mixedQuarterPoint j σ s a).1 / √(cos a ^ 2 - s ^ 2)

private theorem point_measurable (j : Fin 2) (σ : Bool) (s : ℝ) :
    Measurable (mixedQuarterPoint j σ s) := by
  have h : Measurable (quarterHeight s) := by unfold quarterHeight; fun_prop
  have hh : Measurable (mixedQuarterHeight σ s) := by
    cases σ
    · exact h.neg
    · exact h
  fin_cases j
  · exact measurable_id.prodMk hh
  · exact hh.prodMk measurable_id

private theorem point_limit (j : Fin 2) (σ : Bool) {a : ℝ} (ha : a ∈ Jside) :
    Tendsto (fun s ↦ mixedQuarterPoint j σ s a) (𝓝[>] 0) (𝓝 (mixedQuarterSidePoint j σ a)) := by
  have ht := (mixed_quarter_signed_height_tendsto σ ha).mono_right nhdsWithin_le_nhds
  fin_cases j
  · exact tendsto_const_nhds.prodMk_nhds ht
  · exact ht.prodMk_nhds tendsto_const_nhds

private theorem cosWeight_bound (j : Fin 2) (σ : Bool) {s a : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (ha : a ∈ mixedLevelInterval s) :
    ‖mixedLevelCosWeight j σ s a‖ ≤ 2 := by
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have hq := mixed_quarter_graph_mem hs' ha
  have hh := cos_pos_of_mem_Ioo hq.1.1
  have hq' : cos (mixedQuarterPoint j σ s a).1 ∈ Icc 0 (cos a) := by
    fin_cases j
    · exact ⟨hh.le, le_rfl⟩
    · change cos (mixedQuarterHeight σ s a) ∈ _
      cases σ <;>
        simpa only [mixedQuarterHeight, Bool.false_eq_true, ite_false, ite_true, cos_neg] using
          (show cos (quarterHeight s a) ∈ Icc 0 (cos a) from ⟨hq.2.1.le, hq.2.2⟩)
  have hW := mixed_quarter_weight_bound hs ha
  rw [mixedLevelCosWeight, Real.norm_eq_abs, abs_div, abs_of_nonneg hq'.1, abs_of_pos hW.1]
  calc
    _ ≤ cos a / √(cos a ^ 2 - s ^ 2) := div_le_div_of_nonneg_right hq'.2 hW.1.le
    _ = cos a * (1 / √(cos a ^ 2 - s ^ 2)) := by ring
    _ ≤ cos a * (2 / cos a) := mul_le_mul_of_nonneg_left hW.2 hh.le
    _ = _ := by field_simp

private theorem cosWeight_limit (j : Fin 2) (σ : Bool) {a : ℝ} (ha : a ∈ Jside) :
    Tendsto (fun s ↦ mixedLevelCosWeight j σ s a) (𝓝[>] 0) (𝓝 (if j = 0 then 1 else 0)) := by
  have hp := point_limit j σ ha
  have hD : Tendsto (fun s : ℝ ↦ √(cos a ^ 2 - s ^ 2)) (𝓝[>] 0) (𝓝 (cos a)) := by
    have hc : ContinuousAt (fun s : ℝ ↦ √(cos a ^ 2 - s ^ 2)) 0 := by fun_prop
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, sqrt_sq (cos_pos_of_mem_Ioo ha).le]
      using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hp' := (continuous_fst.continuousAt (x := mixedQuarterSidePoint j σ a)).tendsto.comp hp
  have h := (continuous_cos.continuousAt.tendsto.comp hp').div hD
    (cos_pos_of_mem_Ioo ha).ne'
  change Tendsto (fun s ↦ mixedLevelCosWeight j σ s a) _ _ at h
  fin_cases j
  · change Tendsto (fun s ↦ mixedLevelCosWeight 0 σ s a) _ (𝓝 (cos a / cos a)) at h
    simpa using (show Tendsto (fun s ↦ mixedLevelCosWeight 0 σ s a) _ (𝓝 1) from by
      simpa only [div_self (cos_pos_of_mem_Ioo ha).ne'] using h)
  · change Tendsto (fun s ↦ mixedLevelCosWeight 1 σ s a) _ (𝓝 (cos (cellEdgeNormal σ) / cos a)) at h
    change Tendsto (fun s ↦ mixedLevelCosWeight 1 σ s a) _ (𝓝 0)
    cases σ <;> simpa [cellEdgeNormal, neg_div, cos_neg] using h

private theorem side_denom_ne (j : Fin 2) (σ : Bool) {a : ℝ} (ha : a ∈ Jside) :
    mixedLevelR (mixedQuarterSidePoint j σ a) ^ 2 + mixedLevelS (mixedQuarterSidePoint j σ a) ^ 2 ≠ 0 := by
  have hc := (cos_pos_of_mem_Ioo ha).ne'
  fin_cases j <;> cases σ <;>
    simp [mixedLevelR, mixedLevelS, mixedQuarterSidePoint, traceSideCoords, cellEdgeNormal, neg_div, hc]

set_option maxHeartbeats 600000 in
-- Elaborating the specialized ACL limit and the two integral sum rewrites exceeds the default.
/-- Any finite quadratic form in the three weak fields can be restricted
to the moving graph after its time weight has been absorbed by the
Dirichlet cosine. Its limit uses only the canonical traces. -/
private theorem mixed_quarter_cosine_form_limit {ω : L2} (d : MixedQuotientData ω)
    (j : Fin 2) (σ : Bool) {ι : Type*} [Fintype ι]
    (i l : ι → Option (Fin 2)) (B : ι → Plane → ℝ) (C : ι → ℝ)
    (hm : ∀ r, Measurable (B r)) (hb : ∀ r q, ‖B r q‖ ≤ C r)
    (hc : ∀ r a, a ∈ Jside → ContinuousAt (B r) (mixedQuarterSidePoint j σ a)) :
    ∃ N : Set ℝ, volume N = 0 ∧
      let W := fun s a ↦ mixedLevelCosWeight j σ s a *
        ∑ r, B r (mixedQuarterPoint j σ s a) *
          (d.levelField (i r) (mixedQuarterPoint j σ s a) *
            conj (d.levelField (l r) (mixedQuarterPoint j σ s a))).re
      let T := fun a ↦ (if j = 0 then 1 else 0) *
        ∑ r, B r (mixedQuarterSidePoint j σ a) * (d.levelTrace j σ (i r) a *
          conj (d.levelTrace j σ (l r) a)).re
      (∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, IntegrableOn (W s) (mixedLevelInterval s)) ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W s a) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 (∫ a in Jside, T a)) := by
  classical
  obtain ⟨N, hN, H⟩ := mixed_quarter_weak_pair_limit d j σ
  refine ⟨N, hN, ?_⟩
  let K := fun r s a ↦ mixedLevelCosWeight j σ s a * B r (mixedQuarterPoint j σ s a)
  let k := fun r a ↦ (if j = 0 then 1 else 0) * B r (mixedQuarterSidePoint j σ a)
  let W := fun r s a ↦ K r s a * (d.levelField (i r) (mixedQuarterPoint j σ s a) *
    conj (d.levelField (l r) (mixedQuarterPoint j σ s a))).re
  let T := fun r a ↦ k r a * (d.levelTrace j σ (i r) a * conj (d.levelTrace j σ (l r) a)).re
  have hH (r : ι) :
      (∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, IntegrableOn (W r s) (mixedLevelInterval s)) ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W r s a) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 (∫ a in Jside, T r a)) := by
    refine H (i r) (l r) _ _ (2 * C r) ?_ ?_ ?_
    · refine Eventually.of_forall fun s ↦ ?_
      have hq := point_measurable j σ s
      have hw : Measurable (mixedLevelCosWeight j σ s) :=
        (continuous_cos.measurable.comp hq.fst).div (by fun_prop)
      exact (hw.mul ((hm r).comp hq)).aestronglyMeasurable
    · filter_upwards [(Ioo_mem_nhdsGT (by norm_num : 0 < (1 / 2 : ℝ)) :
          Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] 0)] with s hs a ha
      exact (norm_mul _ _).trans_le (mul_le_mul (cosWeight_bound j σ hs ha)
        (hb r _) (norm_nonneg _) (by norm_num))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      exact (cosWeight_limit j σ ha).mul ((hc r a ha).tendsto.comp (point_limit j σ ha))
  have he : ∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, ∀ r, IntegrableOn (W r s) (mixedLevelInterval s) :=
    eventually_all.2 (fun r ↦ (hH r).1)
  have ti (r : ι) : Integrable (T r) νside := by
    have hT (m : Option (Fin 2)) : MemLp (d.levelTrace j σ m) 2 νside := by
      have h := mixed_quotient_side_traces d j σ
      have he : mixedEdgeValue (1 - j) σ d.phi =
          (fun a ↦ d.phi (traceSideCoords j (a, cellEdgeNormal σ))) := by
        fin_cases j <;> rfl
      cases m with
      | none =>
        have hT := h.1.continuousOn
        rw [uIcc_of_le (by linarith [pi_pos])] at hT
        have hM := memLp_top_of_continuousOn_Icc hT
        rw [MixedQuotientData.levelTrace, he]
        rw [neg_div] at hM
        exact (hM.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ⊤)).mono_measure
          (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
      | some m =>
        by_cases hm : m = j
        · simpa only [MixedQuotientData.levelTrace, hm, ite_true, he, neg_div] using h.2.1
        · simp [MixedQuotientData.levelTrace, hm]
    have hconj : MemLp (fun a ↦ conj (d.levelTrace j σ (l r) a)) 2 νside :=
      (hT (l r)).congr_norm
        (Complex.continuous_conj.comp_aestronglyMeasurable (hT (l r)).aestronglyMeasurable)
        (.of_forall fun _ ↦ (Complex.norm_conj _).symm)
    have hi := Complex.reCLM.integrable_comp ((hT (i r)).integrable_mul hconj)
    refine hi.bdd_mul ?_ (show ∀ᵐ a ∂νside, ‖k r a‖ ≤ C r from
      .of_forall fun a ↦ ?_)
    · have hq : Continuous (mixedQuarterSidePoint j σ) := by
        fin_cases j
        · exact continuous_id.prodMk continuous_const
        · exact continuous_const.prodMk continuous_id
      exact (measurable_const.mul ((hm r).comp hq.measurable)).aestronglyMeasurable
    · dsimp only [k]
      have h0 : 0 ≤ C r := (norm_nonneg _).trans (hb r (mixedQuarterSidePoint j σ a))
      split_ifs
      · simpa only [one_mul] using hb r (mixedQuarterSidePoint j σ a)
      · simpa only [zero_mul, norm_zero] using h0
  have hsum (s a : ℝ) : ∑ r, W r s a = mixedLevelCosWeight j σ s a *
      ∑ r, B r (mixedQuarterPoint j σ s a) *
        (d.levelField (i r) (mixedQuarterPoint j σ s a) *
          conj (d.levelField (l r) (mixedQuarterPoint j σ s a))).re := by
    simp only [W, K, Finset.mul_sum, mul_assoc]
  have ht a : ∑ r, T r a = (if j = 0 then 1 else 0) *
      ∑ r, B r (mixedQuarterSidePoint j σ a) *
        (d.levelTrace j σ (i r) a * conj (d.levelTrace j σ (l r) a)).re := by
    simp only [T, k, Finset.mul_sum, mul_assoc]
  simp only [← hsum, ← ht]
  refine ⟨he.mono (fun s hs ↦ integrable_finsetSum _ (fun r _ ↦ hs r)), ?_⟩
  rw [integral_finsetSum _ (fun r _ ↦ ti r)]
  apply (tendsto_finsetSum _ fun r _ ↦ (hH r).2).congr'
  filter_upwards [he] with s hs
  exact (integral_finsetSum _ fun r _ ↦ hs r).symm

private theorem sign_continuousAt {q : Plane}
    (hq : mixedLevelR q ^ 2 + mixedLevelS q ^ 2 ≠ 0) :
    ContinuousAt mixedLevelSign q := by
  unfold mixedLevelSign
  exact ContinuousAt.div (by unfold mixedLevelR mixedLevelS; fun_prop)
    (by unfold mixedLevelR mixedLevelS; fun_prop) hq

private theorem cross_continuousAt {q : Plane}
    (hq : mixedLevelR q ^ 2 + mixedLevelS q ^ 2 ≠ 0) :
    ContinuousAt mixedLevelCross q := by
  unfold mixedLevelCross
  exact ContinuousAt.div (by unfold mixedLevelR mixedLevelS; fun_prop)
    (by unfold mixedLevelR mixedLevelS; fun_prop) hq

private theorem sign_bound (q : Plane) : ‖mixedLevelSign q‖ ≤ 1 :=
  mixed_level_frame_norm_le _ _

private def gradI : Fin 6 → Option (Fin 2) :=
  ![none, some 0, some 1, some 0, some 0, none]

private def gradJ : Fin 6 → Option (Fin 2) :=
  ![none, some 0, some 1, none, some 1, some 1]

private def gradB (r : Fin 6) (q : Plane) : ℝ :=
  ![mixedLevelSign q * cos q.1, -(mixedLevelSign q * cos q.1),
    mixedLevelSign q * cos q.1, 2 * mixedLevelSign q * sin q.1,
    mixedLevelCross q * cos q.1, -(mixedLevelCross q * sin q.1)] r

private def firstI : Fin 3 → Option (Fin 2) := ![none, some 0, some 1]
private def firstB (r : Fin 3) (q : Plane) : ℝ :=
  ![-(mixedLevelS q * sin q.1), mixedLevelS q * cos q.1, mixedLevelR q * cos q.1] r

private theorem gradB_bound (r : Fin 6) (q : Plane) : ‖gradB r q‖ ≤ 2 := by
  have hs := sign_bound q
  have hx := mixed_level_cross_norm_le q
  have hc : ‖cos q.1‖ ≤ 1 := abs_cos_le_one _
  have hu : ‖sin q.1‖ ≤ 1 := abs_sin_le_one _
  have h₁ := mul_le_mul hs hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h₂ := mul_le_mul hs hu (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h₃ := mul_le_mul hx hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h₄ := mul_le_mul hx hu (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Real.norm_eq_abs] at h₁ h₂ h₃ h₄
  fin_cases r <;> simp [gradB, norm_mul] <;> linarith

private theorem firstB_bound (r : Fin 3) (q : Plane) : ‖firstB r q‖ ≤ 1 := by
  have hc (a : ℝ) : ‖cos a‖ ≤ 1 := abs_cos_le_one _
  have hu (a : ℝ) : ‖sin a‖ ≤ 1 := abs_sin_le_one _
  have hh (x y : ℝ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  fin_cases r
  · change ‖-(mixedLevelS q * sin q.1)‖ ≤ 1
    rw [norm_neg]
    exact hh _ _ (hh _ _ (hc _) (hu _)) (hu _)
  · exact hh _ _ (hh _ _ (hc _) (hu _)) (hc _)
  · exact hh _ _ (hh _ _ (hc _) (hu _)) (hc _)

/-- The first-order term in the geometric level density after absorbing
the time weight by the Dirichlet cosine. -/
def MixedQuotientData.levelFirstRemainder {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  ∑ r, firstB r q * (d.levelField (firstI r) q * conj (d.phi q)).re

/-- The part of the signed gradient other than the leading mass, after
factoring out the Dirichlet cosine. -/
def MixedQuotientData.levelGradientRemainder {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  ∑ r, gradB r q * (d.levelField (gradI r) q * conj (d.levelField (gradJ r) q)).re

theorem MixedQuotientData.level_first_remainder_eq {ω : L2} (d : MixedQuotientData ω) (q : Plane) :
    (((cos q.1 : ℂ) * d.phi q) * conj
      ((mixedLevelS q : ℂ) * d.streamA q + (mixedLevelR q : ℂ) * d.streamB q)).re =
        cos q.1 * d.levelFirstRemainder q := by
  simp only [MixedQuotientData.levelFirstRemainder, Fin.sum_univ_succ, Fin.sum_univ_zero,
    firstI, firstB, Matrix.cons_val_zero, Matrix.cons_val_succ, MixedQuotientData.levelField,
    MixedQuotientData.streamA, MixedQuotientData.streamB, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring

theorem MixedQuotientData.level_gradient_remainder_eq {ω : L2} (d : MixedQuotientData ω)
    (q : Plane) :
    -mixedLevelSign q * (‖d.streamA q‖ ^ 2 - ‖d.streamB q‖ ^ 2) +
        mixedLevelCross q * (d.streamA q * conj (d.streamB q)).re =
      -mixedLevelSign q * ‖d.phi q‖ ^ 2 + cos q.1 * d.levelGradientRemainder q := by
  rw [d.level_gradient_split]
  simp only [MixedQuotientData.levelGradientRemainder, Fin.sum_univ_succ, Fin.sum_univ_zero,
    gradI, gradJ, gradB, Matrix.cons_val_zero, Matrix.cons_val_succ, MixedQuotientData.levelField,
    MixedQuotientData.streamA, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem side_sign_cross (σ : Bool) {a : ℝ} (ha : a ∈ Jside) :
    mixedLevelSign (mixedQuarterSidePoint 0 σ a) = 1 ∧ mixedLevelCross (mixedQuarterSidePoint 0 σ a) = 0 := by
  have hc := (cos_pos_of_mem_Ioo ha).ne'
  cases σ <;> simp [mixedLevelSign, mixedLevelCross, mixedLevelR, mixedLevelS, mixedQuarterSidePoint,
    traceSideCoords, cellEdgeNormal, neg_div, hc]

private theorem first_trace_eq_zero {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool)
    (a : ℝ) :
    (if j = 0 then 1 else 0) *
      ∑ r, firstB r (mixedQuarterSidePoint j σ a) *
        (d.levelTrace j σ (firstI r) a * conj (d.levelTrace j σ none a)).re = 0 := by
  by_cases hj : j = 0
  · subst j
    cases σ <;> simp [mixedQuarterSidePoint, firstB, firstI, Fin.sum_univ_succ, traceSideCoords,
      cellEdgeNormal, neg_div, mixedLevelS, MixedQuotientData.levelTrace]
  · simp [hj]

private theorem grad_trace_eval {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool)
    {a : ℝ} (ha : a ∈ Jside) :
    (if j = 0 then 1 else 0) *
      ∑ r, gradB r (mixedQuarterSidePoint j σ a) *
        (d.levelTrace j σ (gradI r) a * conj (d.levelTrace j σ (gradJ r) a)).re =
    if j = 0 then mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a else 0 := by
  by_cases hj : j = 0
  · subst j
    obtain ⟨hS, hX⟩ := side_sign_cross σ ha
    change mixedLevelSign (a, cellEdgeNormal σ) = 1 at hS
    change mixedLevelCross (a, cellEdgeNormal σ) = 0 at hX
    simp [gradB, gradI, gradJ, Fin.sum_univ_succ, MixedQuotientData.levelTrace, hS, hX,
      mixedQuarterSidePoint, traceSideCoords, mixedRellichEdgeDensity, Complex.sq_norm, Complex.normSq_apply]
    ring
  · simp [hj]

/-- On every quarter, the first-order density is integrable for the
level time measure, and its integral tends to zero. -/
theorem mixed_quarter_first_limit {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool) :
    ∃ N : Set ℝ, volume N = 0 ∧
      let W := fun s a ↦ mixedLevelCosWeight j σ s a *
        d.levelFirstRemainder (mixedQuarterPoint j σ s a)
      (∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, IntegrableOn (W s) (mixedLevelInterval s)) ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W s a) (𝓝[Ioo 0 1 \ N] 0) (𝓝 0) := by
  obtain ⟨N, hN, H, L⟩ := mixed_quarter_cosine_form_limit d j σ firstI (fun _ ↦ none)
    firstB (fun _ ↦ 1)
    (fun r ↦ by
      fin_cases r <;> unfold firstB mixedLevelR mixedLevelS <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, measurable_neg_iff] <;> fun_prop)
    firstB_bound
    (fun r a _ ↦ by
      fin_cases r <;> unfold firstB mixedLevelR mixedLevelS <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop)
  refine ⟨N, hN, H, ?_⟩
  simpa only [first_trace_eq_zero, integral_zero, MixedQuotientData.levelFirstRemainder,
    MixedQuotientData.levelField] using L

/-- The nonsingular signed gradient remainder tends to the corrected
Neumann flux. Its Dirichlet limits vanish. -/
theorem mixed_quarter_gradient_remainder_limit {ω : L2} (d : MixedQuotientData ω)
    (j : Fin 2) (σ : Bool) :
    ∃ N : Set ℝ, volume N = 0 ∧
      let W := fun s a ↦ mixedLevelCosWeight j σ s a *
        d.levelGradientRemainder (mixedQuarterPoint j σ s a)
      (∀ᶠ s in 𝓝[Ioo 0 1 \ N] 0, IntegrableOn (W s) (mixedLevelInterval s)) ∧
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W s a) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 (if j = 0 then ∫ a in Jside, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a
          else 0)) := by
  have hm (r : Fin 6) : Measurable (gradB r) := by
    fin_cases r <;> unfold gradB mixedLevelSign mixedLevelCross mixedLevelS mixedLevelR <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, measurable_neg_iff] <;> fun_prop
  have hc (r : Fin 6) (a : ℝ) (ha : a ∈ Jside) : ContinuousAt (gradB r) (mixedQuarterSidePoint j σ a) := by
    have hs := sign_continuousAt (side_denom_ne j σ ha)
    have hx := cross_continuousAt (side_denom_ne j σ ha)
    have hc : ContinuousAt (fun q : Plane ↦ cos q.1) (mixedQuarterSidePoint j σ a) := by fun_prop
    have hu : ContinuousAt (fun q : Plane ↦ sin q.1) (mixedQuarterSidePoint j σ a) := by fun_prop
    fin_cases r
    · exact hs.mul hc
    · exact (hs.mul hc).neg
    · exact hs.mul hc
    · exact (continuousAt_const.mul hs).mul hu
    · exact hx.mul hc
    · exact (hx.mul hu).neg
  obtain ⟨N, hN, H, L⟩ := mixed_quarter_cosine_form_limit d j σ gradI gradJ
    gradB (fun _ ↦ 2) hm gradB_bound hc
  refine ⟨N, hN, H, ?_⟩
  unfold MixedQuotientData.levelGradientRemainder
  rw [← show (∫ a in Jside,
      if j = 0 then mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a else 0) =
      (if j = 0 then ∫ a in Jside, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a else 0) by
    split_ifs <;> simp,
    ← setIntegral_congr_fun measurableSet_Ioo (fun a ha ↦ grad_trace_eval d j σ ha)]
  exact L

/-- The full first-order integral tends to zero, after discarding a null
set of levels for the weak representative identities. -/
theorem mixed_level_first_limit {ω : L2} (d : MixedQuotientData ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun s ↦ levelIntegral s (fun p ↦
        gradNorm p * (streamLift ω p * conj (streamNormal ω p)).re))
        (𝓝[Ioo 0 1 \ N] 0) (𝓝 0) := by
  let F := fun p ↦ gradNorm p * (streamLift ω p * conj (streamNormal ω p)).re
  let W := fun j σ s a ↦ mixedLevelCosWeight j σ s a *
    d.levelFirstRemainder (mixedQuarterPoint j σ s a)
  choose N hN hI hL using fun j σ ↦ mixed_quarter_first_limit d j σ
  let P := fun s ↦ s ∈ Ioo (0 : ℝ) 1 → ∀ (j : Fin 2) (σ : Bool),
    (fun a ↦ mixedQuarterTimeWeight s a * F (diagInv (mixedQuarterPoint j σ s a)))
      =ᵐ[volume.restrict (mixedLevelInterval s)] W j σ s
  have hp : ∀ᵐ s ∂volume, P s := by
    filter_upwards [ae_mixedQuarterPoint_of_ae d.level_first_order_ae] with s hs h j σ
    filter_upwards [hs h j σ] with a ha
    rw [show F (diagInv (mixedQuarterPoint j σ s a)) = _ from ha, d.level_first_remainder_eq]
    unfold mixedQuarterTimeWeight W mixedLevelCosWeight
    ring
  let U := {s | ¬P s} ∪ ⋃ j, ⋃ σ, N j σ
  have hU : volume U = 0 := measure_union_null hp
    (measure_iUnion_null fun j ↦ measure_iUnion_null (hN j))
  refine ⟨U, hU, ?_⟩
  let 𝓕 := 𝓝[Ioo 0 1 \ U] (0 : ℝ)
  have hf (j : Fin 2) (σ : Bool) : 𝓕 ≤ 𝓝[Ioo 0 1 \ N j σ] 0 :=
    nhdsWithin_mono _ (fun s hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inr
      (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨σ, h⟩⟩))⟩)
  have hi : ∀ᶠ s in 𝓕, ∀ (j : Fin 2) (σ : Bool),
      IntegrableOn (W j σ s) (mixedLevelInterval s) :=
    eventually_all.2 (fun j ↦ eventually_all.2 (fun σ ↦ hf j σ (hI j σ)))
  have hl (j : Fin 2) (σ : Bool) :
      Tendsto (fun s ↦ ∫ a in mixedLevelInterval s, W j σ s a) 𝓕 (𝓝 0) :=
    (hL j σ).mono_left (hf j σ)
  have h := tendsto_finsetSum Finset.univ fun j _ ↦
    tendsto_finsetSum Finset.univ fun σ _ ↦ hl j σ
  rw [Finset.sum_const_zero, Finset.sum_const_zero] at h
  apply h.congr'
  filter_upwards [hi, (self_mem_nhdsWithin : Ioo 0 1 \ U ∈ 𝓕)] with s hsi hs
  have hP : P s := not_not.1 (fun hp ↦ hs.2 (Or.inl hp))
  rw [mixed_levelIntegral_eq_signed_quarters hs.1 F
    (fun j σ ↦ (hsi j σ).congr (hP hs.1 j σ).symm)]
  exact Finset.sum_congr rfl (fun j _ ↦ Finset.sum_congr rfl
    (fun σ _ ↦ integral_congr_ae (hP hs.1 j σ).symm))

/-- The time-weighted signed projection is negative on a Neumann
quarter and positive on a Dirichlet quarter, with the same exact model
weight in the two charts. -/
theorem mixed_quarter_signed_weight (j : Fin 2) (σ : Bool) (s a : ℝ) :
    mixedQuarterTimeWeight s a * (-mixedLevelSign (mixedQuarterPoint j σ s a)) =
      (if j = 0 then -1 else 1) * mixedLevelModelWeight s a := by
  have hn (b : ℝ) : mixedLevelSign (a, -b) = mixedLevelSign (a, b) := by
    simp only [mixedLevelSign, mixedLevelR, mixedLevelS, cos_neg, sin_neg, mul_neg, neg_sq]
  have hsw (q : Plane) : mixedLevelSign q.swap = -mixedLevelSign q := mixed_level_frame_swap q
  let b := quarterHeight s a
  have hm : mixedLevelModelWeight s a = mixedLevelSign (a, b) * mixedQuarterTimeWeight s a :=
    rfl
  rw [hm]
  fin_cases j
  · change mixedQuarterTimeWeight s a * (-mixedLevelSign (a, mixedQuarterHeight σ s a)) =
      -1 * (mixedLevelSign (a, b) * mixedQuarterTimeWeight s a)
    cases σ
    · change _ * (-mixedLevelSign (a, -b)) = _
      rw [hn]
      ring
    · change _ * (-mixedLevelSign (a, b)) = _
      ring
  · change mixedQuarterTimeWeight s a * (-mixedLevelSign (a, mixedQuarterHeight σ s a).swap) =
      1 * (mixedLevelSign (a, b) * mixedQuarterTimeWeight s a)
    rw [hsw, neg_neg]
    cases σ
    · change _ * mixedLevelSign (a, -b) = _
      rw [hn]
      ring
    · change _ * mixedLevelSign (a, b) = _
      ring

end NoEmbeddedEigenvalues
