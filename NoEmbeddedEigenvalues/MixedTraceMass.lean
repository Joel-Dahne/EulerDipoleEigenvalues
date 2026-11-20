import NoEmbeddedEigenvalues.MixedRellich
import NoEmbeddedEigenvalues.MixedEdgeDefect
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The trace-mass divergence with a regularized denominator -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ
local notation "halfPi" => (π / 2)
local notation "J" => (Ioo (-halfPi) halfPi)
local notation "ν" => (volume.restrict J)

private def coord (j : Fin 2) (q : Plane) : ℝ := if j = 0 then q.1 else q.2
private def den (q : Plane) : ℝ := cos q.1 + cos q.2

private theorem openCell_eq : mixedOpenCell = J ×ˢ J := by
  simp only [mixedOpenCell, neg_div]

private theorem cos_pos_cell {q : Plane} (hq : q ∈ mixedOpenCell) :
    0 < cos q.1 ∧ 0 < cos q.2 := by
  rw [openCell_eq] at hq
  exact ⟨cos_pos_of_mem_Ioo hq.1, cos_pos_of_mem_Ioo hq.2⟩

private def field (ε : ℝ) (t x : ℝ) : ℝ := sin t / (cos t + cos x + ε)

private def fieldDiff (ε : ℝ) (t x : ℝ) : ℝ :=
  cos t / (cos t + cos x + ε) + sin t ^ 2 / (cos t + cos x + ε) ^ 2

private theorem field_hasDerivAt (ε t x : ℝ) (h : cos t + cos x + ε ≠ 0) :
    HasDerivAt (fun s ↦ field ε s x) (fieldDiff ε t x) t := by
  apply ((hasDerivAt_sin t).div (((hasDerivAt_cos t).add_const (cos x)).add_const ε) h).congr_deriv
  unfold fieldDiff
  field_simp
  ring

private def pair {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (q : Plane) : ℝ :=
  2 * (d.jet [j] q * conj (d.phi q)).re

private def bulk {ω : L2} (d : MixedQuotientData ω) (ε : ℝ) (j : Fin 2) (q : Plane) : ℝ :=
  field ε (coord j q) (coord (1 - j) q) * pair d j q +
    fieldDiff ε (coord j q) (coord (1 - j) q) * ‖d.phi q‖ ^ 2

private theorem pair_integrable {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) :
    IntegrableOn (pair d j) mixedOpenCell := by
  have hφ := d.h2.memLp
  have hC := hφ.congr_norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hφ.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ (Complex.norm_conj (d.phi x)).symm)
  have hD := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo) d.weakJet [j] (by simp)
  exact (Complex.reCLM.integrable_comp (hD.integrable_mul hC)).const_mul 2

private theorem mass_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (fun q ↦ ‖d.phi q‖ ^ 2) mixedOpenCell :=
  d.h2.memLp.norm.integrable_sq

private theorem bulk_integrable {ω : L2} (d : MixedQuotientData ω) {ε : ℝ}
    (hε : 0 < ε) (j : Fin 2) : IntegrableOn (bulk d ε j) mixedOpenCell := by
  let t := coord j
  let x := coord (1 - j)
  have ht : Measurable t := by
    fin_cases j
    · exact measurable_fst
    · exact measurable_snd
  have hx : Measurable x := by
    fin_cases j
    · exact measurable_snd
    · exact measurable_fst
  have hmem := ae_restrict_mem (μ := volume) (s := mixedOpenCell)
    (measurableSet_Ioo.prod measurableSet_Ioo)
  have hden (q : Plane) (hq : q ∈ mixedOpenCell) : ε ≤ cos (t q) + cos (x q) + ε := by
    obtain ⟨h, k⟩ := cos_pos_cell hq
    fin_cases j
    · change ε ≤ cos q.1 + cos q.2 + ε
      linarith
    · change ε ≤ cos q.2 + cos q.1 + ε
      linarith
  have hf : IntegrableOn (fun q ↦ field ε (t q) (x q) * pair d j q) mixedOpenCell := by
    refine (pair_integrable d j).bdd_mul (c := ε⁻¹)
      (show Measurable (fun q ↦ field ε (t q) (x q)) from by
        unfold field
        fun_prop).aestronglyMeasurable ?_
    filter_upwards [hmem] with q hq
    rw [field, Real.norm_eq_abs, abs_div, abs_of_pos (hε.trans_le (hden q hq)),
      ← one_div ε]
    exact (div_le_div_of_nonneg_right (abs_sin_le_one _) (hε.trans_le (hden q hq)).le).trans
      (div_le_div_of_nonneg_left zero_le_one hε (hden q hq))
  have hd : IntegrableOn (fun q ↦ fieldDiff ε (t q) (x q) * ‖d.phi q‖ ^ 2) mixedOpenCell := by
    refine (mass_integrable d).bdd_mul (c := 1 / ε + 1 / ε ^ 2)
      (show Measurable (fun q ↦ fieldDiff ε (t q) (x q)) from by
        unfold fieldDiff
        fun_prop).aestronglyMeasurable ?_
    filter_upwards [hmem] with q hq
    let z := cos (t q) + cos (x q) + ε
    have hz : 0 < z := hε.trans_le (hden q hq)
    change ‖cos (t q) / z + sin (t q) ^ 2 / z ^ 2‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hz]
      exact (div_le_div_of_nonneg_right (abs_cos_le_one _) hz.le).trans
        (div_le_div_of_nonneg_left zero_le_one hε (hden q hq))
    · rw [Real.norm_of_nonneg (by positivity)]
      exact (div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left zero_le_one (by positivity)
          (pow_le_pow_left₀ hε.le (hden q hq) 2))
  exact hf.add hd

private theorem bulk_section {ω : L2} (d : MixedQuotientData ω) {ε : ℝ} (hε : 0 < ε) (j : Fin 2) :
    ∀ᵐ x ∂ν, (∫ t in J, bulk d ε j (axisTraceChart j (x, t))) =
      (‖d.phi (axisTraceChart j (x, halfPi))‖ ^ 2 +
        ‖d.phi (axisTraceChart j (x, -halfPi))‖ ^ 2) / (cos x + ε) := by
  have hW := d.weakJet.2 [] (by decide) j
  rw [d.weakJet.1] at hW
  have hL := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo) d.weakJet [j] (by simp)
  have hsec := rellich_acl_sections j hW d.h2.memLp hL
    (fun σ ↦ mixedEdgeValue 1 σ d.phi) (fun _ σ ↦ (mixed_quotient_neumann_traces d σ).2.2.1)
  rw [neg_div] at hsec
  filter_upwards [hsec, ae_restrict_mem (μ := volume) (s := J) measurableSet_Ioo] with x H hx
  obtain ⟨F, hFac, _, hF⟩ := H
  let C := fun t ↦ axisTraceChart j (x, t)
  have hlr : -halfPi < halfPi := by linarith [pi_pos]
  have hC : Continuous C := by
    fin_cases j
    · exact continuous_id.prodMk continuous_const
    · exact continuous_const.prodMk continuous_id
  have hclosed : ∀ t ∈ Icc (-halfPi) halfPi, C t ∈ closure mixedOpenCell := by
    intro t ht
    rw [openCell_eq, closure_prod_eq, closure_Ioo hlr.ne]
    fin_cases j
    · exact ⟨ht, Ioo_subset_Icc_self hx⟩
    · exact ⟨Ioo_subset_Icc_self hx, ht⟩
  have hFc : ContinuousOn (d.phi ∘ C) (Icc (-halfPi) halfPi) :=
    d.continuous.comp hC.continuousOn hclosed
  have hFa : AbsolutelyContinuousOnInterval F (-halfPi) halfPi := by simpa only [neg_div] using hFac
  have hFc' := hFa.continuousOn
  rw [uIcc_of_le hlr.le] at hFc'
  have hEq : EqOn F (d.phi ∘ C) (Icc (-halfPi) halfPi) :=
    (Measure.eqOn_open_of_ae_eq (hF.mono fun _ h ↦ h.1) isOpen_Ioo
      (hFc'.mono Ioo_subset_Icc_self) (hFc.mono Ioo_subset_Icc_self)).of_subset_closure
      hFc' hFc Ioo_subset_Icc_self (closure_Ioo hlr.ne).ge
  have hden (t : ℝ) (ht : t ∈ Icc (-halfPi) halfPi) : 0 < cos t + cos x + ε := by
    have ht' := cos_nonneg_of_mem_Icc ht
    have hx' := cos_pos_of_mem_Ioo hx
    linarith
  have hct : ContDiffOn ℝ 1 (fun t ↦ field ε t x) (Icc (-halfPi) halfPi) := by
    unfold field
    exact contDiff_sin.contDiffOn.div
      ((contDiff_cos.add contDiff_const).add contDiff_const).contDiffOn
      (fun t ht ↦ (hden t ht).ne')
  let U := fun t ↦ field ε t x * ‖F t‖ ^ 2
  have hU : AbsolutelyContinuousOnInterval U (-halfPi) halfPi := by
    rw [← uIcc_of_le hlr.le] at hct
    have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval hFa
    have hs : AbsolutelyContinuousOnInterval (fun t ↦ ‖F t‖ * ‖F t‖) (-halfPi) halfPi :=
      hn.fun_mul hn
    have hw : AbsolutelyContinuousOnInterval (fun t ↦ field ε t x) (-halfPi) halfPi :=
      hct.absolutelyContinuousOnInterval
    simpa only [U, pow_two] using hw.fun_mul hs
  have hd : (fun t ↦ bulk d ε j (C t)) =ᵐ[ν] deriv U := by
    filter_upwards [hF, ae_restrict_mem (μ := volume) (s := J) measurableSet_Ioo] with t ht tm
    obtain ⟨hval, hder⟩ := ht
    change F t = d.phi (C t) at hval
    change HasDerivAt F (d.jet [j] (C t)) t at hder
    have hdF := hder.norm_sq
    simp only [real_inner_eq_re_inner, RCLike.inner_apply,
      show (RCLike.re : ℂ → ℝ) = Complex.re from rfl, hval] at hdF
    change HasDerivAt (fun s ↦ ‖F s‖ ^ 2) (pair d j (C t)) t at hdF
    have h : deriv U t = fieldDiff ε t x * ‖F t‖ ^ 2 + field ε t x * pair d j (C t) :=
      ((field_hasDerivAt ε t x (hden t (Ioo_subset_Icc_self tm)).ne').mul hdF).deriv
    change bulk d ε j (C t) = deriv U t
    rw [h]
    have h₁ : coord j (C t) = t := by fin_cases j <;> rfl
    have h₂ : coord (1 - j) (C t) = x := by fin_cases j <;> rfl
    simp only [bulk, h₁, h₂, hval]
    ring
  change (∫ t in J, bulk d ε j (C t)) = _
  rw [integral_congr_ae hd, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hlr.le, hU.integral_deriv_eq_sub]
  have hc : halfPi ∈ Icc (-halfPi) halfPi := right_mem_Icc.mpr hlr.le
  have hc' : -halfPi ∈ Icc (-halfPi) halfPi := left_mem_Icc.mpr hlr.le
  simp only [U, hEq hc, hEq hc', field, cos_pi_div_two, cos_neg, sin_neg,
    sin_pi_div_two, zero_add, Function.comp_apply, C]
  ring

private theorem edge_integrable {ω : L2} (d : MixedQuotientData ω)
    (j : Fin 2) (σ : Bool) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x ↦
      ‖d.phi (axisTraceChart j (x, cellEdgeNormal σ))‖ ^ 2 / (cos x + ε)) J := by
  have h := (mixed_quotient_side_traces d (1-j) σ).1.continuousOn
  have h' : ContinuousOn (fun x ↦ d.phi (axisTraceChart j (x, cellEdgeNormal σ)))
      (Icc (-halfPi) halfPi) := by
    rw [neg_div, uIcc_of_le (by linarith [pi_pos])] at h
    fin_cases j <;> exact h
  have hden (x : ℝ) (hx : x ∈ Icc (-halfPi) halfPi) : cos x + ε ≠ 0 :=
    (add_pos_of_nonneg_of_pos (cos_nonneg_of_mem_Icc hx) hε).ne'
  have hh := (h'.norm.pow 2).div (continuous_cos.add continuous_const).continuousOn hden
  exact hh.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem reg_bulk_eq {ω : L2} (d : MixedQuotientData ω) {q : Plane}
    (hq : q ∈ mixedOpenCell) {ε : ℝ} (hε : 0 ≤ ε) :
    bulk d ε 0 q - bulk d ε 1 q =
      den q / (den q + ε) * mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q +
        ε * (cos q.1 - cos q.2) / (den q + ε) ^ 2 * ‖d.phi q‖ ^ 2 := by
  have ⟨h, k⟩ := cos_pos_cell hq
  have hp : den q ≠ 0 := (add_pos h k).ne'
  have hp' : den q + ε ≠ 0 := (add_pos_of_pos_of_nonneg (add_pos h k) hε).ne'
  have hh : sin q.1 ^ 2 - sin q.2 ^ 2 = -(cos q.1 - cos q.2) * den q := by
    unfold den
    nlinarith only [sin_sq_add_cos_sq q.1, sin_sq_add_cos_sq q.2]
  have H : fieldDiff ε q.1 q.2 - fieldDiff ε q.2 q.1 =
      ε * (cos q.1 - cos q.2) / (den q + ε) ^ 2 := by
    unfold fieldDiff
    rw [add_comm (cos q.2) (cos q.1)]
    change cos q.1 / (den q + ε) + sin q.1 ^ 2 / (den q + ε) ^ 2 -
      (cos q.2 / (den q + ε) + sin q.2 ^ 2 / (den q + ε) ^ 2) = _
    rw [show ∀ a b c e : ℝ, a + b - (c + e) = a - c + (b - e) by intros; ring,
      ← sub_div, ← sub_div, hh]
    field_simp
    ring
  have G : mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q =
      (sin q.1 / den q) * pair d 0 q - (sin q.2 / den q) * pair d 1 q := by
    simp only [mixedTraceMassDensity, mixedFieldA, mixedFieldB, den, pair, sub_mul,
      Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  change field ε q.1 q.2 * pair d 0 q + fieldDiff ε q.1 q.2 * ‖d.phi q‖ ^ 2 -
    (field ε q.2 q.1 * pair d 1 q + fieldDiff ε q.2 q.1 * ‖d.phi q‖ ^ 2) = _
  rw [G, ← H]
  unfold field
  rw [add_comm (cos q.2) (cos q.1)]
  change sin q.1 / (den q + ε) * pair d 0 q + _ -
    (sin q.2 / (den q + ε) * pair d 1 q + _) = _
  field_simp
  ring

private theorem regularized_identity {ω : L2} (d : MixedQuotientData ω) {ε : ℝ} (hε : 0 < ε) :
    (∫ q in mixedOpenCell,
      den q / (den q + ε) * mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q +
        ε * (cos q.1 - cos q.2) / (den q + ε) ^ 2 * ‖d.phi q‖ ^ 2) =
      ∫ x in J, mixedEdgeMassDefect d.phi x / (cos x + ε) := by
  have h0 := bulk_integrable d hε 0
  have h1 := bulk_integrable d hε 1
  have hprod : Measure.prod ν ν = volume.restrict mixedOpenCell := by
    rw [openCell_eq, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have he : (fun q ↦ den q / (den q + ε) *
        mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q +
        ε * (cos q.1 - cos q.2) / (den q + ε) ^ 2 * ‖d.phi q‖ ^ 2) =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ bulk d ε 0 q - bulk d ε 1 q := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := mixedOpenCell)
      (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    exact (reg_bulk_eq d hq hε.le).symm
  rw [integral_congr_ae he, integral_sub h0 h1, ← hprod,
    integral_prod_symm _ (hprod.symm ▸ h0), integral_prod _ (hprod.symm ▸ h1)]
  change ((∫ x in J, ∫ t in J, bulk d ε 0 (axisTraceChart 0 (x, t))) -
    (∫ x in J, ∫ t in J, bulk d ε 1 (axisTraceChart 1 (x, t)))) = _
  rw [integral_congr_ae (bulk_section d hε 0), integral_congr_ae (bulk_section d hε 1)]
  have E (j : Fin 2) :
      IntegrableOn (fun x ↦ (‖d.phi (axisTraceChart j (x, halfPi))‖ ^ 2 +
        ‖d.phi (axisTraceChart j (x, -halfPi))‖ ^ 2) / (cos x + ε)) J := by
    simp only [add_div]
    have H (σ : Bool) := edge_integrable d j σ hε
    have h := (H true).add (H false)
    convert h using 1
    funext x
    simp only [Pi.add_apply, cellEdgeNormal, Bool.false_eq_true, ite_false, ite_true, neg_div]
  rw [← integral_sub (E 0) (E 1)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [← sub_div, mixedEdgeMassDefect, cellEdgeNormal, Bool.false_eq_true, ite_false,
    ite_true, neg_div]
  rfl

/-- Integrate the trace-mass current without artificial corner faces.
The smooth denominator regularization has a uniformly bounded divergence
error, and its original side fluxes can be paired before taking the limit. -/
theorem mixed_trace_mass_volume_eq {ω : L2} (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) =
      ∫ x in J, mixedEdgeMassDefect d.phi x / cos x := by
  let μ := volume.restrict mixedOpenCell
  let D := mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1])
  let E := fun x ↦ mixedEdgeMassDefect d.phi x / cos x
  have hD : Integrable D μ := (mixed_rellich_volume_integrable d).2.2
  have hE : Integrable E ν := mixed_edge_mass_defect_integrable d
  let δ (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have Lδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  let F (n : ℕ) (q : Plane) := den q / (den q + δ n) * D q +
    δ n * (cos q.1 - cos q.2) / (den q + δ n) ^ 2 * ‖d.phi q‖ ^ 2
  let G (n : ℕ) (x : ℝ) := cos x / (cos x + δ n) * E x
  have hmem : ∀ᵐ q ∂μ, q ∈ mixedOpenCell :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmem' : ∀ᵐ x ∂ν, x ∈ J := ae_restrict_mem measurableSet_Ioo
  have h0 : Tendsto (fun n ↦ ∫ q, F n q ∂μ) atTop (𝓝 (∫ q, D q ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun q ↦ ‖D q‖ + ‖d.phi q‖ ^ 2)
    · intro n
      have hd : Measurable den := by unfold den; fun_prop
      exact ((show Measurable (fun q ↦ den q / (den q + δ n)) by fun_prop).aestronglyMeasurable.mul
        hD.aestronglyMeasurable).add
        ((show Measurable (fun q : Plane ↦
          δ n * (cos q.1 - cos q.2) / (den q + δ n) ^ 2) by fun_prop).aestronglyMeasurable.mul
          (mass_integrable d).aestronglyMeasurable)
    · exact hD.norm.add (mass_integrable d)
    · intro n
      filter_upwards [hmem] with q hq
      obtain ⟨hh, hk⟩ := cos_pos_cell hq
      have hp : 0 < den q := add_pos hh hk
      have hz := add_pos hp (hδ n)
      have hratio : ‖den q / (den q + δ n)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (div_nonneg hp.le hz.le)]
        exact (div_le_one hz).2 (le_add_of_nonneg_right (hδ n).le)
      have herr : ‖δ n * (cos q.1 - cos q.2) / (den q + δ n) ^ 2‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (hδ n),
          abs_of_nonneg (sq_nonneg (den q + δ n))]
        apply (div_le_one (sq_pos_of_pos hz)).2
        have hab : |cos q.1 - cos q.2| ≤ den q := by
          unfold den
          exact (abs_sub _ _).trans_eq (by rw [abs_of_pos hh, abs_of_pos hk])
        exact (mul_le_mul_of_nonneg_left hab (hδ n).le).trans (by
          nlinarith only [sq_nonneg (den q), sq_nonneg (δ n), mul_nonneg hp.le (hδ n).le])
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · simpa only [norm_mul, one_mul] using mul_le_mul_of_nonneg_right hratio (norm_nonneg (D q))
      · simpa only [norm_mul, Real.norm_of_nonneg (sq_nonneg _), one_mul] using
          mul_le_mul_of_nonneg_right herr (sq_nonneg ‖d.phi q‖)
    · filter_upwards [hmem] with q hq
      obtain ⟨hh, hk⟩ := cos_pos_cell hq
      have hp : den q ≠ 0 := (add_pos hh hk).ne'
      have Lp := Lδ.const_add (den q)
      simp only [add_zero] at Lp
      have h := (((tendsto_const_nhds (x := den q)).div Lp hp).mul
        (tendsto_const_nhds (x := D q))).add
        (((Lδ.mul_const (cos q.1 - cos q.2)).div (Lp.pow 2) (pow_ne_zero _ hp)).mul_const
          (‖d.phi q‖ ^ 2))
      simpa only [F, Pi.div_apply, div_self hp, one_mul, zero_mul, zero_div, add_zero] using h
  have h1 : Tendsto (fun n ↦ ∫ x, G n x ∂ν) atTop (𝓝 (∫ x, E x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖E x‖)
    · intro n
      exact (show Measurable (fun x ↦ cos x / (cos x + δ n)) by fun_prop).aestronglyMeasurable.mul
        hE.aestronglyMeasurable
    · exact hE.norm
    · intro n
      filter_upwards [hmem'] with x hx
      have hp := cos_pos_of_mem_Ioo hx
      have hz := add_pos hp (hδ n)
      have hb : ‖cos x / (cos x + δ n)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (div_nonneg hp.le hz.le)]
        exact (div_le_one hz).2 (le_add_of_nonneg_right (hδ n).le)
      simpa only [G, norm_mul, one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (E x))
    · filter_upwards [hmem'] with x hx
      have hp := (cos_pos_of_mem_Ioo hx).ne'
      have H := (tendsto_const_nhds (x := cos x)).div (Lδ.const_add (cos x)) (by simpa using hp)
      simpa only [G, Pi.div_apply, add_zero, div_self hp, one_mul] using H.mul_const (E x)
  refine tendsto_nhds_unique h0 (h1.congr fun n ↦ ?_)
  rw [regularized_identity d (hδ n)]
  apply integral_congr_ae
  filter_upwards [hmem'] with x hx
  dsimp only [G, E]
  field_simp [(cos_pos_of_mem_Ioo hx).ne', (add_pos (cos_pos_of_mem_Ioo hx) (hδ n)).ne']

end NoEmbeddedEigenvalues
