module

public import EulerDipoleEigenvalues.EvenEven.NormalVirial.NormalVirial
public import EulerDipoleEigenvalues.Regularity.MixedSeparatrix.MixedDividedEquation

/-! # Bulk densities and field comparison for the mixed virial -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter
open scoped Topology ENNReal

local notation "Plane" => ℝ × ℝ

/-- Normal-field virial density in diagonal measure. The normal and tangent
are still physical unit directions in Cartesian coordinates. -/
def mixedNormalVirialDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  let p := diagInv q
  let dx := fun r ↦ (d.streamA (diagCoord r) + d.streamB (diagCoord r)) / 2
  let dy := fun r ↦ (d.streamA (diagCoord r) - d.streamB (diagCoord r)) / 2
  2 * (normalCoeff p * ‖liftL2 ω p‖ ^ 2 +
    (2 - normalC p) * ‖normalDeriv dx dy p‖ ^ 2 +
    normalC p * ‖tangentDeriv dx dy p‖ ^ 2)

private theorem mixed_diagInv_preimage_cell : diagInv ⁻¹' cellSquare = mixedOpenCell := by
  ext q
  simp only [mixedOpenCell, cellSquare, mem_preimage, mem_ofPred_eq, diagCoord_diagInv,
    mem_prod, mem_Ioo, abs_lt, neg_div]

/-- The normal-field vorticity coefficient is controlled by the same
odd-side divisor as the adapted-field coefficient. -/
theorem mixed_normal_coeff_bounds {q : Plane} (hq : q ∈ mixedOpenCell) :
    0 ≤ normalCoeff (diagInv q) ∧
    normalCoeff (diagInv q) * Real.cos q.1 ^ 2 ≤ 2 ∧
    0 ≤ normalC (diagInv q) ∧ normalC (diagInv q) ≤ 1 := by
  let p := diagInv q
  have hp : p ∈ cellSquare := by rwa [← mixed_diagInv_preimage_cell] at hq
  have h0 : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have h2 : dipoleLift p ≤ 2 := by
    unfold dipoleLift
    linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
  change 0 ≤ normalCoeff p ∧ normalCoeff p * _ ≤ 2 ∧ 0 ≤ normalC p ∧ normalC p ≤ 1
  rcases h2.lt_or_eq with h2 | h2
  · obtain ⟨hc0, hc1⟩ := normalC_pos_le_one h0 h2
    refine ⟨normalCoeff_nonneg h0 h2, ?_, hc0.le, hc1⟩
    have hg := gradSq_dipoleLift_pos h0 h2
    have hG : gradSq dipoleLift p = 2 * ((Real.sin q.1 * Real.cos q.2) ^ 2 +
        (Real.cos q.1 * Real.sin q.2) ^ 2) := by
      simp only [p, diagInv_apply, gradSq_dipoleLift, Real.sin_add, Real.sin_sub]
      ring
    have hδ : Real.cos p.1 - Real.cos p.2 = -2 * Real.sin q.1 * Real.sin q.2 := by
      simp only [p, diagInv_apply, Real.cos_add, Real.cos_sub]
      ring
    have hle : (Real.cos p.1 - Real.cos p.2) ^ 2 * Real.cos q.1 ^ 2 ≤
        2 * gradSq dipoleLift p := by
      rw [hδ, hG]
      nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one q.1))
        (sq_nonneg (Real.cos q.1 * Real.sin q.2)),
        sq_nonneg (Real.sin q.1 * Real.cos q.2)]
    calc normalCoeff p * Real.cos q.1 ^ 2 =
        normalC p * (((Real.cos p.1 - Real.cos p.2) ^ 2 * Real.cos q.1 ^ 2) /
          gradSq dipoleLift p) := by
          unfold normalCoeff normalC
          field_simp
      _ ≤ 1 * 2 := by
        gcongr
        exact (div_le_iff₀ hg).2 hle
      _ = 2 := one_mul 2
  · simp [normalCoeff, normalC, h2]

/-- Full-cell integrability on the quotient domain, without a corner trace
or a restriction to particular good levels. -/
theorem mixed_normal_virial_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedNormalVirialDensity d) mixedOpenCell := by
  let μ := volume.restrict mixedOpenCell
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hC : MemLp (fun q : Plane ↦ Real.cos q.1) ∞ μ :=
    memLp_top_of_bound (by fun_prop) 1 (.of_forall fun q ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one q.1)
  have hS : MemLp (fun q : Plane ↦ Real.sin q.1) ∞ μ :=
    memLp_top_of_bound (by fun_prop) 1 (.of_forall fun q ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one q.1)
  have ha := d.h2.memLp_weakJet hU d.weakJet [0] (by decide)
  have hb := d.h2.memLp_weakJet hU d.weakJet [1] (by decide)
  have hA : MemLp d.streamA 2 μ := (hC.smul ha).sub (hS.smul d.h2.memLp)
  have hB : MemLp d.streamB 2 μ := hC.smul hb
  let N := fun q ↦ liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)
  have hN : MemLp N 2 μ := d.vorticity_divided
  let X := fun r ↦ (d.streamA (diagCoord r) + d.streamB (diagCoord r)) / 2
  let Y := fun r ↦ (d.streamA (diagCoord r) - d.streamB (diagCoord r)) / 2
  let O := fun q ↦ liftL2 ω (diagInv q)
  have hmeas (g : Plane → ℂ) (hg : MemLp g 2 μ) :
      AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hM : AEStronglyMeasurable (mixedNormalVirialDensity d) μ := by
    have hMA := hmeas _ hA
    have hMB := hmeas _ hB
    have hO : Measurable O := (measurable_liftL2 ω).comp diagInv.continuous.measurable
    change AEStronglyMeasurable (fun q ↦ 2 * (normalCoeff (diagInv q) * ‖O q‖ ^ 2 +
      (2 - normalC (diagInv q)) * ‖normalDeriv X Y (diagInv q)‖ ^ 2 +
      normalC (diagInv q) * ‖tangentDeriv X Y (diagInv q)‖ ^ 2)) μ
    have hf : Measurable (normalCoeff ∘ diagInv) := by
      simp only [Function.comp_def, normalCoeff, diagInv_apply, gradSq_dipoleLift, dipoleLift]
      fun_prop
    have hc : Measurable (normalC ∘ diagInv) := by
      simp only [Function.comp_def, normalC, diagInv_apply, gradSq_dipoleLift, dipoleLift]
      fun_prop
    have hg : Measurable (fun q ↦ (gradNorm (diagInv q) : ℂ)) := by
      simp only [gradNorm, diagInv_apply]
      fun_prop
    have hs (j : Fin 2) :
        Measurable (fun q ↦ (Real.sin (if j = 0 then (diagInv q).1 else (diagInv q).2) : ℂ)) := by
      split_ifs <;> fun_prop
    have hXm : AEStronglyMeasurable (fun q ↦ X (diagInv q)) μ := by
      simp only [X, diagCoord_diagInv]
      exact (hMA.add hMB).div₀ aestronglyMeasurable_const
    have hYm : AEStronglyMeasurable (fun q ↦ Y (diagInv q)) μ := by
      simp only [Y, diagCoord_diagInv]
      exact (hMA.sub hMB).div₀ aestronglyMeasurable_const
    have hn : AEStronglyMeasurable (fun q ↦ normalDeriv X Y (diagInv q)) μ :=
      (((hs 0).aestronglyMeasurable.mul hXm).add
        ((hs 1).aestronglyMeasurable.mul hYm)).div₀ hg.aestronglyMeasurable
    have ht : AEStronglyMeasurable (fun q ↦ tangentDeriv X Y (diagInv q)) μ :=
      (((hs 1).aestronglyMeasurable.mul hXm).sub
        ((hs 0).aestronglyMeasurable.mul hYm)).div₀ hg.aestronglyMeasurable
    exact ((((hf.aestronglyMeasurable.mul (hO.aestronglyMeasurable.norm.pow 2)).add
      ((aestronglyMeasurable_const.sub hc.aestronglyMeasurable).mul (hn.norm.pow 2))).add
      (hc.aestronglyMeasurable.mul (ht.norm.pow 2))).const_mul 2)
  let R := fun q ↦ ‖d.streamA q‖ + ‖d.streamB q‖
  have hR : MemLp R 2 μ := hA.norm.add hB.norm
  refine ((hN.norm.integrable_sq.const_mul 4).add
    (hR.integrable_sq.const_mul 6)).mono' hM ?_
  filter_upwards [ae_restrict_mem (μ := volume) hU.measurableSet] with q hq
  obtain ⟨hf, hf2, hc0, hc1⟩ := mixed_normal_coeff_bounds hq
  have hc : 0 < Real.cos q.1 :=
    Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)
  have hΩ : normalCoeff (diagInv q) * ‖O q‖ ^ 2 ≤ 2 * ‖N q‖ ^ 2 := by
    have he : ‖O q‖ = Real.cos q.1 * ‖N q‖ := by
      dsimp only [N]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_div_cancel₀ _ hc.ne']
    rw [he, mul_pow, ← mul_assoc]
    gcongr
  have hX : ‖X (diagInv q)‖ ≤ R q / 2 := by
    simp only [X, diagCoord_diagInv, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hY : ‖Y (diagInv q)‖ ≤ R q / 2 := by
    simp only [Y, diagCoord_diagInv, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hn := (norm_normalDeriv_le X Y (diagInv q)).trans
    (show ‖X (diagInv q)‖ + ‖Y (diagInv q)‖ ≤ R q by linarith only [hX, hY])
  have ht := (norm_tangentDeriv_le X Y (diagInv q)).trans
    (show ‖X (diagInv q)‖ + ‖Y (diagInv q)‖ ≤ R q by linarith only [hX, hY])
  change ‖2 * (normalCoeff (diagInv q) * ‖O q‖ ^ 2 +
      (2 - normalC (diagInv q)) * ‖normalDeriv X Y (diagInv q)‖ ^ 2 +
      normalC (diagInv q) * ‖tangentDeriv X Y (diagInv q)‖ ^ 2)‖ ≤
    4 * ‖N q‖ ^ 2 + 6 * R q ^ 2
  have hn' : (2 - normalC (diagInv q)) * ‖normalDeriv X Y (diagInv q)‖ ^ 2 ≤
      2 * R q ^ 2 := by gcongr; linarith
  have ht' : normalC (diagInv q) * ‖tangentDeriv X Y (diagInv q)‖ ^ 2 ≤
      1 * R q ^ 2 := by gcongr
  have hc2 : 0 ≤ 2 - normalC (diagInv q) := by linarith
  rw [Real.norm_of_nonneg (by positivity)]
  linarith only [hΩ, hn', ht']

/-- The quotient-domain normal density agrees with the lift used in the
truncated virial. This is an a.e. identification, not a corner evaluation. -/
theorem mixed_normal_virial_cartesian_ae {ω : L2} (d : MixedQuotientData ω) :
    mixedNormalVirialDensity d =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ 2 * eeBulkDensity ω (diagInv q) := by
  filter_upwards [d.stream_partials_ae] with q hq
  let X := fun r ↦ (d.streamA (diagCoord r) + d.streamB (diagCoord r)) / 2
  let Y := fun r ↦ (d.streamA (diagCoord r) - d.streamB (diagCoord r)) / 2
  have hX : X (diagInv q) = streamLiftX ω (diagInv q) := by
    simp only [X, diagCoord_diagInv, hq.1, hq.2]
    ring
  have hY : Y (diagInv q) = streamLiftY ω (diagInv q) := by
    simp only [Y, diagCoord_diagInv, hq.1, hq.2]
    ring
  change 2 * (normalCoeff (diagInv q) * ‖liftL2 ω (diagInv q)‖ ^ 2 +
    (2 - normalC (diagInv q)) * ‖normalDeriv X Y (diagInv q)‖ ^ 2 +
    normalC (diagInv q) * ‖tangentDeriv X Y (diagInv q)‖ ^ 2) = _
  simp only [eeDensity, streamNormal, streamTangent, normalDeriv, tangentDeriv, hX, hY]

/-- The normal-field bulk integral in the same measure as the truncated
virial. -/
theorem mixed_normal_virial_cartesian {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (eeBulkDensity ω) cellSquare ∧
    (∫ p in cellSquare, eeBulkDensity ω p) =
      ∫ q in mixedOpenCell, mixedNormalVirialDensity d q := by
  let F := eeBulkDensity ω
  let E := diagInv.toHomeomorph.toMeasurableEquiv
  have hm : MeasurableSet cellSquare := isOpen_cellSquare.measurableSet
  have hF := (mixed_normal_virial_integrable d).congr (mixed_normal_virial_cartesian_ae d)
  have hhalf : IntegrableOn (F ∘ diagInv) mixedOpenCell := by
    have h := hF.const_mul (1 / 2 : ℝ)
    simp only [one_div, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
    exact h
  have hmap : Measure.map diagInv (volume.restrict mixedOpenCell) =
      ENNReal.ofReal (2⁻¹ : ℝ) • volume.restrict cellSquare := by
    rw [← mixed_diagInv_preimage_cell, ← Measure.restrict_map diagInv.continuous.measurable hm,
      map_diagInv_volume, Measure.restrict_smul, one_div]
  have h := (E.measurableEmbedding.integrable_map_iff).2 hhalf
  change Integrable F (Measure.map diagInv (volume.restrict mixedOpenCell)) at h
  rw [hmap] at h
  have h' := h.smul_measure (c := ENNReal.ofReal (2 : ℝ)) (by finiteness)
  rw [smul_smul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h'
  norm_num at h'
  refine ⟨h', ?_⟩
  rw [integral_congr_ae (mixed_normal_virial_cartesian_ae d), integral_const_mul]
  have he := E.measurableEmbedding.integral_map F (μ := volume.restrict mixedOpenCell)
  change (∫ p, F p ∂Measure.map diagInv (volume.restrict mixedOpenCell)) =
    ∫ q in mixedOpenCell, F (diagInv q) at he
  rw [← he, hmap, integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by norm_num)]
  ring

/-- Every sequence of regular truncations carrying the normal virial
has the same limit on the bulk side. -/
theorem mixed_normal_level_limit {ω : L2} (d : MixedQuotientData ω) {hs : ℕ → ℝ}
    (hlim : Tendsto hs atTop (𝓝 0))
    (hlevels : ∀ n, (∫ p in {p | p ∈ cellSquare ∧ 2 * hs n < dipoleLift p},
        eeBulkDensity ω p) = eeLevelTerm ω (hs n)) :
    Tendsto (fun n ↦ eeLevelTerm ω (hs n)) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedNormalVirialDensity d q)) := by
  obtain ⟨hi, hI⟩ := mixed_normal_virial_cartesian d
  let S (n : ℕ) := {p : Plane | 2 * hs n < dipoleLift p}
  have hm (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_lt measurable_const (by unfold dipoleLift; fun_prop)
  have he (n : ℕ) :
      eeLevelTerm ω (hs n) = ∫ p in cellSquare, (S n).indicator (eeBulkDensity ω) p := by
    rw [← hlevels n, integral_indicator (hm n), Measure.restrict_restrict (hm n), inter_comm]
    rfl
  simp_rw [he, ← hI]
  apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖eeBulkDensity ω p‖)
  · exact fun n ↦ hi.aestronglyMeasurable.indicator (hm n)
  · exact hi.norm
  · intro n
    filter_upwards with p
    by_cases hp : p ∈ S n
    · simp [indicator_of_mem hp]
    · simp [indicator_of_notMem hp]
  · filter_upwards [ae_restrict_mem (μ := volume) isOpen_cellSquare.measurableSet] with p hp
    have h0 : 0 < dipoleLift p := by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
    have hscaled : Tendsto (fun n ↦ 2 * hs n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (2 : ℝ)
    apply tendsto_const_nhds.congr'
    filter_upwards [hscaled.eventually (gt_mem_nhds h0)] with n hn
    exact (indicator_of_mem (show p ∈ S n from hn) _).symm

/-- Exact tangential difference in diagonal coordinates on the punctured
cell. The antisymmetric cosine factor is retained, rather than bounded by
its absolute value, for cancellation of the leading corner current. -/
theorem mixed_field_tangential_factor {q : Plane} (hq : q ∈ mixedOpenCell)
    (hr : gradSq dipoleLift (diagInv q) ≠ 0) :
    let p := diagInv q
    let h := Real.cos q.1
    let k := Real.cos q.2
    let u := Real.sin q.1
    let v := Real.sin q.2
    let G := u ^ 2 * k ^ 2 + v ^ 2 * h ^ 2
    let c := (h - k) * u * v / ((h + k) * G)
    mixedFieldA q - (normalField₁ p + normalField₂ p) / 2 = c * (h * v) ∧
    mixedFieldB q - (normalField₁ p - normalField₂ p) / 2 = c * (-k * u) := by
  let p := diagInv q
  let h := Real.cos q.1
  let k := Real.cos q.2
  let u := Real.sin q.1
  let v := Real.sin q.2
  let G := u ^ 2 * k ^ 2 + v ^ 2 * h ^ 2
  let C := (h - k) * u * v / ((h + k) * G)
  have hsum : h + k ≠ 0 := (add_pos
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))).ne'
  have hΨ : dipoleLift p = 2 * h * k := by rw [dipoleLift_eq_diag, diagCoord_diagInv]
  have hx : Real.sin p.1 = u * k + h * v := by simp [p, u, k, h, v, Real.sin_add]
  have hy : Real.sin p.2 = u * k - h * v := by simp [p, u, k, h, v, Real.sin_sub]
  have hg : gradSq dipoleLift p = 2 * G := by
    simp only [gradSq_dipoleLift]
    rw [hx, hy]
    dsimp only [G]
    ring
  have hG : G ≠ 0 := by
    intro hz
    exact hr (by rw [hg, hz, mul_zero])
  change u / (h + k) - (normalField₁ p + normalField₂ p) / 2 = C * (h * v) ∧
    v / (h + k) - (normalField₁ p - normalField₂ p) / 2 = C * (-k * u)
  simp only [normalField₁, normalField₂, partialX_dipoleLift, partialY_dipoleLift]
  rw [hx, hy, hg, hΨ]
  have ha : u ^ 2 + h ^ 2 = 1 := Real.sin_sq_add_cos_sq q.1
  have hb : v ^ 2 + k ^ 2 = 1 := Real.sin_sq_add_cos_sq q.2
  have hA : G - (1 - h * k) * k * (h + k) = h * (h - k) * v ^ 2 := by
    dsimp only [G]
    linear_combination k ^ 2 * ha + h * k * hb
  have hB : G - (1 - h * k) * h * (h + k) = -k * (h - k) * u ^ 2 := by
    dsimp only [G]
    linear_combination h ^ 2 * hb + h * k * ha
  dsimp only [C]
  constructor <;> field_simp
  · linear_combination 2 * u * hA
  · linear_combination 2 * v * hB

/-- The scalar coefficient of the tangential boundary current with the
diagonal stream gradient frozen at `(A,0)`, after dividing out `|A|²`. -/
def mixedTangentialCornerKernel (q : Plane) : ℝ :=
  let h := Real.cos q.1
  let k := Real.cos q.2
  let u := Real.sin q.1
  let v := Real.sin q.2
  2 * h * k * u ^ 2 * v ^ 2 * (h - k) /
    ((h + k) * (u ^ 2 * k ^ 2 + v ^ 2 * h ^ 2))

/-- The leading corner current cancels on symmetric level shells, without
a hyperbola approximating the exact level. The weight can include a
symmetric corner cutoff. -/
theorem mixed_tangential_corner_cancel {w : Plane → ℝ}
    (hs : ∀ q, w q.swap = w q)
    (hw : IntegrableOn w mixedOpenCell) :
    IntegrableOn (fun q ↦ w q * mixedTangentialCornerKernel q) mixedOpenCell ∧
      (∫ q in mixedOpenCell, w q * mixedTangentialCornerKernel q) = 0 := by
  have hb (q : Plane) (hq : q ∈ mixedOpenCell) : ‖mixedTangentialCornerKernel q‖ ≤ 1 := by
    let h := Real.cos q.1
    let k := Real.cos q.2
    let u := Real.sin q.1
    let v := Real.sin q.2
    let G := u ^ 2 * k ^ 2 + v ^ 2 * h ^ 2
    have hh : 0 < h := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)
    have hk : 0 < k := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)
    have hG : 0 ≤ G := by dsimp [G]; positivity
    change ‖2 * h * k * u ^ 2 * v ^ 2 * (h - k) / ((h + k) * G)‖ ≤ 1
    rcases hG.eq_or_lt with hz | hg
    · simp [← hz]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (mul_nonneg (add_pos hh hk).le hG),
      div_le_one (mul_pos (add_pos hh hk) hg), abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2 * h * k * u ^ 2 * v ^ 2)]
    have huv : |u| * |v| ≤ 1 := by
      simpa using mul_le_mul (Real.abs_sin_le_one q.1) (Real.abs_sin_le_one q.2)
        (abs_nonneg v) (by norm_num : (0 : ℝ) ≤ 1)
    have hprod : 2 * h * k * u ^ 2 * v ^ 2 ≤ G := by
      calc
        _ = (2 * (k * |u|) * (h * |v|)) * (|u| * |v|) := by
          rw [← sq_abs u, ← sq_abs v]
          ring
        _ ≤ 2 * (k * |u|) * (h * |v|) * 1 :=
          mul_le_mul_of_nonneg_left huv (by positivity)
        _ ≤ G := by
          dsimp only [G]
          nlinarith [sq_nonneg (k * |u| - h * |v|), sq_abs u, sq_abs v,
            congrArg (fun x : ℝ ↦ k ^ 2 * x) (sq_abs u),
            congrArg (fun x : ℝ ↦ h ^ 2 * x) (sq_abs v)]
    have hd : |h - k| ≤ h + k := abs_le.2 ⟨by linarith, by linarith⟩
    calc
      _ ≤ G * (h + k) := mul_le_mul hprod hd (abs_nonneg _) hG
      _ = _ := mul_comm _ _
  have hm : Measurable mixedTangentialCornerKernel := by
    unfold mixedTangentialCornerKernel
    fun_prop
  have hi := hw.bdd_mul hm.aestronglyMeasurable
    ((ae_restrict_mem (μ := volume) (s := mixedOpenCell)
      (measurableSet_Ioo.prod measurableSet_Ioo)).mono hb)
  refine ⟨hi.congr (.of_forall fun q ↦ mul_comm (mixedTangentialCornerKernel q) (w q)), ?_⟩
  let F := mixedOpenCell.indicator (fun q ↦ w q * mixedTangentialCornerKernel q)
  have hk (q : Plane) : mixedTangentialCornerKernel q.swap = -mixedTangentialCornerKernel q := by
    simp only [mixedTangentialCornerKernel, Prod.fst_swap, Prod.snd_swap, ← neg_div]
    congr 1 <;> ring
  have he : (fun q ↦ F q.swap) = fun q ↦ -F q := by
    funext q
    have hq : q.swap ∈ mixedOpenCell ↔ q ∈ mixedOpenCell := by
      exact and_comm
    by_cases hm : q ∈ mixedOpenCell
    · dsimp only [F]
      rw [indicator_of_mem (hq.mpr hm), indicator_of_mem hm, hs, hk, mul_neg]
    · dsimp only [F]
      rw [indicator_of_notMem (mt hq.mp hm), indicator_of_notMem hm, neg_zero]
  have hI : (∫ q : Plane, F q.swap) = ∫ q, F q := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_swap F
  rw [he, integral_neg] at hI
  have hcell : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  rw [← integral_indicator hcell]
  change (∫ q, F q) = 0
  linarith only [hI]

end EulerDipoleEigenvalues
