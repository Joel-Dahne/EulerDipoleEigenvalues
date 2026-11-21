module

public import NoEmbeddedEigenvalues.Mixed.SecondOrderForm.SecondOrderForm
public import NoEmbeddedEigenvalues.Mixed.Conclusion.QuarterCoercivity

/-! # Mixed parity splitting, quarter folding, and coercivity -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- Projection onto odd-in-a (`true`) or even-in-a (`false`). On a centrally
odd function, the respective b parities are even and odd. -/
def mixedParityPart (oddA : Bool) (φ : Plane → ℂ) (q : Plane) : ℂ :=
  (φ q + (if oddA then -1 else 1) * φ (-q.1, q.2)) / 2

private theorem mixed_reflection_preimage (j : Fin 2) :
    axisReflect j ⁻¹' mixedOpenCell = mixedOpenCell := by
  ext q
  have h (x : ℝ) : -x ∈ Ioo (-Real.pi / 2) (Real.pi / 2) ↔
      x ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
    simp only [mem_Ioo]
    constructor <;> intro hx <;> exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  fin_cases j <;> simp [axisReflect, mixedOpenCell, h]

private theorem mixed_closed_reflect (j : Fin 2) :
    MapsTo (axisReflect j) (closure mixedOpenCell) (closure mixedOpenCell) := by
  apply MapsTo.closure
  · intro q hq
    change q ∈ axisReflect j ⁻¹' mixedOpenCell
    rwa [mixed_reflection_preimage]
  · rw [← planeAffine_axisReflectionLinear]
    fun_prop

private theorem isOpen_mixedOpenCell : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo

private theorem mixed_reflection_mp (j : Fin 2) :
    MeasurePreserving (axisReflect j) (volume.restrict mixedOpenCell)
      (volume.restrict mixedOpenCell) := by
  have h := (measurePreserving_axisReflect j).restrict_preimage isOpen_mixedOpenCell.measurableSet
  rwa [mixed_reflection_preimage] at h

private theorem mixed_reflection_integral (j : Fin 2) (f : Plane → ℝ) :
    (∫ q in mixedOpenCell, (f ∘ axisReflect j) q) = ∫ q in mixedOpenCell, f q := by
  have he : MeasurableEmbedding (axisReflect j) := by
    rw [← planeAffine_axisReflectionLinear]
    exact (planeAffine (axisReflectionLinear j) 0).measurableEmbedding
  exact (mixed_reflection_mp j).integral_comp he f

theorem mixed_density_integrable {f a b : Plane → ℂ}
    (hf : MemLp f 2 (volume.restrict mixedOpenCell))
    (ha : MemLp a 2 (volume.restrict mixedOpenCell))
    (hb : MemLp b 2 (volume.restrict mixedOpenCell)) :
    IntegrableOn (mixedSecondOrderDensity f a b) mixedOpenCell := by
  let μ := volume.restrict mixedOpenCell
  have hD : Measurable mixedComparisonDiagonal := by
    unfold mixedComparisonDiagonal mixedD
    fun_prop
  have hJ : Measurable mixedComparisonOffDiagonal := by
    unfold mixedComparisonOffDiagonal mixedC
    fun_prop
  have hV : Measurable mixedComparisonPotential := by
    unfold mixedComparisonPotential mixedV
    fun_prop
  have hd : ∀ᵐ q ∂μ, ‖mixedComparisonDiagonal q‖ ≤ 3 := by
    filter_upwards [ae_restrict_mem isOpen_mixedOpenCell.measurableSet] with q hq
    rw [Real.norm_eq_abs, abs_of_pos (mixed_comparison_matrix_positive hq).1]
    exact (mixed_comparison_coefficient_bounds hq).2.2.1
  have hj : ∀ᵐ q ∂μ, ‖mixedComparisonOffDiagonal q‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem isOpen_mixedOpenCell.measurableSet] with q hq
    exact (mixed_comparison_coefficient_bounds hq).2.2.2
  have hv : ∀ᵐ q ∂μ, ‖mixedComparisonPotential q‖ ≤ 4 := by
    filter_upwards [ae_restrict_mem isOpen_mixedOpenCell.measurableSet] with q hq
    have h := mixed_comparison_coefficient_bounds hq
    rw [Real.norm_eq_abs, abs_of_nonpos (neg_nonneg.mp h.1)]
    exact h.2.1
  have hAa := ha.integrable_norm_pow (by decide)
  have hBb := hb.integrable_norm_pow (by decide)
  have hF := (hf.integrable_norm_pow (by decide)).bdd_mul hV.aestronglyMeasurable hv
  have hDiag := (hAa.add hBb).bdd_mul hD.aestronglyMeasurable hd
  have hCross : Integrable (fun q ↦ (a q * conj (b q)).re) μ := by
    refine ((hAa.add hBb).div_const 2).mono'
      ((Complex.continuous_re.comp_aestronglyMeasurable
        (ha.aestronglyMeasurable.mul
          (Complex.continuous_conj.comp_aestronglyMeasurable hb.aestronglyMeasurable))))
      (Eventually.of_forall fun q ↦ ?_)
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖a q * conj (b q)‖ := Complex.abs_re_le_norm _
      _ = ‖a q‖ * ‖b q‖ := by simp only [norm_mul, Complex.norm_conj]
      _ ≤ _ := by
        change _ ≤ (‖a q‖ ^ 2 + ‖b q‖ ^ 2) / 2
        nlinarith only [sq_nonneg (‖a q‖ - ‖b q‖)]
  have hOff := (hCross.bdd_mul hJ.aestronglyMeasurable hj).const_mul 2
  refine ((hDiag.add hOff).add hF).congr (Eventually.of_forall fun q ↦ ?_)
  simp only [Pi.add_apply, mixedSecondOrderDensity, mixedGradientForm, mul_assoc]

theorem mixed_edge_integrable {f : Plane → ℂ}
    (hc : ContinuousOn f (closure mixedOpenCell)) (σ : Bool) :
    IntegrableOn (fun a ↦ Real.cos a * ‖mixedEdgeValue 1 σ f a‖ ^ 2)
      (Ioo (-Real.pi / 2) (Real.pi / 2)) := by
  have hcl : closure mixedOpenCell =
      Icc (-Real.pi / 2) (Real.pi / 2) ×ˢ Icc (-Real.pi / 2) (Real.pi / 2) := by
    rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos] :
      -Real.pi / 2 ≠ Real.pi / 2)]
  have he : ContinuousOn (mixedEdgeValue 1 σ f) (Icc (-Real.pi / 2) (Real.pi / 2)) := by
    change ContinuousOn (fun a ↦ f (a, cellEdgeNormal σ)) _
    apply hc.comp (by fun_prop)
    rw [hcl]
    intro a ha
    exact ⟨ha, by cases σ <;> simp [cellEdgeNormal] <;> linarith [Real.pi_pos]⟩
  exact ((Real.continuous_cos.continuousOn.mul (he.norm.pow 2)).integrableOn_compact
    isCompact_Icc).mono_set Ioo_subset_Icc_self

private theorem mixed_quadratic_average (g j v : ℝ) (x y a b c e : ℂ) :
    mixedGradientForm g j ((a - c) / 2) ((b - e) / 2) + v * ‖(x - y) / 2‖ ^ 2 +
      (mixedGradientForm g j ((a + c) / 2) ((b + e) / 2) + v * ‖(x + y) / 2‖ ^ 2) =
    (mixedGradientForm g j a b + v * ‖x‖ ^ 2 +
      (mixedGradientForm g j c e + v * ‖y‖ ^ 2)) / 2 := by
  simp only [mixedGradientForm, div_eq_mul_inv, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- Parity splitting, with the actual weak gradients of the projected functions. -/
theorem mixed_parity_split {ω : L2} (d : MixedQuotientData ω) :
    let U := mixedParityPart true d.phi
    let V := mixedParityPart false d.phi
    (∀ q ∈ closure mixedOpenCell,
      d.phi q = U q + V q ∧ U (-q.1, q.2) = -U q ∧ U (q.1, -q.2) = U q ∧
        V (-q.1, q.2) = V q ∧ V (q.1, -q.2) = -V q) ∧
    ∃ Ua Ub Va Vb : Plane → ℂ,
      MemSobolevOn 1 mixedOpenCell U ∧ MemSobolevOn 1 mixedOpenCell V ∧
      HasWeakPartialOn mixedOpenCell 0 U Ua ∧ HasWeakPartialOn mixedOpenCell 1 U Ub ∧
      HasWeakPartialOn mixedOpenCell 0 V Va ∧ HasWeakPartialOn mixedOpenCell 1 V Vb ∧
      mixedSecondOrderForm d.phi (d.jet [0]) (d.jet [1]) (fun σ ↦ mixedEdgeValue 1 σ d.phi) =
        mixedSecondOrderForm U Ua Ub (fun σ ↦ mixedEdgeValue 1 σ U) +
        mixedSecondOrderForm V Va Vb (fun σ ↦ mixedEdgeValue 1 σ V) := by
  let φ := d.phi
  let R := axisReflect 0
  let a := d.jet [0]
  let b := d.jet [1]
  let aR := fun q ↦ -a (R q)
  let bR := b ∘ R
  let U := mixedParityPart true φ
  let V := mixedParityPart false φ
  let halfPart (s : ℂ) (f g : Plane → ℂ) := fun q ↦ (f q + s * g q) / 2
  have href (q : Plane) : R q = (-q.1, q.2) := rfl
  have hpar : ∀ q ∈ closure mixedOpenCell,
      φ q = U q + V q ∧ U (R q) = -U q ∧ U (q.1, -q.2) = U q ∧
        V (R q) = V q ∧ V (q.1, -q.2) = -V q := by
    intro q hq
    have h₁ : φ (q.1, -q.2) = -φ (-q.1, q.2) := by
      have hn := d.central_odd (R q) (mixed_closed_reflect 0 hq)
      rw [href, Prod.neg_mk, neg_neg] at hn
      exact hn
    have h₂ : φ (-q.1, -q.2) = -φ q := d.central_odd q hq
    simp only [href, U, V, mixedParityPart, ite_true, Bool.false_eq_true, ite_false, one_mul,
      neg_one_mul, neg_neg, h₁, h₂]
    exact ⟨by ring, by ring, by ring, by ring, by ring⟩
  have hφa : HasWeakPartialOn mixedOpenCell 0 φ a := by
    simpa only [d.weakJet.1] using d.weakJet.2 [] (by decide) 0
  have hφb : HasWeakPartialOn mixedOpenCell 1 φ b := by
    simpa only [d.weakJet.1] using d.weakJet.2 [] (by decide) 1
  have hmp : MeasurePreserving (planeAffine (axisReflectionLinear 0) 0) := by
    rw [planeAffine_axisReflectionLinear]; exact measurePreserving_axisReflect 0
  have hpre : planeAffine (axisReflectionLinear 0) 0 ⁻¹' mixedOpenCell = mixedOpenCell := by
    rw [planeAffine_axisReflectionLinear, mixed_reflection_preimage]
  have hD := d.weakJet.comp_planeAffine (axisReflectionLinear 0) 0 hmp isOpen_mixedOpenCell
  rw [hpre] at hD
  have hR (j : Fin 2) : HasWeakPartialOn mixedOpenCell j (φ ∘ R)
      (if j = 0 then aR else bR) := by
    have hj := hD.2 [] (by decide) j
    have he (w : List (Fin 2)) : affineJet (axisReflectionLinear 0) 0 d.jet w =
        fun q ↦ (-1 : ℂ) ^ w.count 0 * d.jet w (R q) :=
      funext (affineJet_axisReflectionLinear 0 d.jet w)
    rw [he [], he [j], d.weakJet.1] at hj
    fin_cases j <;> simpa [aR, bR, a, b, φ, Function.comp_def] using hj
  have hRW : MemSobolevOn 1 mixedOpenCell (φ ∘ R) := by
    have h := MemSobolevOn.comp_planeAffine (axisReflectionLinear 0) 0 hmp
      isOpen_mixedOpenCell d.h2
    rw [hpre, planeAffine_axisReflectionLinear] at h
    exact h.of_succ
  have hW (s : ℂ) : MemSobolevOn 1 mixedOpenCell (halfPart s φ (φ ∘ R)) := by
    have he : halfPart s φ (φ ∘ R) = fun q ↦ (1 / 2 : ℂ) * (φ q + s * (φ ∘ R) q) := by
      funext q
      simp only [halfPart]
      ring
    rw [he]
    exact (d.h2.of_succ.add (hRW.const_mul s)).const_mul _
  have hw (j : Fin 2) (s : ℂ) : HasWeakPartialOn mixedOpenCell j (halfPart s φ (φ ∘ R))
      (halfPart s (if j = 0 then a else b) (if j = 0 then aR else bR)) := by
    have h (f g : Plane → ℂ) : halfPart s f g = fun q ↦ (1 / 2 : ℂ) * (f q + s * g q) := by
      funext q; simp only [halfPart]; ring
    have h₀ : HasWeakPartialOn mixedOpenCell j φ (if j = 0 then a else b) := by
      fin_cases j
      · exact hφa
      · exact hφb
    rw [h, h]
    exact (h₀.add ((hR j).const_mul s)).const_mul _
  let Ua := halfPart (-1) a aR
  let Ub := halfPart (-1) b bR
  let Va := halfPart 1 a aR
  let Vb := halfPart 1 b bR
  have hU : MemSobolevOn 1 mixedOpenCell U := hW (-1)
  have hV : MemSobolevOn 1 mixedOpenCell V := hW 1
  have hUa : HasWeakPartialOn mixedOpenCell 0 U Ua := hw 0 (-1)
  have hUb : HasWeakPartialOn mixedOpenCell 1 U Ub := hw 1 (-1)
  have hVa : HasWeakPartialOn mixedOpenCell 0 V Va := hw 0 1
  have hVb : HasWeakPartialOn mixedOpenCell 1 V Vb := hw 1 1
  refine ⟨hpar, Ua, Ub, Va, Vb, hU, hV, hUa, hUb, hVa, hVb, ?_⟩
  have hjet (j : Fin 2) : MemLp (d.jet [j]) 2 (volume.restrict mixedOpenCell) :=
    d.h2.memLp_weakJet isOpen_mixedOpenCell d.weakJet [j] (by simp)
  have hMem {f g : Plane → ℂ} {i : Fin 2} (hf : MemSobolevOn 1 mixedOpenCell f)
      (hg : HasWeakPartialOn mixedOpenCell i f g) : MemLp g 2 (volume.restrict mixedOpenCell) := by
    obtain ⟨_, h, hL⟩ := hf.2 i
    exact hL.ae_eq ((ae_restrict_iff' isOpen_mixedOpenCell.measurableSet).mpr
      (h.ae_eq isOpen_mixedOpenCell hg))
  let E := mixedSecondOrderDensity φ a b
  have hE : IntegrableOn E mixedOpenCell := mixed_density_integrable d.h2.memLp (hjet 0) (hjet 1)
  have hEu := mixed_density_integrable hU.memLp (hMem hU hUa) (hMem hU hUb)
  have hEv := mixed_density_integrable hV.memLp (hMem hV hVa) (hMem hV hVb)
  have hER := (mixed_reflection_mp 0).integrable_comp_of_integrable hE
  have hEven (q : Plane) : mixedComparisonDiagonal (R q) = mixedComparisonDiagonal q ∧
      mixedComparisonOffDiagonal (R q) = -mixedComparisonOffDiagonal q ∧
      mixedComparisonPotential (R q) = mixedComparisonPotential q := by
    simp [href, mixedComparisonDiagonal, mixedComparisonOffDiagonal, mixedComparisonPotential,
      mul_neg, neg_mul]
  have hsum : (fun q ↦ mixedSecondOrderDensity U Ua Ub q + mixedSecondOrderDensity V Va Vb q) =
      fun q ↦ (E q + (E ∘ R) q) / 2 := by
    funext q
    rcases hEven q with ⟨hd, hj, hv⟩
    have he : E (R q) = mixedGradientForm (mixedComparisonDiagonal q)
        (mixedComparisonOffDiagonal q) (aR q) (bR q) +
        mixedComparisonPotential q * ‖φ (R q)‖ ^ 2 := by
      simp only [E, mixedSecondOrderDensity, aR, bR, Function.comp_apply, hd, hj, hv,
        mixedGradientForm, norm_neg, neg_mul, Complex.neg_re, mul_neg]
    simp only [Function.comp_apply, he]
    simpa only [U, V, mixedParityPart, Ua, Ub, Va, Vb, halfPart, ite_true, Bool.false_eq_true,
      ite_false, one_mul, neg_one_mul, ← sub_eq_add_neg, E, mixedSecondOrderDensity, href] using
      mixed_quadratic_average (mixedComparisonDiagonal q) (mixedComparisonOffDiagonal q)
        (mixedComparisonPotential q) (φ q) (φ (R q)) (a q) (b q) (aR q) (bR q)
  have hvol : (∫ q in mixedOpenCell, E q) =
      (∫ q in mixedOpenCell, mixedSecondOrderDensity U Ua Ub q) +
        (∫ q in mixedOpenCell, mixedSecondOrderDensity V Va Vb q) := by
    rw [← integral_add hEu hEv, hsum, integral_div, integral_add hE hER,
      mixed_reflection_integral]
    ring
  have hc (s : ℂ) : ContinuousOn (halfPart s φ (φ ∘ R)) (closure mixedOpenCell) :=
    (d.continuous.add (continuousOn_const.mul
      (d.continuous.comp (by rw [← planeAffine_axisReflectionLinear]; fun_prop)
        (mixed_closed_reflect 0)))).div_const _
  have hedge (σ : Bool) :
      (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖mixedEdgeValue 1 σ φ a‖ ^ 2) =
      (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖mixedEdgeValue 1 σ U a‖ ^ 2) +
      (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖mixedEdgeValue 1 σ V a‖ ^ 2) := by
    let I := Ioo (-Real.pi / 2) (Real.pi / 2)
    let m := fun (f : Plane → ℂ) x ↦ Real.cos x * ‖mixedEdgeValue 1 σ f x‖ ^ 2
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (show MeasurableSet I from measurableSet_Ioo)
    have hn : Neg.neg ⁻¹' I = I := by
      ext x
      simp only [I, mem_preimage, mem_Ioo]
      constructor <;> intro hx <;> exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    change MeasurePreserving Neg.neg (volume.restrict (Neg.neg ⁻¹' I)) (volume.restrict I) at hmp
    rw [hn] at hmp
    have hI : Integrable (m φ) (volume.restrict I) := mixed_edge_integrable d.continuous σ
    have hIR := hmp.integrable_comp_of_integrable hI
    have hs : (fun x ↦ m U x + m V x) = fun x ↦ (m φ x + (m φ ∘ Neg.neg) x) / 2 := by
      funext x
      change Real.cos x * ‖U (x, cellEdgeNormal σ)‖ ^ 2 +
        Real.cos x * ‖V (x, cellEdgeNormal σ)‖ ^ 2 =
        (Real.cos x * ‖φ (x, cellEdgeNormal σ)‖ ^ 2 +
          Real.cos (-x) * ‖φ (-x, cellEdgeNormal σ)‖ ^ 2) / 2
      simp only [U, V, mixedParityPart, ite_true, Bool.false_eq_true, ite_false, one_mul,
        neg_one_mul, ← sub_eq_add_neg, Real.cos_neg, norm_div]
      norm_num
      have h := parallelogram_law_with_norm ℂ (φ (x, cellEdgeNormal σ)) (φ (-x, cellEdgeNormal σ))
      linarith only [congrArg (fun r : ℝ ↦ Real.cos x * r) h]
    have he := hmp.integral_comp (g := m φ) (Homeomorph.neg ℝ).measurableEmbedding
    change (∫ x in I, (m φ ∘ Neg.neg) x) = _ at he
    change (∫ x in I, m φ x) = (∫ x in I, m U x) + (∫ x in I, m V x)
    have hUi : Integrable (m U) (volume.restrict I) := mixed_edge_integrable (hc (-1)) σ
    have hVi : Integrable (m V) (volume.restrict I) := mixed_edge_integrable (hc 1) σ
    rw [← integral_add hUi hVi, hs, integral_div, integral_add hI hIR, he]
    ring
  unfold mixedSecondOrderForm
  rw [hvol]
  have he : (∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
          Real.cos a * ‖mixedEdgeValue 1 σ φ a‖ ^ 2) =
      (∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
          Real.cos a * ‖mixedEdgeValue 1 σ U a‖ ^ 2) +
      ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
          Real.cos a * ‖mixedEdgeValue 1 σ V a‖ ^ 2 := by
    simp_rw [← Finset.sum_add_distrib, ← hedge]
  rw [he]
  ring

private theorem mixed_cos_sq_mul_integrable {f : Plane → ℂ}
    (hf : MemLp f 2 (volume.restrict mixedOpenCell)) :
    IntegrableOn (fun q ↦ Real.cos q.1 ^ 2 * ‖f q‖ ^ 2) mixedOpenCell := by
  refine (hf.integrable_norm_pow (by decide)).mono'
    ((Real.continuous_cos.comp continuous_fst).pow 2 |>.aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.norm.pow 2)) (Eventually.of_forall fun q ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (sq_nonneg _) (by
    nlinarith [Real.cos_le_one q.1, Real.neg_one_le_cos q.1])

section QuarterFold

local notation "c" => (Real.pi / 2)
local notation "J" => (Ioo (-c) c)
local notation "P" => (Ioo (0 : ℝ) c)

private theorem quarter_subset_cell : mixedQuarterCell ⊆ mixedOpenCell := by
  rintro q ⟨ha, hb⟩
  exact ⟨⟨by linarith [ha.1, Real.pi_pos], ha.2⟩, ⟨by linarith [hb.1, Real.pi_pos], hb.2⟩⟩

private theorem fold_partial_memLp {z dz : Plane → ℂ} {j : Fin 2}
    (hz : MemSobolevOn 1 mixedOpenCell z) (hd : HasWeakPartialOn mixedOpenCell j z dz) :
    MemLp dz 2 (volume.restrict mixedOpenCell) := by
  obtain ⟨_, hw, hl⟩ := hz.2 j
  exact hl.ae_eq ((ae_restrict_iff' isOpen_mixedOpenCell.measurableSet).mpr
    (hw.ae_eq isOpen_mixedOpenCell hd))

/-- The continuous closed-cell representative identifies the canonical
quarter trace, including the traces on the two coordinate axes. -/
private theorem fold_quarter_trace {z dz : Plane → ℂ} (j : Fin 2) {t : ℝ}
    (ht : t ∈ Icc 0 c) (hz : MemSobolevOn 1 mixedOpenCell z)
    (hc : ContinuousOn z (closure mixedOpenCell))
    (hd : HasWeakPartialOn mixedOpenCell j z dz) :
    HasTransverseH1Trace 0 c 0 c t (axisTraceChart j) z
      (fun x ↦ z (axisTraceChart j (x, t))) := by
  let C := axisTraceChart j
  let Q := mixedQuarterCell
  have hC : Continuous C := by
    fin_cases j
    · exact continuous_swap
    · exact continuous_id
  have hswap : Prod.swap ⁻¹' Q = Q := by ext q; exact and_comm
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hw : HasWeakPartialOn Q 1 (z ∘ C) (dz ∘ C) := by
    fin_cases j
    · have h := (hd.mono quarter_subset_cell).comp_swap_fst hQ
      rwa [hswap] at h
    · exact hd.mono quarter_subset_cell
  have hcomp {f : Plane → ℂ} (hf : MemLp f 2 (volume.restrict mixedOpenCell)) :
      MemLp (f ∘ C) 2 (volume.restrict Q) := by
    have h := hf.mono_measure (Measure.restrict_mono quarter_subset_cell le_rfl)
    fin_cases j
    · have h' := memLp_comp_swap hQ.measurableSet h
      rwa [hswap] at h'
    · exact h
  have hzl := hcomp hz.memLp
  have hdl := hcomp (fold_partial_memLp hz hd)
  have h0 : 0 < c := half_pos Real.pi_pos
  obtain ⟨G, hm, he, hACL, hline, _⟩ :=
    hw.exists_l2_trace isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 h0) h0 hzl hdl
  refine ⟨h0, h0, ht, G, dz ∘ C, hm, he, hzl.ae_eq he.symm, hdl, hACL, ?_⟩
  have hprod : (volume.restrict P).prod (volume.restrict P) = volume.restrict Q := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hsections := Measure.ae_ae_of_ae_prod
    (p := fun q ↦ G q = (z ∘ C) q) (hprod.symm ▸ he)
  filter_upwards [hsections, hline, ae_restrict_mem (s := P) measurableSet_Ioo] with x hx hL hxP
  have hclosed (b : ℝ) (hb : b ∈ Icc 0 c) : C (x, b) ∈ closure mixedOpenCell := by
    rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos])]
    have hb' : b ∈ Icc (-Real.pi / 2) c := ⟨by linarith [hb.1, Real.pi_pos], hb.2⟩
    have hx' : x ∈ Icc (-Real.pi / 2) c := ⟨by linarith [hxP.1, Real.pi_pos], hxP.2.le⟩
    fin_cases j
    · exact ⟨hb', hx'⟩
    · exact ⟨hx', hb'⟩
  have hcont : ContinuousOn (fun b ↦ z (C (x, b))) (Icc 0 c) :=
    hc.comp (hC.comp (continuous_const.prodMk continuous_id)).continuousOn hclosed
  have hEq := Measure.eqOn_open_of_ae_eq hx isOpen_Ioo
    ((hL.continuousOn_extension h0).mono Ioo_subset_Icc_self |>.congr
      (hL.extension_eq h0).symm) (hcont.mono Ioo_subset_Icc_self)
  exact hL.extension_unique h0 hcont (fun b hb ↦ (hEq hb).symm) ht

private theorem integral_even_half {f : ℝ → ℝ} (hf : IntegrableOn f J)
    (he : (fun x ↦ f (-x)) =ᵐ[volume.restrict P] f) :
    (∫ x in J, f x) = 2 * ∫ x in P, f x := by
  have h0 : 0 < c := half_pos Real.pi_pos
  have hn : -c ≤ 0 := by linarith
  have hm : 0 ≤ c := h0.le
  have hsub : Ioo (-c) (0 : ℝ) ⊆ J := Ioo_subset_Ioo le_rfl hm
  have hs : P ⊆ J := Ioo_subset_Ioo hn le_rfl
  have i₁ : IntervalIntegrable f volume (-c) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hn]
    exact hf.mono_set hsub
  have i₂ : IntervalIntegrable f volume 0 c := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hm]
    exact hf.mono_set hs
  have h := intervalIntegral.integral_add_adjacent_intervals i₁ i₂
  rw [intervalIntegral.integral_of_le hn, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hm, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (hn.trans hm), integral_Ioc_eq_integral_Ioo] at h
  have hr := intervalIntegral.integral_comp_neg (a := 0) (b := c) f
  rw [neg_zero, intervalIntegral.integral_of_le hn, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hm, integral_Ioc_eq_integral_Ioo, integral_congr_ae he] at hr
  linarith

private theorem integral_even_quarter {f : Plane → ℝ} (hf : IntegrableOn f mixedOpenCell)
    (he : ∀ j : Fin 2, f ∘ axisReflect j =ᵐ[volume.restrict mixedOpenCell] f) :
    (∫ q in mixedOpenCell, f q) = 4 * ∫ q in mixedQuarterCell, f q := by
  let μ := volume.restrict J
  let ν := volume.restrict P
  have hI : P ⊆ J := Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl
  have hJJ : μ.prod μ = volume.restrict mixedOpenCell := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, mixedOpenCell, neg_div]
  have hJP : μ.prod ν = volume.restrict (J ×ˢ P) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hPP : ν.prod ν = volume.restrict mixedQuarterCell := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hF : Integrable f (μ.prod μ) := hJJ.symm ▸ hf
  have hJPf : Integrable f (μ.prod ν) := hJP.symm ▸ hf.mono_set (by
    rw [mixedOpenCell, neg_div]
    exact prod_mono Subset.rfl hI)
  have hPPf : Integrable f (ν.prod ν) := hPP.symm ▸ hf.mono_set quarter_subset_cell
  have h1 : (∫ q, f q ∂(μ.prod μ)) = 2 * (∫ q, f q ∂(μ.prod ν)) := by
    rw [integral_prod f hF, integral_prod f hJPf]
    have hR := Measure.ae_ae_of_ae_prod (p := fun q ↦ f (q.1, -q.2) = f q)
      (hJJ.symm ▸ he 1)
    have h : (fun x ↦ ∫ t in J, f (x, t)) =ᵐ[μ] fun x ↦ 2 * ∫ t in P, f (x, t) := by
      filter_upwards [hR, hF.prod_right_ae] with x hx hi
      exact integral_even_half hi (ae_restrict_of_ae_restrict_of_subset hI hx)
    rw [integral_congr_ae h, integral_const_mul]
  have h2 : (∫ q, f q ∂(μ.prod ν)) = 2 * (∫ q, f q ∂(ν.prod ν)) := by
    rw [integral_prod_symm f hJPf, integral_prod_symm f hPPf]
    have hR := Measure.ae_ae_of_ae_prod (p := fun q ↦ f (-q.2, q.1) = f (q.2, q.1))
      ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
        (show ∀ᵐ q ∂(μ.prod μ), f (-q.1, q.2) = f q from hJJ.symm ▸ he 0))
    have h : (fun x ↦ ∫ t in J, f (t, x)) =ᵐ[ν] fun x ↦ 2 * ∫ t in P, f (t, x) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hI hR, hJPf.prod_left_ae] with x hx hi
      exact integral_even_half hi (ae_restrict_of_ae_restrict_of_subset hI hx)
    rw [integral_congr_ae h, integral_const_mul]
  rw [hJJ] at h1
  rw [hPP] at h2
  rw [h1, h2]
  ring

/-- Reflect a function with one odd and one even axis into the quarter.
Its mass and form both acquire the same factor of four. The restricted
canonical traces are the actual continuous edge values. -/
theorem mixed_fold_to_quarter (oddA : Bool) {z za zb : Plane → ℂ}
    (hz : MemSobolevOn 1 mixedOpenCell z)
    (ha : HasWeakPartialOn mixedOpenCell 0 z za) (hb : HasWeakPartialOn mixedOpenCell 1 z zb)
    (hc : ContinuousOn z (closure mixedOpenCell))
    (hp : ∀ q ∈ closure mixedOpenCell,
      z (-q.1, q.2) = (if oddA then -1 else 1) * z q ∧
      z (q.1, -q.2) = (if oddA then 1 else -1) * z q) :
    MixedQuarterFormDomain z za zb (mixedEdgeValue 1 true z) ∧
    MixedQuarterZeroTrace oddA z ∧
    (∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) =
      4 * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ∧
    mixedSecondOrderForm z za zb (fun σ ↦ mixedEdgeValue 1 σ z) =
      4 * mixedQuarterForm z za zb (mixedEdgeValue 1 true z) := by
  let j : Fin 2 := if oddA then 0 else 1
  have h₀ : 0 < c := half_pos Real.pi_pos
  have hclosed : Icc (-c) c ×ˢ Icc (-c) c = closure mixedOpenCell := by
    rw [mixedOpenCell, neg_div, closure_prod_eq, closure_Ioo (by linarith)]
  let D : List (Fin 2) → Plane → ℂ := fun w ↦
    match w with
    | [] => z
    | i :: _ => if i = 0 then za else zb
  have hD : HasWeakJetOn 1 mixedOpenCell z D := by
    refine ⟨rfl, fun w hw i ↦ ?_⟩
    cases w with
    | nil => fin_cases i <;> assumption
    | cons _ _ => simp at hw
  have hsym (k : Fin 2) : ∀ᵐ q ∂volume.restrict mixedOpenCell,
      z (axisReflect k q) = (if k = j then -1 else 1 : ℂ) * z q := by
    filter_upwards [ae_restrict_mem (μ := volume) isOpen_mixedOpenCell.measurableSet] with q hq
    have H := hp q (subset_closure hq)
    cases oddA <;> fin_cases k
    · simpa [j, axisReflect] using H.1
    · simpa [j, axisReflect] using H.2
    · simpa [j, axisReflect] using H.1
    · simpa [j, axisReflect] using H.2
  have hg (i k : Fin 2) : ∀ᵐ q ∂volume.restrict mixedOpenCell,
      (-1 : ℂ) ^ ([i] : List (Fin 2)).count k * D [i] (axisReflect k q) =
        (if k = j then -1 else 1 : ℂ) * D [i] q :=
    hD.axisReflect_entries isOpen_mixedOpenCell k (mixed_reflection_preimage k) (hsym k)
      [i] (by simp)
  refine ⟨⟨hz.mono quarter_subset_cell, ha.mono quarter_subset_cell, hb.mono quarter_subset_cell,
    fold_quarter_trace 1 (right_mem_Icc.mpr h₀.le) hz hc hb⟩, ?_, ?_, ?_⟩
  · have H : HasWeakPartialOn mixedOpenCell j z (D [j]) := by
      cases oddA
      · exact hb
      · exact ha
    have ht := fold_quarter_trace j (left_mem_Icc.mpr h₀.le) hz hc H
    obtain ⟨hl, hr, h0, G, E, hm, he, hG, hE, hA, hT⟩ := ht
    refine ⟨hl, hr, h0, G, E, hm, he, hG, hE, hA, ?_⟩
    filter_upwards [hT, ae_restrict_mem (s := P) measurableSet_Ioo] with x hx hm
    rw [← hx]
    have hx' : x ∈ Icc (-c) c := ⟨by linarith [hm.1], hm.2.le⟩
    have hz' : 0 ∈ Icc (-c) c := ⟨by linarith, h₀.le⟩
    cases oddA
    · have h := (hp (x, 0) (hclosed ▸ (show (x, 0) ∈ _ from ⟨hx', hz'⟩))).2
      simp only [neg_zero, Bool.false_eq_true, ite_false, neg_one_mul] at h
      change 0 = z (x, 0)
      linear_combination -h / 2
    · have h := (hp (0, x) (hclosed ▸ (show (0, x) ∈ _ from ⟨hz', hx'⟩))).1
      simp only [neg_zero, ite_true, neg_one_mul] at h
      change 0 = z (0, x)
      linear_combination -h / 2
  · apply integral_even_quarter (mixed_cos_sq_mul_integrable hz.memLp)
    intro k
    filter_upwards [hsym k] with q h
    change Real.cos (axisReflect k q).1 ^ 2 * ‖z (axisReflect k q)‖ ^ 2 = _
    rw [h]
    cases oddA <;> fin_cases k <;> simp [axisReflect, j]
  · have hvol := integral_even_quarter
      (mixed_density_integrable hz.memLp (fold_partial_memLp hz ha) (fold_partial_memLp hz hb))
      (f := mixedSecondOrderDensity z za zb) (by
        intro k
        filter_upwards [hg 0 k, hg 1 k, hsym k] with q hA hB hZ
        change mixedSecondOrderDensity z za zb (axisReflect k q) = _
        cases oddA <;> fin_cases k <;>
          simp only [D, j, axisReflect, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero,
            Bool.false_eq_true, ite_true, ite_false, List.count_cons, List.count_nil,
            beq_self_eq_true, show ((1 : Fin 2) == 0) = false by decide,
            show ((0 : Fin 2) == 1) = false by decide,
            zero_add, pow_zero, pow_one, one_mul, neg_one_mul, neg_inj,
            show (0 : Fin 2) ≠ 1 by decide] at hA hB hZ
        · have hA' := neg_eq_iff_eq_neg.mp hA
          simp [mixedSecondOrderDensity, mixedGradientForm, mixedComparisonDiagonal,
            mixedComparisonPotential, mixedComparisonOffDiagonal, axisReflect, hA', hB, hZ,
            mul_neg, neg_mul]
          ring
        · simp [mixedSecondOrderDensity, mixedGradientForm, mixedComparisonDiagonal,
            mixedComparisonPotential, mixedComparisonOffDiagonal, axisReflect, hA, hB, hZ,
            mul_neg, neg_mul]
          ring
        · simp [mixedSecondOrderDensity, mixedGradientForm, mixedComparisonDiagonal,
            mixedComparisonPotential, mixedComparisonOffDiagonal, axisReflect, hA, hB, hZ,
            mul_neg, neg_mul]
          ring
        · have hB' := neg_eq_iff_eq_neg.mp hB
          simp [mixedSecondOrderDensity, mixedGradientForm, mixedComparisonDiagonal,
            mixedComparisonPotential, mixedComparisonOffDiagonal, axisReflect, hA, hB', hZ,
            mul_neg, neg_mul]
          ring)
    have hEdge (x : ℝ) (hx : x ∈ J) :
        ‖z (x, -c)‖ = ‖z (x, c)‖ := by
      have hm : (x, c) ∈ closure mixedOpenCell := hclosed ▸
        (show (x, c) ∈ Icc (-c) c ×ˢ Icc (-c) c from
          ⟨Ioo_subset_Icc_self hx, right_mem_Icc.mpr (by linarith)⟩)
      have H := (hp (x, c) hm).2
      change ‖z (x, -(c : ℝ))‖ = _
      rw [H]
      cases oddA <;> simp
    let f := fun x ↦ Real.cos x * ‖z (x, c)‖ ^ 2
    have hTop : (∫ x in J, f x) = 2 * ∫ x in P, f x := by
      apply integral_even_half (by
        simpa only [neg_div, f, mixedEdgeValue, axisTraceChart, one_ne_zero, ite_false,
          cellEdgeNormal, ite_true] using mixed_edge_integrable hc true)
      filter_upwards [ae_restrict_mem (s := P) measurableSet_Ioo] with x hx
      have hm : (x, c) ∈ closure mixedOpenCell := hclosed ▸
        (show (x, c) ∈ Icc (-c) c ×ˢ Icc (-c) c from
          ⟨⟨by linarith [hx.1], hx.2.le⟩, right_mem_Icc.mpr (by linarith)⟩)
      have H := (hp (x, c) hm).1
      change Real.cos (-x) * ‖z (-x, c)‖ ^ 2 = _
      rw [Real.cos_neg, H]
      cases oddA <;> simp [f]
    have hBot : (∫ x in J, Real.cos x * ‖z (x, -c)‖ ^ 2) = ∫ x in J, f x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s := J) measurableSet_Ioo] with x hx
      rw [hEdge x hx]
    unfold mixedSecondOrderForm mixedQuarterForm
    rw [hvol, Fintype.sum_bool, neg_div]
    simp only [mixedEdgeValue, axisTraceChart, one_ne_zero, ite_false, cellEdgeNormal,
      Bool.false_eq_true, ite_true, neg_div]
    change 4 * (∫ q in mixedQuarterCell, mixedSecondOrderDensity z za zb q) +
        ((∫ x in J, f x) + ∫ x in J, Real.cos x * ‖z (x, -c)‖ ^ 2) =
      4 * ((∫ q in mixedQuarterCell, mixedSecondOrderDensity z za zb q) + ∫ x in P, f x)
    rw [hBot, hTop]
    ring

end QuarterFold

/-- The same orthogonal parity decomposition for the weighted mass. -/
theorem mixed_parity_mass {ω : L2} (d : MixedQuotientData ω) :
    let mass := fun (f : Plane → ℂ) ↦ ∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖f q‖ ^ 2
    mass d.phi = mass (mixedParityPart true d.phi) + mass (mixedParityPart false d.phi) := by
  let μ := volume.restrict mixedOpenCell
  let m := fun (f : Plane → ℂ) q ↦ Real.cos q.1 ^ 2 * ‖f q‖ ^ 2
  let R := axisReflect 0
  have hm : MeasurePreserving R μ μ := mixed_reflection_mp 0
  have hφ := d.h2.memLp
  have hφR := hφ.comp_measurePreserving hm
  have hLp (oddA : Bool) : MemLp (mixedParityPart oddA d.phi) 2 μ := by
    convert ((hφ.add (hφR.const_mul (if oddA then -1 else 1))).const_mul (1 / 2 : ℂ)) using 1
    funext q
    change (_ + _ * d.phi (R q)) / 2 = (1 / 2) * (_ + _ * d.phi (R q))
    ring
  have hI : Integrable (m d.phi) μ := mixed_cos_sq_mul_integrable hφ
  have hIR := hm.integrable_comp_of_integrable hI
  have hsum : (fun q ↦ m (mixedParityPart true d.phi) q + m (mixedParityPart false d.phi) q) =
      fun q ↦ (m d.phi q + (m d.phi ∘ R) q) / 2 := by
    funext q
    simp only [m, mixedParityPart, ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul,
      ← sub_eq_add_neg, Function.comp_apply, show R q = (-q.1, q.2) from rfl,
      Real.cos_neg, norm_div]
    norm_num
    have hP := parallelogram_law_with_norm ℂ (d.phi q) (d.phi (-q.1, q.2))
    linarith only [congrArg (fun x : ℝ ↦ Real.cos q.1 ^ 2 * x) hP]
  change (∫ q, m d.phi q ∂μ) = _
  rw [← integral_add (mixed_cos_sq_mul_integrable (hLp true))
    (mixed_cos_sq_mul_integrable (hLp false)), hsum, integral_div,
    integral_add hI hIR]
  rw [mixed_reflection_integral 0 (m d.phi)]
  ring

/-- Lower bound for the second-order part from the two quarter comparisons.
This isolates parity reduction and the Robin bounds from square completion. -/
theorem mixed_second_order_coercivity {ω : L2} (d : MixedQuotientData ω) :
    (1 / 200 : ℝ) * (∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖d.phi q‖ ^ 2) ≤
      mixedSecondOrderForm d.phi (d.jet [0]) (d.jet [1]) (fun σ ↦ mixedEdgeValue 1 σ d.phi) := by
  obtain ⟨hp, Ua, Ub, Va, Vb, hU, hV, hUa, hUb, hVa, hVb, hsplit⟩ := mixed_parity_split d
  have hc (oddA : Bool) : ContinuousOn (mixedParityPart oddA d.phi) (closure mixedOpenCell) :=
    (d.continuous.add (continuousOn_const.mul
      (d.continuous.comp (by rw [← planeAffine_axisReflectionLinear]; fun_prop)
        (mixed_closed_reflect 0)))).div_const _
  obtain ⟨hUq, hUz, hUm, hUf⟩ :=
    mixed_fold_to_quarter true hU hUa hUb (hc true) (fun q hq ↦ by
      simpa only [ite_true, one_mul, neg_one_mul] using ⟨(hp q hq).2.1, (hp q hq).2.2.1⟩)
  obtain ⟨hVq, hVz, hVm, hVf⟩ :=
    mixed_fold_to_quarter false hV hVa hVb (hc false) (fun q hq ↦ by
      simpa only [Bool.false_eq_true, ite_false, one_mul, neg_one_mul] using (hp q hq).2.2.2)
  have hUc := mixed_quarter_coercivity true hUq hUz
  have hVc := mixed_quarter_coercivity false hVq hVz
  have hm := mixed_parity_mass d
  dsimp only at hm
  rw [hsplit, hUf, hVf, hm, hUm, hVm]
  linarith

/-- H¹ bound for the second-order form with canonical traces. As this is a
real quadratic form, the norm bound gives continuity by polarization. -/
theorem mixed_second_order_form_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ da db : Plane → ℂ) (edge : Bool → ℝ → ℂ),
      MemSobolevOn 1 mixedOpenCell φ →
      HasWeakPartialOn mixedOpenCell 0 φ da → HasWeakPartialOn mixedOpenCell 1 φ db →
      (∀ σ, HasMixedEdgeTrace 1 σ φ (edge σ)) →
      |mixedSecondOrderForm φ da db edge| ≤
        C * ∫ q in mixedOpenCell, ‖φ q‖ ^ 2 + ‖da q‖ ^ 2 + ‖db q‖ ^ 2 := by
  let I := Ioo (-Real.pi / 2) (Real.pi / 2)
  let w := Real.pi / 2 - (-Real.pi / 2)
  have hw : 0 < w := by dsimp [w]; linarith [Real.pi_pos]
  let C : ℝ := 5 + 2 * (2 / w + 2 * w)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro φ da db edge hz ha hb he
  let E := fun q ↦ ‖φ q‖ ^ 2 + ‖da q‖ ^ 2 + ‖db q‖ ^ 2
  have hF := hz.memLp
  have hA := fold_partial_memLp hz ha
  have hB := fold_partial_memLp hz hb
  have hE : IntegrableOn E mixedOpenCell :=
    (hF.norm.integrable_sq.add hA.norm.integrable_sq).add hB.norm.integrable_sq
  have hD := mixed_density_integrable hF hA hB
  have hbulk : |∫ q in mixedOpenCell, mixedSecondOrderDensity φ da db q| ≤
      5 * ∫ q in mixedOpenCell, E q := by
    rw [← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hD.norm (hE.const_mul 5) ?_)
    filter_upwards [ae_restrict_mem isOpen_mixedOpenCell.measurableSet] with q hq
    obtain ⟨hv₀, hv₁, hd, hj⟩ := mixed_comparison_coefficient_bounds hq
    have hd₀ := (mixed_comparison_matrix_positive hq).1
    have hcross : ‖(da q * conj (db q)).re‖ ≤ (‖da q‖ ^ 2 + ‖db q‖ ^ 2) / 2 := by
      rw [Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      nlinarith only [sq_nonneg (‖da q‖ - ‖db q‖)]
    have hpos : 0 ≤ ‖da q‖ ^ 2 + ‖db q‖ ^ 2 := by positivity
    unfold mixedSecondOrderDensity mixedGradientForm
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)) |>.trans ?_
    simp only [norm_mul, Real.norm_of_nonneg hd₀.le, Real.norm_of_nonneg hpos,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.norm_of_nonpos (neg_nonneg.mp hv₀), Real.norm_of_nonneg (sq_nonneg ‖φ q‖)]
    have e₁ := mul_le_mul_of_nonneg_right hd hpos
    have e₂ : 2 * ‖mixedComparisonOffDiagonal q‖ * ‖(da q * conj (db q)).re‖ ≤
        2 * (‖da q‖ ^ 2 + ‖db q‖ ^ 2) := by
      calc
        _ ≤ 2 * 2 * ((‖da q‖ ^ 2 + ‖db q‖ ^ 2) / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hj (by norm_num)) hcross
            (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have e₃ := mul_le_mul_of_nonneg_right hv₁ (sq_nonneg ‖φ q‖)
    dsimp [E]
    simp only [Real.norm_eq_abs] at e₂
    linarith only [e₁, e₂, e₃, sq_nonneg ‖φ q‖]
  have htrace (σ : Bool) :
      |∫ a in I, Real.cos a * ‖edge σ a‖ ^ 2| ≤
        (2 / w + 2 * w) * ∫ q in mixedOpenCell, E q := by
    obtain ⟨hL, hbd⟩ := (he σ).l2_estimate_of_weak_snd hb hB
    have hI := hL.norm.integrable_sq
    have hW := hI.bdd_mul Real.continuous_cos.aestronglyMeasurable
      (c := 1) (Eventually.of_forall fun a ↦ Real.abs_cos_le_one a)
    have hi : |∫ a in I, Real.cos a * ‖edge σ a‖ ^ 2| ≤ ∫ a in I, ‖edge σ a‖ ^ 2 := by
      refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hW.norm hI ?_)
      exact Eventually.of_forall fun a ↦ by
        change ‖Real.cos a * ‖edge σ a‖ ^ 2‖ ≤ ‖edge σ a‖ ^ 2
        rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_of_le_one_left (sq_nonneg _) (Real.abs_cos_le_one _)
    have hfE : (∫ q in mixedOpenCell, ‖φ q‖ ^ 2) ≤ ∫ q in mixedOpenCell, E q :=
      integral_mono_ae hF.norm.integrable_sq hE (.of_forall fun q ↦ by
        dsimp [E]; linarith only [sq_nonneg ‖da q‖, sq_nonneg ‖db q‖])
    have hbE : (∫ q in mixedOpenCell, ‖db q‖ ^ 2) ≤ ∫ q in mixedOpenCell, E q :=
      integral_mono_ae hB.norm.integrable_sq hE (.of_forall fun q ↦ by
        dsimp [E]; linarith only [sq_nonneg ‖φ q‖, sq_nonneg ‖da q‖])
    refine hi.trans (hbd.trans ?_)
    change (2 / w) * (∫ q in mixedOpenCell, ‖φ q‖ ^ 2) + 2 * w *
      (∫ q in mixedOpenCell, ‖db q‖ ^ 2) ≤ _
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hfE (by positivity))
      (mul_le_mul_of_nonneg_left hbE (by positivity))
  unfold mixedSecondOrderForm
  rw [Fintype.sum_bool]
  change |(∫ q in mixedOpenCell, mixedSecondOrderDensity φ da db q) +
    ((∫ a in I, Real.cos a * ‖edge true a‖ ^ 2) + ∫ a in I, Real.cos a * ‖edge false a‖ ^ 2)| ≤ _
  refine (abs_add_le _ _).trans ((add_le_add hbulk
    ((abs_add_le _ _).trans (add_le_add (htrace true) (htrace false)))).trans_eq ?_)
  dsimp [C]
  ring

/-- Cartesian stream mass equals twice the diagonal weighted quotient mass. -/
theorem MixedQuotientData.stream_mass {ω : L2} (d : MixedQuotientData ω) :
    (∫ p in cellSquare, ‖liftL2 (invLap ω) p‖ ^ 2) =
      2 * (∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖d.phi q‖ ^ 2) := by
  let f := fun p ↦ ‖liftL2 (invLap ω) p‖ ^ 2
  change (∫ p in cellSquare, f p) = _
  have hpre : diagInv ⁻¹' cellSquare = mixedOpenCell := by
    ext q
    simp only [mixedOpenCell, cellSquare, mem_preimage, mem_ofPred_eq, diagCoord_diagInv,
      abs_lt, neg_div, mem_prod, mem_Ioo]
  have hm : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  rw [← integral_indicator hm, integral_eq_two_smul_integral_diagInv]
  have hind : (fun q ↦ cellSquare.indicator f (diagInv q)) =
      mixedOpenCell.indicator (f ∘ diagInv) := by
    rw [← hpre]
    funext q
    exact (Set.indicator_comp_right (⇑diagInv)).symm
  have hmo : MeasurableSet mixedOpenCell := (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  rw [hind, integral_indicator hmo, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [d.stream_eq] with q hq
  change ‖liftL2 (invLap ω) (diagInv q)‖ ^ 2 = _
  rw [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

end NoEmbeddedEigenvalues
