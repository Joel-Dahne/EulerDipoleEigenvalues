import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SmoothChartTests
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TransversalMollifier

/-!
# Weak derivatives through a constant-Jacobian plane chart

Blueprint: `def:smooth-chart-cofactor`, `lem:smooth-chart-weak-gradient`.

The rotated derivatives of a chart component are a divergence-free cofactor
column. Testing both supplied weak coordinate derivatives against this column
cancels all zeroth-order terms. The determinant supplies the remaining factor
two, exactly matching change of variables. No Sobolev density is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A potential for the cofactor column corresponding to a spatial coordinate. -/
def chartDualPotential (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  if j = 0 then (e q).2 else -(e q).1

/-- The divergence-free cofactor column, before division by the determinant. -/
def chartCofactor (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (j i : Fin 2) (q : ℝ × ℝ) : ℂ :=
  if i = 0 then partialY (chartDualPotential e j) q
  else -partialX (chartDualPotential e j) q

/-- Cartesian derivative candidate in source coordinates. -/
def chartGradient (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (G : Fin 2 → ℝ × ℝ → ℂ) (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  (chartCofactor e j 0 q * G 0 q + chartCofactor e j 1 q * G 1 q) / 2

lemma contDiffOn_chartDualPotential {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source) (j : Fin 2) :
    ContDiffOn ℝ ∞ (chartDualPotential e j) e.source := by
  unfold chartDualPotential
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_snd.comp_contDiffOn he)
  · exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_fst.comp_contDiffOn he)).neg

lemma contDiffOn_chartCofactor {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source) (j i : Fin 2) :
    ContDiffOn ℝ ∞ (chartCofactor e j i) e.source := by
  unfold chartCofactor
  split_ifs
  · exact contDiffOn_coordPartial e.open_source (contDiffOn_chartDualPotential he j) 1
  · exact (contDiffOn_coordPartial e.open_source (contDiffOn_chartDualPotential he j) 0).neg

lemma chartCofactor_divergence {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source) (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ e.source) :
    coordPartial 0 (chartCofactor e j 0) q +
      coordPartial 1 (chartCofactor e j 1) q = 0 := by
  change partialX (partialY (chartDualPotential e j)) q +
    partialY (fun r ↦ -partialX (chartDualPotential e j) r) q = 0
  have hn : partialY (fun r ↦ -partialX (chartDualPotential e j) r) q =
      -partialY (partialX (chartDualPotential e j)) q := deriv.neg
  rw [hn, partialY_partialX_at
    ((contDiffOn_chartDualPotential he j).contDiffAt (e.open_source.mem_nhds hq))]
  ring

lemma chartCofactor_values {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source) (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ e.source) :
    chartCofactor e j 0 q =
      (if j = 0 then ((fderiv ℝ e q (0, 1)).2 : ℂ)
       else -((fderiv ℝ e q (0, 1)).1 : ℂ)) ∧
    chartCofactor e j 1 q =
      (if j = 0 then -((fderiv ℝ e q (1, 0)).2 : ℂ)
       else ((fderiv ℝ e q (1, 0)).1 : ℂ)) := by
  have hd := ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hx := hd.comp_hasDerivAt q.1 ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have hy := hd.comp_hasDerivAt q.2 ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  have hx₁ := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q.1
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 hx)
  have hx₂ := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q.1
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 hx)
  have hy₁ := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q.2
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hy)
  have hy₂ := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q.2
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hy)
  by_cases hj : j = 0
  · constructor
    · simpa [chartCofactor, chartDualPotential, hj, partialY, Function.comp_def] using hy₂.deriv
    · simpa [chartCofactor, chartDualPotential, hj, partialX, Function.comp_def] using
        congrArg Neg.neg hx₂.deriv
  · constructor
    · simpa [chartCofactor, chartDualPotential, hj, partialY, Function.comp_def] using hy₁.neg.deriv
    · simpa [chartCofactor, chartDualPotential, hj, partialX, Function.comp_def] using
        congrArg Neg.neg hx₁.neg.deriv

/-- The cofactor column converts source differentiation of a pulled-back test
to spatial differentiation multiplied by the determinant. -/
lemma chartTest_cofactor_chain_det {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn e.target φ)
    (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ e.source) :
    chartCofactor e j 0 q * coordPartial 0 (chartTest e φ) q +
      chartCofactor e j 1 q * coordPartial 1 (chartTest e φ) q =
      ((fderiv ℝ e q).det : ℂ) * coordPartial j φ (e q) := by
  let A := fderiv ℝ e q
  have hd := (he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt (by simp)
  have hp := hφ.contDiff.differentiable (by simp) (e q)
  have hx := hd.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have hy := hd.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  have hl (v : ℝ × ℝ) : fderiv ℝ φ (e q) v =
      (v.1 : ℂ) * partialX φ (e q) + (v.2 : ℂ) * partialY φ (e q) := by
    rw [partialX_eq_fderiv hp, partialY_eq_fderiv hp]
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hnear : chartTest e φ =ᶠ[𝓝 q] φ ∘ e := by
    filter_upwards [e.open_source.mem_nhds hq] with r hr
    exact chartTest_eq e φ hr
  have hc₀ : coordPartial 0 (chartTest e φ) q =
      ((A (1, 0)).1 : ℂ) * partialX φ (e q) +
        ((A (1, 0)).2 : ℂ) * partialY φ (e q) := by
    rw [coordPartial_congr_nhds hnear 0]
    change deriv (fun x ↦ φ (e (x, q.2))) q.1 = _
    convert! (hp.hasFDerivAt.comp_hasDerivAt q.1 hx).deriv.trans (hl _) using 1
  have hc₁ : coordPartial 1 (chartTest e φ) q =
      ((A (0, 1)).1 : ℂ) * partialX φ (e q) +
        ((A (0, 1)).2 : ℂ) * partialY φ (e q) := by
    rw [coordPartial_congr_nhds hnear 1]
    change deriv (fun t ↦ φ (e (q.1, t))) q.2 = _
    convert! (hp.hasFDerivAt.comp_hasDerivAt q.2 hy).deriv.trans (hl _) using 1
  have hr : (A (1, 0)).1 * (A (0, 1)).2 -
      (A (0, 1)).1 * (A (1, 0)).2 = A.det := by
    have h : LinearMap.det (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = A.det := rfl
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two] at h
    simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
      Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    convert! h using 1
  have hc : ((A (1, 0)).1 : ℂ) * ((A (0, 1)).2 : ℂ) -
      ((A (0, 1)).1 : ℂ) * ((A (1, 0)).2 : ℂ) = (A.det : ℂ) := by exact_mod_cast hr
  rw [hc₀, hc₁, (chartCofactor_values he j hq).1, (chartCofactor_values he j hq).2]
  by_cases hj : j = 0
  · simp only [hj, ite_eq_left, coordPartial]
    linear_combination partialX φ (e q) * hc
  · simp only [hj, ite_false, coordPartial]
    linear_combination partialY φ (e q) * hc

lemma chartTest_cofactor_chain {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn e.target φ)
    (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ e.source) :
    chartCofactor e j 0 q * coordPartial 0 (chartTest e φ) q +
      chartCofactor e j 1 q * coordPartial 1 (chartTest e φ) q =
      (2 : ℂ) * coordPartial j φ (e q) := by
  rw [chartTest_cofactor_chain_det he hφ j hq, hdet q hq]
  norm_num

/-- Two specified weak coordinate derivatives reconstruct a specified Cartesian
weak derivative on the chart image. -/
theorem HasWeakPartialOn.comp_chart_symm
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    {F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn e.source i F (G i)) (j : Fin 2) :
    HasWeakPartialOn e.target j (F ∘ e.symm) (chartGradient e G j ∘ e.symm) := by
  have hC (i : Fin 2) := contDiffOn_chartCofactor he j i
  have hS := ((hg 0).2.1.continuousOn_mul (hC 0).continuousOn
    e.open_source.isLocallyClosed).add
    ((hg 1).2.1.continuousOn_mul (hC 1).continuousOn e.open_source.isLocallyClosed)
  have hL : LocallyIntegrableOn (chartGradient e G j) e.source := by
    convert hS.continuousOn_mul (continuousOn_const (c := (2 : ℂ)⁻¹))
      e.open_source.isLocallyClosed using 1
    funext q
    dsimp [chartGradient]
    ring
  refine ⟨locallyIntegrableOn_comp_chart_symm he hdet (hg 0).1,
    locallyIntegrableOn_comp_chart_symm he hdet hL, ?_⟩
  intro φ hφ
  let ψ := chartTest e φ
  have hψ := isTestFunctionOn_chartTest he hφ
  let τ (i : Fin 2) := fun q ↦ chartCofactor e j i q * ψ q
  have hτ (i : Fin 2) : IsTestFunctionOn e.source (τ i) :=
    hψ.mul_contDiffOn e.open_source (hC i)
  have hτd (i : Fin 2) : IsTestFunctionOn e.source (coordPartial i (τ i)) :=
    ⟨contDiff_coordPartial_top i (hτ i).contDiff, (hτ i).hasCompactSupport_coordPartial i,
      (tsupport_coordPartial_subset i _).trans (hτ i).tsupport_subset⟩
  have hi (i : Fin 2) := integrable_mul_of_tsupport_subset (hg 0).1
    (hτd i).contDiff.continuous (hτd i).hasCompactSupport (hτd i).tsupport_subset
  have hk (i : Fin 2) := integrable_mul_of_tsupport_subset (hg i).2.1
    (hτ i).contDiff.continuous (hτ i).hasCompactSupport (hτ i).tsupport_subset
  have hφd : IsTestFunctionOn e.target (coordPartial j φ) :=
    ⟨contDiff_coordPartial_top j hφ.contDiff, hφ.hasCompactSupport_coordPartial j,
      (tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset⟩
  have hzero (B : ℝ × ℝ → ℂ) {χ : ℝ × ℝ → ℂ} (hχ : IsTestFunctionOn e.source χ) :
      (∫ q, B q * χ q) = ∫ q in e.source, B q * χ q :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hq (hχ.tsupport_subset h)), mul_zero]).symm
  have hsum {q : ℝ × ℝ} (hq : q ∈ e.source) :
      coordPartial 0 (τ 0) q + coordPartial 1 (τ 1) q =
        (2 : ℂ) * coordPartial j φ (e q) := by
    dsimp only [τ]
    rw [coordPartial_mul_at ((hC 0).contDiffAt (e.open_source.mem_nhds hq)
        |>.differentiableAt (by simp)) (hψ.contDiff.differentiable (by simp) q) 0,
      coordPartial_mul_at ((hC 1).contDiffAt (e.open_source.mem_nhds hq)
        |>.differentiableAt (by simp)) (hψ.contDiff.differentiable (by simp) q) 1]
    calc
      _ = (coordPartial 0 (chartCofactor e j 0) q +
          coordPartial 1 (chartCofactor e j 1) q) * ψ q +
        (chartCofactor e j 0 q * coordPartial 0 ψ q +
          chartCofactor e j 1 q * coordPartial 1 ψ q) := by ring
      _ = _ := by rw [chartCofactor_divergence he j hq,
        chartTest_cofactor_chain he hdet hφ j hq]; ring
  have hleft :
      (∫ q, F q * coordPartial 0 (τ 0) q) +
        (∫ q, F q * coordPartial 1 (τ 1) q) =
          ∫ p, (F ∘ e.symm) p * coordPartial j φ p := by
    rw [hzero F (hτd 0), hzero F (hτd 1),
      ← integral_add (hi 0).integrableOn (hi 1).integrableOn,
      integral_mul_test_chart he hdet (F ∘ e.symm) hφd]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro q hq
    simp only [Function.comp_apply, e.left_inv hq]
    rw [← mul_add, hsum hq]
    ring
  have hright :
      (∫ q, G 0 q * τ 0 q) + (∫ q, G 1 q * τ 1 q) =
        ∫ p, (chartGradient e G j ∘ e.symm) p * φ p := by
    rw [hzero (G 0) (hτ 0), hzero (G 1) (hτ 1),
      ← integral_add (hk 0).integrableOn (hk 1).integrableOn,
      integral_mul_test_chart he hdet (chartGradient e G j ∘ e.symm) hφ]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro q hq
    simp only [Function.comp_apply, e.left_inv hq]
    dsimp only [τ, ψ, chartGradient]
    rw [chartTest_eq e φ hq]
    ring
  have hw := congrArg₂ (· + ·) ((hg 0).2.2 (τ 0) (hτ 0))
    ((hg 1).2.2 (τ 1) (hτ 1))
  rw [← neg_add, hleft, hright] at hw
  exact hw

end NoEmbeddedEigenvalues
