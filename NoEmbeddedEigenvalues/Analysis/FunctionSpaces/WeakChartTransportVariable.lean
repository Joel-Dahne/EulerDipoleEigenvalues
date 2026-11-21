module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakChartTransport

/-!
# Weak transport through variable-Jacobian charts of fixed orientation

Blueprint: `lem:oriented-weak-chart`, `lem:negative-jacobian-weak-partial`.

The cofactor column is divergence-free even when the Jacobian varies. Testing
against this column times a pulled-back test cancels its differentiated terms.
The signed determinant on the source matches the absolute area Jacobian with
one common orientation factor on both integrals. Local integrability of the specified
physical entries is supplied separately; it is not inferred from an equality
of totalized integrals.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- A chart with constant orientation transports the specified weak pair.
The target functions and their local integrability are retained, rather than
replaced by inverse-coordinate representatives. -/
theorem HasWeakPartialOn.of_comp_chart_oriented
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (σ : ℝ) (hdet : ∀ q ∈ e.source, |(fderiv ℝ e q).det| = σ * (fderiv ℝ e q).det)
    {f d F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn e.source i F (G i))
    (hf : LocallyIntegrableOn f e.target) (hd : LocallyIntegrableOn d e.target)
    (j : Fin 2) (hv : ∀ q ∈ e.source, f (e q) = F q)
    (hgval : ∀ q ∈ e.source, ((fderiv ℝ e q).det : ℂ) * d (e q) =
      chartCofactor e j 0 q * G 0 q + chartCofactor e j 1 q * G 1 q) :
    HasWeakPartialOn e.target j f d := by
  refine ⟨hf, hd, ?_⟩
  intro φ hφ
  let ψ := chartTest e φ
  have hψ := isTestFunctionOn_chartTest he hφ
  have hC (i : Fin 2) := contDiffOn_chartCofactor he j i
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
  have hzero {V : Set (ℝ × ℝ)} (B : ℝ × ℝ → ℂ) {χ : ℝ × ℝ → ℂ}
      (hχ : IsTestFunctionOn V χ) :
      (∫ q, B q * χ q) = ∫ q in V, B q * χ q :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hq (hχ.tsupport_subset h)), mul_zero]).symm
  have hchange (B : ℝ × ℝ → ℂ) {χ : ℝ × ℝ → ℂ}
      (hχ : IsTestFunctionOn e.target χ) :
      (∫ p, B p * χ p) = ∫ q in e.source,
        Complex.ofReal |(fderiv ℝ e q).det| * B (e q) * χ (e q) := by
    rw [hzero B hχ, integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun q hq ↦ ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt
        (by simp)).hasFDerivAt)]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro q _
    dsimp only
    rw [Complex.real_smul]
    ring
  have hsum {q : ℝ × ℝ} (hq : q ∈ e.source) :
      coordPartial 0 (τ 0) q + coordPartial 1 (τ 1) q =
        ((fderiv ℝ e q).det : ℂ) * coordPartial j φ (e q) := by
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
        chartTest_cofactor_chain_det he hφ j hq]; ring
  have hleft :
      (σ : ℂ) * ((∫ q, F q * coordPartial 0 (τ 0) q) +
        (∫ q, F q * coordPartial 1 (τ 1) q)) =
          ∫ p, f p * coordPartial j φ p := by
    rw [hzero F (hτd 0), hzero F (hτd 1),
      ← integral_add (hi 0).integrableOn (hi 1).integrableOn,
      ← integral_const_mul, hchange f hφd]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro q hq
    dsimp only
    rw [← mul_add, hsum hq, hv q hq, hdet q hq, Complex.ofReal_mul]
    ring
  have hright :
      (σ : ℂ) * ((∫ q, G 0 q * τ 0 q) + (∫ q, G 1 q * τ 1 q)) =
        ∫ p, d p * φ p := by
    rw [hzero (G 0) (hτ 0), hzero (G 1) (hτ 1),
      ← integral_add (hk 0).integrableOn (hk 1).integrableOn,
      ← integral_const_mul, hchange d hφ]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro q hq
    dsimp only [τ, ψ]
    rw [chartTest_eq e φ hq, hdet q hq, Complex.ofReal_mul]
    linear_combination -(σ : ℂ) * φ (e q) * hgval q hq
  have hw := congrArg₂ (· + ·) ((hg 0).2.2 (τ 0) (hτ 0))
    ((hg 1).2.2 (τ 1) (hτ 1))
  rw [← neg_add] at hw
  rw [← hleft, hw, mul_neg, hright]

/-- A variable negative-Jacobian chart transports the specified weak pair.
The target functions and their local integrability are retained, rather than
replaced by inverse-coordinate representatives. -/
theorem HasWeakPartialOn.of_comp_chart_neg
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det < 0)
    {f d F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn e.source i F (G i))
    (hf : LocallyIntegrableOn f e.target) (hd : LocallyIntegrableOn d e.target)
    (j : Fin 2) (hv : ∀ q ∈ e.source, f (e q) = F q)
    (hgval : ∀ q ∈ e.source, ((fderiv ℝ e q).det : ℂ) * d (e q) =
      chartCofactor e j 0 q * G 0 q + chartCofactor e j 1 q * G 1 q) :
    HasWeakPartialOn e.target j f d := by
  apply HasWeakPartialOn.of_comp_chart_oriented he (-1) _ hg hf hd j hv hgval
  intro q hq
  rw [abs_of_neg (hdet q hq)]
  ring

/-- A variable positive-Jacobian chart transports the specified weak pair.
The target functions and their local integrability are retained, rather than
replaced by inverse-coordinate representatives. -/
theorem HasWeakPartialOn.of_comp_chart_pos
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, 0 < (fderiv ℝ e q).det)
    {f d F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn e.source i F (G i))
    (hf : LocallyIntegrableOn f e.target) (hd : LocallyIntegrableOn d e.target)
    (j : Fin 2) (hv : ∀ q ∈ e.source, f (e q) = F q)
    (hgval : ∀ q ∈ e.source, ((fderiv ℝ e q).det : ℂ) * d (e q) =
      chartCofactor e j 0 q * G 0 q + chartCofactor e j 1 q * G 1 q) :
    HasWeakPartialOn e.target j f d := by
  apply HasWeakPartialOn.of_comp_chart_oriented he 1 _ hg hf hd j hv hgval
  intro q hq
  rw [abs_of_pos (hdet q hq), one_mul]

end NoEmbeddedEigenvalues
