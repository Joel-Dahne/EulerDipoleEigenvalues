import NoEmbeddedEigenvalues.Analysis.LocalSobolev.PlaneConvolution
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.LineMollifier

/-!
# Compact Cartesian mollification in L²

A normalized bump averages translations. The averaging contraction bounds the
error by the largest translation error on its support. A translated test also
moves a classical kernel derivative onto the specified weak derivative.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology Pointwise

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Differentiation of a smoothing may use the specified global weak derivative. -/
theorem coordPartial_planeConvolution_of_weak {f d k : ℝ × ℝ → ℂ} {j : Fin 2}
    (hf : LocallyIntegrable f) (hd : HasWeakPartialOn univ j f d)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    coordPartial j (planeConvolution f k) = planeConvolution d k := by
  funext x
  rw [coordPartial_planeConvolution hf hk hc]
  have ht := isTestFunctionOn_kernelTranslate hk hc x (fun _ _ ↦ mem_univ _)
  have he := hd.2.2 _ ht
  simp_rw [coordPartial_comp_sub_left (hk.differentiable (by simp)) j x,
    mul_neg, integral_neg] at he
  exact neg_injective he

/-- Normalized real bump, viewed as a complex kernel for Cartesian convolution. -/
def planeBumpKernel (b : ContDiffBump (0 : ℝ × ℝ)) (p : ℝ × ℝ) : ℂ :=
  b.normed volume p

theorem contDiff_planeBumpKernel (b : ContDiffBump (0 : ℝ × ℝ)) :
    ContDiff ℝ ∞ (planeBumpKernel b) :=
  Complex.ofRealCLM.contDiff.comp b.contDiff_normed

theorem tsupport_planeBumpKernel (b : ContDiffBump (0 : ℝ × ℝ)) :
    tsupport (planeBumpKernel b) ⊆ closedBall 0 b.rOut :=
  (tsupport_comp_subset Complex.ofReal_zero (b.normed volume)).trans_eq b.tsupport_normed_eq

theorem hasCompactSupport_planeBumpKernel (b : ContDiffBump (0 : ℝ × ℝ)) :
    HasCompactSupport (planeBumpKernel b) :=
  (isCompact_closedBall 0 b.rOut).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_planeBumpKernel b)

/-- Convolution by a kernel of radius `r` enlarges support by at most `r`. -/
theorem tsupport_planeConvolution_subset_cthickening {f k : ℝ × ℝ → ℂ} {r : ℝ}
    (hk : tsupport k ⊆ closedBall 0 r) :
    tsupport (planeConvolution f k) ⊆ cthickening r (tsupport f) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  have h := support_convolution_subset (L := mul ℝ ℂ) hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact mem_cthickening_of_dist_le (a + b) a r (tsupport f) (subset_closure ha)
    (by simpa [dist_eq_norm, add_sub_cancel_left] using hk (subset_closure hb))

private def bumpMeasure (b : ContDiffBump (0 : ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  volume.withDensity fun t ↦ ENNReal.ofReal (b.normed volume t)

private theorem isProbabilityMeasure_bumpMeasure (b : ContDiffBump (0 : ℝ × ℝ)) :
    IsProbabilityMeasure (bumpMeasure b) := by
  apply IsProbabilityMeasure.mk
  rw [bumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (b.continuous_normed.integrable_of_hasCompactSupport b.hasCompactSupport_normed)
    (Eventually.of_forall fun t ↦ b.nonneg_normed t), b.integral_normed]
  simp

private theorem ae_mem_ball_bumpMeasure (b : ContDiffBump (0 : ℝ × ℝ)) :
    ∀ᵐ t ∂bumpMeasure b, t ∈ ball 0 b.rOut := by
  rw [ae_iff]
  change bumpMeasure b (ball 0 b.rOut)ᶜ = 0
  rw [bumpMeasure, withDensity_apply _ isOpen_ball.measurableSet.compl]
  apply setLIntegral_eq_zero isOpen_ball.measurableSet.compl
  intro t ht
  have hzero : b.normed volume t = 0 := by
    apply Function.notMem_support.mp
    rwa [b.support_normed_eq]
  simp [hzero]

private theorem planeConvolution_bump_eq_average (b : ContDiffBump (0 : ℝ × ℝ))
    (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    planeConvolution f (planeBumpKernel b) x = ∫ t, f (x - t) ∂bumpMeasure b := by
  rw [planeConvolution_comm]
  change planeConvolution (fun p ↦ (b.normed volume p : ℂ)) f x = _
  rw [planeConvolution_ofReal, bumpMeasure,
    integral_withDensity_eq_integral_toReal_smul
      b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (b.nonneg_normed _)]
  rfl

private theorem eLpNorm_planeConvolution_bump_sub_le {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 volume) (b : ContDiffBump (0 : ℝ × ℝ)) {C : ENNReal}
    (hC : ∀ t ∈ ball 0 b.rOut, eLpNorm (fun x ↦ f (x - t) - f x) 2 volume ≤ C) :
    eLpNorm (planeConvolution f (planeBumpKernel b) - f) 2 volume ≤ C := by
  let ν := bumpMeasure b
  let : IsProbabilityMeasure ν := isProbabilityMeasure_bumpMeasure b
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun p ↦ f (p.2 - p.1)
  let D : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun p ↦ G p - f p.2
  have hskew : MeasurePreserving (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ (p.1, p.2 - p.1))
      (ν.prod volume) (ν.prod volume) := by
    apply (MeasurePreserving.id ν).skew_product (g := fun t x ↦ x - t)
    · exact measurable_snd.sub measurable_fst
    · exact Eventually.of_forall fun t ↦ (measurePreserving_sub_right volume t).map_eq
  have hG : MemLp G 2 (ν.prod volume) := hf.comp_measurePreserving
    (measurePreserving_snd.comp hskew)
  have hD : MemLp D 2 (ν.prod volume) := hG.sub (hf.comp_measurePreserving measurePreserving_snd)
  have havg : planeConvolution f (planeBumpKernel b) - f =ᵐ[volume]
      fun x ↦ ∫ t, D (t, x) ∂ν := by
    filter_upwards [ae_memLp_two_section hG] with x hx
    change planeConvolution f (planeBumpKernel b) x - f x = _
    rw [planeConvolution_bump_eq_average, show (∫ t, D (t, x) ∂ν) =
      (∫ t, G (t, x) ∂ν) - ∫ _t, f x ∂ν from
        integral_sub (hx.integrable (by norm_num))
          (show Integrable (fun _ : ℝ × ℝ ↦ f x) ν from integrable_const _)]
    simp [G, ν]
  rw [eLpNorm_congr_ae havg]
  refine (eLpNorm_integral_prob_le hD).2.trans ?_
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [← eLpNorm_comp_measurePreserving hD.aestronglyMeasurable
    (Measure.measurePreserving_swap (μ := volume) (ν := ν))]
  change eLpNorm (fun p ↦ D p.swap) 2 (volume.prod ν) ^ (2 : ℝ) ≤ _
  rw [eLpNorm_two_prod_rpow_eq hD.aestronglyMeasurable.prod_swap]
  calc
    _ ≤ ∫⁻ t, C ^ (2 : ℝ) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_ball_bumpMeasure b] with t ht
      gcongr
      exact hC t ht
    _ = _ := by simp

/-- Shrinking normalized bumps converge strongly on global L² data. -/
theorem tendsto_eLpNorm_planeConvolution_bump_sub {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 volume) (b : ℕ → ContDiffBump (0 : ℝ × ℝ))
    (hb : Tendsto (fun n ↦ (b n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (planeConvolution f (planeBumpKernel (b n)) - f) 2 volume)
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hs := ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_translate_sub hf) ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hs
  filter_upwards [hb.eventually_lt_const hδ] with n hn
  exact eLpNorm_planeConvolution_bump_sub_le hf (b n) fun t ht ↦
    hball t (ball_subset_ball hn.le ht)

end NoEmbeddedEigenvalues
