import NoEmbeddedEigenvalues.Analysis.WeakLaplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Cartesian smoothing and compact-test harmonicity

Smooth compact kernels differentiate under a genuine locally integrable
convolution. A reflected translated kernel is an admissible weak test whenever
its whole support fits in the original open set. Associativity below proves
its Fubini integrability from an L1 datum and bounded compact kernels.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Complex multiplication convolution on the physical Cartesian plane. -/
def planeConvolution (f g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℂ] g

/-- Commutativity retains the actual integral values. -/
theorem planeConvolution_comm (f g : ℝ × ℝ → ℂ) :
    planeConvolution f g = planeConvolution g f := by
  apply convolution_symm
  ext a b
  exact mul_comm b a

/-- Real kernels agree with the usual real-scalar smoothing integral. -/
theorem planeConvolution_ofReal (k : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) :
    planeConvolution (fun p ↦ (k p : ℂ)) f = k ⋆[lsmul ℝ ℝ] f := by
  funext x
  apply integral_congr_ae
  filter_upwards with y
  exact Complex.real_smul.symm

/-- A smooth compact kernel smooths a raw locally integrable datum. -/
theorem contDiff_planeConvolution {f k : ℝ × ℝ → ℂ} (hf : LocallyIntegrable f)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (planeConvolution f k) :=
  hkc.contDiff_convolution_right _ hf hk

private theorem compact_coordPartial {k : ℝ × ℝ → ℂ} (hkc : HasCompactSupport k)
    (j : Fin 2) : HasCompactSupport (coordPartial j k) :=
  hkc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j k)

/-- The same specified kernel derivative is the classical derivative of smoothing. -/
theorem coordPartial_planeConvolution {f k : ℝ × ℝ → ℂ} (hf : LocallyIntegrable f)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (j : Fin 2) (x : ℝ × ℝ) :
    coordPartial j (planeConvolution f k) x =
      planeConvolution f (coordPartial j k) x := by
  have hd := hkc.hasFDerivAt_convolution_right (mul ℝ ℂ) hf
    (hk.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)) x
  calc
    _ = fderiv ℝ (planeConvolution f k) x (planeDirection j) :=
      coordPartial_eq_fderiv_plane hd.differentiableAt j
    _ = (f ⋆[(mul ℝ ℂ).precompR (ℝ × ℝ)] fderiv ℝ k) x (planeDirection j) := by
      rw [show fderiv ℝ (planeConvolution f k) x = _ from hd.fderiv]
    _ = planeConvolution f (coordPartial j k) x := by
      rw [convolution_precompR_apply (mul ℝ ℂ) hf (hkc.fderiv ℝ)
        (hk.continuous_fderiv (by simp))]
      apply integral_congr_ae
      filter_upwards with y
      change f y * fderiv ℝ k (x - y) (planeDirection j) =
        f y * coordPartial j k (x - y)
      rw [coordPartial_eq_fderiv_plane (hk.differentiable (by simp) (x - y))]

/-- Both repeated entries differentiate under the integral independently. -/
theorem planeLaplacian_planeConvolution {f k : ℝ × ℝ → ℂ}
    (hf : LocallyIntegrable f) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (x : ℝ × ℝ) :
    planeLaplacian (planeConvolution f k) x = planeConvolution f (planeLaplacian k) x := by
  have hfirst (j : Fin 2) : coordPartial j (planeConvolution f k) =
      planeConvolution f (coordPartial j k) :=
    funext (coordPartial_planeConvolution hf hk hkc j)
  have hsecond (j : Fin 2) :
      coordPartial j (coordPartial j (planeConvolution f k)) x =
        planeConvolution f (coordPartial j (coordPartial j k)) x := by
    rw [hfirst]
    exact coordPartial_planeConvolution hf (contDiff_coordPartial_top j hk)
      (compact_coordPartial hkc j) j x
  have hi (j : Fin 2) : Integrable
      (fun y ↦ f y * coordPartial j (coordPartial j k) (x - y)) :=
    (compact_coordPartial (compact_coordPartial hkc j) j).convolutionExists_right
      (mul ℝ ℂ) hf ((contDiff_coordPartial_top j
        (contDiff_coordPartial_top j hk)).continuous) x
  unfold planeLaplacian
  rw [hsecond 0, hsecond 1]
  symm
  change (∫ y, f y * (_ + _)) = _
  simpa only [planeConvolution, convolution_def, mul_apply', mul_add] using
    integral_add (hi 0) (hi 1)

/-- A whole translated kernel support gives a genuine test, not a null-seam test. -/
theorem isTestFunctionOn_kernelTranslate {U : Set (ℝ × ℝ)} {k : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (x : ℝ × ℝ)
    (hs : ∀ q ∈ tsupport k, x - q ∈ U) :
    IsTestFunctionOn U (fun y ↦ k (x - y)) := by
  refine ⟨hk.comp (contDiff_const.sub contDiff_id),
    hkc.comp_homeomorph (Homeomorph.subLeft x), ?_⟩
  intro y hy
  have hm : x - y ∈ tsupport k := by
    change y ∈ tsupport (k ∘ Homeomorph.subLeft x) at hy
    rwa [tsupport_comp_eq_preimage] at hy
  simpa only [sub_sub_cancel] using hs (x - y) hm

/-- Compact-test harmonicity is inherited by each sufficiently local smoothing. -/
theorem planeLaplacian_smoothing_eq_zero {U : Set (ℝ × ℝ)} {f k : ℝ × ℝ → ℂ}
    (hf : LocallyIntegrable f)
    (hw : ∀ φ, IsTestFunctionOn U φ → ∫ p, f p * planeLaplacian φ p = 0)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (x : ℝ × ℝ)
    (hs : ∀ q ∈ tsupport k, x - q ∈ U) :
    planeLaplacian (planeConvolution f k) x = 0 := by
  rw [planeLaplacian_planeConvolution hf hk hkc]
  have htest := isTestFunctionOn_kernelTranslate hk hkc x hs
  have heq : planeConvolution f (planeLaplacian k) x =
      ∫ y, f y * planeLaplacian (fun p ↦ k (x - p)) y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [planeLaplacian_comp_sub_left hk]
    rfl
  rw [heq]
  exact hw _ htest

/-- Pointwise associativity with smooth compact kernels and a genuine L1 datum. -/
theorem planeConvolution_assoc {k l f : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hl : Continuous l) (hlc : HasCompactSupport l) (hf : Integrable f) (x : ℝ × ℝ) :
    planeConvolution (planeConvolution k l) f x =
      planeConvolution k (planeConvolution l f) x := by
  obtain ⟨C, hC⟩ := hl.bounded_above_of_compact_support hlc
  have hi : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) ↦
      k q.2 * (l (q.1 - q.2) * f (x - q.1))) (volume.prod volume) := by
    have hb := ((hf.comp_sub_left x).norm.mul_const C).mul_prod
      (hk.integrable_of_hasCompactSupport (μ := volume) hkc).norm
    apply hb.mono'
    · exact hk.aestronglyMeasurable.comp_snd.mul
        (((hl.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
          (hf.comp_sub_left x).aestronglyMeasurable.comp_fst)
    · filter_upwards with q
      simp only [norm_mul]
      calc
        _ ≤ ‖k q.2‖ * (C * ‖f (x - q.1)‖) := by
          gcongr
          exact hC _
        _ = _ := by ring
  exact convolution_assoc' (mul ℝ ℂ) (mul ℝ ℂ) (mul ℝ ℂ) (mul ℝ ℂ)
    (fun a b c ↦ mul_assoc a b c)
    (Filter.Eventually.of_forall (hkc.convolutionExists_left (mul ℝ ℂ)
      hk hl.locallyIntegrable))
    (Filter.Eventually.of_forall (hlc.convolutionExists_left (mul ℝ ℂ)
      hl hf.locallyIntegrable)) hi

/-- Exchanging the two actual smoothing kernels uses finite Fubini integrals. -/
theorem planeConvolution_swap_kernels {k l f : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hl : Continuous l) (hlc : HasCompactSupport l) (hf : Integrable f) (x : ℝ × ℝ) :
    planeConvolution k (planeConvolution l f) x =
      planeConvolution l (planeConvolution k f) x := by
  rw [← planeConvolution_assoc hk hkc hl hlc hf,
    planeConvolution_comm k l, planeConvolution_assoc hl hlc hk hkc hf]

end NoEmbeddedEigenvalues
