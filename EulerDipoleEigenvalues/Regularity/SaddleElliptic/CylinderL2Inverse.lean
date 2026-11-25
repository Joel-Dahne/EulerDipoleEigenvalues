module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderJointL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Normalized cylinder inversion for arbitrary L² spectral data

The actual integral on L¹ ∩ L² is an isometry. Its domain is dense in spectral
L² because it contains the finite-mass simple functions. Extending that map
constructs genuine joint cylinder L² inverse witnesses without requiring
derivative multipliers to be L¹. On integrable data the extension retains the
same actual integral representative.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory
open scoped ComplexInnerProductSpace

theorem cylinderL2_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h
  · exact L2.integrable_inner f f

theorem cylinderJointSynthesis_congr_ae {H K : ℝ × ℤ → ℂ}
    (h : H =ᵐ[cylinderFourierMeasure] K) :
    cylinderJointSynthesis H = cylinderJointSynthesis K := by
  funext q
  exact integral_congr_ae (h.mono fun p hp ↦ by
    change cylinderJointKernel q p * H p = cylinderJointKernel q p * K p
    rw [hp])

theorem cylinderJointSynthesis_add {H K : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (hK : Integrable K cylinderFourierMeasure) :
    cylinderJointSynthesis (H + K) = cylinderJointSynthesis H + cylinderJointSynthesis K := by
  funext q
  simp only [cylinderJointSynthesis, Pi.add_apply, mul_add]
  exact integral_add (integrable_cylinderJointSynthesis hH q)
    (integrable_cylinderJointSynthesis hK q)

theorem cylinderJointSynthesis_smul (c : ℂ) (H : ℝ × ℤ → ℂ) :
    cylinderJointSynthesis (c • H) = c • cylinderJointSynthesis H := by
  funext q
  simp only [cylinderJointSynthesis, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (cylinderJointKernel q _) c]
  exact integral_const_mul c _

/-- The dense domain of spectral L² classes with an integrable representative. -/
private def cylinderIntegrableSpectrum : Submodule ℂ (Lp ℂ 2 cylinderFourierMeasure) where
  carrier := {f | Integrable f cylinderFourierMeasure}
  zero_mem' := (integrable_zero _ _ _).congr (Lp.coeFn_zero ℂ 2 cylinderFourierMeasure).symm
  add_mem' := fun {f g} hf hg ↦ (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' := fun c f hf ↦ (hf.smul c).congr (Lp.coeFn_smul c f).symm

private theorem cylinderIntegrableSpectrum_dense :
    DenseRange cylinderIntegrableSpectrum.subtype := by
  have hs := Lp.simpleFunc.denseRange (E := ℂ) (μ := cylinderFourierMeasure)
    (p := 2) (by norm_num)
  apply hs.mono
  rintro f ⟨s, rfl⟩
  have hi : Integrable (s : Lp ℂ 2 cylinderFourierMeasure) cylinderFourierMeasure :=
    ((SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mp
      (Lp.simpleFunc.memLp s)).congr (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  exact ⟨⟨s, hi⟩, rfl⟩

private def cylinderIntegrableInverse (f : cylinderIntegrableSpectrum) :
    Lp ℂ 2 logCylinderMeasure :=
  (cylinderJointSynthesis_memLp f.property (Lp.memLp f.val)).toLp
    (cylinderJointSynthesis (f.val : ℝ × ℤ → ℂ))

private theorem cylinderIntegrableInverse_ae (f : cylinderIntegrableSpectrum) :
    (cylinderIntegrableInverse f : ℝ × AddCircle (2 * Real.pi) → ℂ) =ᵐ[logCylinderMeasure]
      cylinderJointSynthesis (f.val : ℝ × ℤ → ℂ) :=
  (cylinderJointSynthesis_memLp f.property (Lp.memLp f.val)).coeFn_toLp

private def cylinderIntegrableInverseLinear :
    cylinderIntegrableSpectrum →ₗ[ℂ] Lp ℂ 2 logCylinderMeasure where
  toFun := cylinderIntegrableInverse
  map_add' f g := by
    have h := (cylinderJointSynthesis_congr_ae (Lp.coeFn_add f.val g.val)).trans
      (cylinderJointSynthesis_add f.property g.property)
    apply Lp.ext
    filter_upwards [cylinderIntegrableInverse_ae (f + g), cylinderIntegrableInverse_ae f,
      cylinderIntegrableInverse_ae g,
      Lp.coeFn_add (cylinderIntegrableInverse f) (cylinderIntegrableInverse g)]
      with q hfg hf hg ha
    rw [ha, Pi.add_apply, hf, hg]
    exact hfg.trans (congrFun h q)
  map_smul' c f := by
    have h := (cylinderJointSynthesis_congr_ae (Lp.coeFn_smul c f.val)).trans
      (cylinderJointSynthesis_smul c (f.val : ℝ × ℤ → ℂ))
    apply Lp.ext
    filter_upwards [cylinderIntegrableInverse_ae (c • f), cylinderIntegrableInverse_ae f,
      Lp.coeFn_smul c (cylinderIntegrableInverse f)] with q hcf hf hs
    change cylinderIntegrableInverse (c • f) q = (c • cylinderIntegrableInverse f) q
    rw [hs, Pi.smul_apply, hf]
    exact hcf.trans (congrFun h q)

private theorem cylinderIntegrableInverse_norm (f : cylinderIntegrableSpectrum) :
    ‖cylinderIntegrableInverseLinear f‖ = ‖cylinderIntegrableSpectrum.subtype f‖ := by
  have h : ‖cylinderIntegrableInverseLinear f‖ ^ 2 = ‖f.val‖ ^ 2 := by
    rw [cylinderL2_norm_sq, cylinderL2_norm_sq]
    calc
      _ = ∫ q, ‖cylinderJointSynthesis (f.val : ℝ × ℤ → ℂ) q‖ ^ 2
          ∂logCylinderMeasure := by
        apply integral_congr_ae
        filter_upwards [cylinderIntegrableInverse_ae f] with q hq
        rw [show cylinderIntegrableInverseLinear f q =
          cylinderJointSynthesis (f.val : ℝ × ℤ → ℂ) q from hq]
      _ = _ := cylinderJointSynthesis_sq_mass f.property (Lp.memLp f.val)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The normalized signed inverse on arbitrary joint L² spectral classes. -/
@[no_expose] def cylinderInverseL2 :
    Lp ℂ 2 cylinderFourierMeasure →ₗᵢ[ℂ] Lp ℂ 2 logCylinderMeasure :=
  cylinderIntegrableInverseLinear.extendOfIsometry cylinderIntegrableSpectrum_dense
    cylinderIntegrableInverse_norm

/-- The extension agrees with the actual integral on every L¹ ∩ L² input. -/
theorem cylinderInverseL2_ae_integral {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    (cylinderInverseL2 (h2.toLp H) : ℝ × AddCircle (2 * Real.pi) → ℂ) =ᵐ[logCylinderMeasure]
      cylinderJointSynthesis H := by
  let f : cylinderIntegrableSpectrum :=
    ⟨h2.toLp H, h1.congr h2.coeFn_toLp.symm⟩
  have he : cylinderInverseL2 (h2.toLp H) = cylinderIntegrableInverse f :=
    cylinderIntegrableInverseLinear.extendOfIsometry_eq
      cylinderIntegrableSpectrum_dense cylinderIntegrableInverse_norm f
  rw [he]
  exact (cylinderIntegrableInverse_ae f).trans
    (Filter.Eventually.of_forall (congrFun (cylinderJointSynthesis_congr_ae h2.coeFn_toLp)))

/-- Inverse witnesses have a genuinely finite joint cylinder norm. -/
theorem cylinderInverseL2_memLp (H : Lp ℂ 2 cylinderFourierMeasure) :
    MemLp (cylinderInverseL2 H : ℝ × AddCircle (2 * Real.pi) → ℂ) 2 logCylinderMeasure :=
  Lp.memLp _

/-- Exact normalized inverse Plancherel for arbitrary L² input representatives. -/
theorem cylinderInverseL2_sq_mass {H : ℝ × ℤ → ℂ}
    (h2 : MemLp H 2 cylinderFourierMeasure) :
    (∫ q, ‖cylinderInverseL2 (h2.toLp H) q‖ ^ 2 ∂logCylinderMeasure) =
      ∫ p, ‖H p‖ ^ 2 ∂cylinderFourierMeasure := by
  rw [← cylinderL2_norm_sq, LinearIsometry.norm_map, cylinderL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with p hp
  rw [hp]

end EulerDipoleEigenvalues
