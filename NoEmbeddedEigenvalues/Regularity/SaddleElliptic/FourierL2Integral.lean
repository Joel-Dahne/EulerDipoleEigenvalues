import Mathlib.Analysis.Fourier.LpSpace

/-!
# Identifying the inverse Fourier integral with the L² inverse

For actual L¹ ∩ L² data, the bounded continuous inverse integral represents the
unitary L² inverse. The proof compares their Schwartz pairings through the
tempered-distribution Fourier transform, then uses locally integrable uniqueness.
It does not assume the inverse integral is L² before identifying it.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory FourierTransform
open scoped ContDiff

/-- Inverse Fourier integration can be transferred across an L¹ pairing. -/
theorem integral_fourierInv_mul_swap {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, (𝓕⁻ f) x * g x) = ∫ x, f x * (𝓕⁻ g) x := by
  have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by
    ext
    simp [LinearMap.flip_apply]
  change (∫ x, VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ)) f x * g x) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ)) g x
  simpa only [hflip, smul_eq_mul] using
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (L := -(innerₗ ℝ)) Real.continuous_fourierChar
      (by fun_prop) hf hg

/-- The genuine inverse integral agrees a.e. with the L² inverse class. -/
theorem fourierInv_L2_ae_integral {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : MemLp f 2 volume) :
    ((𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] (𝓕⁻ f : ℝ → ℂ) := by
  have hcont : Continuous (𝓕⁻ f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hf
  have hDual (ψ : SchwartzMap ℝ ℂ) :
      (∫ x, ψ x * ((𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) x) = ∫ x, ψ x * (𝓕⁻ f) x := by
    calc
      _ = ∫ x, (𝓕⁻ ψ) x * (h2.toLp f) x := by
        have ht := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T ψ)
          (Lp.fourierInv_toTemperedDistribution_eq (h2.toLp f))
        simpa only [TemperedDistribution.fourierInv_apply,
          Lp.toTemperedDistribution_apply, smul_eq_mul] using ht.symm
      _ = ∫ x, (𝓕⁻ (ψ : ℝ → ℂ)) x * f x := by
        apply integral_congr_ae
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hx, SchwartzMap.fourierInv_coe]
      _ = _ := integral_fourierInv_mul_swap ψ.integrable hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume)).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have ht := hDual (hs'.toSchwartzMap hg')
  change (∫ x, (g x : ℂ) * ((𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) x) =
    ∫ x, (g x : ℂ) * (𝓕⁻ f) x at ht
  simpa only [Complex.real_smul] using ht

/-- Finite L² of the actual continuous inverse integral follows from identification. -/
theorem fourierInv_integral_memLp {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : MemLp f 2 volume) : MemLp (𝓕⁻ f : ℝ → ℂ) 2 volume :=
  (Lp.memLp (𝓕⁻ (h2.toLp f) : Lp ℂ 2 volume)).ae_eq (fourierInv_L2_ae_integral hf h2)

end NoEmbeddedEigenvalues
