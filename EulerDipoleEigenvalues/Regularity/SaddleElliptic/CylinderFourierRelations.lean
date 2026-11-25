module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderFourierData

/-!
# Representative-compatible linearity of normalized cylinder Fourier data

Joint cylinder a.e. identities are transported to angular slices before taking
coefficients. Relations then pass through the real-line L² Fourier classes,
and only afterwards to the normalized, jointly measurable spectral representatives.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem cylinderAngularCoeff_congr_ae {F G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (h : F =ᵐ[logCylinderMeasure] G) (n : ℤ) :
    cylinderAngularCoeff F n =ᵐ[volume] cylinderAngularCoeff G n :=
  (Measure.ae_ae_of_ae_prod h).mono fun _ ht ↦ congrFun (_root_.fourierCoeff_congr_ae ht) n

theorem cylinderAngularCoeff_add_ae {F G K : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hG : MemLp G 2 logCylinderMeasure)
    (hK : K =ᵐ[logCylinderMeasure] F + G) (n : ℤ) :
    cylinderAngularCoeff K n =ᵐ[volume]
      cylinderAngularCoeff F n + cylinderAngularCoeff G n := by
  filter_upwards [cylinderAngularCoeff_congr_ae hK n,
    memLp_logCylinder_slices hF, memLp_logCylinder_slices hG] with t ht hf hg
  exact ht.trans (congrFun (_root_.fourierCoeff.add
    (hf.integrable (by norm_num)) (hg.integrable (by norm_num))) n)

theorem cylinderAngularCoeff_smul_ae {F K : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (c : ℂ) (hK : K =ᵐ[logCylinderMeasure] c • F) (n : ℤ) :
    cylinderAngularCoeff K n =ᵐ[volume] fun t ↦ c * cylinderAngularCoeff F n t := by
  filter_upwards [cylinderAngularCoeff_congr_ae hK n] with t ht
  exact ht.trans (_root_.fourierCoeff.const_smul _ c n)

/-- A modewise spectral identity becomes a joint identity, with no exceptional integer. -/
theorem cylinderFourierMeasure_ae_of_modes {P : ℝ × ℤ → Prop}
    (h : ∀ n : ℤ, ∀ᵐ ξ ∂cylinderFrequencyMeasure, P (ξ, n)) :
    ∀ᵐ p ∂cylinderFourierMeasure, P p := by
  have hs := ae_all_iff.mpr h
  exact (Measure.quasiMeasurePreserving_fst.ae hs).mono fun p hp ↦ hp p.2

theorem cylinderFourierMode_congr_ae {F G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hG : MemLp G 2 logCylinderMeasure)
    (h : F =ᵐ[logCylinderMeasure] G) (n : ℤ) :
    cylinderFourierMode hF n = cylinderFourierMode hG n := by
  have he : cylinderTimeMode hF n = cylinderTimeMode hG n := by
    apply Lp.ext
    exact (cylinderTimeMode_ae hF n).trans
      ((cylinderAngularCoeff_congr_ae h n).trans (cylinderTimeMode_ae hG n).symm)
  simp only [cylinderFourierMode, he]

theorem cylinderFourierMode_add_ae {F G K : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hG : MemLp G 2 logCylinderMeasure)
    (hK : MemLp K 2 logCylinderMeasure) (h : K =ᵐ[logCylinderMeasure] F + G) (n : ℤ) :
    cylinderFourierMode hK n = cylinderFourierMode hF n + cylinderFourierMode hG n := by
  have he : cylinderTimeMode hK n = cylinderTimeMode hF n + cylinderTimeMode hG n := by
    apply Lp.ext
    filter_upwards [cylinderTimeMode_ae hK n, cylinderTimeMode_ae hF n,
      cylinderTimeMode_ae hG n, cylinderAngularCoeff_add_ae hF hG h n,
      Lp.coeFn_add (cylinderTimeMode hF n) (cylinderTimeMode hG n)] with t hk hf hg hc ha
    rw [ha, Pi.add_apply, hf, hg, hk]
    exact hc
  simp only [cylinderFourierMode, he, FourierTransform.fourier_add]

theorem cylinderFourierData_congr_ae {F G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hG : MemLp G 2 logCylinderMeasure)
    (h : F =ᵐ[logCylinderMeasure] G) :
    cylinderFourierData hF =ᵐ[cylinderFourierMeasure] cylinderFourierData hG := by
  apply cylinderFourierMeasure_ae_of_modes
  intro n
  filter_upwards [cylinderFourierData_ae hF n, cylinderFourierData_ae hG n] with ξ hf hg
  rw [hf, hg, cylinderFourierMode_congr_ae hF hG h n]

theorem cylinderFourierData_add_ae {F G K : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hG : MemLp G 2 logCylinderMeasure)
    (hK : MemLp K 2 logCylinderMeasure) (h : K =ᵐ[logCylinderMeasure] F + G) :
    cylinderFourierData hK =ᵐ[cylinderFourierMeasure]
      cylinderFourierData hF + cylinderFourierData hG := by
  apply cylinderFourierMeasure_ae_of_modes
  intro n
  have hm := measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae
    (Lp.coeFn_add (cylinderFourierMode hF n) (cylinderFourierMode hG n))
  filter_upwards [cylinderFourierData_ae hK n, cylinderFourierData_ae hF n,
    cylinderFourierData_ae hG n, hm] with ξ hk hf hg ha
  change cylinderFourierData hK (ξ, n) =
    cylinderFourierData hF (ξ, n) + cylinderFourierData hG (ξ, n)
  rw [hk, cylinderFourierMode_add_ae hF hG hK h n, ha, Pi.add_apply, hf, hg]

theorem cylinderFourierData_smul_ae {F K : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hF : MemLp F 2 logCylinderMeasure) (hK : MemLp K 2 logCylinderMeasure)
    (c : ℂ) (h : K =ᵐ[logCylinderMeasure] c • F) :
    cylinderFourierData hK =ᵐ[cylinderFourierMeasure] c • cylinderFourierData hF := by
  apply cylinderFourierMeasure_ae_of_modes
  intro n
  have he : cylinderFourierMode hK n = c • cylinderFourierMode hF n := by
    simp only [cylinderFourierMode, ← FourierTransform.fourier_smul]
    apply congrArg FourierTransform.fourier
    apply Lp.ext
    filter_upwards [cylinderTimeMode_ae hK n, cylinderTimeMode_ae hF n,
      cylinderAngularCoeff_smul_ae c h n, Lp.coeFn_smul c (cylinderTimeMode hF n)]
        with t hk hf hc hs
    rw [hs, Pi.smul_apply, smul_eq_mul, hf, hk]
    exact hc
  have hm := measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae
    (Lp.coeFn_smul c (cylinderFourierMode hF n))
  filter_upwards [cylinderFourierData_ae hK n, cylinderFourierData_ae hF n, hm]
    with ξ hk hf hs
  change cylinderFourierData hK (ξ, n) = c * cylinderFourierData hF (ξ, n)
  rw [hk, he, hs, Pi.smul_apply, smul_eq_mul, hf]

end EulerDipoleEigenvalues
