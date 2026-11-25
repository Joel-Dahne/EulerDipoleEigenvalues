module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderFourierL2

/-!
# Two-sided normalized cylinder Fourier inversion

Coefficient extraction identifies analysis of the actual L¹ ∩ L² integral.
Density and continuity extend this identity to every spectral L² class.
Injectivity of the analysis isometry gives the other round-trip, recovering
arbitrary original cylinder data with no time or joint L¹ hypothesis.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Analysis of the actual joint inverse integral recovers every spectral mode. -/
theorem cylinderFourierData_synthesis_ae {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    cylinderFourierData (cylinderJointSynthesis_memLp h1 h2) =ᵐ[cylinderFourierMeasure] H := by
  apply cylinderFourierMeasure_ae_of_modes
  intro n
  let hn := cylinderFourierMeasure_mode_memLp h2 n
  have he : cylinderTimeMode (cylinderJointSynthesis_memLp h1 h2) n =
      cylinderTimeInverseClass hn := by
    apply Lp.ext
    filter_upwards [cylinderTimeMode_ae (cylinderJointSynthesis_memLp h1 h2) n,
      cylinderTimeSynthesis_ae_inverse (cylinderFourierMeasure_mode_integrable h1 n) hn]
        with t ht hi
    exact ht.trans ((cylinderJointSynthesis_coeff h1 n t).trans hi.symm)
  have hf : cylinderFourierMode (cylinderJointSynthesis_memLp h1 h2) n =
      (hn.comp_measurePreserving measurePreserving_cylinderAngularFrequency).toLp
        (fun η ↦ H ((2 * Real.pi) * η, n)) := by
    rw [cylinderFourierMode, he, cylinderTimeInverseClass,
      FourierTransform.fourier_fourierInv_eq]
  have hc0 :
      ((hn.comp_measurePreserving measurePreserving_cylinderAngularFrequency).toLp
        (fun η ↦ H ((2 * Real.pi) * η, n)) : ℝ → ℂ) =ᵐ[volume]
          (fun η ↦ H ((2 * Real.pi) * η, n)) :=
    (hn.comp_measurePreserving measurePreserving_cylinderAngularFrequency).coeFn_toLp
  have hc := measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae hc0
  filter_upwards [cylinderFourierData_ae (cylinderJointSynthesis_memLp h1 h2) n, hc]
    with ξ hξ hη
  rw [hξ, hf]
  have hz : (2 * Real.pi) * (ξ / (2 * Real.pi)) = ξ := by field_simp
  simpa only [Function.comp_apply, hz] using hη

/-- The class-valued analysis of the actual integral is the input spectral class. -/
theorem cylinderFourierL2_synthesis {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    cylinderFourierL2
      ((cylinderJointSynthesis_memLp h1 h2).toLp (cylinderJointSynthesis H)) = h2.toLp H := by
  rw [cylinderFourierL2_toLp]
  apply Lp.ext
  exact (cylinderFourierData_memLp (cylinderJointSynthesis_memLp h1 h2)).coeFn_toLp.trans
    ((cylinderFourierData_synthesis_ae h1 h2).trans h2.coeFn_toLp.symm)

/-- Analysis after synthesis is the identity on all joint spectral L² classes. -/
theorem cylinderFourierL2_inverse (H : Lp ℂ 2 cylinderFourierMeasure) :
    cylinderFourierL2 (cylinderInverseL2 H) = H := by
  have hc : IsClosed {f : Lp ℂ 2 cylinderFourierMeasure |
      cylinderFourierL2 (cylinderInverseL2 f) = f} :=
    isClosed_eq (by fun_prop) continuous_id
  refine (Lp.simpleFunc.denseRange (E := ℂ) (p := 2) (μ := cylinderFourierMeasure)
    (by norm_num)).induction_on H hc ?_
  intro s
  have hi : Integrable (s : Lp ℂ 2 cylinderFourierMeasure) cylinderFourierMeasure :=
    ((SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mp
      (Lp.simpleFunc.memLp s)).congr (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  have he : cylinderInverseL2 (s : Lp ℂ 2 cylinderFourierMeasure) =
      ((cylinderJointSynthesis_memLp hi (Lp.memLp s.val)).toLp
        (cylinderJointSynthesis (s.val : ℝ × ℤ → ℂ))) := by
    apply Lp.ext
    have h := cylinderInverseL2_ae_integral hi (Lp.memLp s.val)
    rw [Lp.toLp_coeFn] at h
    exact h.trans (cylinderJointSynthesis_memLp hi (Lp.memLp s.val)).coeFn_toLp.symm
  rw [he, cylinderFourierL2_synthesis hi (Lp.memLp s.val), Lp.toLp_coeFn]

/-- Synthesis after analysis is the identity on the original joint cylinder L² class. -/
theorem cylinderInverseL2_fourier (G : Lp ℂ 2 logCylinderMeasure) :
    cylinderInverseL2 (cylinderFourierL2 G) = G := by
  apply cylinderFourierL2.injective
  exact cylinderFourierL2_inverse _

/-- The inverse of the original normalized data is the original raw function a.e. -/
theorem cylinderInverseL2_fourierData_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    (cylinderInverseL2
      ((cylinderFourierData_memLp hG).toLp (cylinderFourierData hG)) :
        ℝ × AddCircle (2 * Real.pi) → ℂ) =ᵐ[logCylinderMeasure] G := by
  rw [← cylinderFourierL2_toLp, cylinderInverseL2_fourier]
  exact hG.coeFn_toLp

end EulerDipoleEigenvalues
