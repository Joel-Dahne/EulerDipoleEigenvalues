module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierRelations
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderL2Inverse

/-!
# Joint normalized cylinder analysis as a linear isometry

The map acts on genuine L² classes, with probability Haar in angle and
`dξ / (2 * π)` in frequency. Its chosen raw spectral representative is exactly
the previously specified normalized Fourier data, up to joint a.e. equality.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

private def cylinderFourierClass (f : Lp ℂ 2 logCylinderMeasure) :
    Lp ℂ 2 cylinderFourierMeasure :=
  (cylinderFourierData_memLp (Lp.memLp f)).toLp (cylinderFourierData (Lp.memLp f))

private theorem cylinderFourierClass_ae (f : Lp ℂ 2 logCylinderMeasure) :
    (cylinderFourierClass f : ℝ × ℤ → ℂ) =ᵐ[cylinderFourierMeasure]
      cylinderFourierData (Lp.memLp f) :=
  (cylinderFourierData_memLp (Lp.memLp f)).coeFn_toLp

private def cylinderFourierLinear :
    Lp ℂ 2 logCylinderMeasure →ₗ[ℂ] Lp ℂ 2 cylinderFourierMeasure where
  toFun := cylinderFourierClass
  map_add' f g := by
    have h := cylinderFourierData_add_ae (Lp.memLp f) (Lp.memLp g) (Lp.memLp (f + g))
      (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [cylinderFourierClass_ae (f + g), cylinderFourierClass_ae f,
      cylinderFourierClass_ae g, h,
      Lp.coeFn_add (cylinderFourierClass f) (cylinderFourierClass g)] with p hfg hf hg hd ha
    rw [ha, Pi.add_apply, hf, hg, hfg]
    exact hd
  map_smul' c f := by
    have h := cylinderFourierData_smul_ae (Lp.memLp f) (Lp.memLp (c • f)) c
      (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [cylinderFourierClass_ae (c • f), cylinderFourierClass_ae f, h,
      Lp.coeFn_smul c (cylinderFourierClass f)] with p hcf hf hd hs
    change cylinderFourierClass (c • f) p = (c • cylinderFourierClass f) p
    rw [hs, Pi.smul_apply, hf, hcf]
    exact hd

/-- Analysis into the normalized joint signed spectrum, on L² classes. -/
@[no_expose] def cylinderFourierL2 :
    Lp ℂ 2 logCylinderMeasure →ₗᵢ[ℂ] Lp ℂ 2 cylinderFourierMeasure where
  toLinearMap := cylinderFourierLinear
  norm_map' f := by
    have h : ‖cylinderFourierLinear f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [cylinderL2_norm_sq, cylinderL2_norm_sq]
      calc
        _ = ∫ p, ‖cylinderFourierData (Lp.memLp f) p‖ ^ 2
            ∂cylinderFourierMeasure := by
          apply integral_congr_ae
          filter_upwards [cylinderFourierClass_ae f] with p hp
          rw [show cylinderFourierLinear f p = cylinderFourierData (Lp.memLp f) p from hp]
        _ = _ := cylinderFourierData_sq_mass (Lp.memLp f)
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem cylinderFourierL2_ae (f : Lp ℂ 2 logCylinderMeasure) :
    (cylinderFourierL2 f : ℝ × ℤ → ℂ) =ᵐ[cylinderFourierMeasure]
      cylinderFourierData (Lp.memLp f) :=
  cylinderFourierClass_ae f

/-- Passing the original raw input to L² does not alter its normalized spectrum. -/
theorem cylinderFourierL2_toLp {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    cylinderFourierL2 (hG.toLp G) =
      (cylinderFourierData_memLp hG).toLp (cylinderFourierData hG) := by
  apply Lp.ext
  exact (cylinderFourierL2_ae _).trans
    ((cylinderFourierData_congr_ae (Lp.memLp (hG.toLp G)) hG hG.coeFn_toLp).trans
      (cylinderFourierData_memLp hG).coeFn_toLp.symm)

end NoEmbeddedEigenvalues
