module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderSignedMass
public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderJointL2

/-!
# The signed spectral inverse of actual cylinder Fourier data

Use the original complex signed spectrum directly, retaining its probability-Haar
normalization. Nonresonance is needed only on the actual allowed support. The
signed integral reconstruction has finite joint cylinder mass by Parseval;
no weak differential equation is inferred from these multiplier identities.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory

/-- Divide the specified normalized signed data by the angular-frequency symbol. -/
def cylinderSignedInverse (a : ℝ) {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (p : ℝ × ℤ) : ℂ :=
  cylinderFourierData hG p / cylinderSymbol a p.1 p.2.natAbs

theorem measurable_cylinderSignedInverse (a : ℝ)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure) :
    Measurable (cylinderSignedInverse a hG) := by
  change Measurable (fun p : ℝ × ℤ ↦
    cylinderFourierData hG p / cylinderSymbol a p.1 p.2.natAbs)
  apply Measurable.div
  · exact measurable_cylinderFourierData hG
  · exact (measurable_cylinderSymbol a).comp
      (f := fun p : ℝ × ℤ ↦ (p.1, p.2.natAbs)) measurable_cylinderAbsModes

/-- Actual signed data have a finite two-derivative inverse and a genuine L¹
integral reconstruction. Zero forbidden modes do not require invertible symbols. -/
theorem cylinderSignedInverse_bounds {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ))
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    (hM : ∀ᵐ p ∂cylinderFourierMeasure,
      p.2.natAbs ∉ M → cylinderFourierData hG p = 0) :
    MemLp (cylinderSignedInverse a hG) 2 cylinderFourierMeasure ∧
      MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * cylinderSignedInverse a hG p)
        2 cylinderFourierMeasure ∧
      Integrable (cylinderSignedInverse a hG) cylinderFourierMeasure ∧
      (∀ᵐ p ∂cylinderFourierMeasure,
        cylinderSymbol a p.1 p.2.natAbs * cylinderSignedInverse a hG p =
          cylinderFourierData hG p) ∧
      ∀ᵐ p ∂cylinderFourierMeasure, p.2.natAbs ∉ M → cylinderSignedInverse a hG p = 0 := by
  obtain ⟨B, hB, hbound⟩ := cylinderSymbol_elliptic_bound ha hgap
  have hVm : AEStronglyMeasurable (cylinderSignedInverse a hG) cylinderFourierMeasure :=
    (measurable_cylinderSignedInverse a hG).aestronglyMeasurable
  have hWm : AEStronglyMeasurable
      (fun p ↦ (cylinderSignedWeight p : ℂ) * cylinderSignedInverse a hG p)
        cylinderFourierMeasure :=
    (Complex.measurable_ofReal.comp measurable_cylinderSignedWeight).aestronglyMeasurable.mul hVm
  have hpoint : ∀ᵐ p ∂cylinderFourierMeasure,
      ‖(cylinderSignedWeight p : ℂ) * cylinderSignedInverse a hG p‖ ≤
        B * ‖cylinderFourierData hG p‖ := by
    filter_upwards [hM] with p hp
    by_cases hm : p.2.natAbs ∈ M
    · have hz := cylinderSymbol_ne_zero (by linarith : 0 < a) (hgap _ hm) (ξ := p.1)
      have hn := norm_pos_iff.mpr hz
      have hw := (one_le_cylinderSignedWeight p).trans' zero_le_one
      dsimp only [cylinderSignedInverse]
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
        ← mul_div_assoc]
      apply (div_le_iff₀ hn).mpr
      have hh := mul_le_mul_of_nonneg_right (hbound _ hm p.1)
        (norm_nonneg (cylinderFourierData hG p))
      dsimp only [cylinderSignedWeight, cylinderSobolevWeight]
      nlinarith only [hh]
    · simp only [cylinderSignedInverse, hp hm, zero_div, mul_zero, norm_zero, le_refl]
  have hWV := (cylinderFourierData_memLp hG).of_le_mul hWm hpoint
  have hV : MemLp (cylinderSignedInverse a hG) 2 cylinderFourierMeasure := by
    apply hWV.of_le_mul hVm (c := 1)
    exact Filter.Eventually.of_forall fun p ↦ by
      rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((one_le_cylinderSignedWeight p).trans' zero_le_one)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_cylinderSignedWeight p) (norm_nonneg (cylinderSignedInverse a hG p))
  refine ⟨hV, hWV, integrable_of_memLp_cylinderSignedWeight hVm hWV, ?_, ?_⟩
  · filter_upwards [hM] with p hp
    by_cases hm : p.2.natAbs ∈ M
    · rw [cylinderSignedInverse, ← mul_div_assoc]
      exact mul_div_cancel_left₀ _ (cylinderSymbol_ne_zero (by linarith) (hgap _ hm))
    · simp [cylinderSignedInverse, hp hm]
  · filter_upwards [hM] with p hp hm
    simp [cylinderSignedInverse, hp hm]

end EulerDipoleEigenvalues
