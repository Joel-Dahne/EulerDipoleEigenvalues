import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal

/-!
# Weighted square integrability in a two-column frame

Blueprint: `lem:weighted-frame`.

For a distance r, the normalized coefficients are a/r and b*r. Boundedness
of these coefficients transfers H ∈ L² and T/r² ∈ L² to (a*H+b*T)/r ∈ L².
The identity is valid even at totalized zero denominators, and does not
require measurability of the unweighted time derivative T.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Filter

/-- Bounded normalized frame coefficients transfer the two quarter weights. -/
theorem memLp_weighted_frame {μ : Measure (ℝ × ℝ)}
    {a b H T : ℝ × ℝ → ℂ} {r : ℝ × ℝ → ℝ} {A B : ℝ}
    (ha : AEStronglyMeasurable (fun q ↦ a q / (r q : ℂ)) μ)
    (hb : AEStronglyMeasurable (fun q ↦ b q * (r q : ℂ)) μ)
    (hAb : ∀ᵐ q ∂μ, ‖a q / (r q : ℂ)‖ ≤ A)
    (hBb : ∀ᵐ q ∂μ, ‖b q * (r q : ℂ)‖ ≤ B)
    (hH : MemLp H 2 μ)
    (hT : MemLp (fun q ↦ T q / (r q ^ 2 : ℂ)) 2 μ) :
    MemLp (fun q ↦ (a q * H q + b q * T q) / (r q : ℂ)) 2 μ := by
  have h₁ : MemLp (fun q ↦ (a q / (r q : ℂ)) * H q) 2 μ := by
    apply hH.of_le_mul (c := A) (ha.mul hH.aestronglyMeasurable)
    filter_upwards [hAb] with q hq
    simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hq (norm_nonneg (H q))
  have h₂ : MemLp (fun q ↦ (b q * (r q : ℂ)) * (T q / (r q ^ 2 : ℂ))) 2 μ := by
    apply hT.of_le_mul (c := B) (hb.mul hT.aestronglyMeasurable)
    filter_upwards [hBb] with q hq
    simpa only [Pi.mul_apply, norm_mul] using
      mul_le_mul_of_nonneg_right hq (norm_nonneg (T q / (r q ^ 2 : ℂ)))
  apply (h₁.add h₂).ae_eq
  exact Eventually.of_forall fun q ↦ by
    simp only [Pi.add_apply]
    by_cases hr : r q = 0
    · simp [hr]
    · have hrc : (r q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
      field_simp

end NoEmbeddedEigenvalues
