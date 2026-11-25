module

public import EulerDipoleEigenvalues.Analysis.Inequalities.IntervalSegmentAverage

/-!
# H² division by a linear factor

Blueprint: `lem:hardy-second`.

The quotient is the segment average of the canonical first derivative. Its H¹
regularity and derivative-energy bound follow from segment averaging; the endpoint
fundamental theorem identifies the product with the original interior numerator.
The same construction works at either endpoint and at every interior point.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Second Hardy: H² division at an interior point or endpoint, with one universal
constant (`lem:hardy-second`). No value of the raw numerator at an endpoint is used. -/
theorem interval_h2_div_sub : ∃ K : ℝ, 0 < K ∧
    ∀ (a b x₀ : ℝ) (N N₁ N₂ : ℝ → ℂ), a < b → x₀ ∈ Icc a b →
      HasIntervalH2 a b N N₁ N₂ → intervalH1Extension a b N N₁ x₀ = 0 →
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 a b Q Q₁ ∧
        (∀ x ∈ Ioo a b, N x = ((x - x₀ : ℝ) : ℂ) * Q x) ∧
        (∫ x in Ioo a b, ‖Q₁ x‖ ^ 2) ≤ K * ∫ x in Ioo a b, ‖N₂ x‖ ^ 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a b x₀ N N₁ N₂ hab hx₀ hN hzero
  obtain ⟨Q, Q₁, hQ, hQeq, hQE⟩ := hN.2.segmentAverage hab hx₀
  refine ⟨Q, Q₁, hQ, ?_, by simpa only [one_mul] using hQE⟩
  intro x hx
  have hprimitive : (∫ s in x₀..x, intervalH1Extension a b N₁ N₂ s) = N x := by
    calc
      _ = ∫ s in x₀..x, N₁ s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne a, volume.ae_ne b] with s hsa hsb hs
        have hsc : s ∈ Icc a b := uIcc_subset_Icc hx₀ (Ioo_subset_Icc_self hx)
          (uIoc_subset_uIcc hs)
        exact hN.2.extension_eq hab
          ⟨lt_of_le_of_ne hsc.1 hsa.symm, lt_of_le_of_ne hsc.2 hsb⟩
      _ = _ := by rw [hN.1.integral_eq_extension_sub hab hx₀ (Ioo_subset_Icc_self hx),
        hzero, sub_zero, hN.1.extension_eq hab hx]
  have hfactor : (x - x₀) • Q x = N x := by
    calc
      _ = (x - x₀) • ∫ t in (0 : ℝ)..1,
          intervalH1Extension a b N₁ N₂ ((x - x₀) * t + x₀) := by
        rw [hQeq x (Ioo_subset_Icc_self hx)]
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        exact congrArg (intervalH1Extension a b N₁ N₂) (by ring)
      _ = ∫ s in x₀..x, intervalH1Extension a b N₁ N₂ s := by
        simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using
          intervalIntegral.smul_integral_comp_mul_add
            (f := intervalH1Extension a b N₁ N₂) (a := 0) (b := 1) (x - x₀) x₀
      _ = N x := hprimitive
  simpa only [Complex.real_smul] using hfactor.symm

end EulerDipoleEigenvalues
