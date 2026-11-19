import NoEmbeddedEigenvalues.IntervalHardy
import NoEmbeddedEigenvalues.IntervalSecondHardy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Angular Hardy -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Angular Hardy on a quadrant with zero canonical traces at both endpoints. The
quotient is in L²; the integral bound does not rely on a convention for divergent integrals. -/
theorem interval_hardy_angular :
    ∃ C : ℝ, 0 < C ∧ ∀ {g d : ℝ → ℂ},
      HasIntervalH1 0 (Real.pi / 2) g d →
      intervalH1Extension 0 (Real.pi / 2) g d 0 = 0 →
      intervalH1Extension 0 (Real.pi / 2) g d (Real.pi / 2) = 0 →
      let q := fun θ ↦ g θ / ((Real.sin θ * Real.cos θ : ℝ) : ℂ)
      MemLp q 2 (volume.restrict (Ioo 0 (Real.pi / 2))) ∧
      (∫ θ in Ioo 0 (Real.pi / 2), ‖q θ‖ ^ 2) ≤
        C * ∫ θ in Ioo 0 (Real.pi / 2), ‖d θ‖ ^ 2 := by
  sorry

end NoEmbeddedEigenvalues
