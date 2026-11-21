module

public import NoEmbeddedEigenvalues.Mixed.SecondOrderForm.MixedCompletionCurrent

/-! # Coercivity of the mixed static form -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues

open Set Filter MeasureTheory Real ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ
local notation "H" => (π / 2)
local notation "I" => (Ioo (-H) H)
local notation "ν" => (volume.restrict I)
local notation "μ" => (volume.restrict mixedOpenCell)

/-- Coercivity with the two normalizations of the mass. -/
theorem mixed_static_coercivity {ω : L2} (d : MixedQuotientData ω) :
    let mass := ∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖d.phi q‖ ^ 2
    (1 / 200 : ℝ) * mass ≤ mixedStaticForm d ∧
    (1 / 200 : ℝ) * mass =
      (1 / 400 : ℝ) * ∫ p in cellSquare, ‖liftL2 (invLap ω) p‖ ^ 2 := by
  have hsq : 0 ≤ ∫ q in mixedOpenCell, mixedCompletionDensity d.phi d.jet q := by
    apply integral_nonneg
    intro q
    unfold mixedCompletionDensity mixedFieldCoeff
    positivity
  constructor
  · calc
      _ ≤ _ := mixed_second_order_coercivity d
      _ ≤ _ := by rw [(mixed_completion d).2.2.2]; linarith
  · rw [d.stream_mass]
    ring

end NoEmbeddedEigenvalues
