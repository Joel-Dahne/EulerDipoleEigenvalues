import NoEmbeddedEigenvalues.FlowBoundaryForm

/-! # Affine splitting in flow time -/

noncomputable section
namespace NoEmbeddedEigenvalues

open Complex MeasureTheory

/-- Subtract the affine interpolant of the two canonical endpoint values of a
weighted-domain profile in the bounded coordinate. The resulting identity is for the
flow-time form, using the corresponding explicit derivatives. -/
theorem flowBoundaryForm_affine_splitting {F D E : ℝ → ℂ}
    (hF : HasWeightedBoundaryH2 F D E) (lam : ℝ) (a b : ℂ)
    (hneg : intervalH1Extension (-1) 1 F D (-1) = a - b)
    (hpos : intervalH1Extension (-1) 1 F D 1 = a + b) :
    let F₀ := fun ξ : ℝ ↦ F ξ - a - b * (ξ : ℂ)
    let D₀ := fun ξ ↦ D ξ - b
    HasWeightedBoundaryH2 F₀ D₀ E ∧
      intervalH1Extension (-1) 1 F₀ D₀ (-1) = 0 ∧
      intervalH1Extension (-1) 1 F₀ D₀ 1 = 0 ∧
      flowBoundaryForm lam (flowValue F) (flowFirst D) (flowSecond D E) =
        flowBoundaryForm lam (flowValue F₀) (flowFirst D₀) (flowSecond D₀ E) +
          lam ^ 2 * normSq b + 2 * lam * (b * star a).im := by
  sorry

end NoEmbeddedEigenvalues
