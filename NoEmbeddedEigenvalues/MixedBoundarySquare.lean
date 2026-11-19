import NoEmbeddedEigenvalues.BoundaryForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The mixed Neumann-edge square

The boundary variable is `x = tanh t`; all integrals are on the open interval.
The weighted identity does not impose any endpoint values or boundary conditions.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory ComplexConjugate
open scoped ContDiff

/-- The transformed transport operator after factoring out `sech t`. -/
def mixedBoundaryTransport (lam : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * ((boundaryWeight x : ℂ) * deriv F x - (x : ℂ) * F x) -
    (lam : ℂ) * F x

/-- Second-order expression in the boundary square. -/
def mixedBoundarySquare (lam : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  (boundaryWeight x : ℂ) * deriv (deriv F) x -
    (3 * (x : ℂ) + Complex.I * (lam : ℂ)) * deriv F x

/-- The mixed boundary square for smooth data (`lem:mixed-boundary-square`). -/
theorem mixed_boundary_square (lam : ℝ) {F : ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (Icc (-1) 1)) :
    let G := mixedBoundaryTransport lam F
    (∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
      ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2 := by
  sorry

/-- Compact-subinterval absolute continuity on `(-1,1)`. -/
def MixedBoundaryLocAC (F : ℝ → ℂ) : Prop :=
  ∀ c d : ℝ, -1 < c → c < d → d < 1 → AbsolutelyContinuousOnInterval F c d

/-- Weighted boundary square (`lem:mixed-boundary-square-weighted`). The continuous
right side of the first-order equation gives an AC representative of `F'` on
every compact subinterval; in fact it equals the classical derivative there. -/
theorem mixed_boundary_square_weighted (lam : ℝ) {F G : ℝ → ℂ}
    (hF : MixedBoundaryLocAC F) (hG : MixedBoundaryLocAC G)
    (htransport : G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F)
    (hbF : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖F x‖ ≤ C)
    (hbG : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖G x‖ ≤ C)
    (henergy : IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) (Ioo (-1) 1)) :
    MixedBoundaryLocAC (deriv F) ∧
    (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖(boundaryWeight x : ℂ) * deriv F x‖ ≤ C) ∧
    IntegrableOn (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) (Ioo (-1) 1) ∧
    (∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
      ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2 := by
  sorry

end NoEmbeddedEigenvalues
