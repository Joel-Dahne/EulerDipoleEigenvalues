import NoEmbeddedEigenvalues.SymmetryL2
import Mathlib.Tactic.Module

/-!
# Parity sectors and reduction

The four projections associated with the two separatrix reflections, their
parities and reconstruction, and preservation of the eigenvalue equation
(blueprint: `def:sectors`, `lem:sector-reduction`, `lem:sector-swap`).
`true` denotes even parity and `false` denotes odd parity.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory
open scoped InnerProductSpace

/-- The sign associated with a parity: true is even (+1), false is odd (-1). -/
def paritySign (ε : Bool) : ℂ := if ε then 1 else -1

/-- Simultaneous parity under the two separatrix reflections. -/
def InSector (ε₁ ε₂ : Bool) (g : L2) : Prop :=
  reflect₁ g = paritySign ε₁ • g ∧ reflect₂ g = paritySign ε₂ • g

/-- The projection (I + ε₁S₁*)(I + ε₂S₂*)/4, expanded in L². -/
def sectorProjection (ε₁ ε₂ : Bool) (g : L2) : L2 :=
  (1 / 4 : ℂ) • (g + paritySign ε₁ • reflect₁ g + paritySign ε₂ • reflect₂ g +
    (paritySign ε₁ * paritySign ε₂) • reflect₁ (reflect₂ g))

theorem sectorProjection_mem (ε₁ ε₂ : Bool) (g : L2) :
    InSector ε₁ ε₂ (sectorProjection ε₁ ε₂ g) := by
  constructor <;> cases ε₁ <;> cases ε₂ <;>
    simp only [sectorProjection, paritySign, Bool.false_eq_true, ite_false, ite_true,
      map_smul, map_add, reflect₁_involutive, reflect₂_involutive, reflect_commute] <;>
    module

theorem sectorProjection_sum (g : L2) :
    sectorProjection true true g + sectorProjection false false g +
      sectorProjection false true g + sectorProjection true false g = g := by
  simp only [sectorProjection, paritySign, Bool.false_eq_true, ite_true, ite_false]
  module

theorem IsEigenSolution.sectorProjection {lam : ℝ} {g : L2}
    (hg : IsEigenSolution lam g) (ε₁ ε₂ : Bool) :
    IsEigenSolution lam (sectorProjection ε₁ ε₂ g) :=
  (((hg.add (hg.reflect₁.smul (paritySign ε₁))).add
    (hg.reflect₂.smul (paritySign ε₂))).add
    (hg.reflect₂.reflect₁.smul (paritySign ε₁ * paritySign ε₂))).smul (1 / 4)

/-- Quarter rotation swaps the two separatrix parities. -/
theorem InSector.rotate {ε₁ ε₂ : Bool} {g : L2} (hg : InSector ε₁ ε₂ g) :
    InSector ε₂ ε₁ (rotate g) := by
  constructor
  · rw [reflect₁_rotate, hg.2, map_smul]
  · rw [reflect₂_rotate, hg.1, map_smul]

end NoEmbeddedEigenvalues
