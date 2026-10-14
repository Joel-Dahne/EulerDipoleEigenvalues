import NoEmbeddedEigenvalues.SymmetryL2
import Mathlib.Tactic.Module

/-!
# Parity sectors and reduction

The four projections associated with the two separatrix reflections, their
parities and reconstruction, and preservation of the eigenvalue equation.
`true` denotes even parity and `false` denotes odd parity.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory
open scoped InnerProductSpace

theorem fourierCoeff_add (g h : L2) (k : ℤ × ℤ) :
    fourierCoeff (g + h) k = fourierCoeff g k + fourierCoeff h k := by
  simp only [fourierCoeff, inner_add_right, mul_add]

theorem fourierCoeff_smul (c : ℂ) (g : L2) (k : ℤ × ℤ) :
    fourierCoeff (c • g) k = c * fourierCoeff g k := by
  simp only [fourierCoeff, inner_smul_right]
  ring

theorem invLap_add (g h : L2) : invLap (g + h) = invLap g + invLap h := by
  apply fourierCoeff_ext
  intro k
  simp only [fourierCoeff_add, fourierCoeff_invLap]
  split_ifs <;> ring

theorem invLap_smul (c : ℂ) (g : L2) : invLap (c • g) = c • invLap g := by
  apply fourierCoeff_ext
  intro k
  simp only [fourierCoeff_smul, fourierCoeff_invLap]
  split_ifs <;> ring

theorem IsEigenSolution.add {lam : ℝ} {g h : L2}
    (hg : IsEigenSolution lam g) (hh : IsEigenSolution lam h) :
    IsEigenSolution lam (g + h) := by
  refine ⟨?_, ?_⟩
  · change fourierCoeff (g + h) 0 = 0
    rw [fourierCoeff_add, hg.1, hh.1, zero_add]
  · have hd := hg.2.add hh.2
    simpa only [invLap_add, add_add_add_comm, smul_add] using hd

theorem IsEigenSolution.smul {lam : ℝ} {g : L2}
    (hg : IsEigenSolution lam g) (c : ℂ) : IsEigenSolution lam (c • g) := by
  refine ⟨?_, ?_⟩
  · change fourierCoeff (c • g) 0 = 0
    rw [fourierCoeff_smul, hg.1, mul_zero]
  · have hd := hg.2.smul c
    rw [smul_comm c (I * lam)] at hd
    simpa only [invLap_smul, smul_add] using hd

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
