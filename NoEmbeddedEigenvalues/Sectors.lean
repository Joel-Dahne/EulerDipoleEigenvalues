import NoEmbeddedEigenvalues.SymmetryL2
import Mathlib.Tactic.Module

/-!
# Parity sectors and reduction

The four projections associated with the two separatrix reflections, their
parities and reconstruction, and preservation of the eigenvalue equation
(blueprint: `def:sectors`, `lem:sector-reduction`, `lem:sector-swap`,
`def:rotation-characters`, `lem:rotation-characters`).
The equal-parity sectors split further into rotation characters ±1.
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

/-- Sectors are closed under addition. -/
theorem InSector.add {ε₁ ε₂ : Bool} {g h : L2}
    (hg : InSector ε₁ ε₂ g) (hh : InSector ε₁ ε₂ h) : InSector ε₁ ε₂ (g + h) := by
  constructor
  · rw [map_add, hg.1, hh.1, smul_add]
  · rw [map_add, hg.2, hh.2, smul_add]

/-- Sectors are closed under complex scalar multiplication. -/
theorem InSector.smul {ε₁ ε₂ : Bool} {g : L2} (hg : InSector ε₁ ε₂ g) (c : ℂ) :
    InSector ε₁ ε₂ (c • g) := by
  constructor
  · rw [map_smul, hg.1, smul_comm]
  · rw [map_smul, hg.2, smul_comm]

/-- The stream function `Δ⁻¹ g` has the parities of `g`. -/
theorem InSector.invLap {ε₁ ε₂ : Bool} {g : L2} (hg : InSector ε₁ ε₂ g) :
    InSector ε₁ ε₂ (invLap g) := by
  constructor
  · change symmetry₁.action (NoEmbeddedEigenvalues.invLap g) = _
    rw [symmetry₁.invLap_commute]
    change NoEmbeddedEigenvalues.invLap (reflect₁ g) = _
    rw [hg.1, map_smul]
  · change symmetry₂.action (NoEmbeddedEigenvalues.invLap g) = _
    rw [symmetry₂.invLap_commute]
    change NoEmbeddedEigenvalues.invLap (reflect₂ g) = _
    rw [hg.2, map_smul]

/-- Rotation character +1 (`true`) or -1 (`false`). -/
def InRotationCharacter (κ : Bool) (g : L2) : Prop :=
  rotate g = paritySign κ • g

/-- The rotation-character component `(g + κ R* g)/2`.
    It is a projection on the equal-parity sectors, not on arbitrary L². -/
def rotationProjection (κ : Bool) (g : L2) : L2 :=
  (1 / 2 : ℂ) • (g + paritySign κ • rotate g)

/-- Rotation is an involution on either equal-parity sector. -/
theorem InSector.rotate_rotate {ε : Bool} {g : L2} (hg : InSector ε ε g) :
    NoEmbeddedEigenvalues.rotate (NoEmbeddedEigenvalues.rotate g) = g := by
  rw [NoEmbeddedEigenvalues.rotate_rotate, centralInversion_eq_reflections,
    hg.2, map_smul, hg.1]
  cases ε <;> simp [paritySign]

/-- Both rotation-character components remain in the original equal-parity sector. -/
theorem InSector.rotationProjection_mem {ε : Bool} {g : L2}
    (hg : InSector ε ε g) (κ : Bool) : InSector ε ε (rotationProjection κ g) :=
  (hg.add (hg.rotate.smul (paritySign κ))).smul (1 / 2)

/-- The component has the specified rotation character. -/
theorem InSector.rotationProjection_character {ε : Bool} {g : L2}
    (hg : InSector ε ε g) (κ : Bool) : InRotationCharacter κ (rotationProjection κ g) := by
  unfold InRotationCharacter rotationProjection
  simp only [map_smul, map_add, hg.rotate_rotate]
  cases κ <;> simp only [paritySign, Bool.false_eq_true, ite_false, ite_true] <;> module

/-- The two components reconstruct the original function. -/
theorem rotationProjection_sum (g : L2) :
    rotationProjection true g + rotationProjection false g = g := by
  simp only [rotationProjection, paritySign, Bool.false_eq_true, ite_true, ite_false]
  module

/-- Rotation-character extraction preserves the eigenvalue equation at the same parameter. -/
theorem IsEigenSolution.rotationProjection {lam : ℝ} {g : L2}
    (hg : IsEigenSolution lam g) (κ : Bool) :
    IsEigenSolution lam (rotationProjection κ g) :=
  (hg.add (hg.rotate.smul (paritySign κ))).smul (1 / 2)

/-- The two rotation-character eigenspaces have zero intersection. -/
theorem rotation_characters_disjoint {g : L2}
    (hplus : InRotationCharacter true g) (hminus : InRotationCharacter false g) : g = 0 := by
  have hp : rotate g = g := by simpa [InRotationCharacter, paritySign] using hplus
  have hm : rotate g = -g := by simpa [InRotationCharacter, paritySign] using hminus
  have hz : (2 : ℂ) • g = 0 := by
    calc
      (2 : ℂ) • g = g + g := by module
      _ = rotate g + g := congrArg (fun h : L2 ↦ h + g) hp.symm
      _ = 0 := by rw [hm, neg_add_cancel]
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Explicit rotation-character decomposition of an equal-parity eigenfunction. -/
theorem IsEigenSolution.rotation_decomposition {lam : ℝ} {g : L2} {ε : Bool}
    (hg : IsEigenSolution lam g) (hsector : InSector ε ε g) :
    ∃ gplus gminus : L2, g = gplus + gminus ∧
      InSector ε ε gplus ∧ InSector ε ε gminus ∧
      InRotationCharacter true gplus ∧ InRotationCharacter false gminus ∧
      IsEigenSolution lam gplus ∧ IsEigenSolution lam gminus := by
  exact ⟨NoEmbeddedEigenvalues.rotationProjection true g,
    NoEmbeddedEigenvalues.rotationProjection false g, (rotationProjection_sum g).symm,
    hsector.rotationProjection_mem true, hsector.rotationProjection_mem false,
    hsector.rotationProjection_character true, hsector.rotationProjection_character false,
    hg.rotationProjection true, hg.rotationProjection false⟩

end NoEmbeddedEigenvalues
