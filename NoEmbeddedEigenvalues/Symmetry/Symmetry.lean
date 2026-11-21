import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Symmetries of the dipole

The reflections `S₁`, `S₂`, the rotation `R` and the central inversion `Ic` of the torus
`(ℝ/2πℤ)²`, and how the dipole stream function `Ψ(x, y) = cos x + cos y` transforms under
them (blueprint: `def:reflections`, `lem:reflection-algebra`).

Here the torus is only a set of points, `Real.Angle × Real.Angle`. The action of the symmetries
on `L²` is in `SymmetryL2.lean`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real

/-- The torus `(ℝ/2πℤ)²` as a set of points. -/
abbrev Torus := Angle × Angle

/-- The stream function of the dipole, `Ψ(x, y) = cos x + cos y`. -/
def Ψ (p : Torus) : ℝ := p.1.cos + p.2.cos

/-- Reflection across the separatrix component `x + y ≡ π`. -/
def S₁ (p : Torus) : Torus := (π - p.2, π - p.1)

/-- Reflection across the separatrix component `x - y ≡ π`. -/
def S₂ (p : Torus) : Torus := (π + p.2, π + p.1)

/-- The clockwise quarter rotation. -/
def R (p : Torus) : Torus := (p.2, -p.1)

/-- The central inversion. -/
def Ic (p : Torus) : Torus := (-p.1, -p.2)

theorem cos_pi_sub (θ : Angle) : (π - θ).cos = -θ.cos := by
  rw [← neg_sub, Angle.cos_neg, Angle.cos_sub_pi]

theorem cos_pi_add (θ : Angle) : (π + θ).cos = -θ.cos := by
  rw [add_comm, Angle.cos_add_pi]

theorem S₁_comp_S₁ : S₁ ∘ S₁ = id := by
  funext ⟨a, b⟩
  simp [S₁]

theorem S₂_comp_S₂ : S₂ ∘ S₂ = id := by
  funext ⟨a, b⟩
  simp [S₂, ← add_assoc, Angle.coe_pi_add_coe_pi]

theorem S₁_comp_S₂ : S₁ ∘ S₂ = Ic := by
  funext ⟨a, b⟩
  simp [S₁, S₂, Ic]

theorem S₂_comp_S₁ : S₂ ∘ S₁ = Ic := by
  funext ⟨a, b⟩
  simp [S₁, S₂, Ic, ← add_sub_assoc, Angle.coe_pi_add_coe_pi]

theorem R_comp_R : R ∘ R = Ic := by
  funext ⟨a, b⟩
  simp [R, Ic]

theorem R_comp_S₁ : R ∘ S₁ = S₂ ∘ R := by
  funext ⟨a, b⟩
  simp only [Function.comp_apply, R, S₁, S₂, Prod.mk.injEq]
  constructor
  · abel
  · rw [neg_sub, sub_eq_add_neg, Angle.neg_coe_pi, add_comm]

theorem R_comp_S₂ : R ∘ S₂ = S₁ ∘ R := by
  funext ⟨a, b⟩
  simp only [Function.comp_apply, R, S₁, S₂, Prod.mk.injEq]
  constructor
  · abel
  · rw [neg_add, Angle.neg_coe_pi, sub_eq_add_neg]

theorem Ψ_comp_S₁ : Ψ ∘ S₁ = -Ψ := by
  funext ⟨a, b⟩
  simp only [Function.comp_apply, Pi.neg_apply, Ψ, S₁, cos_pi_sub]
  ring

theorem Ψ_comp_S₂ : Ψ ∘ S₂ = -Ψ := by
  funext ⟨a, b⟩
  simp only [Function.comp_apply, Pi.neg_apply, Ψ, S₂, cos_pi_add]
  ring

theorem Ψ_comp_R : Ψ ∘ R = Ψ := by
  funext ⟨a, b⟩
  simp only [Function.comp_apply, Ψ, R, Angle.cos_neg]
  ring

theorem Ψ_comp_Ic : Ψ ∘ Ic = Ψ := by
  funext ⟨a, b⟩
  simp [Ψ, Ic]

end NoEmbeddedEigenvalues

end
