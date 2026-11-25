module

public import Mathlib

/-!
# Challenge: no nonzero embedded eigenvalues for Euler linearized around the dipole

This file is the statement a reader audits. It imports only Mathlib, defines the few objects the
statement needs, and states the main theorem together with some sanity checks of the
definitions. Every theorem here is proved in `Solution.lean` from the development in
`EulerDipoleEigenvalues/`. The definitions are copied there verbatim. That the copies and the
statements agree, and which axioms the proofs use, is checked by `lake comparator` with
`comparator.json`. The local check `just challenge` is a quicker, unsandboxed diagnostic.

## The problem

On the torus `𝕋² = (ℝ/2πℤ)²` the vorticity form of the Euler equation is
`∂ₜω + u·∇ω = 0`, `u = ∇^⊥ψ = (-∂_yψ, ∂ₓψ)`, `Δψ = ω`. The dipole `Ω = -cos x - cos y`, with
stream function `Ψ = cos x + cos y` and velocity `u₀ = (sin y, -sin x)`, is a steady state.
Linearizing around it gives `∂ₜω + L₀(ω + ψ) = 0`, `Δψ = ω`, where `L₀ = sin y ∂ₓ - sin x ∂_y` is
the transport along `u₀`: the term `u·∇Ω` equals `u₀·∇ψ`. The main theorem says that the
linearized operator `L = L₀(1 + Δ⁻¹)` has no eigenvalue `iλ` with `λ ≠ 0` real:
if `L₀(ω + Δ⁻¹ω) = iλω` for a mean-zero `ω ∈ L²(𝕋²)`, then `ω = 0`.

## Formulation

The statement is at the level of the operator: `Δ⁻¹` and `L₀` are defined weakly, by testing
against the characters `e_k(x, y) = exp(i(k₁x + k₂y))`, `k ∈ ℤ²`. No Sobolev spaces are needed.

* `IsInvLap ω ψ`: `ψ = Δ⁻¹ω`, the mean-zero solution of `Δψ = ω`.
* `HasL0 g h`: `L₀g = h`.

The theorem assumes `L₀(ω + ψ) ∈ L²` but not `L₀ω ∈ L²`, so it is slightly stronger than the
statement with domain `𝒟 = {g ∈ L² : ∫ g = 0, L₀g ∈ L²}`; the two are equivalent because
`L₀ψ ∈ L²` for every `ω ∈ L²`.

## Reading guide

The definitions are written with Mathlib's `fourier`, `Real.Angle.sin` and the identification
`Real.Angle = AddCircle (2 * π)`. The sanity checks `char_coe` and `L0char_coe` restate the
characters and `L₀ e_k` with `Real.sin`, `Complex.exp` and `deriv` on `ℝ²`, so a reader need not
unfold these. `existsUnique_isInvLap` shows that `IsInvLap` determines `ψ` and can be met for every
mean-zero `ω`, `hasL0_char` shows that `HasL0` agrees with the classical `L₀` on characters (which
fixes its sign and rules out a degenerate definition), and `zero_eigenvalue` shows that the
assumption `λ ≠ 0` cannot be dropped.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex
open scoped Real ComplexConjugate

namespace EulerDipole

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The torus `𝕋² = (ℝ/2πℤ)²`. Its measure `volume` is the product of Mathlib's Haar measures of
total mass `2π` on `ℝ/2πℤ`, that is, Lebesgue measure `dx dy`. -/
abbrev Torus := AddCircle (2 * π) × AddCircle (2 * π)

/-- `L²(𝕋²; ℂ)` with respect to `dx dy`. -/
abbrev L2 := Lp ℂ 2 (volume : Measure Torus)

/-- The character `e_k(x, y) = exp(i(k₁x + k₂y))`, see `char_coe`. Mathlib's `fourier n` is
`x ↦ exp(2πinx/T)` on `ℝ/Tℤ`, here with `T = 2π`. -/
def char (k : ℤ × ℤ) (p : Torus) : ℂ := fourier k.1 p.1 * fourier k.2 p.2

/-- The Fourier coefficient `ĝ(k) = (2π)⁻² ∫_{𝕋²} conj(e_k) g dx dy`. In particular `ĝ(0)` is the
mean of `g`. -/
def coeff (g : L2) (k : ℤ × ℤ) : ℂ := ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, conj (char k p) * g p

/-- `ψ = Δ⁻¹ω`: `ψ` has mean zero and solves `Δψ = ω` weakly. Testing `∫ ψ Δφ = ∫ ω φ` with
`φ = conj(e_k)`, for which `Δφ = -(k₁² + k₂²) φ`, gives the coefficient equations below. For
`k = 0` the equation says that `ω` has mean zero. -/
def IsInvLap (ω ψ : L2) : Prop :=
  coeff ψ 0 = 0 ∧ ∀ k : ℤ × ℤ, -((k.1 : ℂ) ^ 2 + (k.2 : ℂ) ^ 2) * coeff ψ k = coeff ω k

/-- `L₀ e_k = i(k₁ sin y - k₂ sin x) e_k`, where `L₀ = sin y ∂ₓ - sin x ∂_y`, see `L0char_coe`. -/
def L0char (k : ℤ × ℤ) (p : Torus) : ℂ :=
  I * (k.1 * Real.Angle.sin p.2 - k.2 * Real.Angle.sin p.1) * char k p

/-- `L₀g = h` weakly. The vector field `L₀` is real and divergence free, so
`∫ (L₀g) φ = -∫ g L₀φ`; testing with `φ = conj(e_k)`, for which `L₀φ = conj(L₀e_k)`, gives the
equations below. -/
def HasL0 (g h : L2) : Prop :=
  ∀ k : ℤ × ℤ, ∫ p, conj (char k p) * h p = -∫ p, conj (L0char k p) * g p

/-! ### Main theorem -/

/-- **Main theorem.** The Euler equation linearized around the dipole has no nonzero embedded
eigenvalues: if `ψ = Δ⁻¹ω` and `L₀(ω + ψ) = iλω` with `λ ≠ 0` real, then `ω = 0`. -/
theorem no_embedded_eigenvalues (lam : ℝ) (hlam : lam ≠ 0) (ω ψ : L2) (hψ : IsInvLap ω ψ)
    (h : HasL0 (ω + ψ) ((I * lam) • ω)) : ω = 0 := by
  sorry

/-! ### Sanity checks of the definitions -/

/-- The characters are `e_k(x, y) = exp(i(k₁x + k₂y))`. -/
theorem char_coe (k : ℤ × ℤ) (x y : ℝ) :
    char k ((x : AddCircle (2 * π)), (y : AddCircle (2 * π))) =
      exp (I * (k.1 * x + k.2 * y)) := by
  sorry

/-- `L0char k` is `L₀ = sin y ∂ₓ - sin x ∂_y` applied to `e_k`, computed with derivatives of
`(x, y) ↦ exp(i(k₁x + k₂y))` on `ℝ²`. -/
theorem L0char_coe (k : ℤ × ℤ) (x y : ℝ) :
    L0char k ((x : AddCircle (2 * π)), (y : AddCircle (2 * π))) =
      Real.sin y * deriv (fun s : ℝ => exp (I * (k.1 * s + k.2 * y))) x -
        Real.sin x * deriv (fun t : ℝ => exp (I * (k.1 * x + k.2 * t))) y := by
  sorry

/-- `Δ⁻¹ω` exists and is unique for every mean-zero `ω`. -/
theorem existsUnique_isInvLap (ω : L2) (hω : coeff ω 0 = 0) : ∃! ψ, IsInvLap ω ψ := by
  sorry

/-- `HasL0` agrees with the classical `L₀` on the characters: `L₀ e_k = L0char k`. -/
theorem hasL0_char (k : ℤ × ℤ) (g h : L2) (hg : g =ᵐ[volume] char k)
    (hh : h =ᵐ[volume] L0char k) : HasL0 g h := by
  sorry

/-- The assumption `λ ≠ 0` cannot be dropped: for example `ω = e^{ix}` has `Δ⁻¹ω = -ω`, so
`ω + Δ⁻¹ω = 0` and `L₀(ω + Δ⁻¹ω) = 0 = i · 0 · ω`. -/
theorem zero_eigenvalue :
    ∃ ω ψ : L2, ω ≠ 0 ∧ IsInvLap ω ψ ∧ HasL0 (ω + ψ) ((I * (0 : ℝ)) • ω) := by
  sorry

end EulerDipole
