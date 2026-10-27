import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.Sectors

/-!
# Weighted cylinder inverse interface

The input is weighted physical-area L²: F/r^(a-1), not F/r^a. After t = -log r
this is the cylinder weight r^(2-a) F. Parity uses `paritySign`: true is even.
The harmonic remainder is specified by smoothness, the classical Laplace equation
and forbidden Taylor jets; no convergence assertion for an infinite series is needed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff

/-- The two prescribed coordinate reflection parities. -/
def HasAxisParityOn (ε : Fin 2 → Bool) (U : Set (ℝ × ℝ)) (u : ℝ × ℝ → ℂ) : Prop :=
  ∀ j, ∀ᵐ p ∂(volume.restrict U), u (axisReflect j p) = paritySign (ε j) * u p

/-- Allowed nonnegative harmonic angular degrees: even–even permits 0,2,…,
odd–odd permits 2,4,…, and either mixed parity permits 1,3,…. -/
def AllowedSaddleDegree (ε : Fin 2 → Bool) (m : ℕ) : Prop :=
  (Even m ↔ ε 0 = ε 1) ∧ (m = 0 → ε 0 = true ∧ ε 1 = true)

/-- Classical complex jet, used for the smooth harmonic remainder. -/
def classicalComplexJet : List (Fin 2) → (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ
  | [], f => f
  | j :: w, f => coordPartial j (classicalComplexJet w f)

/-- Smooth harmonicity for the Euclidean plane, stated in Cartesian coordinates.
It does not posit an inner-product structure on the maximum-norm product. -/
def IsPlaneHarmonicOn (U : Set (ℝ × ℝ)) (h : ℝ × ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ h U ∧ ∀ p ∈ U,
    coordPartial 0 (coordPartial 0 h) p + coordPartial 1 (coordPartial 1 h) p = 0

/-- Cylinder inversion with physical-area weights and a smooth harmonic remainder
(`lem:cylinder-inverse`). All derivatives in the weighted remainder are weak jets. -/
theorem cylinder_inverse {ρ a : ℝ} (hρ : 0 < ρ) (ha : 1 < a)
    {ε : Fin 2 → Bool} (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hu : MemSobolevOn 2 (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ ρ₁ < ρ ∧ 0 < C ∧
      ∃ (u₀ h : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (localDisk 0 ρ₁) u₀ ∧
        HasWeakJetOn 2 (localDisk 0 ρ₁) u₀ E ∧
        ContinuousOn u₀ (localDisk 0 ρ₁) ∧
        (∀ p ∈ localDisk 0 ρ₁, ‖u₀ p‖ ≤ C * Real.rpow (localRadius 0 p) a) ∧
        (∀ k ≤ 2, RadialJetRpowLp k (a + 1 - (k : ℝ)) (localDisk 0 ρ₁) 0 E) ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ₁)), E [0, 0] p + E [1, 1] p = F p) ∧
        HasAxisParityOn ε (localDisk 0 ρ₁) u₀ ∧
        IsPlaneHarmonicOn (localDisk 0 ρ₁) h ∧ HasAxisParityOn ε (localDisk 0 ρ₁) h ∧
        (∀ w : List (Fin 2), ¬AllowedSaddleDegree ε w.length →
          classicalComplexJet w h 0 = 0) ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ₁)), u p = u₀ p + h p) := by
  sorry

end NoEmbeddedEigenvalues
