import NoEmbeddedEigenvalues.Regularity.CylinderSpectralForcing
import NoEmbeddedEigenvalues.Analysis.CylinderSynthesis

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

/-- The subcritical exponent three halves avoids every integer angular degree. -/
theorem cylinder_gap_three_halves (m : ℕ) : (3 / 2 : ℝ) ≠ (m : ℝ) := by
  intro he
  have hn : 2 * m = (3 : ℕ) := by
    exact_mod_cast (show (2 : ℝ) * (m : ℝ) = 3 by linarith)
  omega

/-- The critical exponent three avoids the even degrees of odd–odd parity. -/
theorem oddOdd_cylinder_gap_three (m : ℕ)
    (hm : AllowedSaddleDegree (fun _ ↦ false) m) : (3 : ℝ) ≠ (m : ℝ) := by
  intro he
  have hm3 : m = 3 := by exact_mod_cast he.symm
  subst m
  norm_num [AllowedSaddleDegree] at hm
  obtain ⟨k, hk⟩ := hm
  omega

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
