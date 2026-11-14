import NoEmbeddedEigenvalues.Regularity.CylinderParity

/-!
# Smooth harmonic comparison of two specified weak Poisson solutions

The two functions and both ordered weak jets occupy the same whole disk,
including its center. Equal weak Laplacians give a smooth harmonic representative
of their difference. Axis parity is transferred a.e.; Taylor-jet consequences
are separate from this comparison.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Same-domain weak Poisson solutions differ by a smooth harmonic representative
with their common parity (`lem:weak-poisson-harmonic-comparison`). -/
theorem weak_poisson_harmonic_comparison {ρ : ℝ} (hρ : 0 < ρ)
    {ε : Fin 2 → Bool} {u v : ℝ × ℝ → ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hu : MemSobolevOn 2 (localDisk 0 ρ) u)
    (hv : MemSobolevOn 2 (localDisk 0 ρ) v)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hE : HasWeakJetOn 2 (localDisk 0 ρ) v E)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)),
      D [0, 0] p + D [1, 1] p = E [0, 0] p + E [1, 1] p)
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hpv : HasAxisParityOn ε (localDisk 0 ρ) v) :
    ∃ h : ℝ × ℝ → ℂ,
      IsPlaneHarmonicOn (localDisk 0 ρ) h ∧
      HasAxisParityOn ε (localDisk 0 ρ) h ∧
      ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), u p = v p + h p := by
  sorry

end NoEmbeddedEigenvalues
