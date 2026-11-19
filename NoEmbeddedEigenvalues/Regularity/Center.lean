import NoEmbeddedEigenvalues.LiftPeriodization
import NoEmbeddedEigenvalues.Sectors

/-! # Eigenfunction regularity at centers and on the torus -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Local vorticity regularity near each lift of either elliptic center. The
condition `|Ψ(P)| = 2` covers both the maximum and the minimum of the dipole.
Nonzero integer parameters are included. -/
theorem center_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {P : ℝ × ℝ} (hP : |dipoleLift P| = 2) :
    ∃ r : ℝ, 0 < r ∧ MemSobolevOn 1 (Metric.ball P r) (liftL2 ω) := by
  sorry

/-- The vorticity is globally H¹ and its stream function globally H³ in each
odd–odd or mixed sector (at least one odd reflection). -/
theorem global_eigenfunction_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {ε₁ ε₂ : Bool} (hs : InSector ε₁ ε₂ ω)
    (hodd : ε₁ = false ∨ ε₂ = false) :
    MemSobolev 1 ω ∧ MemSobolev 3 (invLap ω) := by
  sorry

end NoEmbeddedEigenvalues
