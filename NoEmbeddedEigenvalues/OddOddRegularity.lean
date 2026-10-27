import NoEmbeddedEigenvalues.QuotientLocal
import NoEmbeddedEigenvalues.WeightedTraces
import NoEmbeddedEigenvalues.CylinderInverse
import NoEmbeddedEigenvalues.SaddleNormalForm

/-!
# Odd–odd regularity interfaces below the quotient domain

The saddle polynomial is a multiple of the quadratic Taylor polynomial of Ψ. Thus its
coefficient is normalized so that subtracting `a * Ψ` leaves the same quadratic jet.
Jets and weighted norms use Cartesian weak derivatives; orthonormal changes of saddle
coordinates preserve these qualitative estimates.

Separatrix regularity is local on the lift, so no global L² norm of a periodic lift on
an unbounded neighbourhood is required. Zero traces are canonical interval H¹ traces
of transverse ACL sections, never values assigned to a raw L² function on a line.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- First eigenfunction saddle gain (`prop:saddle-first-gain`), expressed on the
fixed bounded lift neighbourhood rather than taking a global norm on ℝ². -/
theorem saddle_first_gain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    MemLp (fun p ↦ liftL2 ω p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
  sorry

/-- Weighted vorticity and unique quadratic jet (`prop:saddle-dd`). -/
theorem saddle_dd {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    MemLp (fun p ↦ liftL2 ω p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellNeighbourhood) ∧
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃! a : ℂ,
      ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 2 (localDisk c ρ) (fun p ↦ contStream ω p - saddleQuadratic c a p) D ∧
        ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D := by
  sorry

/-- Weaker forcing weights and zero continuous stream values (`lem:dd-weighted-forcing`).
Away from the saddles the weights are bounded, and ordinary H² controls these norms. -/
theorem dd_weighted_forcing {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    MemLp (fun p ↦ contStream ω p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellNeighbourhood) ∧
    (∀ j, MemLp (fun p ↦ liftL2 (streamPartial j ω) p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellNeighbourhood)) ∧
    ∀ p, dipoleLift p = 0 → contStream ω p = 0 := by
  sorry

/-- H¹ vorticity, zero Sobolev traces and H³ stream regularity across the separatrix
(`prop:dd-separatrix-h1`). The neighbourhood may be unbounded; the spaces are local. -/
theorem dd_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      MemSobolevLocOn 1 U (liftL2 ω) ∧ HasZeroSeparatrixTraceOn U (liftL2 ω) ∧
      MemSobolevLocOn 3 U (contStream ω) := by
  sorry

/-- Weak gradient with the extra saddle weight (`prop:dd-weighted-gradient`). -/
theorem dd_weighted_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        HasWeakPartialOn U j (liftL2 ω) (D j) ∧
        MemSobolevLocOn 0 U (fun p ↦ D j p / (saddleDist p : ℂ)) := by
  sorry

/-- Weighted third derivatives of both quadratic and dipole remainders
(`lem:dd-weighted-third-stream`), using the same normalized coefficient a. -/
theorem dd_weighted_third_stream {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : ℂ,
      ∃ D₀ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 3 (localDisk c ρ) (fun p ↦ contStream ω p - saddleQuadratic c a p) D₀ ∧
        HasWeakJetOn 3 (localDisk c ρ) (fun p ↦ contStream ω p - a * (dipoleLift p : ℂ)) D ∧
        (∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c D₀) ∧
        (∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c D) := by
  sorry

end NoEmbeddedEigenvalues
