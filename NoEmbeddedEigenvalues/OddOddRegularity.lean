import NoEmbeddedEigenvalues.OddOddSaddle
import NoEmbeddedEigenvalues.OddOddLogarithmic

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
