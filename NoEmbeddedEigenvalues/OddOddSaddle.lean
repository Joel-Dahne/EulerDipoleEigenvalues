import NoEmbeddedEigenvalues.QuotientLocal
import NoEmbeddedEigenvalues.WeightedTraces
import NoEmbeddedEigenvalues.CylinderInverse
import NoEmbeddedEigenvalues.SaddleNormalForm

/-!
# Odd–odd saddle and ordinary separatrix regularity interfaces

These inputs precede logarithmic forcing and weighted vorticity gradients.
Their separation lets the logarithmic layer use the ordinary H³ stream
regularity without importing the gradient theorem it is intended to prove.
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

end NoEmbeddedEigenvalues
