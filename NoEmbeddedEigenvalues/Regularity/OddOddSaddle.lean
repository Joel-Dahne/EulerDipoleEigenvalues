import NoEmbeddedEigenvalues.Regularity.QuotientLocal
import NoEmbeddedEigenvalues.WeightedTraces
import NoEmbeddedEigenvalues.Regularity.CylinderInverse
import NoEmbeddedEigenvalues.Regularity.SaddleNormalForm

/-!
# Odd–odd saddle and weighted forcing interfaces

These inputs precede ordinary separatrix H¹, logarithmic forcing and weighted
vorticity gradients. The ordinary whole-lift endpoint is in OddOddSeparatrix;
its cellwise ingredients depend on the forcing input here, not on logarithmic
forcing or the weighted-gradient theorem.
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

end NoEmbeddedEigenvalues
