import NoEmbeddedEigenvalues.Regularity.QuotientLocal
import NoEmbeddedEigenvalues.WeakJetOperations

/-!
# Radially weighted interior elliptic regularity

The weighted third-order gain is the dyadic summation corollary of the uniform
annular estimate. It is an analytic input, independent of eigenfunctions or parity.
Lower jet entries are preserved, not replaced by unrelated representatives.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Dyadic summation of the interior Poisson estimate
(`lem:elliptic-weighted-third`). Shrinking avoids the outer boundary. -/
theorem elliptic_weighted_third {c : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    {G : Fin 2 → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) u D)
    (hw : ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D)
    (hG : ∀ j, HasWeakPartialOn (localDisk c ρ) j F (G j))
    (hGw : ∀ j, MemLp (fun p ↦ G j p / (localRadius c p : ℂ)) 2
      (volume.restrict (localDisk c ρ)))
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk c ρ)), D [0, 0] p + D [1, 1] p = F p) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ ρ ∧ ∃ E : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 3 (localDisk c σ) u E ∧
      (∀ w, w.length ≤ 2 → E w = D w) ∧ RadialJetLp 3 1 (localDisk c σ) c E := by
  sorry

end NoEmbeddedEigenvalues
