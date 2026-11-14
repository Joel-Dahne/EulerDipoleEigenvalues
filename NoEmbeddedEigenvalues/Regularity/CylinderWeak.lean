import NoEmbeddedEigenvalues.Analysis.CylinderSignedInverse
import NoEmbeddedEigenvalues.LocalJets

/-!
# Weak inversion on the full logarithmic cylinder

The cylinder has real time and probability-Haar angular measure. Weak identities
are imposed on the entire real-angle lift, not merely on a strip with a null
seam omitted. Derivative entries live on the angular circle and have finite
joint L² norms. The zeroth entry is the actual signed integral reconstruction.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Lift a function on the angular cylinder to the real-angle plane. -/
def cylinderLift (S : ℝ × AddCircle (2 * Real.pi) → ℂ) : ℝ × ℝ → ℂ :=
  S ∘ logCylinderProjection

/-- A specified second cylinder jet: actual zeroth entry, ordered weak
identities on the whole periodic lift, and finite joint norms of every entry. -/
def HasCylinderH2Jet (S : ℝ × AddCircle (2 * Real.pi) → ℂ)
    (E : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) : Prop :=
  E [] = S ∧
    HasWeakJetOn 2 univ (cylinderLift S) (fun w ↦ cylinderLift (E w)) ∧
    ∀ w : List (Fin 2), w.length ≤ 2 → MemLp (E w) 2 logCylinderMeasure

/-- The conjugated polar Laplacian; index zero is time, index one is angle. -/
def cylinderJetOperator (a : ℝ)
    (E : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ)
    (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  E [0, 0] q - (2 * (a : ℂ)) * E [0] q + (a : ℂ) ^ 2 * E [] q + E [1, 1] q

/-- The actual signed inverse integral has a finite weak second jet and solves
`((∂t - a)^2 + ∂θ^2) S = G` on the full cylinder (`lem:cylinder-weak-inverse`). -/
theorem cylinder_signed_inverse_weak {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ))
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    (hM : ∀ᵐ p ∂cylinderFourierMeasure,
      p.2.natAbs ∉ M → cylinderFourierData hG p = 0) :
    ∃ E : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ,
      HasCylinderH2Jet (cylinderJointSynthesis (cylinderSignedInverse a hG)) E ∧
      cylinderJetOperator a E =ᵐ[logCylinderMeasure] G := by
  sorry

end NoEmbeddedEigenvalues
