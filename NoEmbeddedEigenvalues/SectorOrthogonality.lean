import NoEmbeddedEigenvalues.Sectors

/-! # Orthogonality of the parity projections -/

noncomputable section
namespace NoEmbeddedEigenvalues

open scoped InnerProductSpace

/-- The four sector projections are self-adjoint, mutually orthogonal and fix their ranges.
Together with `sectorProjection_sum`, they give the orthogonal decomposition of L². -/
theorem sector_projections_orthogonal :
    (∀ (ε₁ ε₂ : Bool) (g h : L2),
      ⟪sectorProjection ε₁ ε₂ g, h⟫_ℂ = ⟪g, sectorProjection ε₁ ε₂ h⟫_ℂ) ∧
    (∀ (ε₁ ε₂ δ₁ δ₂ : Bool) (g : L2),
      sectorProjection ε₁ ε₂ (sectorProjection δ₁ δ₂ g) =
        if ε₁ = δ₁ ∧ ε₂ = δ₂ then sectorProjection δ₁ δ₂ g else 0) ∧
    (∀ (ε₁ ε₂ : Bool) (g : L2), InSector ε₁ ε₂ g → sectorProjection ε₁ ε₂ g = g) := by
  sorry

end NoEmbeddedEigenvalues
