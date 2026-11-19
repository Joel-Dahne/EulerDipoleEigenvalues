import NoEmbeddedEigenvalues.TraceH2
import NoEmbeddedEigenvalues.LocalJets

/-! # Tangential differentiation of the one-sided H² trace -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped Topology

/-- The rectangle coordinates with the tangential coordinate listed first. -/
def traceSideCoords (j : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then p else p.swap

/-- On either side normal to coordinate `1 - j`, the canonical L² traces of an H²
function and its tangential weak partial are represented by an absolutely continuous
function on the closed side and its a.e. derivative, respectively. The interior
function need not have a pointwise representative on the side. -/
theorem hasWeakJetOn_h2_boundary_trace (j : Fin 2) {a₀ a₁ b₀ b₁ t : ℝ}
    (ha : a₀ < a₁) (hb : b₀ < b₁) (ht : t = b₀ ∨ t = b₁)
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (traceSideCoords j '' (Ioo a₀ a₁ ×ˢ Ioo b₀ b₁)) F D)
    (hL : ∀ w, w.length ≤ 2 →
      MemLp (D w) 2 (volume.restrict (traceSideCoords j '' (Ioo a₀ a₁ ×ˢ Ioo b₀ b₁)))) :
    ∃ G H : ℝ × ℝ → ℂ, ∃ T : ℝ → ℂ,
      let I := Ioo a₀ a₁
      let J := Ioo b₀ b₁
      let E := D [1 - j] ∘ traceSideCoords j
      let E' := D [1 - j, j] ∘ traceSideCoords j
      G =ᵐ[volume.restrict (I ×ˢ J)] (F ∘ traceSideCoords j) ∧
      H =ᵐ[volume.restrict (I ×ˢ J)] (D [j] ∘ traceSideCoords j) ∧
      HasACLSectionsOn I J G E ∧ HasACLSectionsOn I J H E' ∧
      MemLp (aclTrace b₀ b₁ G E t) 2 (volume.restrict I) ∧
      MemLp (aclTrace b₀ b₁ H E' t) 2 (volume.restrict I) ∧
      T =ᵐ[volume.restrict I] aclTrace b₀ b₁ G E t ∧
      AbsolutelyContinuousOnInterval T a₀ a₁ ∧
      ContinuousOn T (Icc a₀ a₁) ∧
      (∃ M : ℝ, ∀ a ∈ Icc a₀ a₁, ‖T a‖ ≤ M) ∧
      (∀ᵐ a ∂volume.restrict I, HasDerivAt T (aclTrace b₀ b₁ H E' t a) a) := by
  sorry

end NoEmbeddedEigenvalues
