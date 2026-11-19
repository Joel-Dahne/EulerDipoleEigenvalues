import NoEmbeddedEigenvalues.LocalJets

/-! # Radial Hardy bounds for an even H² corner -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped Topology

/-- An H² function even in both axes has the indicated weighted remainders after
subtracting its continuous value at the corner. The derivative is taken from the
specified weak jet. -/
theorem even_h2_corner_hardy {R : ℝ} (hR : 0 < R) {F : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (localDisk 0 R))
    (hD : HasWeakJetOn 2 (localDisk 0 R) F D)
    (hL : ∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict (localDisk 0 R)))
    (he : ∀ j : Fin 2, ∀ᵐ q ∂volume.restrict (localDisk 0 R), F (axisReflect j q) = F q) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ RadialJetLp 1 1 (localDisk 0 r) 0 D ∧
      MemLp (fun q ↦ (F q - F 0) / (localRadius 0 q ^ 2 : ℂ)) 2
        (volume.restrict (localDisk 0 r)) := by
  sorry

end NoEmbeddedEigenvalues
