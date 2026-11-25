module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalJets
public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval

/-!
# Finite specified weak jets and removal of one point

Finite norms are hypotheses on the whole target domain at every ordered level.
They supply recursive Sobolev membership and the local integrability needed to
extend each specified weak pair through an isolated point.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- A specified weak jet with finite norms gives recursive Sobolev membership
without replacing its entries by newly chosen derivative representatives. -/
theorem HasWeakJetOn.memSobolevOn {n : ℕ} {U : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U F D)
    (hL : ∀ w, w.length ≤ n → MemLp (D w) 2 (volume.restrict U)) :
    MemSobolevOn n U F := by
  induction n generalizing F D with
  | zero =>
    change MemLp F 2 (volume.restrict U)
    simpa only [hD.1] using hL [] (by simp)
  | succ n ih =>
    refine ⟨by simpa only [hD.1] using hL [] (by simp), fun j ↦ ?_⟩
    refine ⟨D [j], by simpa only [hD.1] using hD.2 [] (by simp) j, ?_⟩
    apply ih (D := fun w ↦ D (w ++ [j]))
    · refine ⟨rfl, fun w hw i ↦ ?_⟩
      exact hD.2 (w ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega) i
    · intro w hw
      exact hL (w ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)

/-- Whole-domain finite norms remove the point separately for every ordered
weak pair. Merely local norms away from the point would not suffice. -/
theorem HasWeakJetOn.remove_point {n : ℕ} {U : Set (ℝ × ℝ)} {c : ℝ × ℝ}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n (U \ {c}) F D)
    (hL : ∀ w, w.length ≤ n → MemLp (D w) 2 (volume.restrict U)) :
    HasWeakJetOn n U F D := by
  refine ⟨hD.1, fun w hw j ↦ (hD.2 w hw j).remove_point ?_ ?_⟩
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hL w (Nat.le_of_lt hw)).locallyIntegrable (by norm_num))
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hL (j :: w) (by simpa using Nat.succ_le_of_lt hw)).locallyIntegrable (by norm_num))

end EulerDipoleEigenvalues
