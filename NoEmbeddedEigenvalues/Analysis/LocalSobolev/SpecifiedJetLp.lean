module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets

/-!
# Finite norms of a specified weak jet

Blueprint: `lem:specified-jet-lp`, `lem:specified-first-jet-extension`.

Recursive Sobolev membership gives finite norms for the original supplied jet,
not just for a newly selected family. The word head remains the outer derivative;
induction peels off the innermost (last) index. No mixed entries are identified.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Every entry of a supplied weak jet inherits the actual finite norm from
recursive Sobolev membership on an open domain. -/
theorem MemSobolevOn.memLp_weakJet {n : ℕ} {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevOn n U f) (hU : IsOpen U)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hD : HasWeakJetOn n U f D) :
    ∀ w, w.length ≤ n → MemLp (D w) 2 (volume.restrict U) := by
  induction n generalizing f D with
  | zero =>
    intro w hw
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    simpa only [he, hD.1] using (show MemLp f 2 (volume.restrict U) from hf)
  | succ n ih =>
    intro w hw
    cases w using List.reverseRecOn with
    | nil => simpa only [hD.1] using hf.1
    | append_singleton w j =>
      obtain ⟨G, hG, hGs⟩ := hf.2 j
      have hfirst := hD.2 [] (by simp) j
      rw [hD.1] at hfirst
      have hDj : MemSobolevOn n U (D [j]) :=
        (show MemSobolevOn n U G from hGs).congr_ae_on hU.measurableSet
          (hG.ae_eq hU hfirst)
      have hshift : HasWeakJetOn n U (D [j]) (fun v ↦ D (v ++ [j])) := by
        refine ⟨rfl, fun v hv i ↦ ?_⟩
        exact hD.2 (v ++ [j]) (by simpa using Nat.succ_lt_succ hv) i
      exact ih hDj hshift w (by simpa using hw)

/-- Extend the supplied first derivatives to a genuine second weak jet,
without replacing those first entries or assuming any second entries. -/
theorem MemSobolevOn.exists_weakJet_two_with_first {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevOn 2 U f) (hU : IsOpen U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j)) :
    ∃ J : List (Fin 2) → ℝ × ℝ → ℂ, HasWeakJetOn 2 U f J ∧ ∀ j, J [j] = D j := by
  have hfirst (j : Fin 2) : MemSobolevOn 1 U (D j) := by
    obtain ⟨G, hG, hGs⟩ := hf.2 j
    exact (show MemSobolevOn 1 U G from hGs).congr_ae_on hU.measurableSet
      (hG.ae_eq hU (hD j))
  choose E hE hEL using fun j ↦ (hfirst j).2
  let J : List (Fin 2) → ℝ × ℝ → ℂ
    | [] => f
    | [j] => D j
    | [i, j] => E j i
    | _ => 0
  refine ⟨J, ⟨rfl, ?_⟩, fun _ ↦ rfl⟩
  intro w hw i
  cases w with
  | nil => exact hD i
  | cons j w =>
    cases w with
    | nil => exact hE j i
    | cons k w => simp at hw

end NoEmbeddedEigenvalues
