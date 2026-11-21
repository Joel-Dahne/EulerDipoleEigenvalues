module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleDistanceWeights
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SobolevGluing

/-!
# Finite-norm removal of the lifted saddle lattice

Blueprint: `lem:saddle-set-h1-removal`.

Full-domain local L² bounds give finite H¹ on a whole punctured neighborhood
of each saddle. Uniform saddle separation isolates that one missing point.
Point removal and local Sobolev gluing then recover H¹ on the original open
set. Merely local H¹ away from the lattice would not supply these finite norms.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Specified weak derivatives away from the saddle lattice extend to ordinary
local H¹ when the value and derivative norms are locally finite on the full set. -/
theorem memSobolevLocOn_of_weakGradient_off_saddleSet {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hF : MemSobolevLocOn 0 U F)
    (hD : ∀ j, HasWeakPartialOn (U \ saddleSet) j F (D j) ∧
      MemSobolevLocOn 0 U (D j)) : MemSobolevLocOn 1 U F := by
  classical
  apply memSobolevLocOn_of_locally
  intro p hp
  let W := if p ∈ saddleSet then U ∩ Metric.ball p (Real.pi / 2) else U \ saddleSet
  have hW : IsOpen W := by
    dsimp [W]
    split_ifs
    · exact hU.inter Metric.isOpen_ball
    · exact hU.inter isClosed_saddleSet.isOpen_compl
  have hWU : W ⊆ U := by
    dsimp [W]
    split_ifs
    · exact inter_subset_left
    · exact sdiff_subset
  have hpW : p ∈ W := by
    dsimp [W]
    split_ifs with hs
    · exact ⟨hp, Metric.mem_ball_self (by positivity)⟩
    · exact ⟨hp, hs⟩
  obtain ⟨V, hV, hpV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    isCompact_singleton hW (singleton_subset_iff.mpr hpW)
  have hVU : closure V ⊆ U := hVW.trans hWU
  have hpunct : V \ {p} ⊆ U \ saddleSet := by
    intro q hq
    have hqW := hVW (subset_closure hq.1)
    refine ⟨hWU hqW, ?_⟩
    intro hqs
    by_cases hps : p ∈ saddleSet
    · have hqb : dist q p < Real.pi / 2 := by
        have h := hqW
        simp only [W, hps, ite_true] at h
        exact h.2
      have hsep := pi_le_dist_saddles hqs hps (by simpa only [mem_singleton_iff] using hq.2)
      linarith [Real.pi_pos]
    · have h := hqW
      simp only [W, hps, ite_false] at h
      exact h.2 hqs
  have hFV : MemLp F 2 (volume.restrict V) := hF V hV hVc hVU
  have hSob : MemSobolevOn 1 (V \ {p}) F := by
    refine ⟨hFV.mono_measure (Measure.restrict_mono sdiff_subset le_rfl), fun j ↦ ?_⟩
    have hDV : MemLp (D j) 2 (volume.restrict V) := (hD j).2 V hV hVc hVU
    exact ⟨D j, (hD j).1.mono hpunct,
      hDV.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)⟩
  exact ⟨V, hV, hpV (mem_singleton p), hSob.remove_point.memSobolevLocOn⟩

end NoEmbeddedEigenvalues
