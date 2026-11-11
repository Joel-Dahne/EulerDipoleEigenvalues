import NoEmbeddedEigenvalues.Regularity.OddOddSaddle
import NoEmbeddedEigenvalues.DipoleLogMultiplier
import NoEmbeddedEigenvalues.WeakJetOperations
import NoEmbeddedEigenvalues.StreamJet

/-!
# Ordinary logarithmic stream-jet mass near the separatrix

Blueprint: `lem:dd-log-ordinary-bulk`.

The H³ stream gain puts the fixed first and second Fourier jet entries in H¹.
The physical logarithmic multiplier controls these same raw representatives,
without changing the derivative data used by the orbit numerators or ray traces.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The unweighted-in-distance part of logarithmic forcing, with the canonical
stream jet on one neighbourhood of the whole lifted separatrix. -/
theorem dd_log_ordinary_bulk {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∀ w : List (Fin 2), w.length = 1 ∨ w.length = 2 →
        MemSobolevLocOn 0 U (fun p ↦
          (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω w p) := by
  obtain ⟨U, hU, hsep, _, _, hF⟩ := dd_separatrix_h1 hlam hω hs
  refine ⟨U, hU, hsep, fun w hw ↦ ?_⟩
  have hJ := (streamJet2_weak ω U).memSobolevLocOn hF w (by omega) (by omega)
  have hH1 : MemSobolevLocOn 1 U (streamJet2 ω w) := by
    rcases hw with hw | hw
    · rw [hw] at hJ
      exact hJ.of_succ
    · simpa only [hw] using hJ
  exact hH1.log_dipole_mul hU

end NoEmbeddedEigenvalues
