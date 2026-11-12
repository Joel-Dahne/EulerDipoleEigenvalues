import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix
import NoEmbeddedEigenvalues.Regularity.OddOddLogSaddle
import NoEmbeddedEigenvalues.DipoleLogMultiplier
import NoEmbeddedEigenvalues.WeakJetOperations
import NoEmbeddedEigenvalues.StreamJet

/-!
# Logarithmic stream-jet mass near the separatrix

Blueprint: `lem:dd-log-ordinary-bulk`, `lem:dd-log-bulk`.

The H³ stream gain puts the fixed first and second Fourier jet entries in H¹.
The physical logarithmic multiplier controls these same raw representatives,
without changing the derivative data used by the orbit numerators or ray traces.
Near each saddle the quadratic and remainder bounds are summed and transferred
to the lattice distance by a bounded measurable multiplier. Away from saddles,
inverse distance is continuous. Local gluing retains one lifted neighbourhood.
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

/-- All logarithmic bulk assertions on one open neighbourhood of the full lifted
separatrix. Only ray traces and their weighted bounds are omitted. -/
theorem dd_log_bulk {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      (∀ j : Fin 2, MemSobolevLocOn 0 U (fun p ↦
        (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω [j] p /
          (Real.rpow (saddleDist p) (3 / 2) : ℂ))) ∧
      (∀ w : List (Fin 2), w.length = 1 ∨ w.length = 2 →
        MemSobolevLocOn 0 U (fun p ↦
          (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω w p)) := by
  obtain ⟨U, hU, hsep, hord⟩ := dd_log_ordinary_bulk hlam hω hs
  refine ⟨U, hU, hsep, fun j ↦ ?_, hord⟩
  apply memSobolevLocOn_of_locally
  intro p hp
  by_cases hc : p ∈ saddleSet
  · obtain ⟨ρ, hρ, hgrad⟩ := dd_log_saddle_gradient hlam hω hs p hc
    have ho : IsOpen (localDisk p ρ) := by
      apply isOpen_lt _ continuous_const
      unfold localRadius
      fun_prop
    refine ⟨localDisk p ρ, ho, ?_, hgrad j⟩
    simpa [localDisk, localRadius] using hρ
  · let W := U ∩ {q | 0 < saddleDist q}
    have hd : Continuous saddleDist := Metric.continuous_infDist_pt saddleSet
    have ho : IsOpen W := hU.inter (isOpen_lt continuous_const hd)
    have hpW : p ∈ W := ⟨hp, lt_of_le_of_ne Metric.infDist_nonneg
      (Ne.symm (mt saddleDist_eq_zero_iff.mp hc))⟩
    have hpow : Continuous (fun q ↦ Real.rpow (saddleDist q) (3 / 2)) :=
      hd.rpow_const (fun _ ↦ Or.inr (by norm_num))
    have hG : ContinuousOn (fun q ↦ (Real.rpow (saddleDist q) (3 / 2) : ℂ)⁻¹) W :=
      (Complex.continuous_ofReal.comp hpow).continuousOn.inv₀ (fun q hq ↦
        Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq.2 _).ne')
    have hl := ((hord [j] (Or.inl (by simp))).mono
      (show W ⊆ U from inter_subset_left)).zero_mul_continuousOn hG
    refine ⟨W, ho, hpW, ?_⟩
    simpa only [div_eq_mul_inv, mul_comm] using hl

end NoEmbeddedEigenvalues
