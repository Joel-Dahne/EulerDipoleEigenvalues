import NoEmbeddedEigenvalues.Regularity.OddOddQuarterTime
import NoEmbeddedEigenvalues.QuarterInverseFrame
import NoEmbeddedEigenvalues.WeakDerivativeGluing

/-!
# Specified separatrix gradient and inverse-frame data

Blueprint: `lem:dd-separatrix-weak-gradient`, `lem:dd-base-quarter-inverse-frame`.

The ordinary separatrix H¹ input supplies one weak gradient on the whole
neighbourhood. Independently, the strong base-quarter estimates construct
weighted L² Cartesian candidates. Equating these objects requires the weak
coordinate chain rule; finiteness of the candidates alone does not give it.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Extract a single specified weak gradient from ordinary local H¹ regularity. -/
theorem dd_separatrix_weak_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        Measurable (D j) ∧ HasWeakPartialOn U j (liftL2 ω) (D j) ∧
          MemSobolevLocOn 0 U (D j) := by
  obtain ⟨U, hU, hsep, hH, _, _⟩ := dd_separatrix_h1 hlam hω hs
  obtain ⟨D, hD⟩ := hH.exists_measurable_weakGradient hU
  exact ⟨U, hU, hsep, D, hD⟩

/-- Retain the actual weak quarter derivatives on a common smaller strip and
construct the two weighted Cartesian inverse-frame candidates. -/
theorem dd_base_quarter_inverse_frame {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ H T : ℝ × ℝ → ℂ,
      HasWeakPartialOn (quarterOrbitStrip b) 0
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) H ∧
      HasWeakPartialOn (quarterOrbitStrip b) 1
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) T ∧
      MemLp H 2 (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) ∧
      ∀ j : Fin 2, MemLp (fun q ↦ quarterInverseGradient H T j q /
        (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
          (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨h₀, hh₀, hhhalf, H, T, hH, hT, hHl, hTl⟩ :=
    dd_base_quarter_weighted_derivatives hlam hω hs hκ
  obtain ⟨δ, hδ, _, hInv⟩ := quarterInverseGradient_memLp
  let b := min h₀ δ
  have hb : 0 < b := lt_min hh₀ hδ
  have hbh : b ≤ h₀ := min_le_left _ _
  have hbδ : b ≤ δ := min_le_right _ _
  have hsub : quarterOrbitStrip b ⊆ quarterOrbitStrip h₀ :=
    fun _ hq ↦ ⟨hq.1, hq.2.1.trans_le hbh, hq.2.2⟩
  have hHl' := hHl.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hTl' := hTl.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact ⟨b, hb, hbh.trans_lt hhhalf, H, T, hH.mono hsub, hT.mono hsub,
    hHl', hTl', hInv b hbδ H T hHl' hTl'⟩

end NoEmbeddedEigenvalues
