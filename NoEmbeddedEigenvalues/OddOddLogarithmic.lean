import NoEmbeddedEigenvalues.OddOddSaddle
import NoEmbeddedEigenvalues.WeightedNumerators
import NoEmbeddedEigenvalues.StreamJet
import NoEmbeddedEigenvalues.LogarithmicWeights

/-!
# Odd–odd logarithmic forcing and numerator interfaces

The canonical Fourier stream jet fixes the derivative data shared by bulk,
ray and orbit bounds. Periodic lifts have local weighted norms on an open
neighbourhood of the whole lifted separatrix, not a global finite plane norm.
The ray estimates use a bounded radial interval and canonical gradient traces.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Logarithmic bulk and endpoint-ray forcing estimates (`lem:dd-log-forcing`). -/
theorem dd_log_forcing {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      (∀ j : Fin 2, MemSobolevLocOn 0 U (fun p ↦
        (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω [j] p /
          (Real.rpow (saddleDist p) (3 / 2) : ℂ))) ∧
      (∀ w : List (Fin 2), w.length = 1 ∨ w.length = 2 →
        MemSobolevLocOn 0 U (fun p ↦
          (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω w p)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ (k : Fin 4) (side : Bool),
        rotatedQuarterEndpointRay k side '' Icc 0 ρ ⊆ U ∧
        MemLp (fun (r : ℝ) ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
          contStream ω (rotatedQuarterEndpointRay k side r) / (Real.rpow r (3 / 2) : ℂ)) 2
          (volume.restrict (Ioo 0 ρ)) ∧
        ∃ T : Fin 2 → ℝ → ℂ, ∀ j,
          HasQuarterRayTrace U ρ k side (streamJet2 ω [j]) (T j) ∧
          MemLp (fun (r : ℝ) ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * T j r /
            (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 ρ)) := by
  sorry

/-- Logarithmic numerator estimates with the same canonical jet and compatible
unweighted derivative/trace data (`lem:dd-log-numerators`). -/
theorem dd_log_numerators {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧
      ∃ d : WeightedQuarterNumeratorData lam cellNeighbourhood (contStream ω) (streamJet2 ω) h₀,
        IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 (3 / 2) (streamJet2 ω) h)
          (Ioo 0 h₀) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.first h) 2
          (volume.restrict (Ioo 0 h₀)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.halfFirst h) 2
          (volume.restrict (Ioo 0 h₀)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * (h : ℂ) * d.second h) 2
          (volume.restrict (Ioo 0 h₀)) := by
  sorry

end NoEmbeddedEigenvalues
