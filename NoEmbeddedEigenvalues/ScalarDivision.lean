import NoEmbeddedEigenvalues.PhaseCellEstimates

/-!
# Scalar interfaces for phase-cell division

Quarter scalars are defined in `QuarterScalars.lean`; the complete-cell estimates
are proved in `PhaseCellEstimates.lean`.

Endpoint Hardy uses the primitive averaging mechanism in `HardyAverage.lean`;
second-order division uses H¹ segment averaging in `IntervalSegmentAverage.lean`.
Endpoints always mean canonical H¹ traces. Local H² data use specified first and
second derivatives, and hence actual continuous numerator values at interior resonances.

The phase-cell estimates export uniform constants on complete cells. This quantitative
interface, not merely qualitative unweighted division, is what logarithmic weighted
summation uses. All four quarter characters are allowed. Angular Hardy is not part
of these interfaces and is not required by the odd–odd quotient route.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Global division after decreasing the upper endpoint to a full-cell boundary
(`lem:phase-cell-division`). The quotient extends continuously through resonances,
and its zero-endpoint value is the canonical H¹ trace. -/
theorem phase_cell_division {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) {N N₁ N₂ : ℝ → ℂ}
    (hN : HasIntervalH2Loc 0 h₀ N N₁ N₂)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hN₁ : MemLp N₁ 2 (volume.restrict (Ioo 0 h₀)))
    (hN₂ : MemLp (fun (h : ℝ) ↦ (h : ℂ) * N₂ h) 2 (volume.restrict (Ioo 0 h₀))) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam κ h₁ ∧
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
        (∀ h ∈ Ioo 0 h₁, quarterDivisor lam κ h * Q h = N h) ∧
        MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 h₁)) ∧
        intervalH1Extension 0 h₁ Q Q₁ 0 = 0 := by
  sorry

end NoEmbeddedEigenvalues
