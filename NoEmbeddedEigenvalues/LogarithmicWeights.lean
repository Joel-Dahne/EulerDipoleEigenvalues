import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.ScalarDivision
import NoEmbeddedEigenvalues.OrbitNumerators

/-!
# Logarithmic multipliers and scalar phase division

The level weight is only used for 0 < h < 1. Its lift is assigned value one
on the separatrix. The rectangle weight's arbitrary axis values are harmless.
Weighted integrability is explicit; phase division returns an H¹ extension.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

def logLevelWeight (h : ℝ) : ℝ := 1 + Real.log (1 / h)

def torusDipoleLogWeight (p : Torus) : ℝ :=
  if Ψ p = 0 then 1 else logLevelWeight (|Ψ p| / 2)

def dipoleLogWeight (p : ℝ × ℝ) : ℝ :=
  if dipoleLift p = 0 then 1 else logLevelWeight (|dipoleLift p| / 2)

def logRadiusWeight (r : ℝ) : ℝ := 1 + |Real.log r|

def logRectangleWeight (p : ℝ × ℝ) : ℝ :=
  1 + abs (Real.log (abs p.1)) + abs (Real.log (abs p.2))

/-- Coordinate slicing supplies the logarithmic multiplier, without a finite-p
embedding (`lem:log-multiplier-rectangle`). -/
theorem log_multiplier_rectangle {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      let Q := Ioo (-ρ) ρ ×ˢ Ioo (-ρ) ρ
      MemSobolevOn 1 Q F → HasWeakJetOn 1 Q F D →
      MemLp (fun p ↦ (Real.sqrt (logRectangleWeight p) : ℂ) * F p) 2
        (volume.restrict Q) ∧
      (∫ p in Q, logRectangleWeight p * ‖F p‖ ^ 2) ≤ K * weakJetEnergy 1 Q D := by
  sorry

/-- Uniform complete-cell estimates transfer to the logarithmic measure
(`lem:log-phase-cell-division`), with no differentiated logarithm. -/
theorem log_phase_cell_division {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) {N N₁ N₂ : ℝ → ℂ}
    (hN : HasIntervalH2Loc 0 h₀ N N₁ N₂)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hN₁ : MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * N₁ h) 2
      (volume.restrict (Ioo 0 h₀)))
    (hN₂ : MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * (h : ℂ) * N₂ h) 2
      (volume.restrict (Ioo 0 h₀))) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam κ h₁ ∧
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
        (∀ h ∈ Ioo 0 h₁, quarterDivisor lam κ h * Q h = N h) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ)) 2
          (volume.restrict (Ioo 0 h₁)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h) 2
          (volume.restrict (Ioo 0 h₁)) ∧
        intervalH1Extension 0 h₁ Q Q₁ 0 = 0 := by
  sorry

end NoEmbeddedEigenvalues
