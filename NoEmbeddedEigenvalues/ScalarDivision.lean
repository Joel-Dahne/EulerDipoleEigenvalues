import NoEmbeddedEigenvalues.HardyAverage
import NoEmbeddedEigenvalues.IntervalH1
import NoEmbeddedEigenvalues.Period
import NoEmbeddedEigenvalues.DipoleFlow

/-!
# Scalar interfaces for phase-cell division

The interval Hardy statements are wrappers around the primitive averaging mechanism
in `HardyAverage.lean`. Endpoints always mean canonical H¹ traces. Local H² data use
specified first and second derivatives, and hence actual continuous numerator values
at interior resonances.

The phase-cell estimates export uniform constants on complete cells. This quantitative
interface, not merely qualitative unweighted division, is what logarithmic weighted
summation uses. All four quarter characters are allowed. Angular Hardy is not part
of these interfaces and is not required by the odd–odd quotient route.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Endpoint Hardy with an explicit integrability conclusion (`lem:hardy-endpoint`). -/
theorem HasIntervalH1.hardy_endpoint {η : ℝ} (hη : 0 < η) {F D : ℝ → ℂ}
    (hF : HasIntervalH1 0 η F D) (h0 : intervalH1Extension 0 η F D 0 = 0) :
    MemLp (fun x ↦ F x / (x : ℂ)) 2 (volume.restrict (Ioo 0 η)) ∧
      (∫ x in Ioo 0 η, ‖F x / (x : ℂ)‖ ^ 2) ≤
        4 * ∫ x in Ioo 0 η, ‖D x‖ ^ 2 := by
  sorry

/-- Second Hardy: H² division at an interior point or endpoint, with one universal
constant (`lem:hardy-second`). No value of the raw numerator at an endpoint is used. -/
theorem interval_h2_div_sub : ∃ K : ℝ, 0 < K ∧
    ∀ (a b x₀ : ℝ) (N N₁ N₂ : ℝ → ℂ), a < b → x₀ ∈ Icc a b →
      HasIntervalH2 a b N N₁ N₂ → intervalH1Extension a b N N₁ x₀ = 0 →
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 a b Q Q₁ ∧
        (∀ x ∈ Ioo a b, N x = ((x - x₀ : ℝ) : ℂ) * Q x) ∧
        (∫ x in Ioo a b, ‖Q₁ x‖ ^ 2) ≤ K * ∫ x in Ioo a b, ‖N₂ x‖ ^ 2 := by
  sorry

/-- Coarse period derivative bounds; smoothness and strict decrease are already in
`Period.lean` (`lem:period-derivative-bounds`). -/
theorem eighthPeriod_derivative_bounds : ∃ c C h₀ : ℝ,
    0 < c ∧ 0 < C ∧ 0 < h₀ ∧ h₀ < 1 ∧ ∀ h ∈ Ioo 0 h₀,
      c ≤ -h * deriv eighthPeriod h ∧ -h * deriv eighthPeriod h ≤ C ∧
      h ^ 2 * |deriv (deriv eighthPeriod) h| ≤ C := by
  sorry

/-- Quarter-orbit phase, including the sign of the real spectral parameter. -/
def quarterPhase (lam h : ℝ) : ℝ := 2 * lam * eighthPeriod h

/-- The actual divisor, not an abstract function with assumed simple zeros. -/
def quarterDivisor (lam : ℝ) (κ : ℂ) (h : ℝ) : ℂ :=
  κ - Complex.exp (Complex.I * (quarterPhase lam h : ℂ))

/-- Quarter-orbit numerator. Analytic uses supply the continuous forcing representative. -/
def quarterNumerator (lam : ℝ) (f : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ t in (-eighthPeriod h)..(eighthPeriod h),
    f (dipoleOrbit h t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))

/-- Raw quotient, used only off divisor zeros; extension across zeros is separate. -/
def quarterQuotient (lam : ℝ) (κ : ℂ) (f : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  quarterNumerator lam f h / quarterDivisor lam κ h

/-- A cell endpoint lies halfway between adjacent resonances, not at a divisor zero. -/
def IsPhaseCellEndpoint (lam : ℝ) (κ : ℂ) (h : ℝ) : Prop :=
  Complex.exp (Complex.I * (quarterPhase lam h : ℂ)) = -κ

/-- Local interval H¹ with a compatible specified derivative. -/
def HasIntervalH1Loc (a b : ℝ) (N N₁ : ℝ → ℂ) : Prop :=
  ∀ c d, a < c → c < d → d < b → HasIntervalH1 c d N N₁

/-- Local H² on an open interval with compatible specified derivatives. -/
def HasIntervalH2Loc (a b : ℝ) (N N₁ N₂ : ℝ → ℂ) : Prop :=
  ∀ c d, a < c → c < d → d < b → HasIntervalH2 c d N N₁ N₂

/-- Uniform complete-cell estimates (`lem:phase-cell-estimates`). The endpoints have
phase distance π from the central resonance. Constants are uniform over all cells,
numerators and four quarter characters; they may depend on lam. -/
theorem phase_cell_estimates {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 ∧
      ∀ (κ : ℂ), κ ^ 4 = 1 → ∀ (a z b : ℝ),
        0 < a → a < z → z < b → b < h₀ → quarterDivisor lam κ z = 0 →
        |quarterPhase lam a - quarterPhase lam z| = Real.pi →
        |quarterPhase lam b - quarterPhase lam z| = Real.pi →
        ∀ N N₁ N₂ : ℝ → ℂ, HasIntervalH2 a b N N₁ N₂ → N z = 0 →
          ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 a b Q Q₁ ∧
            (∀ h ∈ Ioo a b, quarterDivisor lam κ h * Q h = N h) ∧
            MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo a b)) ∧
            (∫ h in Ioo a b, ‖Q h / (h : ℂ)‖ ^ 2) ≤
              K * (∫ h in Ioo a b, ‖N₁ h‖ ^ 2) ∧
            (∫ h in Ioo a b, ‖Q₁ h‖ ^ 2) ≤
              K * (∫ h in Ioo a b, ‖N₁ h‖ ^ 2 + h ^ 2 * ‖N₂ h‖ ^ 2) := by
  sorry

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
