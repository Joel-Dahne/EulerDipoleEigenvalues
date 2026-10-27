import NoEmbeddedEigenvalues.QuarterCoordinates
import NoEmbeddedEigenvalues.ScalarDivision
import NoEmbeddedEigenvalues.ResonantVanishing

/-!
# Quarter-orbit endpoints and resonant zeros

Both unknown and forcing have the same quarter character. All four fourth roots
of unity are allowed. Endpoint functions are separate locally L² functions of the
level; they are values of orbitwise ACL representatives, not raw spatial traces.
The numerator uses continuous forcing, so its values at resonances are canonical.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A.e. quarter-rotation character on a specified region. -/
def HasQuarterCharacterOn (κ : ℂ) (A : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℂ) : Prop :=
  ∀ᵐ p ∂(volume.restrict A), F (rotLift p) = κ * F p

/-- Midpoint half numerator, with the same phase convention as the full numerator. -/
def quarterHalfNumerator (lam : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ t in (-eighthPeriod h)..0,
    g (dipoleOrbit h t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))

/-- Endpoint formula with locally L² endpoint functions and orbitwise ACL witnesses
(`lem:quarter-endpoint-formula`). No joint choice of raw orbit values is required. -/
theorem quarter_endpoint_formula {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) f) :
    ∃ Eminus Eplus : ℝ → ℂ,
      (∀ a b, 0 < a → a < b → b < h₀ →
        MemLp Eminus 2 (volume.restrict (Ioo a b)) ∧
        MemLp Eplus 2 (volume.restrict (Ioo a b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∃ Z : ℝ → ℂ,
        (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
        Function.Periodic Z (orbitPeriod h) ∧
        (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
        (∀ᵐ t, HasDerivAt Z
          (Complex.I * ((lam : ℂ) * Z t + g (dipoleOrbit h t))) t) ∧
        Z (-eighthPeriod h) = Eminus h ∧ Z (eighthPeriod h) = Eplus h ∧
        Eplus h = κ * Eminus h ∧
        quarterDivisor lam κ h * Eminus h =
          Complex.I * Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) *
            quarterNumerator lam g h ∧
        (quarterDivisor lam κ h ≠ 0 → ‖Eminus h‖ = ‖quarterQuotient lam κ g h‖) := by
  sorry

/-- Canonical local H¹ numerator and resonant cancellation (`lem:numerator-zeros`). -/
theorem numerator_zeros {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) f) :
    (∃ N₁ : ℝ → ℂ, HasIntervalH1Loc 0 h₀ (quarterNumerator lam g) N₁) ∧
      ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → quarterNumerator lam g h = 0 := by
  sorry

/-- Simple resonances, geometric ratio bounds and uniform full-cell comparisons.
The cutoff can be chosen arbitrarily small; no exact geometric progression is claimed. -/
theorem quarter_divisor_geometry {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ K qlower qupper : ℝ, 0 < ρ ∧ ρ < η ∧ ρ < 1 ∧ 1 < K ∧
      0 < qlower ∧ qlower ≤ qupper ∧ qupper < 1 ∧
      (∀ h ∈ Ioo 0 ρ, quarterDivisor lam κ h = 0 → deriv (quarterDivisor lam κ) h ≠ 0) ∧
      (∃ hs : ℕ → ℝ,
        (∀ n, hs n ∈ Ioo 0 ρ ∧ quarterDivisor lam κ (hs n) = 0 ∧
          qlower ≤ hs (n + 1) / hs n ∧ hs (n + 1) / hs n ≤ qupper) ∧
        (∀ h ∈ Ioo 0 ρ, quarterDivisor lam κ h = 0 ↔ ∃ n, h = hs n)) ∧
      (∀ z ∈ Ioo 0 ρ, quarterDivisor lam κ z = 0 → ∀ h ∈ Ioo 0 ρ,
        |quarterPhase lam h - quarterPhase lam z| ≤ Real.pi →
          z / K ≤ h ∧ h ≤ K * z ∧ |h - z| / (K * z) ≤ ‖quarterDivisor lam κ h‖) := by
  sorry

end NoEmbeddedEigenvalues
