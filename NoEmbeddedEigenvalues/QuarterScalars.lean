import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.IntervalH1

/-!
# Scalar data for quarter-orbit division

The signed phase, actual complex divisor, orbit numerator, and compatible local
interval Sobolev data. All four quarter characters use the same definitions.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

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

end NoEmbeddedEigenvalues
