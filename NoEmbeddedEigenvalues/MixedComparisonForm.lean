import NoEmbeddedEigenvalues.MixedComparison
import NoEmbeddedEigenvalues.WeightedTraces

/-!
# Mixed second-order comparison forms

Everything in this file uses diagonal coordinates and Lebesgue measure `da db`.
The boundary inputs are transverse Sobolev traces, not evaluations of an
arbitrary almost-everywhere representative.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory ComplexConjugate
open scoped ContDiff

/-- The Robin side of the quarter form uses tangential coordinate `a`. -/
def mixedQuarterForm (z za zb : ℝ × ℝ → ℂ) (top : ℝ → ℂ) : ℝ :=
  (∫ q in mixedQuarterCell, mixedComparisonDiagonal q * (‖za q‖ ^ 2 + ‖zb q‖ ^ 2) +
    2 * mixedComparisonOffDiagonal q * (za q * conj (zb q)).re +
    mixedComparisonPotential q * ‖z q‖ ^ 2) +
  ∫ a in Ioo (0 : ℝ) (Real.pi / 2), Real.cos a * ‖top a‖ ^ 2

/-- Finite H¹ data on the quarter, including the canonical trace on its Robin side. -/
structure MixedQuarterFormDomain (z za zb : ℝ × ℝ → ℂ) (top : ℝ → ℂ) : Prop where
  h1 : MemSobolevOn 1 mixedQuarterCell z
  weakA : HasWeakPartialOn mixedQuarterCell 0 z za
  weakB : HasWeakPartialOn mixedQuarterCell 1 z zb
  topTrace : HasTransverseH1Trace 0 (Real.pi / 2) 0 (Real.pi / 2) (Real.pi / 2) id z top

/-- The vanishing trace is on `a=0` for odd-in-a and on `b=0` for odd-in-b. -/
def MixedQuarterZeroTrace (oddA : Bool) (z : ℝ × ℝ → ℂ) : Prop :=
  HasTransverseH1Trace 0 (Real.pi / 2) 0 (Real.pi / 2) 0
    (axisTraceChart (if oddA then 0 else 1)) z (fun _ ↦ 0)

/-- The logarithmic multiplier hypotheses in `(h,k)`. Smoothness includes the
regular Robin edge `k=0, h>0`, but does not prescribe derivatives at the corner. -/
structure MixedRobinMultiplier (ρ : ℝ × ℝ → ℝ) : Prop where
  smooth : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ U ∧
    ContDiffOn ℝ ∞ ρ U
  continuous : ContinuousOn ρ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  bounded : ∃ m M : ℝ, 0 < m ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    m ≤ ρ q ∧ ρ q ≤ M
  derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |partialX ρ q| + |partialY ρ q| ≤ C * (1 + |Real.log q.1|)

/-- The actual interior comparison built from a multiplier. -/
def mixedRobinComparison (oddA : Bool) (ρ : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (if oddA then Real.sin q.1 else Real.sin q.2) * ρ (Real.cos q.1, Real.cos q.2)

/-- The logarithmic Robin comparison lemma for either odd axis. -/
theorem mixed_robin_comparison (oddA : Bool) {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    (hrobin : ∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ mixedRobinNumerator oddA ρ h)
    {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ}
    (hz : MixedQuarterFormDomain z za zb top) (hzero : MixedQuarterZeroTrace oddA z) :
    c * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      mixedQuarterForm z za zb top := by
  sorry

end NoEmbeddedEigenvalues
