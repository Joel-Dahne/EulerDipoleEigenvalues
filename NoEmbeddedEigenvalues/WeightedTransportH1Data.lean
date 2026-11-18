import NoEmbeddedEigenvalues.IntervalH1
import NoEmbeddedEigenvalues.QuarterCoordinates
import NoEmbeddedEigenvalues.OrbitNumerators

/-!
# Scalar and joint weak data for weighted quarter reconstruction

Blueprint: `def:quarter-h1-scalar-data`, `def:weighted-quarter-derivative-data`,
`lem:weighted-quarter-data-algebra`.

The quotient trace is canonical. The planar fields are derivatives of the same
raw profiles, with coordinate-area measure and physical-distance weights.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Ordinary scalar division data, without the logarithmic quantitative bundle. -/
def HasQuarterH1ScalarData (lam : ℝ) (κ : ℂ) (g : ℝ × ℝ → ℂ) (b : ℝ) : Prop :=
  ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 b Q Q₁ ∧
    (∀ h ∈ Ioo 0 b, quarterDivisor lam κ h * Q h = quarterNumerator lam g h) ∧
    MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 b)) ∧
    intervalH1Extension 0 b Q Q₁ 0 = 0 ∧
    HasIntervalH1 0 b (quarterHalfNumerator lam g) (deriv (quarterHalfNumerator lam g))

/-- Joint weak derivatives of the same raw field on all four recentered quarters. -/
def HasWeightedQuarterDerivatives (b : ℝ) (v : ℝ × ℝ → ℂ)
    (A B : Fin 4 → ℝ × ℝ → ℂ) : Prop :=
  ∀ k, HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ v (recenteredQuarterMap k q)) (A k) ∧
    HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ v (recenteredQuarterMap k q)) (B k) ∧
    MemLp (fun q ↦ (saddleDist (recenteredQuarterMap k q) : ℂ) * A k q) 2
      (volume.restrict (quarterOrbitStrip b)) ∧
    MemLp (fun q ↦ B k q / (saddleDist (recenteredQuarterMap k q) : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b))

/-- Restriction keeps the same joint fields and their distance weights. -/
theorem HasWeightedQuarterDerivatives.mono {b c : ℝ} {v : ℝ × ℝ → ℂ}
    {A B : Fin 4 → ℝ × ℝ → ℂ} (h : HasWeightedQuarterDerivatives b v A B)
    (hcb : c ≤ b) : HasWeightedQuarterDerivatives c v A B := by
  have hs : quarterOrbitStrip c ⊆ quarterOrbitStrip b :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans_le hcb, hq.2.2⟩
  exact fun k ↦ ⟨(h k).1.mono hs, (h k).2.1.mono hs,
    (h k).2.2.1.mono_measure (Measure.restrict_mono_set _ hs),
    (h k).2.2.2.mono_measure (Measure.restrict_mono_set _ hs)⟩

/-- Finite sums preserve actual weak derivatives and both genuine L² norms. -/
theorem HasWeightedQuarterDerivatives.add {b : ℝ} {v w : ℝ × ℝ → ℂ}
    {A B C E : Fin 4 → ℝ × ℝ → ℂ}
    (h : HasWeightedQuarterDerivatives b v A B)
    (h' : HasWeightedQuarterDerivatives b w C E) :
    HasWeightedQuarterDerivatives b (v + w) (A + C) (B + E) := by
  intro k
  refine ⟨(h k).1.add (h' k).1, (h k).2.1.add (h' k).2.1, ?_, ?_⟩
  · apply ((h k).2.2.1.add (h' k).2.2.1).ae_eq
    exact Eventually.of_forall fun q ↦ by
      dsimp only [Pi.add_apply]
      ring
  · apply ((h k).2.2.2.add (h' k).2.2.2).ae_eq
    exact Eventually.of_forall fun q ↦ (add_div _ _ _).symm

end NoEmbeddedEigenvalues
