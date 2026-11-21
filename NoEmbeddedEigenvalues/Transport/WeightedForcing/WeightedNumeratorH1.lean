module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedFirstNumerator
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1LocalToGlobal

/-!
# Global first-order regularity of the weighted numerators

Blueprint: `lem:weighted-numerators-h1`.

Local interval H¹ and the actual global first-derivative norm give global H¹
on a bounded collar. This applies to both the full and half numerators on one
collar for every real frequency. The endpoint traces are canonical extensions;
no agreement with raw endpoint assignments or zero trace is asserted.
This is first-order regularity, not local H² or a second-derivative estimate.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Original weighted forcing and its supplied gradient give both numerator
values and their specified first derivatives actual global interval H¹ data. -/
theorem IsTransportPair.weighted_numerators_h1
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
      | [j] => D j
      | _ => 0
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
      HasIntervalH1 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J) ∧
      HasIntervalH1 0 h₀ (quarterHalfNumerator μ g) (quarterHalfNumeratorDerivative μ g J) := by
  obtain ⟨h₀, hh₀, hh₀h, hBoth⟩ :=
    hp.weighted_numerator_first_derivatives hcell hg hfg hD hf hDf
  have hglobal {F E : ℝ → ℂ} (hloc : HasIntervalH1Loc 0 h₀ F E)
      (hE : MemLp E 2 (volume.restrict (Ioo 0 h₀))) : HasIntervalH1 0 h₀ F E := by
    apply hasIntervalH1_of_local_derivative hh₀ hE
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    refine ⟨x / 2, (x + h₀) / 2, by linarith, by linarith,
      ⟨by linarith, by linarith⟩, hloc _ _ (by linarith) (by linarith) (by linarith)⟩
  exact ⟨h₀, hh₀, hh₀h, fun μ ↦
    ⟨hglobal (hBoth μ).1.1 (hBoth μ).1.2, hglobal (hBoth μ).2.1 (hBoth μ).2.2⟩⟩

end NoEmbeddedEigenvalues
