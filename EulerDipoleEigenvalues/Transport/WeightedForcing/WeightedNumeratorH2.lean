module

public import EulerDipoleEigenvalues.Transport.WeightedGains.OrbitNumeratorH2
public import EulerDipoleEigenvalues.Transport.WeightedForcing.WeightedNumeratorH1
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalContinuousRepresentative

/-!
# Weighted first data with local numerator H²

Blueprint: `lem:weighted-numerator-local-h2`.

The original weighted inputs give a single all-frequency collar with global
first-order data and local H² for the full numerator. Its ordinary derivative
agrees a.e. with the existing supplied-gradient first-derivative candidate;
the half numerator keeps its specified candidate unchanged.
No global hN″ norm or second moving-endpoint formula is asserted.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- The original forcing and specified Cartesian first gradient give local
numerator H² on the same collar as all global first-order full/half data. -/
theorem IsTransportPair.weighted_numerator_local_h2
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
      HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
        (deriv (deriv (quarterNumerator μ g))) ∧
      HasIntervalH1 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g)) ∧
      HasIntervalH1 0 h₀ (quarterHalfNumerator μ g) (quarterHalfNumeratorDerivative μ g J) ∧
      quarterNumeratorDerivative μ g J =ᵐ[volume.restrict (Ioo 0 h₀)]
        deriv (quarterNumerator μ g) := by
  obtain ⟨h₀, hh₀, hh₀h, hBoth⟩ := hp.weighted_numerators_h1 hcell hg hfg hD hf hDf
  have hA : orbitAnnulus 0 h₀ ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  refine ⟨h₀, hh₀, hh₀h, fun μ ↦ ?_⟩
  refine ⟨hp.quarterNumerator_h2Loc hg hfg (by linarith) hA μ,
    (hBoth μ).1.with_deriv, (hBoth μ).2, ?_⟩
  filter_upwards [ae_restrict_of_ae (hBoth μ).1.hasDerivAt_ae,
    ae_restrict_mem measurableSet_Ioo] with h hh hhI
  exact (hh hhI).deriv.symm

/-- No continuous forcing representative is an additional premise: the
original transport pair supplies one, with the same specified weighted gradient. -/
theorem IsTransportPair.exists_weighted_numerator_local_h2
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ g : ℝ × ℝ → ℂ, ContinuousOn g U ∧ f =ᵐ[volume.restrict U] g ∧
      let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
        | [j] => D j
        | _ => 0
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
        HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
          (deriv (deriv (quarterNumerator μ g))) ∧
        HasIntervalH1 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g)) ∧
        HasIntervalH1 0 h₀ (quarterHalfNumerator μ g) (quarterHalfNumeratorDerivative μ g J) ∧
        quarterNumeratorDerivative μ g J =ᵐ[volume.restrict (Ioo 0 h₀)]
          deriv (quarterNumerator μ g) := by
  obtain ⟨g, hg, hfg⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    hp.isOrbitUnion.1 hp.memSobolevOn.memSobolevLocOn
  exact ⟨g, hg, hfg, hp.weighted_numerator_local_h2 hcell hg hfg hD hf hDf⟩

end EulerDipoleEigenvalues
