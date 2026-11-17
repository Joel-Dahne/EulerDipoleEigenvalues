import NoEmbeddedEigenvalues.WeightedFirstNumerator
import NoEmbeddedEigenvalues.WeightedTransportMass
import NoEmbeddedEigenvalues.WeightedQuarterProjections
import NoEmbeddedEigenvalues.LocalContinuousRepresentative

/-!
# Second transport mass from the original weighted L² forcing

Blueprint: `lem:weighted-transport-second-mass`.

Produce first numerator data for each projected original forcing and supplied
weak gradient, then use the raw-profile mass assembly. This is the mass
conclusion of weighted transport H¹, independent of second numerator data,
gradient-ray traces and the spatial weak-gradient/gluing conclusion.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Preserve a supplied continuous forcing representative throughout the
weighted first-numerator construction and four-character mass assembly. -/
theorem weighted_transport_second_mass_with_rep
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨V, hV, _, hVU, hcellV, hRV⟩ :=
    exists_rotationInvariant_transport_neighbourhood hp.isOrbitUnion hb hcell
  have hpV := hp.mono hV hVU
  have hgV := hg.mono hVU
  have hfgV := ae_restrict_of_ae_restrict_of_subset hVU hfg
  have hDV (j : Fin 2) := (hD j).mono hVU
  apply weighted_transport_mass_of_first_numerators hp hb hcell hg hfg hf
  intro κ _
  obtain ⟨E, hE⟩ := exists_weightedGradient_quarterCharacterProjection hV.1 hRV hDV hDf κ
  obtain ⟨r, hr, _, hN⟩ :=
    (hpV.quarterCharacterProjection hRV κ).weighted_first_numerator_estimates hcellV
      (continuousOn_quarterCharacterProjection hgV hRV κ)
      (quarterCharacterProjection_congr_ae hV.1.measurableSet hRV hfgV κ)
      (fun j ↦ (hE j).1) (memLp_quarterCharacterProjection_div_saddleDist_pow hf κ)
      (fun j ↦ (hE j).2)
  exact ⟨r, hr, _, (hN lam).1, (hN lam).2⟩

/-- The mass component of weighted transport H¹, with exactly its original
weighted forcing and supplied first-gradient hypotheses. No scalar-data,
pointwise growth or trace hypothesis is added. -/
theorem weighted_transport_second_mass {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨g, hg, hfg⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    hp.isOrbitUnion.1 hp.memSobolevOn.memSobolevLocOn
  exact weighted_transport_second_mass_with_rep hp hb hcell hg hfg hD hf hDf

end NoEmbeddedEigenvalues
