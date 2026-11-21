import NoEmbeddedEigenvalues.Transport.WeightedGains.SubcriticalNumerator
import NoEmbeddedEigenvalues.Transport.WeightedGains.PhaseCellSecondMass

/-!
# Scalar second mass for a subcritical transport character

Blueprint: `lem:subcritical-quotient-mass`.

The original continuous forcing and specified `Fin 2` weak gradient give
local H¹ numerator data and an actual L² first derivative. Resonant
cancellation and first-derivative second-mass division yield Q/h in L².
Physical reconstruction and recombination of characters are separate.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Subcritical forcing gives the scalar second mass for every fourth-root
character, retaining the original forcing and supplied first weak gradient. -/
theorem IsTransportPair.subcritical_quarterQuotient_memLp
    {lam δ : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hbU : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U) (hδ : δ < 1)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧ η < 1 / 2 ∧ IsPhaseCellEndpoint lam κ η ∧
      MemLp (fun h ↦ quarterQuotient lam κ g h / (h : ℂ)) 2
        (volume.restrict (Ioo 0 η)) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 η)), quarterDivisor lam κ h ≠ 0 := by
  let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
    | [j] => D j
    | _ => 0
  obtain ⟨K, h₀, _, hh₀, hh₀h, hN, _, hNL, _⟩ :=
    hp.subcritical_numerator_estimates_of_first_gradient hbU hcell hδ hg hfg hbound hD hw
  let b := min r h₀
  have hb : 0 < b := lt_min hr hh₀
  have hbr : b ≤ r := min_le_left _ _
  have hbh₀ : b ≤ h₀ := min_le_right _ _
  have hb1 : b < 1 := hbh₀.trans_lt (hh₀h.trans (by norm_num))
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 h₀ := Ioo_subset_Ioo le_rfl hbh₀
  have hAr : orbitAnnulus 0 b ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans_le hbr⟩
  have hA : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  have hzero := (numerator_zeros hκ hp hb hb1 hA hg hfg
    (ae_restrict_of_ae_restrict_of_subset hAr hvκ)
    (ae_restrict_of_ae_restrict_of_subset hAr hfκ)).2
  have hNb : HasIntervalH1Loc 0 b (quarterNumerator lam g)
      (quarterNumeratorDerivative lam g J) := fun a c ha hac hc ↦
    hN lam a c ha hac (hc.trans_le hbh₀)
  have hNlb : MemLp (quarterNumeratorDerivative lam g J) 2
      (volume.restrict (Ioo 0 b)) :=
    (hNL lam).mono_measure (Measure.restrict_mono_set _ hsub)
  obtain ⟨η, hη, hηb, hηend, hQ, hne⟩ :=
    phase_cell_second_mass_division hp.ne_zero hκ hb hNb hzero hNlb
  exact ⟨η, hη, hηb.trans_le hbr, (hηb.trans_le hbh₀).trans hh₀h, hηend, hQ, hne⟩

end NoEmbeddedEigenvalues
