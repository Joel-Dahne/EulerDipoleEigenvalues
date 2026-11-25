module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterCellMass
public import EulerDipoleEigenvalues.Transport.WeightedGains.SubcriticalReconstruction
public import EulerDipoleEigenvalues.Transport.WeightedGains.FirstTransportGain

/-!
# Second physical-cell mass for a supplied subcritical quarter character

Blueprint: `lem:subcritical-character-mass`.

The reverse quarter chart and a finite rotated cover give second mass on a
full physical collar. Apply the first-mass interior-complement lemma to v/d,
whose genuine cell L² norm is supplied by First transport gain. This gives
v/d² on the entire cell, without assigning raw endpoint values or selecting
one collar shared by different characters.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- The original pair and specified weighted first gradient give second mass
on the full physical cell for any supplied fourth-root quarter character. -/
theorem IsTransportPair.subcritical_character_memLp
    {lam δ : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hbU : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    MemLp (fun p ↦ v p / ((saddleDist p) ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
  obtain ⟨b, hb, hbr, hbh, hq⟩ := hp.subcritical_quarter_memLp
    hκ hbU hcell hδ0 hδ1 hg hfg hbound hD hw hr hvκ hfκ
  have hb1 : b < 1 := hbh.trans (by norm_num)
  have hκ0 : κ ≠ 0 := by
    intro hz
    simp [hz] at hκ
  have hsub : cellSeparatrixStrip (2 * b) ⊆ orbitAnnulus 0 r := by
    rw [cellSeparatrixStrip_eq_orbitAnnulus hb1.le]
    exact fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.trans hbr⟩
  have hchar : HasQuarterCharacterOn κ (cellSeparatrixStrip (2 * b))
      (fun p ↦ v p / ((saddleDist p) ^ 2 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvκ] with p hp
    rw [saddleDist_rotLift, hp, mul_div_assoc]
  have hColl := memLp_cell_collar_of_quarter_character hb1.le hκ0 hchar hq
  have he (p : ℝ × ℝ) : (v p / (saddleDist p : ℂ)) / (saddleDist p : ℂ) =
      v p / ((saddleDist p) ^ 2 : ℂ) := by rw [div_div, pow_two]
  have hWhole := memLp_div_saddleDist_of_cell_collar hb (transport_first_gain hp hbU hcell)
    (hColl.ae_eq (Eventually.of_forall fun p ↦ (he p).symm))
  exact hWhole.ae_eq (Eventually.of_forall he)

end EulerDipoleEigenvalues
