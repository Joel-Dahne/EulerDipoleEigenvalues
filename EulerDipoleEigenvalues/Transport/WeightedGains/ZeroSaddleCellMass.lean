module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterCellMass
public import EulerDipoleEigenvalues.Transport.WeightedGains.ZeroSaddleReconstruction

/-!
# Zero-saddle first mass for a single quarter character

Blueprint: `lem:zero-saddle-character-mass`.

The base-quarter bound becomes a physical-area bound by constant-Jacobian
transport and a finite rotated cover. Character identities are used only on
the smaller collar where they are supplied. The original L² norm controls
the interior complement, since the stream level bounds saddle distance below.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- A fourth-root character component of the original transport pair has the
first weighted mass gain on the entire physical cell. -/
theorem IsTransportPair.zero_saddle_character_memLp
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0)
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨b, hb, hbr, hbh, hq⟩ := hp.zero_saddle_quarter_memLp
    hκ hcell hg hfg hz hr hvκ hfκ
  have hb1 : b < 1 := hbh.trans (by norm_num)
  have hκ0 : κ ≠ 0 := by
    intro hz
    simp [hz] at hκ
  have hsub : cellSeparatrixStrip (2 * b) ⊆ orbitAnnulus 0 r := by
    rw [cellSeparatrixStrip_eq_orbitAnnulus hb1.le]
    exact fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.trans hbr⟩
  have hchar : HasQuarterCharacterOn κ (cellSeparatrixStrip (2 * b))
      (fun p ↦ v p / (saddleDist p : ℂ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvκ] with p hp
    rw [saddleDist_rotLift, hp, mul_div_assoc]
  exact memLp_div_saddleDist_of_cell_collar hb
    (hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
    (memLp_cell_collar_of_quarter_character hb1.le hκ0 hchar hq)

end EulerDipoleEigenvalues
