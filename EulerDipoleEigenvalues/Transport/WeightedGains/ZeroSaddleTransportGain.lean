module

public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterTransportProjections
public import EulerDipoleEigenvalues.Transport.WeightedGains.ZeroSaddleCellMass

/-!
# First transport gain with zero saddle values

Blueprint: `lem:transport-first-gain-zero`.

Restrict to a rotation-invariant neighbourhood and project both original raw
fields into the four complex quarter characters. Project the supplied continuous
forcing by the same formula. Each character has a full physical-cell norm, so
pointwise recombination needs neither common collar cutoffs nor endpoint values.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- The first gain when the continuous forcing vanishes at the four cell saddles
(`lem:transport-first-gain-zero`). No pointwise representative of v is used. -/
theorem transport_first_gain_zero {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) {g : ℝ × ℝ → ℂ}
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hzero : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0) :
    MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨V, hV, _, hVU, hcellV, hRV⟩ :=
    exists_rotationInvariant_transport_neighbourhood hp.isOrbitUnion hb hcell
  have hpV := hp.mono hV hVU
  have hgV := hg.mono hVU
  have hfgV := ae_restrict_of_ae_restrict_of_subset hVU hfg
  have hchar (κ : ℂ) (hκ : κ ^ 4 = 1) :
      MemLp (fun p ↦ quarterCharacterProjection κ v p / (saddleDist p : ℂ)) 2
        (volume.restrict cellSquare) := by
    apply (hpV.quarterCharacterProjection hRV κ).zero_saddle_character_memLp
      hκ hcellV (continuousOn_quarterCharacterProjection hgV hRV κ)
      (quarterCharacterProjection_congr_ae hV.1.measurableSet hRV hfgV κ)
      (quarterCharacterProjection_zero_at_saddles hzero κ)
      (r := 1 / 2) (by norm_num)
    · exact Eventually.of_forall (quarterCharacterProjection_rotLift hκ v)
    · exact Eventually.of_forall (quarterCharacterProjection_rotLift hκ f)
  have hsum := (((hchar 1 (by norm_num)).add (hchar (-1) (by norm_num))).add
    (hchar Complex.I (by norm_num))).add (hchar (-Complex.I) (by
      calc (-Complex.I) ^ 4 = Complex.I ^ 4 := by ring
           _ = 1 := by norm_num))
  apply hsum.ae_eq
  exact Eventually.of_forall fun p ↦ by
    simp only [Pi.add_apply, ← add_div, quarterCharacterProjection_sum]

end EulerDipoleEigenvalues
