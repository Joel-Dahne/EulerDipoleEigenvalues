module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedTransportH1Inputs
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedTransportSecondMass

/-!
# Four-character assembly of ordinary weak quarter derivatives

Blueprint: `lem:weighted-transport-quarter-assembly`.

Restrict the original pair to a rotation-invariant neighbourhood. The supplied
weighted Cartesian gradient produces actual projected gradients there. Ordinary
scalar division uses the actual second norm, without the stronger logarithmic
numerator package. Each character's joint quarter derivatives are restricted to
one common collar before finite summation; pointwise Fourier recombination then
returns the original raw field. Physical-cell H¹ gluing is a separate interface.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Assemble actual weighted weak derivatives of all four raw recentered profiles
from the scalar second-norm and single-character reconstruction interfaces. -/
theorem weighted_transport_quarter_derivatives
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ A B : Fin 4 → ℝ × ℝ → ℂ,
      HasWeightedQuarterDerivatives b v A B := by
  obtain ⟨g, hg, hfg⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    hp.isOrbitUnion.1 hp.memSobolevOn.memSobolevLocOn
  obtain ⟨V, hV, _, hVU, hcellV, hRV⟩ :=
    exists_rotationInvariant_transport_neighbourhood hp.isOrbitUnion hb hcell
  have hpV := hp.mono hV hVU
  have hgV := hg.mono hVU
  have hfgV := ae_restrict_of_ae_restrict_of_subset hVU hfg
  have hDV (j : Fin 2) := (hD j).mono hVU
  have hchar (κ : ℂ) (hκ : κ ^ 4 = 1) :
      ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ A B : Fin 4 → ℝ × ℝ → ℂ,
        HasWeightedQuarterDerivatives b (quarterCharacterProjection κ v) A B := by
    have hpκ := hpV.quarterCharacterProjection hRV κ
    have hgκ := continuousOn_quarterCharacterProjection hgV hRV κ
    have hfgκ := quarterCharacterProjection_congr_ae hV.1.measurableSet hRV hfgV κ
    obtain ⟨E, hE⟩ := exists_weightedGradient_quarterCharacterProjection hV.1 hRV hDV hDf κ
    have hfκ := memLp_quarterCharacterProjection_div_saddleDist_pow hf κ
    have hvchar : HasQuarterCharacterOn κ cellSquare (quarterCharacterProjection κ v) :=
      Eventually.of_forall (quarterCharacterProjection_rotLift hκ v)
    have hfchar : HasQuarterCharacterOn κ cellSquare (quarterCharacterProjection κ f) :=
      Eventually.of_forall (quarterCharacterProjection_rotLift hκ f)
    obtain ⟨r, hr, _, hsecond⟩ := hpκ.weighted_numerator_second_norm hcellV hgκ hfgκ
      (fun j ↦ (hE j).1) hfκ (fun j ↦ (hE j).2)
    obtain ⟨s, hs, hsh, _, hscalar⟩ := hpκ.quarter_h1_scalar_data_of_second_norm hκ hcellV
      hgκ hfgκ (fun j ↦ (hE j).1) hfκ (fun j ↦ (hE j).2) hvchar hfchar hr (hsecond lam)
    obtain ⟨b, hb, hbs, A, B, hAB⟩ := hpκ.weighted_character_quarter_derivatives hκ hcellV
      hgκ hfgκ (fun j ↦ (hE j).1) hfκ (fun j ↦ (hE j).2) hvchar hfchar hs hsh hscalar
    exact ⟨b, hb, hbs.trans hsh, A, B, hAB⟩
  obtain ⟨r₁, hr₁, hr₁h, A₁, B₁, h₁⟩ := hchar 1 (by norm_num)
  obtain ⟨r₂, hr₂, _, A₂, B₂, h₂⟩ := hchar (-1) (by norm_num)
  obtain ⟨r₃, hr₃, _, A₃, B₃, h₃⟩ := hchar Complex.I (by norm_num)
  obtain ⟨r₄, hr₄, _, A₄, B₄, h₄⟩ := hchar (-Complex.I) (by
    calc (-Complex.I) ^ 4 = Complex.I ^ 4 := by ring
         _ = 1 := by norm_num)
  let b := min r₁ (min r₂ (min r₃ r₄))
  have hb : 0 < b := lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hr₄))
  have hb₁ : b ≤ r₁ := min_le_left _ _
  have hb₂ : b ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₃ : b ≤ r₃ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hb₄ : b ≤ r₄ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsum := ((((h₁.mono hb₁).add (h₂.mono hb₂)).add (h₃.mono hb₃)).add (h₄.mono hb₄))
  have he : quarterCharacterProjection 1 v + quarterCharacterProjection (-1) v +
      quarterCharacterProjection Complex.I v + quarterCharacterProjection (-Complex.I) v = v :=
    funext (quarterCharacterProjection_sum v)
  rw [he] at hsum
  exact ⟨b, hb, lt_of_le_of_lt hb₁ hr₁h, A₁ + A₂ + A₃ + A₄, B₁ + B₂ + B₃ + B₄, hsum⟩

end NoEmbeddedEigenvalues
