module

public import EulerDipoleEigenvalues.Transport.WeightedGains.PhaseCellMassDivision
public import EulerDipoleEigenvalues.Transport.WeightedGains.ZeroSaddleNumerator
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The first scalar mass gain for a zero-saddle transport component

Blueprint: `lem:zero-saddle-quotient-mass`.

The original continuous forcing and its first weak gradient supply the numerator
estimate. Multiplication by h leaves an integrable coarea energy plus 1/√h.
Resonant cancellation and first-derivative phase-cell summation then give
`quarterQuotient / √h ∈ L²`. This is a single rotation-character component;
physical transport reconstruction and assembly of all four components are
separate from this scalar mass conclusion.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Zero saddle forcing gives the scalar first mass gain for any fourth-root
character on an initial collar, with the original continuous forcing. -/
theorem IsTransportPair.zero_saddle_quarterQuotient_memLp
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0)
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧ η < 1 / 2 ∧ IsPhaseCellEndpoint lam κ η ∧
      MemLp (fun h ↦ quarterQuotient lam κ g h / (√h : ℂ)) 2
        (volume.restrict (Ioo 0 η)) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 η)), quarterDivisor lam κ h ≠ 0 := by
  obtain ⟨D, _, K, h₀, hK, hh₀, hh₀1, hN, hE, hbound⟩ :=
    hp.zero_saddle_numerator_estimates hcell hg hfg hz
  let b := min r h₀
  have hb : 0 < b := lt_min hr hh₀
  have hbr : b ≤ r := min_le_left _ _
  have hbh₀ : b ≤ h₀ := min_le_right _ _
  have hb1 : b < 1 := hbh₀.trans_lt (hh₀1.trans (by norm_num))
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 h₀ := Ioo_subset_Ioo le_rfl hbh₀
  have hAr : orbitAnnulus 0 b ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans_le hbr⟩
  have hvκ' : HasQuarterCharacterOn κ (orbitAnnulus 0 b) v :=
    ae_restrict_of_ae_restrict_of_subset hAr hvκ
  have hfκ' : HasQuarterCharacterOn κ (orbitAnnulus 0 b) f :=
    ae_restrict_of_ae_restrict_of_subset hAr hfκ
  have hA : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  have hzero := (numerator_zeros hκ hp hb hb1 hA hg hfg hvκ' hfκ').2
  have hNb : HasIntervalH1Loc 0 b (quarterNumerator lam g)
      (quarterNumeratorDerivative lam g D) := fun a c ha hac hc ↦
    hN lam a c ha hac (hc.trans_le hbh₀)
  have hInv : IntegrableOn (fun h : ℝ ↦ 1 / √h) (Ioo 0 b) := by
    have hi : IntegrableOn (fun h : ℝ ↦ h ^ (-(1 / 2 : ℝ))) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).2 (by norm_num)
    apply hi.congr_fun _ measurableSet_Ioo
    intro h hh
    dsimp only
    rw [Real.rpow_neg hh.1.le, ← Real.sqrt_eq_rpow, one_div]
  let F := fun h ↦ K * quarterJetEnergy 1 0 D h + K / √h
  have hF : IntegrableOn F (Ioo 0 b) := by
    change Integrable F (volume.restrict (Ioo 0 b))
    convert! ((hE.mono_set hsub).const_mul K).add (hInv.const_mul K) using 1
    funext h
    dsimp only [F, Pi.add_apply]
    ring
  have hFb : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      h * ‖quarterNumeratorDerivative lam g D h‖ ^ 2 ≤ F h := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hbound,
      ae_restrict_mem measurableSet_Ioo] with h hh hI
    have hm := mul_le_mul_of_nonneg_left (hh.2 lam).2 hI.1.le
    apply hm.trans_eq
    dsimp only [F]
    field_simp [hI.1.ne', (Real.sqrt_pos.2 hI.1).ne']
  obtain ⟨η, hη, hηb, hηend, hQ, hne⟩ :=
    phase_cell_mass_division hp.ne_zero hκ hb hNb hzero hF hFb
  exact ⟨η, hη, hηb.trans_le hbr, (hηb.trans_le hbh₀).trans hh₀1,
    hηend, hQ, hne⟩

end EulerDipoleEigenvalues
