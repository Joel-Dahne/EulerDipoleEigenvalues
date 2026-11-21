import NoEmbeddedEigenvalues.OddOdd.BoundaryForm.BoundaryIdentification

/-! # Odd–odd Picone current limit and bulk decomposition -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- Ordinary-integral Picone identity after cancellation of the corner finite parts. -/
theorem dd_picone_current {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω)
    (b : DDBoundaryData lam κ q.phi) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    IntegrableOn (ddVorticityDensity q.nu) cellSquare ∧
      IntegrableOn (ddPiconeGradient q.phi dx dy) cellSquare ∧
      IntegrableOn (ddPiconePotential q.phi) cellSquare ∧
      (∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
        (∫ p in cellSquare, ddPiconePotential q.phi p) =
      -(8 / 3 : ℝ) * ∑ k : Fin 4,
        correctedBoundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  have hv := dd_vorticityDensity_integrable q.nu q.weighted_nu
  obtain ⟨_, hg⟩ := dd_gradient_energies_integrable q.regular q.even hdx hdy
  have hp := dd_piconePotential_integrable q.regular
  refine ⟨hv, hg, hp, ?_⟩
  have hBulk : Tendsto (ddPiconeBulk q.phi q.nu dx dy) (𝓝[>] 0)
      (𝓝 ((∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
          ∫ p in cellSquare, ddPiconePotential q.phi p)) :=
    ((tendsto_ddTruncatedCell_integral hv).add
      (tendsto_ddTruncatedCell_integral hg)).add (tendsto_ddTruncatedCell_integral hp)
  have h := (dd_character_virial_limit hlam hω hs q hκ hdx hdy).sub
    (dd_ground_current_limit q.regular)
  have hLevel := h.congr' (f₂ := ddPiconeBulk q.phi q.nu dx dy) (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with ε hε
    obtain ⟨hr, _, _, _, ht⟩ := dd_truncated_picone q.regular hdx hdy hε
    have hvε := hv.mono_set (show ddTruncatedCell ε ⊆ cellSquare from fun _ hp ↦ hp.1)
    dsimp only [ddRawBulk, ddPiconeBulk]
    rw [integral_add hvε hr, ht]
    ring)
  have hforms : (∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
      (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t) =
      ∑ k : Fin 4, correctedBoundaryForm lam
        (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ q.correctedBoundaryForm_eq hlam hκ b k
  calc
    _ = -(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) + ddValueFinitePart q.phi) -
        (-(8 / 3 : ℝ) * (ddValueFinitePart q.phi -
          ∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := tendsto_nhds_unique hBulk hLevel
    _ = -(8 / 3 : ℝ) * ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
        (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := by ring
    _ = _ := by rw [hforms]

/-- Bulk coercivity on the finite-energy domain. Integrability is a hypothesis, so the
    default value of a divergent Bochner integral cannot masquerade as an energy. -/
theorem dd_bulk_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    (hc : centralInversion φ = φ)
    (hmean : (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 φ p) = 0)
    (hgrad : IntegrableOn (ddPiconeGradient φ dx dy) cellSquare)
    (hpot : IntegrableOn (ddPiconePotential φ) cellSquare) :
    (25 / 54 : ℝ) * (∫ p in cellSquare, ddMassDensity φ p) ≤
      (∫ p in cellSquare, ddPiconeGradient φ dx dy p) +
        ∫ p in cellSquare, ddPiconePotential φ p := by
  have hg := dd_bulk_gradient_bound hφ hdx hdy hc hmean hgrad
  have hp := dd_bulk_potential_bound φ hpot
  linarith

end NoEmbeddedEigenvalues
