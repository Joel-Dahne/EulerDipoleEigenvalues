module

public import EulerDipoleEigenvalues.OddOdd.Picone.CurrentLimit

/-! # Odd–odd sector exclusion -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology

/-- Nonnegativity of the retained vorticity term. -/
theorem ddVorticityDensity_nonneg {p : ℝ × ℝ} (hp : p ∈ cellSquare) (ν : L2) :
    0 ≤ ddVorticityDensity ν p := by
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hle : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
  have hcube : dipoleLift p ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le hle 3
  have h8 : 0 ≤ 8 - dipoleLift p ^ 3 := by linarith
  unfold ddVorticityDensity ddF
  positivity

/-- Zero weighted mass gives zero quotient in the even sector. -/
theorem dd_eq_zero_of_mass_eq_zero {φ : L2} (hs : InSector true true φ)
    (hmass : (∫ p in cellSquare, ddMassDensity φ p) = 0) : φ = 0 := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hn : 0 ≤ᵐ[volume.restrict cellSquare] ddMassDensity φ :=
    Eventually.of_forall fun p ↦ by unfold ddMassDensity ddWeight; positivity
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (integrableOn_ddMassDensity φ)).1 hmass
  apply hs.eq_zero_of_lift_ae_zero_on_cellSquare
  filter_upwards [hz, ae_restrict_mem hcell] with p hp hpc
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hpc
  change dipoleLift p ^ 2 * ‖liftL2 φ p‖ ^ 2 = 0 at hp
  have hsq : ‖liftL2 φ p‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hpos.ne')
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (liftL2 φ p)])

/-- Recovering the vorticity from a vanishing quotient uses only the Poisson relation. -/
theorem DDQuotientData.vorticity_eq_zero {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hm : MeanZero ω) (hz : q.phi = 0) : ω = 0 := by
  have hφ := Lp.eq_zero_iff_ae_eq_zero.mp hz
  have hψ : invLap ω = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [q.stream_eq, hφ] with t ht hzt
    simp only [Pi.zero_apply] at hzt ⊢
    rw [ht, hzt, mul_zero]
  apply fourierCoeff_ext
  intro k
  simpa only [hψ, fourierCoeff_zero_fun, mul_zero] using hasFourierLaplacian_invLap ω hm k

/-- Final contradiction in one rotation character, conditional on the analytic interfaces. -/
theorem odd_odd_character_exclusion {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) : ω = 0 := by
  obtain ⟨q⟩ := dd_exclusion_domain hlam hω hs
  obtain ⟨hmean, hc⟩ := dd_orthogonality hlam hω hs q
  obtain ⟨b⟩ := dd_boundary_regularity hlam q hκ
  have h1 : MemSobolev 1 q.phi := q.regular.mono (by norm_num)
  obtain ⟨dx, hdx⟩ := h1.exists_hasFourierPartial 0
  obtain ⟨dy, hdy⟩ := h1.exists_hasFourierPartial 1
  obtain ⟨hv, hg, hp, hid⟩ := dd_picone_current hlam hω hs q hκ b hdx hdy
  have hbulk := dd_bulk_picone q.regular hdx hdy hc hmean hg hp
  have hsum : 0 ≤ ∑ k : Fin 4, correctedBoundaryForm lam
      (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) :=
    Finset.sum_nonneg fun k _ ↦
      (correctedBoundaryForm_nonneg hlam (b.regular k) (b.endpoints k)).2
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hν : 0 ≤ ∫ p in cellSquare, ddVorticityDensity q.nu p :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem hcell fun p hp ↦
      ddVorticityDensity_nonneg hp q.nu)
  have hmass : (∫ p in cellSquare, ddMassDensity q.phi p) = 0 := by
    have hn : 0 ≤ ∫ p in cellSquare, ddMassDensity q.phi p :=
      integral_nonneg fun p ↦ by unfold ddMassDensity ddWeight; positivity
    nlinarith
  exact q.vorticity_eq_zero hω.1 (dd_eq_zero_of_mass_eq_zero q.even hmass)

/-- An eigenfunction odd under both separatrix reflections vanishes
    at every nonzero real spectral parameter. -/
theorem odd_odd_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false false ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, odd_odd_character_exclusion hlam hep hsp hkp,
    odd_odd_character_exclusion hlam hem hsm hkm, add_zero]

end EulerDipoleEigenvalues
