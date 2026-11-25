module

public import EulerDipoleEigenvalues.Transport.WeightedGains.PhaseCellMassEstimates
public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterPhaseCells
public import EulerDipoleEigenvalues.Analysis.Inequalities.CountableCellEnergy
public import EulerDipoleEigenvalues.Transport.WeightedGains.DescendingIntervalPartition

/-!
# First-derivative phase-cell mass summation

Blueprint: `lem:phase-cell-mass-division`.

Local H¹ numerator data, resonant cancellation and an integrable majorant of
`h * ‖N₁ h‖²` suffice for `N / D / √h` to be L². The quotient here is the
ordinary totalized quotient. No continuous extension, quotient derivative or
canonical trace at zero is asserted. All resonances and cell endpoints form
null sets for this mass estimate.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Global first mass division from an integrable weighted first-derivative
majorant, after shrinking to a complete-cell endpoint. -/
theorem phase_cell_mass_division {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {h₀ : ℝ} (hh₀ : 0 < h₀) {N N₁ : ℝ → ℂ}
    (hN : HasIntervalH1Loc 0 h₀ N N₁)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    {E : ℝ → ℝ} (hE : IntegrableOn E (Ioo 0 h₀))
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), h * ‖N₁ h‖ ^ 2 ≤ E h) :
    ∃ η : ℝ, 0 < η ∧ η < h₀ ∧ IsPhaseCellEndpoint lam κ η ∧
      MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (√h : ℂ)) 2
        (volume.restrict (Ioo 0 η)) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 η)), quarterDivisor lam κ h ≠ 0 := by
  obtain ⟨K, r, hK, hr, _, hest⟩ := phase_cell_mass_estimates hlam
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_ae_quarterDivisor_ne_zero hlam hκ (lt_min hh₀ hr)
  obtain ⟨e, z, he, het, hep, hzp⟩ := exists_complete_phase_cells hlam hκ hρ
  let s := fun n ↦ Ioo (e (n + 1)) (e n)
  have heh₀ (n : ℕ) : e n < h₀ := ((hep n).2.1.trans hρr).trans_le (min_le_left _ _)
  have her (n : ℕ) : e n < r := ((hep n).2.1.trans hρr).trans_le (min_le_right _ _)
  have hsubc (n : ℕ) : s n ⊆ Ioo 0 h₀ := fun x hx ↦
    ⟨(hep (n + 1)).1.trans hx.1, hx.2.trans (heh₀ n)⟩
  have hsub : (⋃ n, s n) ⊆ Ioo 0 h₀ := iUnion_subset hsubc
  have hcell (n : ℕ) := hest κ (e (n + 1)) (z n) (e n)
    (hep (n + 1)).1 (hzp n).1 (hzp n).2.1 (her n) (hzp n).2.2.1
    (hzp n).2.2.2.1 (hzp n).2.2.2.2 N N₁
    (hN _ _ (hep (n + 1)).1 (he (Nat.lt_succ_self n)) (heh₀ n))
    (hzero (z n) ⟨(hep (n + 1)).1.trans (hzp n).1,
      (hzp n).2.1.trans (heh₀ n)⟩ (hzp n).2.2.1)
  have hEn : IntegrableOn (fun h ↦ ‖E h‖) (Ioo 0 h₀) := hE.norm
  have hQL : MemLp (fun h ↦ (N h / quarterDivisor lam κ h) / (√h : ℂ)) 2
      (volume.restrict (⋃ n, s n)) := by
    apply memLp_two_of_cell_energy (fun _ ↦ measurableSet_Ioo)
      (descending_cells_disjoint he) hK.le (hEn.mono_set hsub)
      (fun x _ ↦ norm_nonneg (E x)) (fun n ↦ (hcell n).1)
    intro n
    apply (hcell n).2.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply integral_mono_of_nonneg _ (hEn.mono_set (hsubc n))
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsubc n) hbound] with h hh
      exact hh.trans (le_abs_self _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      exact mul_nonneg ((hep (n + 1)).1.trans hh.1).le (sq_nonneg _)
  refine ⟨e 0, (hep 0).1, heh₀ 0, (hep 0).2.2.1, ?_, ?_⟩
  · rwa [Measure.restrict_congr_set
      (descending_cells_ae_cover he (fun n ↦ (hep n).1) het)] at hQL
  · exact ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl (hep 0).2.1.le) hne

end EulerDipoleEigenvalues
