module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LogarithmicWeights

/-! # Logarithmic weights in the phase cell -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The logarithmic level weight is uniformly comparable to its value at the
right endpoint on all sufficiently small complete phase cells
(`lem:log-phase-weight-comparison`). -/
theorem logLevelWeight_phase_cell_comparable {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ (κ : ℂ) (a z b : ℝ),
      0 < a → a < z → z < b → b < r → quarterDivisor lam κ z = 0 →
      |quarterPhase lam a - quarterPhase lam z| = Real.pi →
      |quarterPhase lam b - quarterPhase lam z| = Real.pi →
      1 ≤ logLevelWeight b ∧ ∀ h ∈ Ioo a b,
        logLevelWeight b ≤ logLevelWeight h ∧ logLevelWeight h ≤ A * logLevelWeight b := by
  obtain ⟨B, _, r, hB, _, hr, hr1, hf⟩ := quarterDivisor_inverse_factor hlam
  let L := |Real.log (B ^ 2)|
  refine ⟨r, 1 + L, hr, by dsimp [L]; positivity, ?_⟩
  intro κ a z b ha haz hzb hbr hz hl hu
  have hb : 0 < b := ha.trans (haz.trans hzb)
  have hWb : 1 ≤ logLevelWeight b := by
    unfold logLevelWeight
    exact le_add_of_nonneg_right
      (Real.log_nonneg ((one_le_div hb).2 (hbr.trans hr1).le))
  obtain ⟨_, _, _, _, _, hR⟩ := hf κ a z b ha haz hzb hbr hz hl hu
  refine ⟨hWb, fun h hh ↦ ?_⟩
  have hh0 := ha.trans hh.1
  have hbz := (hR b (right_mem_Icc.2 (haz.trans hzb).le)).2.1
  have hzh := (div_le_iff₀ hB).1 (hR h (Ioo_subset_Icc_self hh)).1
  have hrat : b / h ≤ B ^ 2 := by
    apply (div_le_iff₀ hh0).2
    calc
      b ≤ B * z := hbz
      _ ≤ B * (h * B) := mul_le_mul_of_nonneg_left hzh hB.le
      _ = B ^ 2 * h := by ring
  have hlog : Real.log (b / h) ≤ L :=
    (Real.log_le_log (div_pos hb hh0) hrat).trans (le_abs_self _)
  have hsplit : logLevelWeight h = logLevelWeight b + Real.log (b / h) := by
    simp only [logLevelWeight, Real.log_div one_ne_zero hh0.ne',
      Real.log_div one_ne_zero hb.ne', Real.log_div hb.ne' hh0.ne']
    ring
  rw [hsplit]
  refine ⟨le_add_of_nonneg_right (Real.log_nonneg ((one_le_div hh0).2 hh.2.le)), ?_⟩
  calc
    _ ≤ logLevelWeight b + L := add_le_add_right hlog _
    _ ≤ (1 + L) * logLevelWeight b := by
      rw [add_mul, one_mul]
      exact add_le_add_right (le_mul_of_one_le_right (abs_nonneg _) hWb) _

/-- Uniform complete-cell estimates transfer to the logarithmic measure
(`lem:log-phase-cell-division`), with no differentiated logarithm. -/
theorem log_phase_cell_division {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) {N N₁ N₂ : ℝ → ℂ}
    (hN : HasIntervalH2Loc 0 h₀ N N₁ N₂)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hN₁ : MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * N₁ h) 2
      (volume.restrict (Ioo 0 h₀)))
    (hN₂ : MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * (h : ℂ) * N₂ h) 2
      (volume.restrict (Ioo 0 h₀))) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam κ h₁ ∧
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
        (∀ h ∈ Ioo 0 h₁, quarterDivisor lam κ h * Q h = N h) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ)) 2
          (volume.restrict (Ioo 0 h₁)) ∧
        MemLp (fun (h : ℝ) ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h) 2
          (volume.restrict (Ioo 0 h₁)) ∧
        intervalH1Extension 0 h₁ Q Q₁ 0 = 0 := by
  obtain ⟨r, A, hr, hA, hcomp⟩ := logLevelWeight_phase_cell_comparable hlam
  have hW : Measurable logLevelWeight := by unfold logLevelWeight; fun_prop
  have hW1 (h : ℝ) (hh : h ∈ Ioo 0 h₀) : 1 ≤ logLevelWeight h := by
    unfold logLevelWeight
    exact le_add_of_nonneg_right
      (Real.log_nonneg ((one_le_div hh.1).2 (hh.2.trans hh₀1).le))
  have hc (a z b : ℝ) (ha : 0 < a) (haz : a < z) (hzb : z < b) (hbr : b < r)
      (hz : quarterDivisor lam κ z = 0)
      (hl : |quarterPhase lam a - quarterPhase lam z| = Real.pi)
      (hu : |quarterPhase lam b - quarterPhase lam z| = Real.pi) :
      ∃ w : ℝ, 0 ≤ w ∧ ∀ h ∈ Ioo a b,
        w ≤ logLevelWeight h ∧ logLevelWeight h ≤ A * w := by
    obtain ⟨hw, hbound⟩ := hcomp κ a z b ha haz hzb hbr hz hl hu
    exact ⟨logLevelWeight b, zero_le_one.trans hw, hbound⟩
  simpa only [mul_div_assoc] using
    phase_cell_division_of_comparable_weight hlam hκ hh₀ hh₀1 hr hA hW hW1 hc hN hzero hN₁
      (by simpa only [← mul_assoc] using hN₂)

end NoEmbeddedEigenvalues
