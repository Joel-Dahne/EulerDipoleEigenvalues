import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.ScalarDivision
import NoEmbeddedEigenvalues.OrbitNumerators
import NoEmbeddedEigenvalues.PhaseCellDivision
import NoEmbeddedEigenvalues.SeparableMultiplier
import NoEmbeddedEigenvalues.WeakJetOperations

/-!
# Logarithmic multipliers and scalar phase division

The level weight is only used for 0 < h < 1. Its lift is assigned value one
on the separatrix. The rectangle weight's arbitrary axis values are harmless.
Weighted integrability is explicit; phase division returns an H¹ extension.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

def logLevelWeight (h : ℝ) : ℝ := 1 + Real.log (1 / h)

def torusDipoleLogWeight (p : Torus) : ℝ :=
  if Ψ p = 0 then 1 else logLevelWeight (|Ψ p| / 2)

def dipoleLogWeight (p : ℝ × ℝ) : ℝ :=
  if dipoleLift p = 0 then 1 else logLevelWeight (|dipoleLift p| / 2)

def logRadiusWeight (r : ℝ) : ℝ := 1 + |Real.log r|

def logRectangleWeight (p : ℝ × ℝ) : ℝ :=
  1 + abs (Real.log (abs p.1)) + abs (Real.log (abs p.2))

/-- Coordinate slicing supplies the logarithmic multiplier, without a finite-p
embedding (`lem:log-multiplier-rectangle`). -/
theorem log_multiplier_rectangle {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      let Q := Ioo (-ρ) ρ ×ˢ Ioo (-ρ) ρ
      MemSobolevOn 1 Q F → HasWeakJetOn 1 Q F D →
      MemLp (fun p ↦ (Real.sqrt (logRectangleWeight p) : ℂ) * F p) 2
        (volume.restrict Q) ∧
      (∫ p in Q, logRectangleWeight p * ‖F p‖ ^ 2) ≤ K * weakJetEnergy 1 Q D := by
  let I := Ioo (-ρ) ρ
  let w := fun t ↦ |Real.log t|
  let M := ∫ t in I, w t
  let C := 2 / (ρ - -ρ)
  let L := 2 * (ρ - -ρ)
  let K := 1 + 2 * M * C + M * L
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ abs_nonneg _)
  have hlen : 0 < ρ - -ρ := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun F D hF hD ↦ ?_⟩
  have hI : -ρ < ρ := by linarith
  have hQ : IsOpen (I ×ˢ I) := isOpen_Ioo.prod isOpen_Ioo
  have hd (j : Fin 2) : HasWeakPartialOn (I ×ˢ I) j F (D [j]) := by
    simpa only [hD.1] using hD.2 [] (by simp) j
  have hDj (j : Fin 2) : MemLp (D [j]) 2 (volume.restrict (I ×ˢ I)) :=
    (hd j).memSobolevOn hQ hF
  have mw : Measurable w := by unfold w; fun_prop
  have hw : ∀ t, 0 ≤ w t := fun _ ↦ abs_nonneg _
  have iw : IntegrableOn w I :=
    intervalIntegral.intervalIntegrable_log'.abs.1.mono_set Ioo_subset_Ioc_self
  obtain ⟨hu, hEu⟩ := (hd 0).sqrt_weight_fst hI hI mw hw iw hF.1 (hDj 0)
  obtain ⟨hv, hEv⟩ := (hd 1).sqrt_weight_snd hI hI mw hw iw hF.1 (hDj 1)
  have hW : ∀ p, 0 ≤ logRectangleWeight p := by
    intro p
    unfold logRectangleWeight
    positivity
  have mW : Measurable logRectangleWeight := by unfold logRectangleWeight; fun_prop
  have hWF := memLp_sqrt_weight_of_le_sum mW hW (fun p ↦ hw p.1) (fun p ↦ hw p.2)
    (fun _ ↦ by simp [logRectangleWeight, w, Real.log_abs]) hF.1 hu hv
  refine ⟨hWF, ?_⟩
  have hn (p : ℝ × ℝ) (t : ℝ) :
      ‖(Real.sqrt (w t) : ℂ) * F p‖ ^ 2 = w t * ‖F p‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw _)]
  have iF := hF.1.integrable_norm_pow (by norm_num)
  have iu := hu.integrable_norm_pow (by norm_num)
  have iv := hv.integrable_norm_pow (by norm_num)
  simp_rw [hn] at iu iv
  have hsplit : (fun p ↦ logRectangleWeight p * ‖F p‖ ^ 2) =
      ((fun p ↦ ‖F p‖ ^ 2) + (fun p ↦ w p.1 * ‖F p‖ ^ 2)) +
        (fun p ↦ w p.2 * ‖F p‖ ^ 2) := by
    funext p
    simp only [logRectangleWeight, w, Real.log_abs, Pi.add_apply]
    ring
  rw [hsplit, integral_add' (iF.add iu) iv, integral_add' iF iu]
  have hE1 : radialJetEnergy 1 0 (I ×ˢ I) 0 D =
      (∫ p in I ×ˢ I, ‖D [0] p‖ ^ 2) + (∫ p in I ×ˢ I, ‖D [1] p‖ ^ 2) := by
    unfold radialJetEnergy
    simp only [pow_zero, div_one]
    trans ∑ j : Fin 2, ∫ p in I ×ˢ I, ‖D [j] p‖ ^ 2
    · exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ (fun f ↦ by
        simp [List.ofFn_succ])
    · exact Fin.sum_univ_two _
  have hE : weakJetEnergy 1 (I ×ˢ I) D =
      (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
        ((∫ p in I ×ˢ I, ‖D [0] p‖ ^ 2) + (∫ p in I ×ˢ I, ‖D [1] p‖ ^ 2)) := by
    simp only [weakJetEnergy, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    change radialJetEnergy 0 0 (I ×ˢ I) 0 D + radialJetEnergy 1 0 (I ×ˢ I) 0 D = _
    rw [hE1]
    congr 1
    simp [radialJetEnergy, hD.1]
  have hAK : 1 + 2 * M * C ≤ K := by
    dsimp [K]
    linarith only [mul_nonneg hM hL.le]
  have hBK : M * L ≤ K := by
    dsimp [K]
    linarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) hC.le]
  calc
    _ ≤ (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
        M * (C * (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
          L * (∫ p in I ×ˢ I, ‖D [0] p‖ ^ 2)) +
        M * (C * (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
          L * (∫ p in I ×ˢ I, ‖D [1] p‖ ^ 2)) := add_le_add (add_le_add le_rfl hEu) hEv
    _ = (1 + 2 * M * C) * (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
        M * L * (∫ p in I ×ˢ I, ‖D [0] p‖ ^ 2) +
        M * L * (∫ p in I ×ˢ I, ‖D [1] p‖ ^ 2) := by ring
    _ ≤ K * (∫ p in I ×ˢ I, ‖F p‖ ^ 2) +
        K * (∫ p in I ×ˢ I, ‖D [0] p‖ ^ 2) +
        K * (∫ p in I ×ˢ I, ‖D [1] p‖ ^ 2) := by
      gcongr
    _ = K * weakJetEnergy 1 (I ×ˢ I) D := by rw [hE]; ring

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
