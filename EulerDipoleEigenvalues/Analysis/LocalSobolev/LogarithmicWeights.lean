module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalJets
public import EulerDipoleEigenvalues.Analysis.Inequalities.ScalarDivision
public import EulerDipoleEigenvalues.Transport.WeightedGains.OrbitNumerators
public import EulerDipoleEigenvalues.Transport.WeightedGains.PhaseCellDivision
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SeparableMultiplier
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.WeakJetOperations

/-! # Logarithmic weights and the physical multiplier estimate -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
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

end EulerDipoleEigenvalues
