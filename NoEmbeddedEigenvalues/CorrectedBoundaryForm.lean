import NoEmbeddedEigenvalues.WeightedBoundaryForm
import NoEmbeddedEigenvalues.Sectors
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmically corrected boundary form

The forcing is an H¹ function on the weighted second-order domain.
The logarithmic coefficient, its integrability, and the endpoint-character
energy estimates are separated. All endpoint values are H¹ traces.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex ComplexConjugate MeasureTheory Set Filter Topology

/-- The transformed edge trace `g = -iwf' - λf`. -/
def correctedBoundaryTrace (lam : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * (boundaryWeight x : ℂ) * D x - (lam : ℂ) * F x

/-- The correction `β`, expressed in the interval coordinate. Endpoint values are
    irrelevant to the integrals and the domain uses genuine H¹ traces. -/
def correctedBoundaryBeta (x : ℝ) : ℝ :=
  (3 / 4 - 3 / 16 * boundaryWeight x +
      (1 / 4 - 25 / 64 * boundaryWeight x) * Real.log (boundaryWeight x)) /
    (1 + 1 / 8 * boundaryWeight x -
      1 / 64 * boundaryWeight x ^ 2 * Real.log (boundaryWeight x))

/-- The ordinary interval correction density. -/
def correctedBoundaryTerm (lam : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℝ :=
  correctedBoundaryBeta x * ‖correctedBoundaryTrace lam F D x‖ ^ 2

/-- The corrected boundary form, with the existing weighted-domain boundary form. -/
def correctedBoundaryForm (lam : ℝ) (F D E : ℝ → ℂ) : ℝ :=
  boundaryForm lam F D E + ∫ x in (-1 : ℝ)..1, correctedBoundaryTerm lam F D x

/-- The logarithmic denominator is positive throughout the open interval. -/
theorem correctedBoundaryBeta_denominator_ge_one {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 ≤ 1 + 1 / 8 * boundaryWeight x -
      1 / 64 * boundaryWeight x ^ 2 * Real.log (boundaryWeight x) := by
  obtain ⟨hw, hw1, _⟩ := boundaryWeight_bounds (Ioo_subset_Icc_self hx)
  have hp : 0 < boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [mul_pos (by linarith [hx.2] : 0 < 1 - x) (by linarith [hx.1] : 0 < 1 + x)]
  have hl := Real.log_nonpos hp.le hw1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (boundaryWeight x)) hl]

/-- The elementary lower bound used in both endpoint-character estimates. -/
theorem correctedBoundaryBeta_lower {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 / 2 + 1 / 4 * Real.log (boundaryWeight x) ≤ correctedBoundaryBeta x := by
  obtain ⟨hw, hw1, _⟩ := boundaryWeight_bounds (Ioo_subset_Icc_self hx)
  have hp : 0 < boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [mul_pos (by linarith [hx.2] : 0 < 1 - x) (by linarith [hx.1] : 0 < 1 + x)]
  have hl := Real.log_nonpos hp.le hw1
  have hd := correctedBoundaryBeta_denominator_ge_one hx
  unfold correctedBoundaryBeta
  apply (le_div_iff₀ (by linarith)).2
  have hm : (boundaryWeight x ^ 2 - 54 * boundaryWeight x) *
      Real.log (boundaryWeight x) ≥ 0 :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith [sq_nonneg (boundaryWeight x - 1)]) hl
  have hs : boundaryWeight x ^ 2 * Real.log (boundaryWeight x) ^ 2 ≥ 0 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- Absolute logarithmic control, independent of an eigenvalue or boundary function. -/
theorem abs_correctedBoundaryBeta_le {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |correctedBoundaryBeta x| ≤ 1 + |Real.log (boundaryWeight x)| := by
  obtain ⟨hw, hw1, _⟩ := boundaryWeight_bounds (Ioo_subset_Icc_self hx)
  have hp : 0 < boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [mul_pos (by linarith [hx.2] : 0 < 1 - x) (by linarith [hx.1] : 0 < 1 + x)]
  have hl := Real.log_nonpos hp.le hw1
  have hd := correctedBoundaryBeta_denominator_ge_one hx
  have hdpos : 0 < 1 + 1 / 8 * boundaryWeight x -
      1 / 64 * boundaryWeight x ^ 2 * Real.log (boundaryWeight x) := by linarith
  rw [correctedBoundaryBeta, abs_div, abs_of_pos hdpos]
  apply le_trans (div_le_self (abs_nonneg _) hd)
  rw [abs_le, abs_of_nonpos hl]
  have h₁ := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 1 / 4 - 25 / 64 * boundaryWeight x + 1 by linarith) hl
  have h₂ := mul_nonneg_of_nonpos_of_nonpos
    (show 1 / 4 - 25 / 64 * boundaryWeight x - 1 ≤ 0 by linarith) hl
  constructor <;> nlinarith

/-- The derivative of the transformed forcing, with specified weak derivatives. -/
def correctedBoundaryTraceDerivative (lam : ℝ) (D E : ℝ → ℂ) (x : ℝ) : ℂ :=
  -I * (boundaryWeight x : ℂ) * E x + (2 * I * (x : ℂ) - (lam : ℂ)) * D x

theorem hasDerivAt_correctedBoundaryTrace (lam : ℝ) {F D E : ℝ → ℂ} {x : ℝ}
    (hf : HasDerivAt F (D x) x) (hd : HasDerivAt D (E x) x) :
    HasDerivAt (correctedBoundaryTrace lam F D)
      (correctedBoundaryTraceDerivative lam D E x) x := by
  have h := (((hasDerivAt_boundaryWeight x).ofReal_comp.mul hd).const_mul (-I)).sub
    (hf.const_mul (lam : ℂ))
  convert h using 1
  · ext y
    simp [correctedBoundaryTrace, mul_assoc]
  · simp [correctedBoundaryTraceDerivative]
    ring

/-- Weighted second-order regularity gives ordinary H¹ regularity of the forcing. -/
theorem HasWeightedBoundaryH2.correctedBoundaryTrace_h1 {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    HasIntervalH1 (-1) 1 (correctedBoundaryTrace lam F D)
      (correctedBoundaryTraceDerivative lam D E) where
  memLp_value := by
    have hwD := memLp_ofReal_mul_of_continuousOn
      (show ContinuousOn boundaryWeight (Icc (-1) 1) by unfold boundaryWeight; fun_prop)
      h.h1.memLp_derivative
    convert (hwD.const_mul (-I)).sub (h.h1.memLp_value.const_mul (lam : ℂ)) using 1
    ext x
    simp [correctedBoundaryTrace, mul_assoc]
  memLp_derivative := by
    have hx := memLp_ofReal_mul_of_continuousOn continuousOn_id h.h1.memLp_derivative
    convert ((h.memLp_weighted_second.const_mul (-I)).add (hx.const_mul (2 * I))).sub
      (h.h1.memLp_derivative.const_mul (lam : ℂ)) using 1
    ext x
    simp [correctedBoundaryTraceDerivative]
    ring
  locally_absolutelyContinuous c d hc hcd hd := by
    have hw : AbsolutelyContinuousOnInterval (fun x ↦ (boundaryWeight x : ℂ)) c d := by
      simpa using! ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
        (absolutelyContinuousOnInterval_boundaryWeight c d)
    have hh := ((hw.fun_smul (h.locally_absolutelyContinuous_first c d hc hcd hd)).const_smul
      (-I)).fun_sub ((h.h1.locally_absolutelyContinuous c d hc hcd hd).const_smul (lam : ℂ))
    convert hh using 1
    ext x
    simp [correctedBoundaryTrace, smul_eq_mul, mul_assoc]
  hasDerivAt_ae := by
    filter_upwards [h.h1.hasDerivAt_ae, h.hasDerivAt_first_ae] with x hf hd hx
    exact hasDerivAt_correctedBoundaryTrace lam (hf hx) (hd hx)

/-- The logarithmic weight is integrable at both endpoints. -/
theorem integrableOn_log_boundaryWeight :
    IntegrableOn (fun x ↦ Real.log (boundaryWeight x)) (Ioo (-1) 1) := by
  have ha : IntervalIntegrable (fun x ↦ Real.log (1 + x)) volume (-1) 1 := by
    convert (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2)).comp_add_left 1
      using 1 <;> norm_num
  have hb : IntervalIntegrable (fun x ↦ Real.log (1 - x)) volume (-1) 1 := by
    convert ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2)).comp_sub_left 1).symm
      using 1 <;> norm_num
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    (ha.add hb)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h₁ : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
  have h₂ : 1 - x ≠ 0 := ne_of_gt (by linarith [hx.2])
  rw [show boundaryWeight x = (1 + x) * (1 - x) by unfold boundaryWeight; ring,
    Real.log_mul h₁ h₂]

theorem integrableOn_correctedBoundaryBeta :
    IntegrableOn correctedBoundaryBeta (Ioo (-1) 1) := by
  apply ((integrableOn_const (s := Ioo (-1 : ℝ) 1) (C := (1 : ℝ)) (by simp)).add
    integrableOn_log_boundaryWeight.norm).mono'
      (show AEStronglyMeasurable correctedBoundaryBeta (volume.restrict (Ioo (-1) 1)) by
        apply Measurable.aestronglyMeasurable
        unfold correctedBoundaryBeta boundaryWeight
        measurability)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_correctedBoundaryBeta_le hx

/-- Multiplication by the squared norm of an H¹ function preserves integrability. -/
theorem HasIntervalH1.integrable_correctedBoundaryBeta {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V) :
    IntegrableOn (fun x ↦ correctedBoundaryBeta x * ‖G x‖ ^ 2) (Ioo (-1) 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (h.continuousOn_extension (by norm_num : (-1 : ℝ) < 1)).norm
  apply integrableOn_correctedBoundaryBeta.mul_bdd (c := C ^ 2)
    (h.memLp_value.aestronglyMeasurable.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb : ‖G x‖ ≤ C := by
    rw [← h.extension_eq (by norm_num : (-1 : ℝ) < 1) hx]
    exact hC (mem_image_of_mem _ (Ioo_subset_Icc_self hx))
  simpa only [Real.norm_eq_abs, Pi.pow_apply, abs_pow, abs_norm] using
    pow_le_pow_left₀ (norm_nonneg (G x)) hb 2

/-- Absolute integrability of the correction is independent of the endpoint character. -/
theorem HasWeightedBoundaryH2.integrable_correctedBoundaryTerm {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    IntegrableOn (correctedBoundaryTerm lam F D) (Ioo (-1) 1) :=
  (h.correctedBoundaryTrace_h1 lam).integrable_correctedBoundaryBeta

/-- A uniform positive lower bound on the central interval. -/
theorem correctedBoundaryBeta_central {x : ℝ} (hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    5 / 12 ≤ correctedBoundaryBeta x := by
  have hi : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hw : 3 / 4 ≤ boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x + 1 / 2)
      (by linarith [hx.2] : 0 ≤ 1 / 2 - x)]
  have hp : 0 < boundaryWeight x := by linarith
  have hinv : (boundaryWeight x)⁻¹ ≤ 4 / 3 := by
    apply (inv_le_iff_one_le_mul₀ hp).2
    linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hb := correctedBoundaryBeta_lower hi
  linarith

/-- An exact rational cutoff suffices in place of the manuscript's `exp (-2)`. -/
theorem log_seven_lt_two : Real.log 7 < 2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).2 (by linarith)

/-- Pointwise localization of the negative part to the endpoint logarithmic layers. -/
theorem correctedBoundaryBeta_negative_le {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    max (-correctedBoundaryBeta x) 0 ≤
      1 / 4 * max (Real.log ((1 / 7) / (1 - |x|))) 0 := by
  have hab : |x| < 1 := abs_lt.mpr hx
  have hd : 0 < 1 - |x| := by linarith
  have hw : 1 - |x| ≤ boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hab.le)]
  have hl := Real.log_le_log hd hw
  have hb := correctedBoundaryBeta_lower hx
  have he := log_seven_lt_two
  rw [Real.log_div (by norm_num : (1 / 7 : ℝ) ≠ 0) hd.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0), Real.log_one]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4), mul_zero]
  exact max_le_max (by linarith) le_rfl

/-- The affine forcing corresponding to the boundary function `b*x`. -/
def correctedAffineForcing (lam : ℝ) (b : ℂ) (x : ℝ) : ℂ :=
  b * (-I * (boundaryWeight x : ℂ) - (lam : ℂ) * (x : ℂ))

/-- The central mass of the affine forcing is an exact polynomial integral. -/
theorem integral_correctedAffineForcing_central (lam : ℝ) (b : ℂ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2), ‖correctedAffineForcing lam b x‖ ^ 2) =
      (203 / 240 + lam ^ 2 / 12) * ‖b‖ ^ 2 := by
  have hnorm (x : ℝ) : ‖correctedAffineForcing lam b x‖ ^ 2 =
      ‖b‖ ^ 2 * (boundaryWeight x ^ 2 + lam ^ 2 * x ^ 2) := by
    rw [correctedAffineForcing, norm_mul, mul_pow]
    congr 1
    rw [← normSq_eq_norm_sq]
    simp [normSq_apply]
    ring
  have hw : (∫ x in (-1 / 2 : ℝ)..(1 / 2), boundaryWeight x ^ 2) = 203 / 240 := by
    have he (x : ℝ) : boundaryWeight x ^ 2 = x ^ 4 - 2 * x ^ 2 + 1 := by
      unfold boundaryWeight
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_add
      ((intervalIntegral.intervalIntegrable_pow 4).sub
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul 2)) intervalIntegrable_const,
      intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow 4)
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul 2),
      intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((show Continuous (fun x ↦ boundaryWeight x ^ 2) by
        unfold boundaryWeight; fun_prop).intervalIntegrable _ _)
      ((intervalIntegral.intervalIntegrable_pow 2).const_mul (lam ^ 2)),
    hw, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]
  ring

/-- A half-interval endpoint estimate sufficient here; no sharp Poincaré constant is used. -/
theorem HasIntervalH1.integral_sq_le_half_derivative {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V)
    (hm : intervalH1Extension (-1) 1 G V (-1) = 0)
    (hp : intervalH1Extension (-1) 1 G V 1 = 0) :
    (∫ x in (-1 : ℝ)..1, ‖G x‖ ^ 2) ≤
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2 := by
  let T := intervalH1Extension (-1) 1 G V
  have hc := (h.continuousOn_extension (by norm_num : (-1 : ℝ) < 1)).norm.pow 2
  have hTL : IntervalIntegrable (fun x ↦ ‖T x‖ ^ 2) volume (-1) 0 :=
    (hc.mono (Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
  have hTR : IntervalIntegrable (fun x ↦ ‖T x‖ ^ 2) volume 0 1 :=
    (hc.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc (by norm_num)
  have hEL : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      (h.integrableOn_sq_norm_derivative.mono_set
        (Icc_subset_Icc le_rfl (by norm_num : (0 : ℝ) ≤ 1)))
  have hER : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      (h.integrableOn_sq_norm_derivative.mono_set
        (Icc_subset_Icc (by norm_num : (-1 : ℝ) ≤ 0) le_rfl))
  have hleft : (∫ x in (-1 : ℝ)..0, ‖T x‖ ^ 2) ≤
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..0, ‖V x‖ ^ 2 := by
    calc
      _ ≤ ∫ x in (-1 : ℝ)..0, (x + 1) * (∫ t in (-1 : ℝ)..0, ‖V t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hTL
          ((intervalIntegral.intervalIntegrable_id.add intervalIntegrable_const).mul_const _)
        intro x hx
        have he := h.extension_sq_le_left (by norm_num) hm
          (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1, by linarith [hx.2]⟩)
        have hi := intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
          (Eventually.of_forall fun _ ↦ sq_nonneg _) hEL
        have hh := mul_le_mul_of_nonneg_left hi (by linarith [hx.1] : 0 ≤ x + 1)
        dsimp [T]
        linarith
      _ = _ := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
            intervalIntegrable_const]
        norm_num [integral_id]
  have hright : (∫ x in (0 : ℝ)..1, ‖T x‖ ^ 2) ≤
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, ‖V x‖ ^ 2 := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, (1 - x) * (∫ t in (0 : ℝ)..1, ‖V t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hTR
          ((intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id).mul_const _)
        intro x hx
        have he := h.extension_sq_le_right (by norm_num) hp
          (show x ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hx.1], hx.2⟩)
        have hi := intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
          (Eventually.of_forall fun _ ↦ sq_nonneg _) hER
        have hh := mul_le_mul_of_nonneg_left hi (by linarith [hx.2] : 0 ≤ 1 - x)
        dsimp [T]
        linarith
      _ = _ := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_sub intervalIntegrable_const
            intervalIntegral.intervalIntegrable_id]
        norm_num [integral_id]
  have hrep : (∫ x in (-1 : ℝ)..1, ‖T x‖ ^ 2) = ∫ x in (-1 : ℝ)..1, ‖G x‖ ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change ‖T x‖ ^ 2 = ‖G x‖ ^ 2
    rw [show T x = G x from h.extension_eq (by norm_num) hx]
  rw [← hrep, ← intervalIntegral.integral_add_adjacent_intervals hTL hTR,
    ← intervalIntegral.integral_add_adjacent_intervals hEL hER]
  linarith

/-- The affine forcing is a polynomial H¹ pair. -/
theorem correctedAffineForcing_h1 (lam : ℝ) (b : ℂ) :
    HasIntervalH1 (-1) 1 (correctedAffineForcing lam b)
      (fun x ↦ b * (2 * I * (x : ℂ) - (lam : ℂ))) where
  memLp_value :=
    ((memLp_top_of_continuousOn_Icc
      (show ContinuousOn (correctedAffineForcing lam b) (Icc (-1) 1) by
        unfold correctedAffineForcing boundaryWeight; fun_prop)).mono_exponent
          (by simp)).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  memLp_derivative :=
    ((memLp_top_of_continuousOn_Icc (by fun_prop)).mono_exponent (by simp)).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  locally_absolutelyContinuous c d _ _ _ := by
    have hw : AbsolutelyContinuousOnInterval (fun x ↦ (boundaryWeight x : ℂ)) c d := by
      simpa using! ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
        (absolutelyContinuousOnInterval_boundaryWeight c d)
    have hid : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ (x : ℂ)) c d := by
      simpa using! ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
        (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval (a := c) (b := d))
    convert (((hw.const_smul (-I)).fun_sub (hid.const_smul (lam : ℂ))).const_smul b) using 1
    ext x
    simp [correctedAffineForcing, smul_eq_mul]
  hasDerivAt_ae := by
    apply Eventually.of_forall
    intro x _
    have ht := ((((hasDerivAt_boundaryWeight x).ofReal_comp.const_mul (-I)).sub
      ((hasDerivAt_id x).ofReal_comp.const_mul (lam : ℂ))).const_mul b)
    convert ht using 1
    · rfl
    · push_cast
      ring

/-- Zero-trace boundary energy controls the forcing derivative and its endpoint traces. -/
theorem HasWeightedBoundaryH2.correctedBoundaryTrace_zero_energy {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hm : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hp : intervalH1Extension (-1) 1 F D 1 = 0) :
    (∫ x in (-1 : ℝ)..1, ‖correctedBoundaryTraceDerivative lam D E x‖ ^ 2) ≤
        4 * boundaryForm lam F D E ∧
      intervalH1Extension (-1) 1 (correctedBoundaryTrace lam F D)
        (correctedBoundaryTraceDerivative lam D E) (-1) = 0 ∧
      intervalH1Extension (-1) 1 (correctedBoundaryTrace lam F D)
        (correctedBoundaryTraceDerivative lam D E) 1 = 0 := by
  sorry

/-- A first-order midpoint estimate for the logarithmic correction.
    The constants use only the central bound and logarithmic endpoint moments. -/
theorem HasIntervalH1.correctedBoundaryBeta_midpoint_bound {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V) :
    5 / 112 * ‖G 0‖ ^ 2 -
        53 / 448 * (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, correctedBoundaryBeta x * ‖G x‖ ^ 2 := by
  sorry

/-- Negative endpoint layers for a zero-trace remainder plus an affine forcing. -/
theorem HasIntervalH1.correctedBoundary_negative_affine {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V)
    (hm : intervalH1Extension (-1) 1 G V (-1) = 0)
    (hp : intervalH1Extension (-1) 1 G V 1 = 0) (lam : ℝ) (b : ℂ) :
    (∫ x in (-1 : ℝ)..1,
      max (-(correctedBoundaryBeta x * ‖G x + correctedAffineForcing lam b x‖ ^ 2)) 0) ≤
      1 / 392 * (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) +
        (4 / 3087 + lam ^ 2 / 7) * ‖b‖ ^ 2 := by
  sorry

/-- Positive central mass for a zero-trace remainder plus an affine forcing. -/
theorem HasIntervalH1.correctedBoundary_positive_affine {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V)
    (hm : intervalH1Extension (-1) 1 G V (-1) = 0)
    (hp : intervalH1Extension (-1) 1 G V 1 = 0) (lam : ℝ) (b : ℂ) :
    -(1 / 8) * (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) +
        (203 / 1920 + lam ^ 2 / 96) * ‖b‖ ^ 2 ≤
      ∫ x in (-1 : ℝ)..1,
        max (correctedBoundaryBeta x * ‖G x + correctedAffineForcing lam b x‖ ^ 2) 0 := by
  let A : ℝ → ℂ := fun x ↦ G x + correctedAffineForcing lam b x
  have hA := h.add (correctedAffineForcing_h1 lam b)
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hhalf : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hsub : uIcc (-1 / 2 : ℝ) (1 / 2) ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le hhalf, uIcc_of_le hle]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  have hAi : IntervalIntegrable (fun x ↦ ‖A x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).2 hA.memLp_value.norm.integrable_sq
  have hGi : IntervalIntegrable (fun x ↦ ‖G x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).2 h.memLp_value.norm.integrable_sq
  have hBi : IntervalIntegrable (fun x ↦ ‖correctedAffineForcing lam b x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).2
      (correctedAffineForcing_h1 lam b).memLp_value.norm.integrable_sq
  have hPi : IntervalIntegrable (fun x ↦ max (correctedBoundaryBeta x * ‖A x‖ ^ 2) 0)
      volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).2
      hA.integrable_correctedBoundaryBeta.pos_part
  have hPfull := intervalIntegral.integral_mono_interval
    (by norm_num : (-1 : ℝ) ≤ -1 / 2) hhalf (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (Eventually.of_forall fun x ↦ le_max_right (correctedBoundaryBeta x * ‖A x‖ ^ 2) 0) hPi
  have hcentral : (∫ x in (-1 / 2 : ℝ)..(1 / 2), (1 / 4 : ℝ) * ‖A x‖ ^ 2) ≤
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), max (correctedBoundaryBeta x * ‖A x‖ ^ 2) 0 := by
    apply intervalIntegral.integral_mono_on hhalf
      ((hAi.mono_set hsub).const_mul _) (hPi.mono_set hsub)
    intro x hx
    have hb : (1 / 4 : ℝ) ≤ correctedBoundaryBeta x :=
      le_trans (by norm_num : (1 / 4 : ℝ) ≤ 5 / 12) (correctedBoundaryBeta_central hx)
    exact (mul_le_mul_of_nonneg_right hb (sq_nonneg ‖A x‖)).trans (le_max_left _ _)
  have hyoung : (∫ x in (-1 / 2 : ℝ)..(1 / 2),
      (1 / 8 : ℝ) * ‖correctedAffineForcing lam b x‖ ^ 2 - (1 / 4 : ℝ) * ‖G x‖ ^ 2) ≤
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), (1 / 4 : ℝ) * ‖A x‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hhalf
      (((hBi.mono_set hsub).const_mul _).sub ((hGi.mono_set hsub).const_mul _))
      ((hAi.mono_set hsub).const_mul _)
    intro x _
    have ht : ‖correctedAffineForcing lam b x‖ ≤ ‖A x‖ + ‖G x‖ := by
      simpa [A] using norm_sub_le (G x + correctedAffineForcing lam b x) (G x)
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖A x‖ - ‖G x‖)]
  rw [intervalIntegral.integral_const_mul] at hcentral
  rw [intervalIntegral.integral_sub ((hBi.mono_set hsub).const_mul _)
    ((hGi.mono_set hsub).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_correctedAffineForcing_central] at hyoung
  have hGfull := intervalIntegral.integral_mono_interval
    (by norm_num : (-1 : ℝ) ≤ -1 / 2) hhalf (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (Eventually.of_forall fun _ ↦ sq_nonneg _) hGi
  have hGenergy := h.integral_sq_le_half_derivative hm hp
  change _ ≤ ∫ x in (-1 : ℝ)..1, max (correctedBoundaryBeta x * ‖A x‖ ^ 2) 0
  nlinarith

/-- The signed correction can be split because both parts are integrable. -/
theorem HasWeightedBoundaryH2.correctedBoundaryForm_eq_parts {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    correctedBoundaryForm lam F D E = boundaryForm lam F D E +
      (∫ x in (-1 : ℝ)..1, max (correctedBoundaryTerm lam F D x) 0) -
      (∫ x in (-1 : ℝ)..1, max (-correctedBoundaryTerm lam F D x) 0) := by
  have hi := h.integrable_correctedBoundaryTerm lam
  have hip := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).2 hi.pos_part
  have hin := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).2 hi.neg_part
  have he : (∫ x in (-1 : ℝ)..1, correctedBoundaryTerm lam F D x) =
      (∫ x in (-1 : ℝ)..1, max (correctedBoundaryTerm lam F D x) 0) -
      (∫ x in (-1 : ℝ)..1, max (-correctedBoundaryTerm lam F D x) 0) := by
    rw [← intervalIntegral.integral_sub hip hin]
    apply intervalIntegral.integral_congr
    intro x _
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  unfold correctedBoundaryForm
  rw [he]
  ring

/-- Nonnegativity for equal endpoint traces; the parameter may be zero. -/
theorem HasWeightedBoundaryH2.correctedBoundaryForm_nonneg_equal {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hends : intervalH1Extension (-1) 1 F D 1 = intervalH1Extension (-1) 1 F D (-1)) :
    0 ≤ correctedBoundaryForm lam F D E := by
  let a := intervalH1Extension (-1) 1 F D (-1)
  let U : ℝ → ℂ := fun x ↦ F x - a
  have hu : HasWeightedBoundaryH2 U D E := by
    simpa only [zero_mul, sub_zero] using h.subAffine a 0
  have hm : intervalH1Extension (-1) 1 U D (-1) = 0 := by
    have ht := h.extension_subAffine a 0 (show (-1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    simpa [U, a] using ht
  have hp : intervalH1Extension (-1) 1 U D 1 = 0 := by
    have ht := h.extension_subAffine a 0 (show (1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    simpa [U, a, hends] using ht
  have hf := h.affine_splitting lam a 0 (by simp [a]) (by simpa [a] using hends)
  have hf' : boundaryForm lam F D E = boundaryForm lam U D E := by
    simpa only [normSq_zero, mul_zero, zero_mul, sub_zero, add_zero, mul_im,
      zero_re, zero_im] using hf
  have hzero := (hu.correctedBoundaryTrace_zero_energy lam hm hp).1
  have hnon := hu.boundaryForm_nonneg lam (Or.inl (hp.trans hm.symm))
  have hcorr := (h.correctedBoundaryTrace_h1 lam).correctedBoundaryBeta_midpoint_bound
  unfold correctedBoundaryForm correctedBoundaryTerm
  rw [hf']
  nlinarith [sq_nonneg (‖correctedBoundaryTrace lam F D 0‖)]

/-- Nonnegativity for opposite endpoint traces; all numerical margins are rational. -/
theorem HasWeightedBoundaryH2.correctedBoundaryForm_nonneg_opposite {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hends : intervalH1Extension (-1) 1 F D 1 = -intervalH1Extension (-1) 1 F D (-1)) :
    0 ≤ correctedBoundaryForm lam F D E := by
  let b := intervalH1Extension (-1) 1 F D 1
  let U : ℝ → ℂ := fun x ↦ F x - b * (x : ℂ)
  let V : ℝ → ℂ := fun x ↦ D x - b
  have hu : HasWeightedBoundaryH2 U V E := by
    simpa only [sub_zero] using h.subAffine 0 b
  have hneg : intervalH1Extension (-1) 1 F D (-1) = 0 - b := by
    dsimp [b]
    rw [hends]
    simp
  have hm : intervalH1Extension (-1) 1 U V (-1) = 0 := by
    have ht := h.extension_subAffine 0 b (show (-1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    simpa [U, V, hneg] using ht
  have hp : intervalH1Extension (-1) 1 U V 1 = 0 := by
    have ht := h.extension_subAffine 0 b (show (1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    simpa [U, V, b] using ht
  have hf : boundaryForm lam F D E = boundaryForm lam U V E + lam ^ 2 * ‖b‖ ^ 2 := by
    simpa [U, V, normSq_eq_norm_sq] using h.affine_splitting lam 0 b hneg (by simp [b])
  obtain ⟨henergy, hgneg, hgpos⟩ := hu.correctedBoundaryTrace_zero_energy lam hm hp
  have hgh1 := hu.correctedBoundaryTrace_h1 lam
  have hn := hgh1.correctedBoundary_negative_affine hgneg hgpos lam b
  have hp' := hgh1.correctedBoundary_positive_affine hgneg hgpos lam b
  have he (x : ℝ) : correctedBoundaryBeta x *
      ‖correctedBoundaryTrace lam U V x + correctedAffineForcing lam b x‖ ^ 2 =
      correctedBoundaryTerm lam F D x := by
    apply congrArg (fun z : ℂ ↦ correctedBoundaryBeta x * ‖z‖ ^ 2)
    dsimp [correctedBoundaryTrace, correctedAffineForcing, U, V]
    ring
  simp_rw [he] at hn hp'
  have hnon := hu.boundaryForm_nonneg lam (Or.inl (hp.trans hm.symm))
  rw [h.correctedBoundaryForm_eq_parts lam, hf]
  have hmargin : 2 / 5 * boundaryForm lam U V E +
      (1 / 10 + 4 / 5 * lam ^ 2) * ‖b‖ ^ 2 ≤
      boundaryForm lam U V E + lam ^ 2 * ‖b‖ ^ 2 +
        (∫ x in (-1 : ℝ)..1, max (correctedBoundaryTerm lam F D x) 0) -
        (∫ x in (-1 : ℝ)..1, max (-correctedBoundaryTerm lam F D x) 0) := by
    nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg ‖b‖)]
  nlinarith [sq_nonneg ‖b‖, mul_nonneg (sq_nonneg lam) (sq_nonneg ‖b‖)]

/-- Nonnegativity on the weighted second-order domain, including integrability.
    The exclusion needs no strict positivity or boundary equality classification. -/
theorem correctedBoundaryForm_nonneg {lam : ℝ} (hlam : lam ≠ 0) {κ : Bool}
    {F D E : ℝ → ℂ} (hF : HasWeightedBoundaryH2 F D E)
    (hends : intervalH1Extension (-1) 1 F D 1 =
      paritySign κ * intervalH1Extension (-1) 1 F D (-1)) :
    IntegrableOn (correctedBoundaryTerm lam F D) (Ioo (-1) 1) ∧
      0 ≤ correctedBoundaryForm lam F D E := by
  clear hlam
  refine ⟨hF.integrable_correctedBoundaryTerm lam, ?_⟩
  cases κ with
  | false => exact hF.correctedBoundaryForm_nonneg_opposite lam (by simpa [paritySign] using hends)
  | true => exact hF.correctedBoundaryForm_nonneg_equal lam (by simpa [paritySign] using hends)


end NoEmbeddedEigenvalues
