module

public import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.WeightedBoundaryForm
public import NoEmbeddedEigenvalues.Symmetry.Sectors
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmically corrected boundary form

The forcing is an H¹ function on the weighted second-order domain.
The logarithmic coefficient, its integrability, endpoint logarithmic moments,
and the endpoint-character energy estimates are separated. All endpoint values
are H¹ traces.
-/

@[expose] public section

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

/-- Logarithmic moments on an endpoint layer. The integrand is nonnegative,
    absolutely integrable, and has an exact value for every natural power;
    the boundary estimates use only the powers zero, one and two. -/
theorem logarithmic_endpoint_moment {a : ℝ} (ha : 0 < a) (j : ℕ) :
    (∀ d ∈ Ioo (0 : ℝ) a, 0 ≤ d ^ j * Real.log (a / d)) ∧
      IntervalIntegrable (fun d ↦ d ^ j * Real.log (a / d)) volume 0 a ∧
      (∫ d in (0 : ℝ)..a, d ^ j * Real.log (a / d)) =
        a ^ (j + 1) / ((j : ℝ) + 1) ^ 2 := by
  have hn : (j : ℝ) + 1 ≠ 0 := by positivity
  have hlog (d : ℝ) (hd : 0 < d) :
      Real.log (a / d) = Real.log a - Real.log d :=
    Real.log_div ha.ne' hd.ne'
  -- The logarithmic singularity is integrable; the polynomial factor is bounded.
  have hint : IntervalIntegrable (fun d ↦ d ^ j * Real.log (a / d)) volume 0 a := by
    have h := ((intervalIntegrable_const (c := Real.log a)).sub
      (intervalIntegral.intervalIntegrable_log' (a := 0) (b := a))).continuousOn_mul
        (show ContinuousOn (fun d : ℝ ↦ d ^ j) _ by fun_prop)
    apply h.congr_uIoo
    intro d hd
    rw [uIoo_of_lt ha] at hd
    dsimp only
    rw [hlog d hd.1]
  refine ⟨?_, hint, ?_⟩
  · intro d hd
    exact mul_nonneg (pow_nonneg hd.1.le j)
      (Real.log_nonneg ((one_le_div hd.1).2 hd.2.le))
  · let P : ℝ → ℝ := fun d ↦
      d ^ (j + 1) * Real.log a / ((j : ℝ) + 1) -
        Real.log d * d ^ (j + 1) / ((j : ℝ) + 1) +
        d ^ (j + 1) / ((j : ℝ) + 1) ^ 2
    have hzero : Tendsto P (𝓝[>] 0) (𝓝 0) := by
      have hp : Tendsto (fun d : ℝ ↦ d ^ (j + 1)) (𝓝[>] 0) (𝓝 0) := by
        simpa using ((continuous_pow (j + 1)).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have hl : Tendsto (fun d : ℝ ↦ Real.log d * d ^ (j + 1))
          (𝓝[>] 0) (𝓝 0) := by
        simpa only [Real.rpow_natCast] using
          (tendsto_log_mul_rpow_nhdsGT_zero
            (show (0 : ℝ) < (j + 1 : ℕ) by positivity))
      simpa [P] using ((hp.mul_const (Real.log a)).div_const ((j : ℝ) + 1) |>.sub
        (hl.div_const ((j : ℝ) + 1))).add (hp.div_const (((j : ℝ) + 1) ^ 2))
    have htop : Tendsto P (𝓝[<] a) (𝓝 (P a)) := by
      have hc : ContinuousAt P a := by
        dsimp [P]
        fun_prop (disch := exact ha.ne')
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have hderiv : ∀ d ∈ Ioo (0 : ℝ) a,
        HasDerivAt P (d ^ j * Real.log (a / d)) d := by
      intro d hd
      have hp := hasDerivAt_pow (j + 1) d
      have h := (((hp.mul_const (Real.log a)).div_const ((j : ℝ) + 1)).sub
        (((Real.hasDerivAt_log hd.1.ne').mul hp).div_const ((j : ℝ) + 1))).add
          (hp.div_const (((j : ℝ) + 1) ^ 2))
      convert h using 1
      rw [hlog d hd.1]
      push_cast
      rw [pow_succ]
      field_simp [hd.1.ne', hn]
      ring
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      ha hderiv hint hzero htop
    simpa [P, mul_comm] using heq

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

-- Integration by parts gives ∫|(xF)'|² = ∫x²|F'|² when F has zero traces.
private theorem integral_normSq_id_product_derivative_le {F D : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 F D)
    (hm : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hp : intervalH1Extension (-1) 1 F D 1 = 0) :
    (∫ x in (-1 : ℝ)..1, Complex.normSq (F x + (x : ℂ) * D x)) ≤
      ∫ x in (-1 : ℝ)..1, Complex.normSq (D x) := by
  let A : ℝ → ℂ := fun x ↦ F x + (x : ℂ) * D x
  let Q : ℝ → ℝ := fun x ↦ x * Complex.normSq (F x)
  let q : ℝ → ℝ := fun x ↦ Complex.normSq (A x) - x ^ 2 * Complex.normSq (D x)
  have hA : MemLp A 2 (volume.restrict (Ioo (-1) 1)) :=
    h.memLp_value.add (memLp_ofReal_mul_of_continuousOn continuousOn_id h.memLp_derivative)
  have hAi : IntervalIntegrable (fun x ↦ Complex.normSq (A x)) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (integrable_normSq_of_memLp hA)
  have hDi : IntervalIntegrable (fun x ↦ Complex.normSq (D x)) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (integrable_normSq_of_memLp h.memLp_derivative)
  have hWi := hDi.continuousOn_mul (show ContinuousOn (fun x : ℝ ↦ x ^ 2) _ by fun_prop)
  have hqi : IntervalIntegrable q volume (-1) 1 := hAi.sub hWi
  have hder : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt Q (q x) x := by
    filter_upwards [h.hasDerivAt_ae] with x hx hxI
    have hfr : HasDerivAt (fun y ↦ (F y).re) (D x).re x := by
      simpa using! reCLM.hasFDerivAt.comp_hasDerivAt x (hx hxI)
    have hfi : HasDerivAt (fun y ↦ (F y).im) (D x).im x := by
      simpa using! imCLM.hasFDerivAt.comp_hasDerivAt x (hx hxI)
    convert (hasDerivAt_id x).mul ((hfr.mul hfr).add (hfi.mul hfi)) using 1
    · ext y
      simp [Q, normSq_apply]
    · simp [q, A, normSq_apply]
      ring
  have hprim : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1,
      (∫ t in x..y, q t) = Q y - Q x := by
    intro x hx y hy
    have hF := h.absolutelyContinuous hx hy
    have hFr := absolutelyContinuousOnInterval_re hF
    have hFi := absolutelyContinuousOnInterval_im hF
    have hac : AbsolutelyContinuousOnInterval Q x y := by
      have hid := LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
        (a := x) (b := y)
      convert hid.fun_mul ((hFr.fun_mul hFr).fun_add (hFi.fun_mul hFi)) using 1
      ext t
      simp [Q, normSq_apply]
    rw [← hac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder] with t ht htI
    exact (ht (ordConnected_Ioo.uIcc_subset hx hy (uIoc_subset_uIcc htI))).deriv.symm
  have htleft : Tendsto Q (𝓝[>] (-1)) (𝓝 0) := by
    have hf := h.tendsto_left (by norm_num)
    rw [hm] at hf
    simpa [Q] using (tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 (-1)) (𝓝 (-1)))).mul
        ((continuous_normSq.tendsto 0).comp hf)
  have htright : Tendsto Q (𝓝[<] 1) (𝓝 0) := by
    have hf := h.tendsto_right (by norm_num)
    rw [hp] at hf
    simpa [Q] using (tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 1) (𝓝 1))).mul
        ((continuous_normSq.tendsto 0).comp hf)
  have hz := intervalIntegral_eq_of_frequently (La := 0) (Lb := 0)
    (by norm_num : (-1 : ℝ) < 1) hqi hprim
    (fun ε hε ↦ by simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 htleft ε hε).frequently)
    (fun ε hε ↦ by simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 htright ε hε).frequently)
  change (∫ x in (-1 : ℝ)..1, Complex.normSq (A x) - x ^ 2 * Complex.normSq (D x)) = 0 - 0 at hz
  rw [intervalIntegral.integral_sub hAi hWi] at hz
  have hle : (∫ x in (-1 : ℝ)..1, x ^ 2 * Complex.normSq (D x)) ≤
      ∫ x in (-1 : ℝ)..1, Complex.normSq (D x) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hWi hDi
    intro x hx
    have hx2 : x ^ 2 ≤ 1 := sub_nonneg.mp (boundaryWeight_bounds hx).1
    simpa using mul_le_mul_of_nonneg_right hx2 (normSq_nonneg (D x))
  change (∫ x in (-1 : ℝ)..1, Complex.normSq (A x)) ≤ _
  linarith

-- The forcing has a limit, and wD is frequently small by square integrability.
-- With zero value trace, this forces the forcing trace itself to vanish.
private theorem correctedBoundaryTrace_endpoint_zero {l : Filter ℝ} [l.NeBot]
    {F D : ℝ → ℂ} {c : ℂ} (lam : ℝ)
    (hI : ∀ᶠ x in l, x ∈ Icc (-1 : ℝ) 1)
    (hF : Tendsto F l (𝓝 0)) (hg : Tendsto (correctedBoundaryTrace lam F D) l (𝓝 c))
    (hD : ∀ ε > 0, ∃ᶠ x in l, boundaryWeight x * ‖D x‖ < ε ∧
      boundaryWeight x * ‖D x‖ ^ 2 < ε) : c = 0 := by
  have ht : Tendsto (fun x ↦ (boundaryWeight x : ℂ) * D x) l (𝓝 (I * c)) := by
    convert ((hg.add (hF.const_mul (lam : ℂ))).const_mul I) using 1
    · ext x
      simp [correctedBoundaryTrace]
      ring_nf
      simp
    · simp
  apply norm_le_zero_iff.mp
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hsmall : ∃ᶠ x in l, ‖(boundaryWeight x : ℂ) * D x‖ ≤ ε := by
    refine ((hD ε hε).and_eventually hI).mono ?_
    rintro x ⟨⟨hx, -⟩, hxI⟩
    simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg (boundaryWeight_bounds hxI).1]
      using hx.le
  have hle := le_of_tendsto_of_frequently ht.norm hsmall
  simpa [norm_mul] using hle

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
  have hg := h.correctedBoundaryTrace_h1 lam
  have hD2 := h.h1.memLp_derivative.norm.integrable_sq
  have hleft : intervalH1Extension (-1) 1 (correctedBoundaryTrace lam F D)
      (correctedBoundaryTraceDerivative lam D E) (-1) = 0 := by
    apply correctedBoundaryTrace_endpoint_zero lam
      (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1))
        fun _ hx ↦ Ioo_subset_Icc_self hx)
      (by simpa only [hm] using h.h1.tendsto_left (by norm_num))
      (hg.tendsto_left (by norm_num))
    exact fun ε hε ↦ frequently_weight_small_left hD2 hε
  have hright : intervalH1Extension (-1) 1 (correctedBoundaryTrace lam F D)
      (correctedBoundaryTraceDerivative lam D E) 1 = 0 := by
    apply correctedBoundaryTrace_endpoint_zero lam
      (eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1))
        fun _ hx ↦ Ioo_subset_Icc_self hx)
      (by simpa only [hp] using h.h1.tendsto_right (by norm_num))
      (hg.tendsto_right (by norm_num))
    exact fun ε hε ↦ frequently_weight_small_right hD2 hε
  refine ⟨?_, hleft, hright⟩
  let A : ℝ → ℂ := fun x ↦ F x + (x : ℂ) * D x
  have hAm : MemLp A 2 (volume.restrict (Ioo (-1) 1)) := h.h1.memLp_value.add
    (memLp_ofReal_mul_of_continuousOn continuousOn_id h.h1.memLp_derivative)
  have hAi : IntervalIntegrable (fun x ↦ Complex.normSq (A x)) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (integrable_normSq_of_memLp hAm)
  have hSi : IntervalIntegrable (fun x ↦ Complex.normSq (boundarySquare lam F D E x))
      volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (integrable_normSq_of_memLp (h.memLp_boundarySquare lam))
  have hgi : IntervalIntegrable (fun x ↦ ‖correctedBoundaryTraceDerivative lam D E x‖ ^ 2)
      volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      hg.memLp_derivative.norm.integrable_sq
  have hpoint (x : ℝ) : ‖correctedBoundaryTraceDerivative lam D E x‖ ^ 2 ≤
      2 * Complex.normSq (boundarySquare lam F D E x) + 2 * Complex.normSq (A x) := by
    have he : I * correctedBoundaryTraceDerivative lam D E x =
        boundarySquare lam F D E x - A x := by
      apply Complex.ext <;>
        simp [correctedBoundaryTraceDerivative, boundarySquare, A, mul_re, mul_im] <;> ring
    have hn : ‖correctedBoundaryTraceDerivative lam D E x‖ =
        ‖boundarySquare lam F D E x - A x‖ := by
      rw [← he, norm_mul, norm_I, one_mul]
    rw [hn]
    simp only [Complex.normSq_eq_norm_sq]
    have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (boundarySquare lam F D E x) (A x)) 2
    nlinarith [sq_nonneg (‖boundarySquare lam F D E x‖ - ‖A x‖)]
  have hi := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hgi
    ((hSi.const_mul 2).add (hAi.const_mul 2)) (fun x _ ↦ hpoint x)
  rw [intervalIntegral.integral_add (hSi.const_mul 2) (hAi.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hAcontrol := integral_normSq_id_product_derivative_le h.h1 hm hp
  have hsos := h.sum_of_squares lam hm hp
  change (∫ x in (-1 : ℝ)..1, Complex.normSq (A x)) ≤ _ at hAcontrol
  linarith

-- The positive part of the logarithm vanishes outside the endpoint layer.
private theorem logarithmic_positive_moment (j : ℕ) :
    IntervalIntegrable (fun d : ℝ ↦ d ^ j * max (Real.log ((1 / 7) / d)) 0)
        volume 0 1 ∧
      (∫ d in (0 : ℝ)..1, d ^ j * max (Real.log ((1 / 7) / d)) 0) =
        (1 / 7 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) ^ 2 := by
  have hm := logarithmic_endpoint_moment (by norm_num : (0 : ℝ) < 1 / 7) j
  have hsmall : IntervalIntegrable
      (fun d : ℝ ↦ d ^ j * max (Real.log ((1 / 7) / d)) 0) volume 0 (1 / 7) := by
    apply hm.2.1.congr_uIoo
    intro d hd
    rw [uIoo_of_lt (by norm_num : (0 : ℝ) < 1 / 7)] at hd
    dsimp only
    rw [max_eq_left (Real.log_nonneg ((one_le_div hd.1).2 hd.2.le))]
  have hlarge : ∀ d ∈ Icc (1 / 7 : ℝ) 1,
      d ^ j * max (Real.log ((1 / 7) / d)) 0 = 0 := by
    intro d hd
    have hdpos : 0 < d := by linarith [hd.1]
    rw [max_eq_right (Real.log_nonpos (by positivity) ((div_le_one hdpos).2 hd.1)),
      mul_zero]
  have htail : IntervalIntegrable
      (fun d : ℝ ↦ d ^ j * max (Real.log ((1 / 7) / d)) 0) volume (1 / 7) 1 := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr
    intro d hd
    rw [uIoc_of_le (by norm_num : (1 / 7 : ℝ) ≤ 1)] at hd
    exact (hlarge d ⟨hd.1.le, hd.2⟩).symm
  refine ⟨hsmall.trans htail, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hsmall htail]
  have hs : (∫ d in (0 : ℝ)..(1 / 7), d ^ j * max (Real.log ((1 / 7) / d)) 0) =
      ∫ d in (0 : ℝ)..(1 / 7), d ^ j * Real.log ((1 / 7) / d) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro d hd
    dsimp only
    rw [max_eq_left (Real.log_nonneg ((one_le_div hd.1).2 hd.2.le))]
  have ht : (∫ d in (1 / 7 : ℝ)..1, d ^ j * max (Real.log ((1 / 7) / d)) 0) = 0 := by
    calc
      _ = ∫ _ in (1 / 7 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro d hd
        exact hlarge d (Ioo_subset_Icc_self hd)
      _ = 0 := by simp
  rw [hs, ht, add_zero, hm.2.2]

/-- A first-order midpoint estimate for the logarithmic correction.
    The constants use only the central bound and logarithmic endpoint moments. -/
theorem HasIntervalH1.correctedBoundaryBeta_midpoint_bound {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V) :
    5 / 112 * ‖G 0‖ ^ 2 -
        53 / 448 * (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, correctedBoundaryBeta x * ‖G x‖ ^ 2 := by
  let C := ‖G 0‖ ^ 2
  let U : ℝ → ℝ := fun x ↦ ‖G x - G 0‖ ^ 2
  let P : ℝ → ℝ := fun x ↦ max (correctedBoundaryBeta x * ‖G x‖ ^ 2) 0
  let N : ℝ → ℝ := fun x ↦ max (-(correctedBoundaryBeta x * ‖G x‖ ^ 2)) 0
  let EL := ∫ x in (-1 : ℝ)..0, ‖V x‖ ^ 2
  let ER := ∫ x in (0 : ℝ)..1, ‖V x‖ ^ 2
  have hLsub : uIcc (-1 : ℝ) 0 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hRsub : uIcc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hCsub : uIcc (-1 / 2 : ℝ) (1 / 2) ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  have hE : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      h.integrableOn_sq_norm_derivative
  have hEL := hE.mono_set hLsub
  have hER := hE.mono_set hRsub
  have hEL0 : 0 ≤ EL := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hER0 : 0 ≤ ER := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hUi : IntervalIntegrable U volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (h.memLp_value.sub (memLp_const (G 0))).norm.integrable_sq
  have hPi : IntervalIntegrable P volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      h.integrable_correctedBoundaryBeta.pos_part
  have hNi : IntervalIntegrable N volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      h.integrable_correctedBoundaryBeta.neg_part
  -- Midpoint Cauchy–Schwarz uses only the energy on the same half-interval.
  have hincL : ∀ x ∈ Ioc (-1 : ℝ) 0, U x ≤ -x * EL := by
    intro x hx
    have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have he := h.extension_sub_sq_le (by norm_num) (Ioo_subset_Icc_self hxfull)
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) hx.2
    rw [h.extension_eq (by norm_num) hxfull,
      h.extension_eq (by norm_num) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1), norm_sub_rev] at he
    have hi := intervalIntegral.integral_mono_interval hx.1.le hx.2 le_rfl
      (Eventually.of_forall fun _ ↦ sq_nonneg _) hEL
    exact he.trans (by simpa [EL] using mul_le_mul_of_nonneg_left hi (neg_nonneg.mpr hx.2))
  have hincR : ∀ x ∈ Ico (0 : ℝ) 1, U x ≤ x * ER := by
    intro x hx
    have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have he := h.extension_sub_sq_le (by norm_num)
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) (Ioo_subset_Icc_self hxfull) hx.1
    rw [h.extension_eq (by norm_num) hxfull,
      h.extension_eq (by norm_num) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)] at he
    have hi := intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2.le
      (Eventually.of_forall fun _ ↦ sq_nonneg _) hER
    exact he.trans (by simpa [ER] using mul_le_mul_of_nonneg_left hi hx.1)
  have hcentral : (∫ x in (-1 / 2 : ℝ)..(1 / 2), U x) ≤ (EL + ER) / 8 := by
    have hUL : IntervalIntegrable U volume (-1 / 2) 0 := hUi.mono_set (by
      rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 0),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) (by norm_num))
    have hUR : IntervalIntegrable U volume 0 (1 / 2) := hUi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) (by norm_num))
    have hl : (∫ x in (-1 / 2 : ℝ)..0, U x) ≤ EL / 8 := by
      calc
        _ ≤ ∫ x in (-1 / 2 : ℝ)..0, -x * EL := by
          apply intervalIntegral.integral_mono_on (by norm_num) hUL
            (intervalIntegral.intervalIntegrable_id.neg.mul_const EL)
          intro x hx
          exact hincL x ⟨by linarith [hx.1], hx.2⟩
        _ = _ := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg]
          norm_num [integral_id]
          ring
    have hr : (∫ x in (0 : ℝ)..(1 / 2), U x) ≤ ER / 8 := by
      calc
        _ ≤ ∫ x in (0 : ℝ)..(1 / 2), x * ER := by
          apply intervalIntegral.integral_mono_on (by norm_num) hUR
            (intervalIntegral.intervalIntegrable_id.mul_const ER)
          intro x hx
          exact hincR x ⟨hx.1, by linarith [hx.2]⟩
        _ = _ := by
          rw [intervalIntegral.integral_mul_const]
          norm_num [integral_id]
          ring
    rw [← intervalIntegral.integral_add_adjacent_intervals hUL hUR]
    linarith
  -- The central mass dominates half the midpoint value, minus the increment.
  have hpositive : 3 / 16 * C - 3 / 64 * (EL + ER) ≤ ∫ x in (-1 : ℝ)..1, P x := by
    have hfull : (∫ x in (-1 / 2 : ℝ)..(1 / 2), P x) ≤
        ∫ x in (-1 : ℝ)..1, P x := intervalIntegral.integral_mono_interval
      (by norm_num : (-1 : ℝ) ≤ -1 / 2) (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (Eventually.of_forall fun x ↦ le_max_right _ _) hPi
    have hc : (∫ x in (-1 / 2 : ℝ)..(1 / 2), 3 / 16 * C - 3 / 8 * U x) ≤
        ∫ x in (-1 / 2 : ℝ)..(1 / 2), P x := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (intervalIntegrable_const.sub ((hUi.mono_set hCsub).const_mul _)) (hPi.mono_set hCsub)
      intro x hx
      have hb : (3 / 8 : ℝ) ≤ correctedBoundaryBeta x :=
        (by norm_num : (3 / 8 : ℝ) ≤ 5 / 12).trans (correctedBoundaryBeta_central hx)
      have ht : ‖G 0‖ ≤ ‖G x‖ + ‖G x - G 0‖ := by
        simpa [norm_sub_rev] using norm_sub_le (G x) (G x - G 0)
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖G x‖)
      have hp : correctedBoundaryBeta x * ‖G x‖ ^ 2 ≤ P x := le_max_left _ _
      dsimp [C, U]
      nlinarith [sq_nonneg (‖G x‖ - ‖G x - G 0‖)]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((hUi.mono_set hCsub).const_mul _)] at hc
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      smul_eq_mul] at hc
    rw [show (1 / 2 : ℝ) - -1 / 2 = 1 by norm_num, one_mul] at hc
    linarith only [hc, hfull, hcentral]
  have hlog := logarithmic_positive_moment 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, one_pow, pow_one, div_one] at hlog
  have hnegative_density : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ E : ℝ,
      U x ≤ E → N x ≤ (C + E) / 2 * max (Real.log ((1 / 7) / (1 - |x|))) 0 := by
    intro x hx E hUE
    have ht : ‖G x‖ ≤ ‖G 0‖ + ‖G x - G 0‖ := by
      simpa using norm_add_le (G 0) (G x - G 0)
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hsq : ‖G x‖ ^ 2 ≤ 2 * C + 2 * E := by
      dsimp [U] at hUE
      dsimp [C]
      nlinarith only [hs, hUE, sq_nonneg (‖G 0‖ - ‖G x - G 0‖)]
    calc
      N x = max (-correctedBoundaryBeta x) 0 * ‖G x‖ ^ 2 := by
        dsimp [N]
        rw [max_mul_of_nonneg _ _ (sq_nonneg _), zero_mul, neg_mul]
      _ ≤ (1 / 4 * max (Real.log ((1 / 7) / (1 - |x|))) 0) * ‖G x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (correctedBoundaryBeta_negative_le hx) (sq_nonneg _)
      _ ≤ (1 / 4 * max (Real.log ((1 / 7) / (1 - |x|))) 0) * (2 * C + 2 * E) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  -- Each endpoint logarithmic layer has mass 1/7; outside it the weight vanishes.
  have hnegative : (∫ x in (-1 : ℝ)..1, N x) ≤ C / 7 + (EL + ER) / 14 := by
    have hl : (∫ x in (-1 : ℝ)..0, N x) ≤ (C + EL) / 14 := by
      calc
        _ ≤ ∫ x in (-1 : ℝ)..0,
            (C + EL) / 2 * max (Real.log ((1 / 7) / (x + 1))) 0 := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hNi.mono_set hLsub)
            (by simpa using (hlog.1.comp_add_right 1).const_mul ((C + EL) / 2))
          intro x hx
          have hUE : U x ≤ EL := (hincL x ⟨hx.1, hx.2.le⟩).trans
            (by nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x + 1) hEL0])
          simpa only [abs_of_nonpos hx.2.le, sub_neg_eq_add, add_comm 1 x] using
            hnegative_density x ⟨hx.1, by linarith [hx.2]⟩ EL hUE
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right
            (fun d : ℝ ↦ max (Real.log ((1 / 7) / d)) 0) 1]
          norm_num only [neg_add_cancel, zero_add]
          rw [hlog.2]
          ring
    have hr : (∫ x in (0 : ℝ)..1, N x) ≤ (C + ER) / 14 := by
      calc
        _ ≤ ∫ x in (0 : ℝ)..1,
            (C + ER) / 2 * max (Real.log ((1 / 7) / (1 - x))) 0 := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hNi.mono_set hRsub)
            (by simpa using ((hlog.1.comp_sub_left 1).symm).const_mul ((C + ER) / 2))
          intro x hx
          have hUE : U x ≤ ER := (hincR x ⟨hx.1.le, hx.2⟩).trans
            (by nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x) hER0])
          simpa only [abs_of_nonneg hx.1.le] using
            hnegative_density x ⟨by linarith [hx.1], hx.2⟩ ER hUE
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
            (fun d : ℝ ↦ max (Real.log ((1 / 7) / d)) 0) 1]
          norm_num only [sub_self, sub_zero]
          rw [hlog.2]
          ring
    rw [← intervalIntegral.integral_add_adjacent_intervals (hNi.mono_set hLsub)
      (hNi.mono_set hRsub)]
    linarith
  have hsplit : (∫ x in (-1 : ℝ)..1, correctedBoundaryBeta x * ‖G x‖ ^ 2) =
      (∫ x in (-1 : ℝ)..1, P x) - ∫ x in (-1 : ℝ)..1, N x := by
    rw [← intervalIntegral.integral_sub hPi hNi]
    apply intervalIntegral.integral_congr
    intro x _
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hsplit, ← intervalIntegral.integral_add_adjacent_intervals hEL hER]
  change 5 / 112 * C - 53 / 448 * (EL + ER) ≤ _
  linarith

-- After the two-term square bound, E is the derivative energy on one half,
-- B is the squared affine coefficient, and d is distance to its endpoint.
private def correctedNegativeMajorant (E B lam d : ℝ) : ℝ :=
  (d * E / 2 + (2 * d ^ 2 + lam ^ 2 / 2) * B) *
    max (Real.log ((1 / 7) / d)) 0

private theorem correctedNegativeMajorant_moment (E B lam : ℝ) :
    IntervalIntegrable (correctedNegativeMajorant E B lam) volume 0 1 ∧
      (∫ d in (0 : ℝ)..1, correctedNegativeMajorant E B lam d) =
        E / 392 + (2 / 3087 + lam ^ 2 / 14) * B := by
  have h0 := logarithmic_positive_moment 0
  have h1 := logarithmic_positive_moment 1
  have h2 := logarithmic_positive_moment 2
  have he : correctedNegativeMajorant E B lam = fun d ↦
      E / 2 * (d ^ 1 * max (Real.log ((1 / 7) / d)) 0) +
      (2 * B) * (d ^ 2 * max (Real.log ((1 / 7) / d)) 0) +
      (lam ^ 2 * B / 2) * (d ^ 0 * max (Real.log ((1 / 7) / d)) 0) := by
    funext d
    dsimp [correctedNegativeMajorant]
    ring
  rw [he]
  refine ⟨((h1.1.const_mul _).add (h2.1.const_mul _)).add (h0.1.const_mul _), ?_⟩
  rw [intervalIntegral.integral_add ((h1.1.const_mul _).add (h2.1.const_mul _))
      (h0.1.const_mul _),
    intervalIntegral.integral_add (h1.1.const_mul _) (h2.1.const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [h0.2, h1.2, h2.2]
  norm_num
  ring

private theorem correctedBoundary_negative_density_le {x E : ℝ} {g : ℂ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hg : ‖g‖ ^ 2 ≤ (1 - |x|) * E)
    (lam : ℝ) (b : ℂ) :
    max (-(correctedBoundaryBeta x * ‖g + correctedAffineForcing lam b x‖ ^ 2)) 0 ≤
      correctedNegativeMajorant E (‖b‖ ^ 2) lam (1 - |x|) := by
  have hab : |x| < 1 := abs_lt.mpr hx
  have hd : 0 ≤ 1 - |x| := by linarith
  have hw : 0 ≤ boundaryWeight x := (boundaryWeight_bounds (Ioo_subset_Icc_self hx)).1
  have hwle : boundaryWeight x ≤ 2 * (1 - |x|) := by
    unfold boundaryWeight
    nlinarith [sq_abs x, sq_nonneg (1 - |x|)]
  have hxsq : x ^ 2 ≤ 1 := sub_nonneg.mp hw
  have hbsq : ‖correctedAffineForcing lam b x‖ ^ 2 =
      ‖b‖ ^ 2 * (boundaryWeight x ^ 2 + lam ^ 2 * x ^ 2) := by
    rw [correctedAffineForcing, norm_mul, mul_pow]
    congr 1
    rw [← normSq_eq_norm_sq]
    simp [normSq_apply]
    ring
  have hb : ‖correctedAffineForcing lam b x‖ ^ 2 ≤
      ‖b‖ ^ 2 * (4 * (1 - |x|) ^ 2 + lam ^ 2) := by
    rw [hbsq]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hw2 := pow_le_pow_left₀ hw hwle 2
    have hx2 := mul_le_mul_of_nonneg_left hxsq (sq_nonneg lam)
    nlinarith
  have hsum : ‖g + correctedAffineForcing lam b x‖ ^ 2 ≤
      2 * ((1 - |x|) * E) + 2 * (‖b‖ ^ 2 * (4 * (1 - |x|) ^ 2 + lam ^ 2)) := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le g
      (correctedAffineForcing lam b x)) 2
    nlinarith [sq_nonneg (‖g‖ - ‖correctedAffineForcing lam b x‖)]
  calc
    _ = max (-correctedBoundaryBeta x) 0 * ‖g + correctedAffineForcing lam b x‖ ^ 2 := by
      rw [max_mul_of_nonneg _ _ (sq_nonneg _), zero_mul, neg_mul]
    _ ≤ (1 / 4 * max (Real.log ((1 / 7) / (1 - |x|))) 0) *
        ‖g + correctedAffineForcing lam b x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (correctedBoundaryBeta_negative_le hx) (sq_nonneg _)
    _ ≤ (1 / 4 * max (Real.log ((1 / 7) / (1 - |x|))) 0) *
        (2 * ((1 - |x|) * E) + 2 * (‖b‖ ^ 2 * (4 * (1 - |x|) ^ 2 + lam ^ 2))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by unfold correctedNegativeMajorant; ring

/-- Negative endpoint layers for a zero-trace remainder plus an affine forcing. -/
theorem HasIntervalH1.correctedBoundary_negative_affine {G V : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 G V)
    (hm : intervalH1Extension (-1) 1 G V (-1) = 0)
    (hp : intervalH1Extension (-1) 1 G V 1 = 0) (lam : ℝ) (b : ℂ) :
    (∫ x in (-1 : ℝ)..1,
      max (-(correctedBoundaryBeta x * ‖G x + correctedAffineForcing lam b x‖ ^ 2)) 0) ≤
      1 / 392 * (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) +
        (4 / 3087 + lam ^ 2 / 7) * ‖b‖ ^ 2 := by
  let N : ℝ → ℝ := fun x ↦
    max (-(correctedBoundaryBeta x * ‖G x + correctedAffineForcing lam b x‖ ^ 2)) 0
  -- Keep the two half-energies separate to avoid losing a factor of two.
  let EL := ∫ x in (-1 : ℝ)..0, ‖V x‖ ^ 2
  let ER := ∫ x in (0 : ℝ)..1, ‖V x‖ ^ 2
  have hE : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      h.integrableOn_sq_norm_derivative
  have hEL : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume (-1) 0 :=
    hE.mono_set (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc le_rfl (by norm_num))
  have hER : IntervalIntegrable (fun x ↦ ‖V x‖ ^ 2) volume 0 1 :=
    hE.mono_set (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc (by norm_num) le_rfl)
  have hN : IntervalIntegrable N volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2
      (h.add (correctedAffineForcing_h1 lam b)).integrable_correctedBoundaryBeta.neg_part
  have hNL : IntervalIntegrable N volume (-1) 0 :=
    hN.mono_set (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc le_rfl (by norm_num))
  have hNR : IntervalIntegrable N volume 0 1 :=
    hN.mono_set (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc (by norm_num) le_rfl)
  have hML := correctedNegativeMajorant_moment EL (‖b‖ ^ 2) lam
  have hMR := correctedNegativeMajorant_moment ER (‖b‖ ^ 2) lam
  have hleft : (∫ x in (-1 : ℝ)..0, N x) ≤
      EL / 392 + (2 / 3087 + lam ^ 2 / 14) * ‖b‖ ^ 2 := by
    calc
      _ ≤ ∫ x in (-1 : ℝ)..0, correctedNegativeMajorant EL (‖b‖ ^ 2) lam (x + 1) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hNL
          (by simpa using hML.1.comp_add_right 1)
        intro x hx
        have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
        have he := h.extension_sq_le_left (by norm_num) hm (Ioo_subset_Icc_self hxfull)
        rw [h.extension_eq (by norm_num) hxfull] at he
        have hi := intervalIntegral.integral_mono_interval le_rfl hx.1.le hx.2.le
          (Eventually.of_forall fun _ ↦ sq_nonneg _) hEL
        have hg : ‖G x‖ ^ 2 ≤ (1 - |x|) * EL := by
          rw [abs_of_nonpos hx.2.le, sub_neg_eq_add]
          calc
            _ ≤ (x + 1) * (∫ t in (-1 : ℝ)..x, ‖V t‖ ^ 2) := by simpa using he
            _ ≤ _ := by simpa [EL, add_comm] using
              mul_le_mul_of_nonneg_left hi (by linarith [hx.1] : 0 ≤ x + 1)
        simpa only [abs_of_nonpos hx.2.le, sub_neg_eq_add, add_comm 1 x] using
          correctedBoundary_negative_density_le hxfull hg lam b
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_right]
        norm_num only [neg_add_cancel, zero_add]
        exact hML.2
  have hright : (∫ x in (0 : ℝ)..1, N x) ≤
      ER / 392 + (2 / 3087 + lam ^ 2 / 14) * ‖b‖ ^ 2 := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, correctedNegativeMajorant ER (‖b‖ ^ 2) lam (1 - x) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hNR
          (by simpa using (hMR.1.comp_sub_left 1).symm)
        intro x hx
        have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
        have he := h.extension_sq_le_right (by norm_num) hp (Ioo_subset_Icc_self hxfull)
        rw [h.extension_eq (by norm_num) hxfull] at he
        have hi := intervalIntegral.integral_mono_interval hx.1.le hx.2.le le_rfl
          (Eventually.of_forall fun _ ↦ sq_nonneg _) hER
        have hg : ‖G x‖ ^ 2 ≤ (1 - |x|) * ER := by
          rw [abs_of_nonneg hx.1.le]
          exact he.trans (mul_le_mul_of_nonneg_left hi (by linarith [hx.2]))
        simpa only [abs_of_nonneg hx.1.le] using
          correctedBoundary_negative_density_le hxfull hg lam b
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        norm_num only [sub_self, sub_zero]
        exact hMR.2
  change (∫ x in (-1 : ℝ)..1, N x) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hNL hNR,
    ← intervalIntegral.integral_add_adjacent_intervals hEL hER]
  dsimp [EL, ER] at hleft hright
  linarith

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
