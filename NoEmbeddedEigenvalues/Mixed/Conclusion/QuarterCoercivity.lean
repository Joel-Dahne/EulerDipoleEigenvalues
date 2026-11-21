import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedComparisonForm

/-! # Coercivity on a mixed comparison quarter -/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory ComplexConjugate Filter
open scoped Topology
open scoped ContDiff

local notation "L" => (Real.pi / 2)
local notation "Q" => mixedQuarterCell
local notation "S" => (Ioo (0 : ℝ) L)

private theorem mixed_exp_partials {q : ℝ × ℝ} (hs : 0 < q.1 + q.2) :
    partialX (fun p ↦ Real.exp (mixedOddAExponent p)) q =
      Real.exp (mixedOddAExponent q) * partialX mixedOddAExponent q ∧
    partialY (fun p ↦ Real.exp (mixedOddAExponent p)) q =
      Real.exp (mixedOddAExponent q) * partialY mixedOddAExponent q := by
  have h := (mixedOddAExponent_contDiffAt (n := 1) hs).differentiableAt (by norm_num)
  have hx := h.comp q.1 (show DifferentiableAt ℝ (fun x : ℝ ↦ (x, q.2)) q.1 by fun_prop)
  have hy := h.comp q.2 (show DifferentiableAt ℝ (fun y : ℝ ↦ (q.1, y)) q.2 by fun_prop)
  exact ⟨hx.hasDerivAt.exp.deriv, hy.hasDerivAt.exp.deriv⟩

/-- The two explicit multipliers meet the regularity and boundedness
hypotheses for logarithmic Robin comparison. -/
theorem mixed_explicit_robin_multipliers :
    MixedRobinMultiplier (fun q ↦ Real.exp (mixedOddAExponent q)) ∧
    MixedRobinMultiplier mixedOddBMultiplier := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn mixedOddAExponent K := mixedOddAExponent_continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hM' (q : ℝ × ℝ) (hq : q ∈ K) :
      Real.exp (-M) ≤ Real.exp (mixedOddAExponent q) ∧
        Real.exp (mixedOddAExponent q) ≤ Real.exp M := by
    have hb : |mixedOddAExponent q| ≤ M := by simpa only [Real.norm_eq_abs] using hM q hq
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp hb).1, Real.exp_le_exp.mpr (abs_le.mp hb).2⟩
  constructor
  · refine ⟨?_, Real.continuous_exp.comp_continuousOn hcont,
      ⟨Real.exp (-M), Real.exp M, Real.exp_pos _, hM'⟩, ?_⟩
    · refine ⟨{q | 0 < q.1 + q.2}, isOpen_lt continuous_const
        (continuous_fst.add continuous_snd), fun q hq ↦ ?_, fun q hq ↦ ?_⟩
      · exact add_pos_of_pos_of_nonneg hq.1.1 hq.2.1
      · exact (Real.contDiff_exp.contDiffAt.comp q
          (mixedOddAExponent_contDiffAt hq)).contDiffWithinAt
    · obtain ⟨C, hC, hb⟩ := mixed_odd_a_exponent_bounds_regular
      refine ⟨2 * Real.exp M * C, by positivity, fun q hq ↦ ?_⟩
      obtain ⟨hx, hy⟩ := mixed_exp_partials (add_pos_of_pos_of_nonneg hq.1.1 hq.2.1)
      obtain ⟨_, hbx, hby⟩ := hb q hq
      have hE := (hM' q ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩).2
      rw [hx, hy, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ Real.exp M * C + Real.exp M * C :=
          add_le_add (mul_le_mul hE hbx (abs_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul hE hby (abs_nonneg _) (Real.exp_pos _).le)
        _ = 2 * Real.exp M * C := by ring
        _ ≤ _ := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (abs_nonneg _))
  · refine ⟨?_, mixedOddBMultiplier_continuous.continuousOn,
      ⟨3 / 4, 5 / 3, by norm_num, fun _ hq ↦ mixed_odd_b_multiplier_closed_bounds hq⟩,
      mixed_odd_b_multiplier_derivative_bound⟩
    exact ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst, fun _ hq ↦ hq.1.1,
      fun _ hq ↦ (mixedOddBMultiplier_contDiffAt hq).contDiffWithinAt⟩

/-- The Robin numerator of the exponential multiplier, with its positive
exponential factored out. -/
private theorem mixed_odd_a_robin_exp {h : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) :
    0 ≤ mixedRobinNumerator true (fun q ↦ Real.exp (mixedOddAExponent q)) h := by
  obtain ⟨hx', hy'⟩ := mixed_exp_partials (q := (h, 0)) (by simpa using hh.1)
  unfold mixedRobinNumerator
  simp only [ite_true, hx', hy']
  have hsign : 0 ≤ 3 * h - 2 * (1 - h ^ 2) * partialX mixedOddAExponent (h, 0) -
      (2 - h ^ 2) * partialY mixedOddAExponent (h, 0) :=
    (div_nonneg hh.1.le (by norm_num) : 0 ≤ h / 250).trans (mixed_odd_a_robin h hh)
  convert mul_nonneg (Real.exp_pos (mixedOddAExponent (h, 0))).le hsign using 1; ring

/-- Both certified quarter comparisons give the common lower bound 1/200. -/
theorem mixed_quarter_coercivity (oddA : Bool) {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ}
    (hz : MixedQuarterFormDomain z za zb top) (hzero : MixedQuarterZeroTrace oddA z) :
    (1 / 200 : ℝ) * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      mixedQuarterForm z za zb top := by
  cases oddA
  · have h := mixed_robin_comparison false mixed_explicit_robin_multipliers.2
      (c := 1 / 100) (fun _ hq ↦ mixed_odd_b_interior hq)
      (fun h hh ↦ (mul_nonneg (by norm_num) hh.1.le : 0 ≤ 1789 / 2500 * h).trans
        (mixed_odd_b_multiplier_robin.2 h hh)) hz hzero
    exact (mul_le_mul_of_nonneg_right (by norm_num)
      (integral_nonneg fun _ ↦ by positivity)).trans h
  · exact mixed_robin_comparison true mixed_explicit_robin_multipliers.1
      (fun _ hq ↦ mixed_odd_a_interior hq) (fun _ hh ↦ mixed_odd_a_robin_exp hh) hz hzero

end NoEmbeddedEigenvalues
