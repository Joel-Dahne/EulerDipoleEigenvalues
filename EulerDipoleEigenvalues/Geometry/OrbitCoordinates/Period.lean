module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import EulerDipoleEigenvalues.Analysis.Inequalities.SmoothIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The period function of the dipole orbits

Blueprint: `def:period`, `lem:period-integral`, `lem:period-basic`, `lem:period-regularity`,
`lem:period-leading-asymptotic`.
Coarse logarithmic and exponential bounds are proved in `OrbitCoordinates.lean`, after
constructing the flow and proving the half-quarter endpoint estimates.

For `0 < h < 1` the orbit on the level `{Ψ = 2h}` in the positive cell takes flow time
`L(h) = ∫₀^{arccos √h} da / √(cos² a - h²)` to go from its point on the axis `a = 0` to
the diagonal; the full period is `S(h) = 8 L(h)`. The substitution `sin a = √(1 - h) t`
gives `L(h) = ∫₀¹ dt / (√(1 - (1 - h) t²) √(1 + h - t²))`, and hence `L(h) ≤ 1/h`.
This regular quadrature also proves smoothness and strict negativity of the derivative:
its squared denominator has strictly positive `h` derivative on `[0, 1]`.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real intervalIntegral

/-- `L(h) = ∫₀^{arccos √h} da / √(cos² a - h²)`, an eighth of the period. -/
def eighthPeriod (h : ℝ) : ℝ := ∫ a in (0 : ℝ)..arccos (√h), 1 / √(cos a ^ 2 - h ^ 2)

/-- The period `S(h) = 8 L(h)` of the orbit on the level `{Ψ = 2h}`. -/
def orbitPeriod (h : ℝ) : ℝ := 8 * eighthPeriod h

/-- The orbital frequency `b(h) = 2π / S(h)`. -/
def orbitFrequency (h : ℝ) : ℝ := 2 * π / orbitPeriod h

/-- The second formula for `L(h)`, by the substitution `sin a = √(1 - h) t`. -/
theorem eighthPeriod_eq {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    eighthPeriod h = ∫ t in (0 : ℝ)..1, 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)) := by
  set s := √(1 - h) with hs_def
  have hs0 : 0 < s := sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 - h := sq_sqrt (by linarith)
  have hs1 : s < 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact sqrt_lt_sqrt (by linarith) (by linarith)
  -- Bounds on `[0, 1]`.
  have hst : ∀ t ∈ Set.uIcc (0 : ℝ) 1, (s * t) ^ 2 < 1 := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have : s * t ≤ s := by nlinarith [ht.1, ht.2]
    have : 0 ≤ s * t := by nlinarith [ht.1]
    nlinarith
  have hcos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, cos (arcsin (s * t)) ^ 2 = 1 - (s * t) ^ 2 := by
    intro t ht
    rw [cos_arcsin, sq_sqrt (by linarith [hst t ht])]
  have hfact : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cos (arcsin (s * t)) ^ 2 - h ^ 2 = (1 - h) * (1 + h - t ^ 2) := by
    intro t ht
    rw [hcos t ht, mul_pow, hs2]
    ring
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (1 - h) * (1 + h - t ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    apply mul_pos (by linarith)
    nlinarith [ht.1, ht.2]
  -- The substitution `a = arcsin (s t)`.
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t ↦ arcsin (s * t))
      (1 / √(1 - (s * t) ^ 2) * s) t := by
    intro t ht
    have h1 : s * t ≠ -1 := by intro h; nlinarith [hst t ht]
    have h2 : s * t ≠ 1 := by intro h; nlinarith [hst t ht]
    convert (hasDerivAt_arcsin h1 h2).comp t ((hasDerivAt_id t).const_mul s) using 1
    · rfl
    · rw [mul_one]
  have hcont' : ContinuousOn (fun t ↦ 1 / √(1 - (s * t) ^ 2) * s) (Set.uIcc 0 1) := by
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact (sqrt_pos.2 (by linarith [hst t ht])).ne'
  have hcontg : ContinuousOn (fun a ↦ 1 / √(cos a ^ 2 - h ^ 2))
      ((fun t ↦ arcsin (s * t)) '' Set.uIcc 0 1) := by
    rintro _ ⟨t, ht, rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    rw [hfact t ht]
    exact (sqrt_pos.2 (hpos t ht)).ne'
  have hsub := integral_comp_mul_deriv' hderiv hcont' hcontg
  have hend : arcsin (s * 1) = arccos √h := by
    rw [mul_one, arccos_eq_arcsin (sqrt_nonneg h), sq_sqrt h0.le]
  simp only [mul_zero, arcsin_zero, hend] at hsub
  rw [eighthPeriod, ← hsub]
  apply integral_congr
  intro t ht
  simp only [Function.comp_apply]
  rw [hfact t ht, sqrt_mul (by linarith), ← hs_def]
  have hA : 0 < √(1 + h - t ^ 2) := by
    have := hpos t ht
    exact sqrt_pos.2 (by nlinarith)
  have hB : 0 < √(1 - (s * t) ^ 2) := sqrt_pos.2 (by linarith [hst t ht])
  rw [mul_pow, hs2] at hB ⊢
  field_simp

/-- `L(h) > 0`, so the period and the frequency are positive. -/
theorem eighthPeriod_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : 0 < eighthPeriod h := by
  rw [eighthPeriod_eq h0 h1]
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - (1 - h) * t ^ 2 := fun t ht ↦ by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 1 - h)]
  have hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + h - t ^ 2 := fun t ht ↦ by
    nlinarith [ht.1, ht.2]
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)))
      (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact (mul_pos (sqrt_pos.2 (hA t ht)) (sqrt_pos.2 (hB t ht))).ne'
  refine intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc zero_le_one)
    (fun t ht ↦ ?_) zero_lt_one
  have ht' := Set.Ioo_subset_Icc_self ht
  exact one_div_pos.2 (mul_pos (sqrt_pos.2 (hA t ht')) (sqrt_pos.2 (hB t ht')))

/-- `L(h) ≤ 1/h`: in the second formula for `L(h)` both square roots are at least `√h`. -/
theorem eighthPeriod_le_inv {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : eighthPeriod h ≤ 1 / h := by
  rw [eighthPeriod_eq h0 h1]
  have hpos : 0 < √h := Real.sqrt_pos.2 h0
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, √h ≤ √(1 - (1 - h) * t ^ 2) ∧ √h ≤ √(1 + h - t ^ 2) := by
    intro t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact ⟨Real.sqrt_le_sqrt (by nlinarith), Real.sqrt_le_sqrt (by linarith)⟩
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)))
      (Set.Icc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun t ht ↦ ?_
    exact (mul_pos (hpos.trans_le (hlow t ht).1) (hpos.trans_le (hlow t ht).2)).ne'
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)) ≤ 1 / h := by
    intro t ht
    obtain ⟨hA, hB⟩ := hlow t ht
    have hsh : √h * √h = h := Real.mul_self_sqrt h0.le
    apply one_div_le_one_div_of_le h0
    nlinarith [mul_le_mul hA hB hpos.le (hpos.le.trans hA)]
  calc (∫ t in (0 : ℝ)..1, 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)))
      ≤ ∫ t in (0 : ℝ)..1, 1 / h :=
        intervalIntegral.integral_mono_on zero_le_one
          (hcont.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const hb
    _ = 1 / h := by simp

private theorem integral_periodLogModel {h : ℝ} (h0 : 0 < h) :
    (∫ t in (0 : ℝ)..1, 1 / (-2 * t + (2 + h))) = log ((2 + h) / h) / 2 := by
  rw [intervalIntegral.integral_comp_mul_add (f := fun x ↦ 1 / x) (by norm_num : (-2 : ℝ) ≠ 0),
    integral_one_div_of_pos (by linarith) (by linarith)]
  rw [smul_eq_mul, mul_zero, zero_add, mul_one, show -2 + (2 + h) = h by ring,
    show h / (2 + h) = ((2 + h) / h)⁻¹ by field_simp, log_inv]
  ring

/-- `L(h) ≥ ½ log(1/h)`. In the second formula for `L(h)` both square roots are at most
`√(1 - t² + h)`, and `1 - t² + h ≤ 2(1 - t) + h` on `[0, 1]`, so
`L(h) ≥ ∫₀¹ dt / (2(1 - t) + h) = ½ log((2 + h)/h)`. -/
theorem log_le_eighthPeriod {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    log (1 / h) / 2 ≤ eighthPeriod h := by
  rw [eighthPeriod_eq h0 h1]
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - (1 - h) * t ^ 2 := fun t ht ↦ by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 1 - h)]
  have hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + h - t ^ 2 := fun t ht ↦ by
    nlinarith [ht.1, ht.2]
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)))
      (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact (mul_pos (sqrt_pos.2 (hA t ht)) (sqrt_pos.2 (hB t ht))).ne'
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < -2 * t + (2 + h) := fun t ht ↦ by linarith [ht.2]
  have hcont' : ContinuousOn (fun t : ℝ ↦ 1 / (-2 * t + (2 + h))) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) fun t ht ↦ (hD t ht).ne'
  calc log (1 / h) / 2 ≤ log ((2 + h) / h) / 2 := by
        refine div_le_div_of_nonneg_right (log_le_log (by positivity) ?_) (by norm_num)
        exact div_le_div_of_nonneg_right (by linarith) h0.le
    _ = ∫ t in (0 : ℝ)..1, 1 / (-2 * t + (2 + h)) := (integral_periodLogModel h0).symm
    _ ≤ ∫ t in (0 : ℝ)..1, 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)) := by
      refine intervalIntegral.integral_mono_on zero_le_one
        (hcont'.intervalIntegrable_of_Icc zero_le_one)
        (hcont.intervalIntegrable_of_Icc zero_le_one) fun t ht ↦ ?_
      have hc : 0 ≤ 1 - t ^ 2 + h := by nlinarith [ht.1, ht.2]
      have hle : √(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2) ≤ -2 * t + (2 + h) := by
        have h1' : √(1 - (1 - h) * t ^ 2) ≤ √(1 - t ^ 2 + h) :=
          sqrt_le_sqrt (by
            nlinarith [mul_le_mul_of_nonneg_left (show t ^ 2 ≤ 1 by nlinarith [ht.1, ht.2]) h0.le])
        have h2' : √(1 + h - t ^ 2) = √(1 - t ^ 2 + h) := by ring_nf
        rw [h2']
        calc √(1 - (1 - h) * t ^ 2) * √(1 - t ^ 2 + h) ≤ √(1 - t ^ 2 + h) * √(1 - t ^ 2 + h) :=
              mul_le_mul_of_nonneg_right h1' (sqrt_nonneg _)
          _ = 1 - t ^ 2 + h := mul_self_sqrt hc
          _ ≤ -2 * t + (2 + h) := by nlinarith [ht.1, ht.2]
      exact one_div_le_one_div_of_le (mul_pos (sqrt_pos.2 (hA t ht)) (sqrt_pos.2 (hB t ht))) hle

open Filter Topology in
/-- `L` is continuous on `(0, 1)`: dominated convergence in the second formula, whose integrand
is at most `1/h`. -/
theorem continuousOn_eighthPeriod : ContinuousOn eighthPeriod (Set.Ioo 0 1) := by
  intro h₀ hh₀
  apply ContinuousAt.continuousWithinAt
  set F : ℝ → ℝ → ℝ := fun h t ↦ 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2))
  have he : eighthPeriod =ᶠ[𝓝 h₀] fun h ↦ ∫ t in (0 : ℝ)..1, F h t := by
    filter_upwards [Ioo_mem_nhds hh₀.1 hh₀.2] with h hh using eighthPeriod_eq hh.1 hh.2
  refine ContinuousAt.congr ?_ he.symm
  have hnear : ∀ᶠ h in 𝓝 h₀, h ∈ Set.Ioo (h₀ / 2) 1 :=
    Ioo_mem_nhds (by linarith [hh₀.1]) hh₀.2
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ ↦ 2 / h₀)
    (Eventually.of_forall fun h ↦ (by fun_prop : Measurable (F h)).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_
  · filter_upwards [hnear] with h hh
    refine Eventually.of_forall fun t ht ↦ ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h0 : 0 < h := by linarith [hh.1, hh₀.1]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hA : √h ≤ √(1 - (1 - h) * t ^ 2) := sqrt_le_sqrt (by
      nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith [hh.2] : (0 : ℝ) ≤ 1 - h)])
    have hB : √h ≤ √(1 + h - t ^ 2) := sqrt_le_sqrt (by linarith)
    have hpos : 0 < √h := sqrt_pos.2 h0
    have hprod : h ≤ √(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2) := by
      calc h = √h * √h := (mul_self_sqrt h0.le).symm
        _ ≤ _ := mul_le_mul hA hB hpos.le (hpos.le.trans hA)
    have hF : 0 ≤ F h t := by simp only [F]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hF]
    calc F h t ≤ 1 / h := one_div_le_one_div_of_le h0 hprod
      _ ≤ 2 / h₀ := by
        rw [div_le_div_iff₀ h0 (by linarith [hh₀.1])]
        linarith [hh.1]
  · refine Eventually.of_forall fun t ht ↦ ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hA : 0 < 1 - (1 - h₀) * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith [hh₀.2] : (0 : ℝ) ≤ 1 - h₀),
        hh₀.1]
    have hB : 0 < 1 + h₀ - t ^ 2 := by linarith [hh₀.1]
    exact continuousAt_const.div (by fun_prop)
      (mul_pos (sqrt_pos.2 hA) (sqrt_pos.2 hB)).ne'

/-- The period is continuous on `(0, 1)`. -/
theorem continuousOn_orbitPeriod : ContinuousOn orbitPeriod (Set.Ioo 0 1) :=
  continuousOn_eighthPeriod.const_smul (8 : ℝ)

open Filter Topology in
/-- The period tends to infinity at the separatrix. -/
theorem tendsto_orbitPeriod_atTop : Tendsto orbitPeriod (𝓝[>] 0) atTop := by
  have hl : Tendsto (fun h : ℝ ↦ 4 * log (1 / h)) (𝓝[>] 0) atTop := by
    simp only [one_div]
    exact (tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hl
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  have := log_le_eighthPeriod hh.1 hh.2
  unfold orbitPeriod
  linarith

theorem orbitPeriod_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : 0 < orbitPeriod h := by
  have := eighthPeriod_pos h0 h1
  unfold orbitPeriod
  positivity

theorem orbitFrequency_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : 0 < orbitFrequency h := by
  have := orbitPeriod_pos h0 h1
  unfold orbitFrequency
  positivity

/-! ### Differentiation of the regular fixed-interval quadrature -/

open Filter Topology Set Metric
open scoped ContDiff

/-- The squared denominator in the regular quadrature. -/
def periodDenom (q : ℝ × ℝ) : ℝ :=
  (1 - (1 - q.1) * q.2 ^ 2) * (1 + q.1 - q.2 ^ 2)

private theorem period_radicands_pos {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - (1 - h) * t ^ 2 ∧ 0 < 1 + h - t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ht2 (by linarith [hh.2] : (0 : ℝ) ≤ 1 - h), hh.1]
  · linarith [hh.1]

/-- The regular squared denominator is positive on every physical vertical segment. -/
theorem periodDenom_pos {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < periodDenom (h, t) := by
  obtain ⟨hA, hB⟩ := period_radicands_pos hh ht
  exact mul_pos hA hB

/-- Smoothness of the regular integrand wherever its squared denominator is positive. -/
theorem contDiffOn_periodIntegrand :
    ContDiffOn ℝ ∞ (fun q ↦ 1 / √(periodDenom q)) {q | 0 < periodDenom q} := by
  have hQ : ContDiff ℝ ∞ periodDenom := by unfold periodDenom; fun_prop
  exact contDiffOn_const.div (hQ.contDiffOn.sqrt (fun q hq ↦ ne_of_gt hq))
    (fun q hq ↦ (sqrt_pos.2 hq).ne')

/-- The fixed-interval quadrature with a single squared denominator. -/
theorem eighthPeriod_eq_regular {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    eighthPeriod h = ∫ t in (0 : ℝ)..1, 1 / √(periodDenom (h, t)) := by
  rw [eighthPeriod_eq hh.1 hh.2]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  dsimp only [periodDenom]
  rw [sqrt_mul (period_radicands_pos hh ht).1.le]

/-- `L` is smooth on `(0, 1)`, by its regular fixed-interval quadrature. -/
theorem contDiffOn_eighthPeriod : ContDiffOn ℝ ∞ eighthPeriod (Ioo 0 1) := by
  have hU : IsOpen {q | 0 < periodDenom q} := by
    apply isOpen_lt continuous_const
    unfold periodDenom; fun_prop
  exact (contDiffOn_integral_unitInterval hU isOpen_Ioo
    (fun q hq ↦ periodDenom_pos hq.1 hq.2) contDiffOn_periodIntegrand).congr
      (fun h hh ↦ eighthPeriod_eq_regular hh)

/-- The period function is smooth on `(0, 1)`. -/
theorem contDiffOn_orbitPeriod : ContDiffOn ℝ ∞ orbitPeriod (Ioo 0 1) :=
  contDiffOn_eighthPeriod.const_smul (8 : ℝ)

/-- `L` is differentiable on `(0, 1)` with `L' < 0`; in particular `S` has simple level sets. -/
theorem deriv_eighthPeriod_neg {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    DifferentiableAt ℝ eighthPeriod h ∧ deriv eighthPeriod h < 0 := by
  let F : ℝ × ℝ → ℝ := fun q ↦ 1 / √(periodDenom q)
  let G : ℝ → ℝ := fun t ↦ fderiv ℝ F (h, t) (1, 0)
  have hF : ContDiffOn ℝ ∞ F {q | 0 < periodDenom q} := contDiffOn_periodIntegrand
  have hU : IsOpen {q | 0 < periodDenom q} := by
    apply isOpen_lt continuous_const
    unfold periodDenom; fun_prop
  have hd : HasDerivAt eighthPeriod (∫ t in (0 : ℝ)..1, G t) h := by
    have hd := hasDerivAt_integral_smooth hU hF (h := h) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩; rcases mem_singleton_iff.1 hx with rfl
      exact periodDenom_pos ⟨h0, h1⟩ ht)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    exact eighthPeriod_eq_regular hx
  have hGc : ContinuousOn G (Icc 0 1) :=
    ((hF.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const).continuousOn.comp
      (by fun_prop) (fun t ht ↦ periodDenom_pos ⟨h0, h1⟩ ht)
  have hGn : ∀ t ∈ Icc (0 : ℝ) 1, G t < 0 := by
    intro t ht
    obtain ⟨hA, hB⟩ := period_radicands_pos ⟨h0, h1⟩ ht
    have hQpos := periodDenom_pos ⟨h0, h1⟩ ht
    have hroot : 0 < √(periodDenom (h, t)) := sqrt_pos.2 hQpos
    have hdA : HasDerivAt (fun x : ℝ ↦ 1 - (1 - x) * t ^ 2) (t ^ 2) h := by
      convert! (hasDerivAt_const h (1 : ℝ)).sub
        (((hasDerivAt_const h (1 : ℝ)).sub (hasDerivAt_id h)).mul_const (t ^ 2)) using 1
      ring
    have hdB : HasDerivAt (fun x : ℝ ↦ 1 + x - t ^ 2) 1 h := by
      simpa using! ((hasDerivAt_const h (1 : ℝ)).add (hasDerivAt_id h)).sub_const (t ^ 2)
    have hdQ : HasDerivAt (fun x ↦ periodDenom (x, t))
        (t ^ 2 * (1 + h - t ^ 2) + (1 - (1 - h) * t ^ 2)) h := by
      simpa [periodDenom] using! hdA.mul hdB
    have hdF := (hdQ.sqrt hQpos.ne').inv hroot.ne'
    have hdG : HasDerivAt (fun x ↦ F (x, t)) (G t) h := by
      have hder : HasFDerivAt F (fderiv ℝ F (h, t)) (h, t) :=
        ((hF.contDiffAt (hU.mem_nhds hQpos)).differentiableAt (by simp)).hasFDerivAt
      exact hder.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h t))
    have he := hdG.unique (by simpa only [F, one_div] using! hdF)
    rw [he]
    have hN : 0 < t ^ 2 * (1 + h - t ^ 2) + (1 - (1 - h) * t ^ 2) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg t) hB.le) hA
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hN (by positivity))) (by positivity)
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hlt := integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one hGc
    (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Icc 0 1))
    (fun t ht ↦ (hGn t (Ioc_subset_Icc_self ht)).le)
    ⟨0, ⟨le_rfl, zero_le_one⟩, hGn 0 ⟨le_rfl, zero_le_one⟩⟩
  simpa using hlt

/-- `L` is strictly decreasing on `(0, 1)`. -/
theorem eighthPeriod_strictAntiOn : StrictAntiOn eighthPeriod (Set.Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · exact fun h hh ↦ (deriv_eighthPeriod_neg hh.1 hh.2).1.continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    exact (deriv_eighthPeriod_neg hh.1 hh.2).2

/-- `S' = 8L' < 0` on `(0, 1)`. -/
theorem deriv_orbitPeriod_neg {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    DifferentiableAt ℝ orbitPeriod h ∧ deriv orbitPeriod h < 0 := by
  obtain ⟨hd, hneg⟩ := deriv_eighthPeriod_neg h0 h1
  have hS : HasDerivAt orbitPeriod (8 * deriv eighthPeriod h) h :=
    hd.hasDerivAt.const_mul 8
  exact ⟨hS.differentiableAt, hS.deriv ▸ mul_neg_of_pos_of_neg (by norm_num) hneg⟩

/-- The full period is strictly decreasing on `(0, 1)`. -/
theorem orbitPeriod_strictAntiOn : StrictAntiOn orbitPeriod (Ioo 0 1) := by
  intro h hh k hk hhk
  exact mul_lt_mul_of_pos_left (eighthPeriod_strictAntiOn hh hk hhk) (by norm_num)

/-! ### Further period estimates -/

/-- The remainder after subtracting the integrable logarithmic model at each `h > 0`. -/
private def periodLogRemainder (h t : ℝ) : ℝ :=
  1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)) - 1 / (-2 * t + (2 + h))

private theorem periodLogRemainder_bounds {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ periodLogRemainder h t ∧ periodLogRemainder h t ≤ 1 := by
  let A := 1 - (1 - h) * t ^ 2
  let B := 1 + h - t ^ 2
  let M := -2 * t + (2 + h)
  obtain ⟨hA, hB⟩ : 0 < A ∧ 0 < B := period_radicands_pos hh ht
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hAB : A ≤ B := by
    dsimp [A, B]
    nlinarith only [mul_nonneg hh.1.le (sub_nonneg.mpr ht2)]
  have hBM : B ≤ M := by dsimp [B, M]; nlinarith only [sq_nonneg (1 - t)]
  have hM := hB.trans_le hBM
  have hprodA : A ≤ √A * √B := calc
    A = √A * √A := (mul_self_sqrt hA.le).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hAB) (sqrt_nonneg A)
  have hprodM : √A * √B ≤ M := calc
    √A * √B ≤ √B * √B := mul_le_mul_of_nonneg_right (sqrt_le_sqrt hAB) (sqrt_nonneg B)
    _ = B := mul_self_sqrt hB.le
    _ ≤ M := hBM
  change 0 ≤ 1 / (√A * √B) - 1 / M ∧ 1 / (√A * √B) - 1 / M ≤ 1
  refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le (hA.trans_le hprodA) hprodM), ?_⟩
  have hgap : M - A ≤ A * M := calc
    M - A ≤ (1 - t ^ 2) * M := by
      dsimp [A, M]
      have h : 0 ≤ (1 - t) ^ 2 * (1 + 2 * t) :=
        mul_nonneg (sq_nonneg _) (by linarith [ht.1])
      nlinarith only [h]
    _ ≤ A * M := by
      apply mul_le_mul_of_nonneg_right _ hM.le
      dsimp [A]
      nlinarith only [mul_nonneg hh.1.le (sq_nonneg t)]
  calc
    1 / (√A * √B) - 1 / M ≤ 1 / A - 1 / M := by
      exact sub_le_sub_right (one_div_le_one_div_of_le hA hprodA) _
    _ = (M - A) / (A * M) := by field_simp
    _ ≤ 1 := (div_le_one (mul_pos hA hM)).2 hgap

open Filter Topology MeasureTheory in
private theorem tendsto_integral_periodLogRemainder :
    Tendsto (fun h ↦ ∫ t in (0 : ℝ)..1, periodLogRemainder h t) (𝓝[>] 0) (𝓝 (log 2 / 2)) := by
  have hc : ContinuousWithinAt (fun h ↦ ∫ t in (0 : ℝ)..1, periodLogRemainder h t) (Ioi 0) 0 := by
    refine continuousWithinAt_of_dominated_interval (bound := fun _ ↦ 1)
      (Eventually.of_forall fun h ↦ (by unfold periodLogRemainder; fun_prop :
        Measurable (periodLogRemainder h)).aestronglyMeasurable)
      ?_ intervalIntegrable_const ?_
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
      refine Eventually.of_forall fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      obtain ⟨h₀, h₁⟩ := periodLogRemainder_bounds hh (Ioc_subset_Icc_self ht)
      rwa [Real.norm_eq_abs, abs_of_nonneg h₀]
    · filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have htlt := lt_of_le_of_ne ht.2 ht1
      have htq : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr htlt) (by linarith [ht.1] : 0 < 1 + t)]
      unfold periodLogRemainder
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.sub
      · apply ContinuousAt.div continuousAt_const (by fun_prop)
        simpa using (sqrt_pos.2 htq).ne'
      · exact continuousAt_const.div (by fun_prop) (by simp; linarith)
  have hval : (∫ t in (0 : ℝ)..1, periodLogRemainder 0 t) = log 2 / 2 := calc
    _ = ∫ t in (0 : ℝ)..1, (1 / 2) * (1 / (t + 1)) := by
      apply integral_congr_Ioo_of_le zero_le_one
      intro t ht
      have htq : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < 1 + t)]
      have hdiff : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
      have htadd : t + 1 ≠ 0 := by linarith [ht.1]
      change 1 / (√(1 - (1 - 0) * t ^ 2) * √(1 + 0 - t ^ 2)) -
        1 / (-2 * t + (2 + 0)) = (1 / 2) * (1 / (t + 1))
      simp only [sub_zero, one_mul, add_zero, mul_self_sqrt htq.le]
      rw [show 1 - t ^ 2 = (1 - t) * (t + 1) by ring, show -2 * t + 2 = 2 * (1 - t) by ring]
      field_simp
      ring
    _ = log 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_comp_add_right (f := fun x ↦ 1 / x),
        integral_one_div_of_pos (by norm_num) (by norm_num)]
      norm_num [div_eq_mul_inv, mul_comm]
  rw [← hval]
  exact hc

/-- Leading value asymptotic from the fixed-interval quadrature, without a sharp
remainder or any claim about its derivative (`lem:period-leading-asymptotic`). -/
theorem eighthPeriod_leading_asymptotic :
    Tendsto (fun h ↦ eighthPeriod h - log (4 / h) / 2) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun h : ℝ ↦ log (2 + h) / 2 - log 4 / 2) (𝓝[>] 0)
      (𝓝 (log 2 / 2 - log 4 / 2)) := by
    have hc : ContinuousAt (fun h : ℝ ↦ log (2 + h) / 2 - log 4 / 2) 0 := by
      fun_prop (disch := norm_num)
    simpa using hc.continuousWithinAt.tendsto (s := Ioi 0)
  have hsum := tendsto_integral_periodLogRemainder.add hlog
  have hfour : log 4 = log 2 + log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num)]
  rw [show log 2 / 2 + (log 2 / 2 - log 4 / 2) = 0 by rw [hfour]; ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
  have hF : IntervalIntegrable (fun t ↦ 1 / (√(1 - (1 - h) * t ^ 2) * √(1 + h - t ^ 2)))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    refine continuousOn_const.div (by fun_prop) fun t ht ↦ ?_
    obtain ⟨hA, hB⟩ := period_radicands_pos hh ht
    exact (mul_pos (sqrt_pos.2 hA) (sqrt_pos.2 hB)).ne'
  have hM : IntervalIntegrable (fun t ↦ 1 / (-2 * t + (2 + h))) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    refine continuousOn_const.div (by fun_prop) fun t ht ↦ ?_
    linarith [hh.1, ht.2]
  change (∫ t in (0 : ℝ)..1, periodLogRemainder h t) + (log (2 + h) / 2 - log 4 / 2) =
    eighthPeriod h - log (4 / h) / 2
  unfold periodLogRemainder
  rw [eighthPeriod_eq hh.1 hh.2, integral_sub hF hM,
    integral_periodLogModel hh.1, log_div (by linarith [hh.1]) hh.1.ne',
    log_div (by norm_num : (4 : ℝ) ≠ 0) hh.1.ne']
  ring

/-- The corresponding leading value asymptotic for the full orbit period. -/
theorem orbitPeriod_leading_asymptotic :
    Tendsto (fun h ↦ orbitPeriod h - 4 * log (4 / h)) (𝓝[>] 0) (𝓝 0) := by
  have h := eighthPeriod_leading_asymptotic.const_mul 8
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun h ↦ ?_)
  unfold orbitPeriod
  ring

end EulerDipoleEigenvalues
