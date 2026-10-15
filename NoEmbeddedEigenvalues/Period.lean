import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The period function of the dipole orbits

Blueprint: `def:period`, `lem:period-integral`; `lem:period` (stated: `L' < 0`, the
elliptic-integral formula, asymptotics; monotonicity is derived from `L' < 0`).

For `0 < h < 1` the orbit on the level `{Ψ = 2h}` in the positive cell takes flow time
`L(h) = ∫₀^{arccos √h} da / √(cos² a - h²)` to go from its point on the axis `a = 0` to
the diagonal; the full period is `S(h) = 8 L(h)`. The substitution `sin a = √(1 - h) t`
gives `L(h) = ∫₀¹ dt / (√(1 - (1 - h) t²) √(1 + h - t²))`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

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

theorem orbitPeriod_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : 0 < orbitPeriod h := by
  have := eighthPeriod_pos h0 h1
  unfold orbitPeriod
  positivity

theorem orbitFrequency_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : 0 < orbitFrequency h := by
  have := orbitPeriod_pos h0 h1
  unfold orbitFrequency
  positivity

/-! ### The period function (`lem:period`, stated) -/

/-- `L` is differentiable on `(0, 1)` with `L' < 0`; in particular `S` has simple level sets. -/
theorem deriv_eighthPeriod_neg {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    DifferentiableAt ℝ eighthPeriod h ∧ deriv eighthPeriod h < 0 := by
  sorry

/-- `L` is strictly decreasing on `(0, 1)`. -/
theorem eighthPeriod_strictAntiOn : StrictAntiOn eighthPeriod (Set.Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · exact fun h hh ↦ (deriv_eighthPeriod_neg hh.1 hh.2).1.continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    exact (deriv_eighthPeriod_neg hh.1 hh.2).2

/-- `S(h) = 4 K(1 - h²)` with `K(m) = ∫₀^{π/2} (1 - m sin² θ)^{-1/2} dθ`. -/
theorem orbitPeriod_eq_ellipticK {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    orbitPeriod h = 4 * ∫ θ in (0 : ℝ)..π / 2, 1 / √(1 - (1 - h ^ 2) * sin θ ^ 2) := by
  sorry

/-- `L(h) = ½ log(4/h) + O(h² log(1/h))` and `L'(h) = -1/(2h) + O(h log(1/h))` as `h → 0`. -/
theorem eighthPeriod_asymptotics : ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Set.Ioo 0 h₀,
    |eighthPeriod h - log (4 / h) / 2| ≤ C * h ^ 2 * log (1 / h) ∧
      |deriv eighthPeriod h + 1 / (2 * h)| ≤ C * h * log (1 / h) := by
  sorry

/-- `e^{L(h)} ≤ C h^{-1/2}` on `(0, 1)`. -/
theorem exp_eighthPeriod_le : ∃ C : ℝ, ∀ h ∈ Set.Ioo (0 : ℝ) 1,
    exp (eighthPeriod h) ≤ C / √h := by
  sorry

end NoEmbeddedEigenvalues
