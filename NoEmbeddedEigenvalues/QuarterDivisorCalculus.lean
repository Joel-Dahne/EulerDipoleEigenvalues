import NoEmbeddedEigenvalues.QuarterScalars
import NoEmbeddedEigenvalues.PeriodDerivativeBounds

/-!
# Quantitative derivatives of the quarter divisor

Blueprint: `lem:quarter-divisor-derivatives`.

The unit modulus of the exponential removes dependence on the character and
phase value. Coarse period derivatives give inverse first- and second-power
bounds, uniformly for either sign of the spectral parameter.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- Smoothness of the actual quarter divisor on the regular level interval. -/
theorem contDiffOn_quarterDivisor (lam : ℝ) (κ : ℂ) :
    ContDiffOn ℝ ∞ (quarterDivisor lam κ) (Ioo 0 1) := by
  apply contDiffOn_const.sub
  apply ContDiffOn.cexp
  exact contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul contDiffOn_eighthPeriod))

private theorem divisor_second_bound (lam : ℝ) (κ : ℂ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖deriv (quarterDivisor lam κ) x‖ = 2 * |lam| * |deriv eighthPeriod x| ∧
      ‖deriv (deriv (quarterDivisor lam κ)) x‖ ≤
        (2 * |lam| * |deriv eighthPeriod x|) ^ 2 +
          2 * |lam| * |deriv (deriv eighthPeriod) x| := by
  let w := fun h ↦ Complex.I * ((2 * lam * eighthPeriod h : ℝ) : ℂ)
  let w₁ := fun h ↦ Complex.I * ((2 * lam * deriv eighthPeriod h : ℝ) : ℂ)
  let w₂ := fun h ↦ Complex.I * ((2 * lam * deriv (deriv eighthPeriod) h : ℝ) : ℂ)
  have hw (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) : HasDerivAt w (w₁ h) h := by
    exact ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt h
      ((deriv_eighthPeriod_neg hh.1 hh.2).1.hasDerivAt.const_mul (2 * lam))).const_mul Complex.I)
  have hw₁ : HasDerivAt w₁ (w₂ x) x := by
    have hd := ((contDiffOn_eighthPeriod.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp)).contDiffAt
      (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp)
    exact ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (hd.hasDerivAt.const_mul (2 * lam))).const_mul Complex.I)
  have hd (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (quarterDivisor lam κ) (-(Complex.exp (w h) * w₁ h)) h := by
    simpa only [quarterDivisor, quarterPhase, w, Pi.sub_apply, zero_sub] using!
      (hasDerivAt_const h κ).sub ((hw h hh).cexp)
  have hd' := ((hw x hx).cexp.neg.mul hw₁)
  have hD : HasDerivAt (deriv (quarterDivisor lam κ))
      (-(Complex.exp (w x) * w₁ x) * w₁ x + -Complex.exp (w x) * w₂ x) x := by
    apply hd'.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul] using (hd y hy).deriv
  have he : ‖Complex.exp (w x)‖ = 1 := by
    simp [w, Complex.norm_exp, Complex.mul_re]
  have hn₁ : ‖w₁ x‖ = 2 * |lam| * |deriv eighthPeriod x| := by
    simp [w₁, Complex.norm_real, Real.norm_eq_abs]
  have hn₂ : ‖w₂ x‖ = 2 * |lam| * |deriv (deriv eighthPeriod) x| := by
    simp [w₂, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, ?_⟩
  · rw [(hd x hx).deriv, norm_neg, norm_mul, he, one_mul, hn₁]
  · rw [hD.deriv]
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_mul, norm_neg, he, one_mul, hn₁, hn₂, pow_two])

/-- Constants independent of the character control both divisor derivatives. -/
theorem quarterDivisor_derivative_bounds {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ r < 1 ∧
      ∀ (κ : ℂ) (x : ℝ), x ∈ Ioo 0 r →
        c ≤ x * ‖deriv (quarterDivisor lam κ) x‖ ∧
        x * ‖deriv (quarterDivisor lam κ) x‖ ≤ C ∧
        x ^ 2 * ‖deriv (deriv (quarterDivisor lam κ)) x‖ ≤ C := by
  obtain ⟨c, C, r, hc, hC, hr, hr1, hb⟩ := eighthPeriod_derivative_bounds
  let A := 2 * |lam|
  have hA : 0 < A := mul_pos (by norm_num) (abs_pos.2 hlam)
  let B := A * C
  let T := B ^ 2 + B + 1
  have hB : 0 < B := mul_pos hA hC
  refine ⟨A * c, T, r, mul_pos hA hc, by dsimp [T]; positivity, hr, hr1, ?_⟩
  intro κ x hx
  obtain ⟨hl, hu, hsecond⟩ := hb x hx
  obtain ⟨he, hD₂⟩ := divisor_second_bound lam κ ⟨hx.1, hx.2.trans hr1⟩
  have hn : |deriv eighthPeriod x| = -deriv eighthPeriod x :=
    abs_of_neg (deriv_eighthPeriod_neg hx.1 (hx.2.trans hr1)).2
  have hfirst : A * c ≤ x * ‖deriv (quarterDivisor lam κ) x‖ ∧
      x * ‖deriv (quarterDivisor lam κ) x‖ ≤ B := by
    rw [he, hn]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hA.le,
      mul_le_mul_of_nonneg_left hu hA.le]
  refine ⟨hfirst.1, hfirst.2.trans ?_, ?_⟩
  · dsimp [T]; nlinarith [sq_nonneg B]
  · have hs : (x * (A * |deriv eighthPeriod x|)) ^ 2 ≤ B ^ 2 := by
      apply (sq_le_sq₀ (mul_nonneg hx.1.le (mul_nonneg hA.le (abs_nonneg _))) hB.le).2
      simpa only [he] using hfirst.2
    have hm := mul_le_mul_of_nonneg_left hD₂ (sq_nonneg x)
    have hm₂ := mul_le_mul_of_nonneg_left hsecond hA.le
    dsimp only [T, B, A] at *
    nlinarith

end NoEmbeddedEigenvalues
