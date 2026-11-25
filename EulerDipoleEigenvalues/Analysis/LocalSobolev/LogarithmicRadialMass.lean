module

public import EulerDipoleEigenvalues.Transport.WeightedGains.LogarithmicDivision
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Integrable logarithmic mass divided by radius

Blueprint: `lem:logarithmic-radial-mass`, `lem:radial-log-absorption`.

A product of one-dimensional powers dominates the crossing logarithm divided
by Euclidean radius. This avoids polar coordinates and treats the null axes
only by a.e. equality, without assigning curve values to L² representatives.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- Absolute powers of exponent greater than -1 are integrable on bounded intervals. -/
theorem integrableOn_abs_rpow {s ρ : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ ↦ Real.rpow |x| s) (Ioo (-ρ) ρ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ ↦ Real.rpow |x| s) volume := by
    simpa only [Real.rpow_eq_pow] using
      ((show Measurable (fun x : ℝ ↦ |x|) by fun_prop).pow_const s).aestronglyMeasurable
  have h := integrableOn_ball_of_norm_le_rpow (E := ℝ) (μ := volume)
    (C := 1) (α := -s) (r := ρ) (by simp) (by simp; linarith) (f := fun x ↦
      Real.rpow |x| s) (Filter.Eventually.of_forall (fun x ↦ by
        simp only [neg_neg, one_mul, Real.norm_eq_abs]
        exact le_of_eq (abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) s)))) hm
  simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using h

private theorem log_quarter_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log x| * Real.rpow x (1 / 4) ≤ 4 := by
  have h := Real.abs_log_mul_self_rpow_lt x (1 / 4) hx hx1 (by norm_num)
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)] at h
  simpa only [Real.rpow_eq_pow, one_div_div, div_one] using h.le

/-- A separable integrable majorant for the logarithm divided by radius. -/
theorem logRectangleWeight_div_radius_le {p : ℝ × ℝ}
    (hx : 0 < |p.1|) (hx1 : |p.1| ≤ 1) (hy : 0 < |p.2|) (hy1 : |p.2| ≤ 1) :
    logRectangleWeight p / localRadius 0 p ≤
      9 * (Real.rpow |p.1| (-(3 / 4)) * Real.rpow |p.2| (-(3 / 4))) := by
  let a := Real.rpow |p.1| (1 / 4)
  let b := Real.rpow |p.2| (1 / 4)
  have ha : 0 < a := Real.rpow_pos_of_pos hx _
  have hb : 0 < b := Real.rpow_pos_of_pos hy _
  have ha1 : a ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
  have hb1 : b ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
  have hab : a * b ≤ 1 := by nlinarith
  have hlx : |Real.log (abs p.1)| * a * b ≤ 4 :=
    (mul_le_mul_of_nonneg_right (log_quarter_bound hx hx1) hb.le).trans (by nlinarith)
  have hly : |Real.log (abs p.2)| * b * a ≤ 4 :=
    (mul_le_mul_of_nonneg_right (log_quarter_bound hy hy1) ha.le).trans (by nlinarith)
  have hw : logRectangleWeight p * (a * b) ≤ 9 := by
    dsimp only [logRectangleWeight]
    nlinarith only [hab, hlx, hly]
  have hr0 : 0 ≤ localRadius 0 p := Real.sqrt_nonneg _
  have hrs : localRadius 0 p ^ 2 = |p.1| ^ 2 + |p.2| ^ 2 := by
    simp only [localRadius, Prod.fst_zero, Prod.snd_zero, sub_zero,
      Real.sq_sqrt (by positivity : 0 ≤ p.1 ^ 2 + p.2 ^ 2), sq_abs]
  have hr : 0 < localRadius 0 p := by nlinarith [sq_pos_of_pos hx]
  have hroot : Real.sqrt |p.1| * Real.sqrt |p.2| ≤ localRadius 0 p := by
    have hsx := Real.sq_sqrt hx.le
    have hsy := Real.sq_sqrt hy.le
    have hsq : (Real.sqrt |p.1| * Real.sqrt |p.2|) ^ 2 = |p.1| * |p.2| := by
      rw [mul_pow, hsx, hsy]
    have hn : 0 ≤ Real.sqrt |p.1| * Real.sqrt |p.2| := by positivity
    nlinarith [sq_nonneg (|p.1| - |p.2|), mul_pos hx hy]
  have he (x : ℝ) (hx : 0 < x) :
      Real.rpow x (-(3 / 4)) * Real.rpow x (1 / 4) * Real.sqrt x = 1 := by
    rw [Real.sqrt_eq_rpow]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    norm_num
  let M := Real.rpow |p.1| (-(3 / 4)) * Real.rpow |p.2| (-(3 / 4))
  have hM : 0 < M := mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
  have hid : M * (a * b) * (Real.sqrt |p.1| * Real.sqrt |p.2|) = 1 := by
    calc
      _ = (Real.rpow |p.1| (-(3 / 4)) * a * Real.sqrt |p.1|) *
        (Real.rpow |p.2| (-(3 / 4)) * b * Real.sqrt |p.2|) := by dsimp [M]; ring
      _ = 1 := by rw [he _ hx, he _ hy]; ring
  have hmajor : 1 ≤ M * (a * b) * localRadius 0 p := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hroot (mul_nonneg hM.le (mul_nonneg ha.le hb.le))
  apply (div_le_iff₀ hr).2
  apply le_of_mul_le_mul_right (a := a * b) (b := logRectangleWeight p)
    (c := 9 * M * localRadius 0 p) ?_ (mul_pos ha hb)
  exact hw.trans (by nlinarith only [hmajor])

/-- Genuine integrability of the crossing logarithm divided by Euclidean radius. -/
theorem integrableOn_logRectangleWeight_div_radius :
    IntegrableOn (fun p ↦ logRectangleWeight p / localRadius 0 p)
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
  have hi := (integrableOn_abs_rpow (ρ := 1) (by norm_num : -1 < -(3 / 4 : ℝ)))
  have hprod := hi.mul_prod hi
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  have hm : Measurable (fun p ↦ logRectangleWeight p / localRadius 0 p) := by
    unfold logRectangleWeight localRadius
    fun_prop
  apply (hprod.const_mul 9).mono' hm.aestronglyMeasurable
  have hn : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h0,
      Measure.quasiMeasurePreserving_snd.ae h0] with p hx hy
    exact ⟨hx, hy⟩
  filter_upwards [ae_restrict_of_ae hn, ae_restrict_mem (measurableSet_Ioo.prod
    measurableSet_Ioo)] with p hn hp
  have hp0 : 0 ≤ logRectangleWeight p / localRadius 0 p :=
    div_nonneg (by unfold logRectangleWeight; positivity) (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  exact logRectangleWeight_div_radius_le (abs_pos.mpr hn.1) (abs_le.mpr
    ⟨hp.1.1.le, hp.1.2.le⟩) (abs_pos.mpr hn.2) (abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩)

/-- Every positive power absorbs the radial logarithm on the unit interval. -/
theorem logRadiusWeight_mul_rpow_le {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) : logRadiusWeight r * Real.rpow r s ≤ 1 + 1 / s := by
  have h := Real.abs_log_mul_self_rpow_lt r s hr hr1 hs
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr s)] at h
  have hp := Real.rpow_le_one hr.le hr1 hs.le
  dsimp only [logRadiusWeight]
  simp only [Real.rpow_eq_pow]
  nlinarith only [h.le, hp]

/-- Multiplying an actual radial L² trace by a positive power and the square-root
logarithm preserves L² on a bounded subcritical interval. -/
theorem memLp_logRadius_mul_rpow {ρ s : ℝ} (hρ : ρ ≤ 1) (hs : 0 < s)
    {T : ℝ → ℂ} (hT : MemLp T 2 (volume.restrict (Ioo 0 ρ))) :
    MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      (Real.rpow r s : ℂ) * T r) 2 (volume.restrict (Ioo 0 ρ)) := by
  have hm : Measurable (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      (Real.rpow r s : ℂ)) := by
    unfold logRadiusWeight
    simp only [Real.rpow_eq_pow]
    fun_prop
  have hb : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      (Real.rpow r s : ℂ)) ⊤ (volume.restrict (Ioo 0 ρ)) := by
    apply memLp_top_of_bound hm.aestronglyMeasurable (1 + 1 / s)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (show 0 < Real.rpow r s from Real.rpow_pos_of_pos hr.1 s)]
    have hlog : 1 ≤ logRadiusWeight r := by
      unfold logRadiusWeight
      linarith [abs_nonneg (Real.log r)]
    exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hlog))
      (Real.rpow_pos_of_pos hr.1 s).le).trans
      (logRadiusWeight_mul_rpow_le hr.1 (hr.2.le.trans hρ) hs)
  exact hb.mul hT

/-- Rescaling an actual L² trace by a higher integer power absorbs the logarithm
and a weaker denominator. This treats value and gradient rays with the same rule. -/
theorem memLp_logRadius_nat_mul_div {ρ t : ℝ} {n : ℕ}
    (hρ : ρ ≤ 1) (ht : t < n) {T : ℝ → ℂ}
    (hT : MemLp T 2 (volume.restrict (Ioo 0 ρ))) :
    MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * (r ^ n : ℂ) * T r /
      (Real.rpow r t : ℂ)) 2 (volume.restrict (Ioo 0 ρ)) := by
  apply (memLp_logRadius_mul_rpow hρ (sub_pos.mpr ht) hT).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  simp only [Real.rpow_eq_pow, Real.rpow_sub hr.1, Real.rpow_natCast,
    Complex.ofReal_div, Complex.ofReal_pow]
  ring

end EulerDipoleEigenvalues
