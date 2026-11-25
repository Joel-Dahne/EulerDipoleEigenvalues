module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.LogarithmicQuarterMass
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Logarithmic endpoint-ray change of variables

Blueprint: `lem:log-endpoint-change-variables`.

The map r(h) = 2 arcsin sqrt(h) has positive derivative. Its Jacobian turns
r⁻³ dr into h⁻² dh and r⁻¹ dr into h⁻¹ dh, up to bounded factors.
Measurability on the level interval is supplied separately, so arbitrary
representatives on null rays are never composed without justification.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter Real

theorem quarterEndpointRadius_pos {h : ℝ} (h0 : 0 < h) : 0 < quarterEndpointRadius h := by
  unfold quarterEndpointRadius
  exact mul_pos (by norm_num) (arcsin_pos.mpr (sqrt_pos.mpr h0))

theorem monotone_quarterEndpointRadius : Monotone quarterEndpointRadius := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (monotone_arcsin (sqrt_le_sqrt hxy)) (by norm_num)

theorem hasDerivAt_quarterEndpointRadius {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt quarterEndpointRadius (1 / (sqrt h * sqrt (1 - h))) h := by
  have hs := sqrt_pos.mpr h0
  have ht := sqrt_pos.mpr (sub_pos.mpr h1)
  have ha := (hasDerivAt_arcsin (by linarith : sqrt h ≠ -1)
    (ne_of_lt ((sqrt_lt' zero_lt_one).mpr (by simpa using h1)))).comp h (hasDerivAt_sqrt h0.ne')
  convert ha.const_mul 2 using 1
  · rfl
  · rw [sq_sqrt h0.le]
    field_simp

theorem quarterEndpointRadius_le_four_sqrt {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    quarterEndpointRadius h ≤ 4 * sqrt h := by
  have hz : sqrt h ≤ 1 := sqrt_le_one.mpr h1.le
  have ha : 0 ≤ arcsin (sqrt h) := arcsin_nonneg.mpr (sqrt_nonneg _)
  have hj := mul_le_sin ha (arcsin_le_pi_div_two (sqrt h))
  rw [sin_arcsin (by linarith [sqrt_nonneg h]) hz] at hj
  have hb : arcsin (sqrt h) ≤ π / 2 * sqrt h := by
    calc
      _ = π / 2 * (2 / π * arcsin (sqrt h)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)
  unfold quarterEndpointRadius
  nlinarith [pi_lt_four, sqrt_nonneg h]

/-- The logarithmic level weight is bounded by a fixed multiple of the radial
logarithm; no derivative of either logarithmic weight occurs. -/
theorem logLevelWeight_le_endpoint {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    logLevelWeight h ≤ (3 + log 16) * logRadiusWeight (quarterEndpointRadius h) := by
  have hr := quarterEndpointRadius_pos h0
  have hu := quarterEndpointRadius_le_four_sqrt h0 h1
  have hs : quarterEndpointRadius h ^ 2 ≤ 16 * h := by
    nlinarith [sq_sqrt h0.le, sq_le_sq₀ hr.le (by positivity : 0 ≤ 4 * sqrt h) |>.mpr hu]
  have hl := log_le_log (sq_pos_of_pos hr) hs
  rw [log_pow, log_mul (by norm_num : (16 : ℝ) ≠ 0) h0.ne'] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have h16 : 0 ≤ log (16 : ℝ) := log_nonneg (by norm_num)
  have ha := neg_le_abs (log (quarterEndpointRadius h))
  rw [logLevelWeight, log_div (by norm_num : (1 : ℝ) ≠ 0) h0.ne', log_one,
    logRadiusWeight]
  nlinarith [abs_nonneg (log (quarterEndpointRadius h)),
    mul_nonneg h16 (abs_nonneg (log (quarterEndpointRadius h)))]

private theorem endpoint_jacobian_bound {h : ℝ} (h0 : 0 < h) (h1 : h < 1)
    {n : ℕ} (hn : n = 1 ∨ n = 2) :
    quarterEndpointRadius h ^ (2 * n - 1) ≤
      64 * h ^ n * (1 / (sqrt h * sqrt (1 - h))) := by
  have hs := sqrt_pos.mpr h0
  have ht := sqrt_pos.mpr (sub_pos.mpr h1)
  have ht1 : sqrt (1 - h) ≤ 1 := sqrt_le_one.mpr (by linarith)
  have hj : sqrt h ≤ h * (1 / (sqrt h * sqrt (1 - h))) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (mul_pos hs ht)).mpr
    nlinarith [sq_sqrt h0.le, mul_le_mul_of_nonneg_left ht1 h0.le]
  have hr := quarterEndpointRadius_pos h0
  have hu := quarterEndpointRadius_le_four_sqrt h0 h1
  rcases hn with rfl | rfl
  · norm_num only [Nat.reduceMul, Nat.reduceSub, pow_one]
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) (mul_pos hs ht)]
  · norm_num only [Nat.reduceMul, Nat.reduceSub]
    have hc : quarterEndpointRadius h ^ 3 ≤ (4 * sqrt h) ^ 3 := by gcongr
    nlinarith [sq_sqrt h0.le, mul_le_mul_of_nonneg_left hj h0.le]

/-- Weighted radial mass controls either endpoint energy (n=1 or n=2).
Level-side measurability is an explicit premise, typically supplied by the
unweighted endpoint L² bound already in the compatible numerator data. -/
theorem integrable_log_endpoint_pullback {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {n : ℕ} (hn : n = 1 ∨ n = 2)
    {B : ℝ → ℝ} (hB : ∀ r, 0 ≤ B r)
    (hm : AEStronglyMeasurable (fun h ↦ logLevelWeight h * B (quarterEndpointRadius h) / h ^ n)
      (volume.restrict (Ioo 0 b)))
    (hi : IntegrableOn (fun r ↦ logRadiusWeight r * B r / r ^ (2 * n - 1)) (Ioo 0 ρ)) :
    IntegrableOn (fun h ↦ logLevelWeight h * B (quarterEndpointRadius h) / h ^ n) (Ioo 0 b) := by
  have hder (h : ℝ) (hh : h ∈ Ioo 0 b) :=
    (hasDerivAt_quarterEndpointRadius hh.1 (hh.2.trans hb)).hasDerivWithinAt
      (s := Ioo 0 b)
  have hinj : InjOn quarterEndpointRadius (Ioo 0 b) := by
    intro x hx y hy he
    have hx1 : sqrt x ≤ 1 := sqrt_le_one.mpr (hx.2.trans hb).le
    have hy1 : sqrt y ≤ 1 := sqrt_le_one.mpr (hy.2.trans hb).le
    have hs : arcsin (sqrt x) = arcsin (sqrt y) := by
      unfold quarterEndpointRadius at he; linarith
    have hs' := congrArg sin hs
    rw [sin_arcsin (by linarith [sqrt_nonneg x]) hx1,
      sin_arcsin (by linarith [sqrt_nonneg y]) hy1] at hs'
    nlinarith [sq_sqrt hx.1.le, sq_sqrt hy.1.le]
  have hsub : quarterEndpointRadius '' Ioo 0 b ⊆ Ioo 0 ρ := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨quarterEndpointRadius_pos hh.1,
      (monotone_quarterEndpointRadius hh.2.le).trans_lt hρ⟩
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    hder hinj _).mp (hi.mono_set hsub)
  let C : ℝ := (3 + log 16) * 64
  apply (hj.const_mul C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hh1 := hh.2.trans hb
  have hr := quarterEndpointRadius_pos hh.1
  have hJ : 0 < 1 / (sqrt h * sqrt (1 - h)) :=
    div_pos zero_lt_one (mul_pos (sqrt_pos.mpr hh.1) (sqrt_pos.mpr (sub_pos.mpr hh1)))
  have hlog : 0 ≤ logRadiusWeight (quarterEndpointRadius h) := by
    unfold logRadiusWeight; positivity
  have hC : 0 ≤ 3 + log (16 : ℝ) := by linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 16)]
  have hw := logLevelWeight_le_endpoint hh.1 hh1
  have hratio : 1 / h ^ n ≤ 64 * (1 / (sqrt h * sqrt (1 - h))) /
      quarterEndpointRadius h ^ (2 * n - 1) := by
    apply (div_le_div_iff₀ (pow_pos hh.1 n) (pow_pos hr _)).mpr
    nlinarith [endpoint_jacobian_bound hh.1 hh1 hn]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (mul_nonneg (logLevelWeight_nonneg hh.1 hh1.le) (hB _)) (pow_nonneg hh.1.le _))]
  change logLevelWeight h * B (quarterEndpointRadius h) / h ^ n ≤
    C * (|1 / (sqrt h * sqrt (1 - h))| •
      (logRadiusWeight (quarterEndpointRadius h) * B (quarterEndpointRadius h) /
        quarterEndpointRadius h ^ (2 * n - 1)))
  rw [abs_of_pos hJ, smul_eq_mul]
  calc
    _ ≤ ((3 + log 16) * logRadiusWeight (quarterEndpointRadius h)) *
        B (quarterEndpointRadius h) / h ^ n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw (hB _)) (pow_nonneg hh.1.le n)
    _ = ((3 + log 16) * logRadiusWeight (quarterEndpointRadius h) *
        B (quarterEndpointRadius h)) * (1 / h ^ n) := by ring
    _ ≤ ((3 + log 16) * logRadiusWeight (quarterEndpointRadius h) *
        B (quarterEndpointRadius h)) *
        (64 * (1 / (sqrt h * sqrt (1 - h))) / quarterEndpointRadius h ^ (2 * n - 1)) :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (mul_nonneg hC hlog) (hB _))
    _ = _ := by dsimp [C]; ring

end EulerDipoleEigenvalues
