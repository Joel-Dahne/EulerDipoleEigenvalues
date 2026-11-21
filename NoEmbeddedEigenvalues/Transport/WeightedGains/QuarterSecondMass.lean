import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Second weighted mass from a quarter-profile bound

Blueprint: `lem:quarter-second-mass`.

A homogeneous amplitude Q/h in L² and a remainder exp(-(2-δ)|t|),
0<δ<1, give V/d² in L² on the quarter strip. Exact exponential time
moments cost h⁻² for the amplitude and h⁻δ for the remainder, with no
logarithmic loss. Actual integrability precedes all energy integrals.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

private theorem second_profile_sq_bound {c A B q s d x δ : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hd : c * exp (-s) ≤ d)
    (hb : x ≤ A * q + B * exp (-(2 - δ) * s)) :
    (x / d ^ 2) ^ 2 ≤
      (2 * A ^ 2 * q ^ 2 / c ^ 4) * exp (4 * s) +
        (2 * B ^ 2 / c ^ 4) * exp (2 * δ * s) := by
  have hd0 : 0 < d := (mul_pos hc (exp_pos _)).trans_le hd
  have hd2 : (c * exp (-s)) ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (by positivity) hd0.le).2 hd
  have heinv : exp (-s) ^ 2 = (exp (2 * s))⁻¹ := by
    rw [exp_neg, inv_pow, ← exp_nat_mul]
    norm_num
  have hetail : exp (-(2 - δ) * s) * exp (2 * s) = exp (δ * s) := by
    rw [← exp_add]
    congr 1
    ring
  have hdiv : x / d ^ 2 ≤ (A / c ^ 2 * q) * exp (2 * s) +
      (B / c ^ 2) * exp (δ * s) := by
    calc x / d ^ 2 ≤ (A * q + B * exp (-(2 - δ) * s)) / d ^ 2 :=
          div_le_div_of_nonneg_right hb (sq_nonneg _)
         _ ≤ (A * q + B * exp (-(2 - δ) * s)) / (c * exp (-s)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hd2
         _ = (A / c ^ 2 * q) * exp (2 * s) +
             (B / c ^ 2) * (exp (-(2 - δ) * s) * exp (2 * s)) := by
          rw [mul_pow, heinv]
          field_simp
         _ = _ := by rw [hetail]
  have hs := (sq_le_sq₀ (div_nonneg hx (sq_nonneg _)) (by positivity)).2 hdiv
  have hsum : ((A / c ^ 2 * q) * exp (2 * s) + (B / c ^ 2) * exp (δ * s)) ^ 2 ≤
      2 * ((A / c ^ 2 * q) * exp (2 * s)) ^ 2 +
        2 * ((B / c ^ 2) * exp (δ * s)) ^ 2 := by
    nlinarith [sq_nonneg ((A / c ^ 2 * q) * exp (2 * s) - (B / c ^ 2) * exp (δ * s))]
  have he4 : exp (2 * s) ^ 2 = exp (4 * s) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have heδ : exp (δ * s) ^ 2 = exp (2 * δ * s) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  apply hs.trans (hsum.trans_eq ?_)
  simp only [mul_pow, div_pow, he4, heδ, ← pow_mul]
  ring

/-- A raw measurable profile with Q/h in L² and a subcritical exponential
remainder has genuine second saddle-distance mass. -/
theorem memLp_quarter_div_saddleDist_sq_of_exp_bound
    {b c A B δ : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Q : ℝ → ℂ} {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (volume.restrict (quarterOrbitStrip b)))
    (hQ : MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 b)))
    (hd : ∀ h ∈ Ioo 0 b, ∀ t, |t| ≤ eighthPeriod h →
      c * exp (-|t|) ≤ saddleDist (dipoleOrbit h t))
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
        ‖V (h, t)‖ ≤ A * ‖Q h‖ + B * exp (-(2 - δ) * |t|)) :
    MemLp (fun q ↦ V q / ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  let W := fun q ↦ V q / ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)
  have hdm : Continuous (fun q : ℝ × ℝ ↦
      ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit)).pow 2
  have hWm : AEStronglyMeasurable W (volume.restrict (quarterOrbitStrip b)) :=
    hV.div₀ hdm.aestronglyMeasurable
  have hInv : IntegrableOn (fun h : ℝ ↦ h ^ (-δ)) (Ioo 0 b) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hb).2 (by linarith)
  let G := fun h ↦ (2 * A ^ 2 * exp 8 / c ^ 4) * ‖Q h / (h : ℂ)‖ ^ 2 +
    (2 * B ^ 2 * exp (4 * δ) / (δ * c ^ 4)) * h ^ (-δ)
  have hG : IntegrableOn G (Ioo 0 b) := by
    change Integrable G (volume.restrict (Ioo 0 b))
    exact ((hQ.integrable_norm_pow (by norm_num)).const_mul _).add (hInv.const_mul _)
  apply memLp_quarterStrip_of_integral_bound hWm hG
  filter_upwards [hbound, aestronglyMeasurable_quarterStrip_sections hWm,
    ae_restrict_mem measurableSet_Ioo] with h hv hwm hh
  have hh1 : h < 1 := hh.2.trans hb1
  have hL : 0 ≤ eighthPeriod h := (eighthPeriod_pos hh.1 hh1).le
  have hLL : -eighthPeriod h ≤ eighthPeriod h := by linarith
  let M₁ := fun t ↦ (2 * A ^ 2 * ‖Q h‖ ^ 2 / c ^ 4) * exp (4 * |t|)
  let M₂ := fun t ↦ (2 * B ^ 2 / c ^ 4) * exp (2 * δ * |t|)
  have hm₁ : Continuous M₁ := by dsimp [M₁]; fun_prop
  have hm₂ : Continuous M₂ := by dsimp [M₂]; fun_prop
  have hi₁ : IntegrableOn M₁ (Ioo (-eighthPeriod h) (eighthPeriod h)) :=
    hm₁.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi₂ : IntegrableOn M₂ (Ioo (-eighthPeriod h) (eighthPeriod h)) :=
    hm₂.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hdom : ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
      ‖W (h, t)‖ ^ 2 ≤ M₁ t + M₂ t := by
    filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hdt := hd h hh t (abs_le.2 ⟨htI.1.le, htI.2.le⟩)
    dsimp only [W]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact second_profile_sq_bound hc hA hB (norm_nonneg _) (norm_nonneg _) hdt ht
  have hiSq : IntegrableOn (fun t ↦ ‖W (h, t)‖ ^ 2)
      (Ioo (-eighthPeriod h) (eighthPeriod h)) := by
    apply (hi₁.add hi₂).mono' (hwm.norm.pow 2)
    filter_upwards [hdom] with t ht
    change |‖W (h, t)‖ ^ 2| ≤ M₁ t + M₂ t
    rw [abs_of_nonneg (sq_nonneg _)]
    exact ht
  refine ⟨hiSq, (integral_mono_ae hiSq (hi₁.add hi₂) hdom).trans ?_⟩
  have hexp (a : ℝ) (ha : a ≠ 0) :
      (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), exp (a * |t|)) =
        2 * (exp (a * eighthPeriod h) - 1) / a := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hLL]
    exact integral_exp_mul_abs ha hL
  have hcoarse := log_le_log (mul_pos (exp_pos _) (sqrt_pos.2 hh.1))
    (exp_eighthPeriod_mul_sqrt_le hh.1 hh1)
  rw [log_mul (exp_pos _).ne' (sqrt_pos.2 hh.1).ne', log_exp,
    log_sqrt hh.1.le, log_exp] at hcoarse
  have he_moment (a : ℝ) (ha : 0 < a) :
      exp (a * eighthPeriod h) ≤ exp (2 * a) * h ^ (-(a / 2)) := by
    rw [rpow_def_of_pos hh.1, ← exp_add]
    apply exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left hcoarse ha.le]
  have he4L : exp (4 * eighthPeriod h) ≤ exp 8 / h ^ 2 := by
    convert he_moment 4 (by norm_num) using 1
    norm_num [rpow_neg hh.1.le, rpow_two, div_eq_mul_inv]
  have heδL : exp ((2 * δ) * eighthPeriod h) ≤ exp (4 * δ) * h ^ (-δ) := by
    simpa only [show 2 * (2 * δ) = 4 * δ by ring, show -(2 * δ / 2) = -δ by ring]
      using he_moment (2 * δ) (by positivity)
  have he₁ : (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), exp (4 * |t|)) ≤
      exp 8 / h ^ 2 := by
    rw [hexp 4 (by norm_num)]
    linarith [exp_pos (4 * eighthPeriod h)]
  have he₂ : (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), exp (2 * δ * |t|)) ≤
      (exp (4 * δ) / δ) * h ^ (-δ) := by
    rw [hexp (2 * δ) (by positivity)]
    calc 2 * (exp (2 * δ * eighthPeriod h) - 1) / (2 * δ) =
          (exp (2 * δ * eighthPeriod h) - 1) / δ := by ring
         _ ≤ exp (2 * δ * eighthPeriod h) / δ :=
          div_le_div_of_nonneg_right (by linarith) hδ0.le
         _ ≤ (exp (4 * δ) * h ^ (-δ)) / δ :=
          div_le_div_of_nonneg_right heδL hδ0.le
         _ = _ := by ring
  have hqn : ‖Q h / (h : ℂ)‖ ^ 2 = ‖Q h‖ ^ 2 / h ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh.1, div_pow]
  simp only [Pi.add_apply]
  rw [integral_add hi₁ hi₂]
  dsimp only [M₁, M₂]
  rw [integral_const_mul, integral_const_mul]
  calc _ ≤ (2 * A ^ 2 * ‖Q h‖ ^ 2 / c ^ 4) * (exp 8 / h ^ 2) +
        (2 * B ^ 2 / c ^ 4) * ((exp (4 * δ) / δ) * h ^ (-δ)) :=
      add_le_add (mul_le_mul_of_nonneg_left he₁ (by positivity))
        (mul_le_mul_of_nonneg_left he₂ (by positivity))
       _ = G h := by dsimp only [G]; rw [hqn]; ring

end NoEmbeddedEigenvalues
