module

public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# First weighted mass from a quarter-profile bound

Blueprint: `lem:quarter-first-mass`.

An amplitude with Q/√h in L² and a remainder decaying as exp(-|t|/2)
give a profile divided by saddle distance in L². Exponential time moments
avoid a logarithmic loss from estimating the moving interval by its length.
All fiber and global square integrals are established as integrable.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter Real

private theorem weighted_profile_sq_bound {c A B q s d x : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hd : c * exp (-s) ≤ d)
    (hb : x ≤ A * q + B * exp (-s / 2)) :
    (x / d) ^ 2 ≤
      (2 * A ^ 2 * q ^ 2 / c ^ 2) * exp (2 * s) +
        (2 * B ^ 2 / c ^ 2) * exp s := by
  have hd0 : 0 < d := (mul_pos hc (exp_pos _)).trans_le hd
  have he : exp (-s / 2) * exp s = exp (s / 2) := by
    rw [← exp_add]
    congr 1
    ring
  have hdiv : x / d ≤ (A / c * q) * exp s + (B / c) * exp (s / 2) := by
    calc x / d ≤ (A * q + B * exp (-s / 2)) / d :=
          div_le_div_of_nonneg_right hb hd0.le
         _ ≤ (A * q + B * exp (-s / 2)) / (c * exp (-s)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hc (exp_pos _)) hd
         _ = (A / c * q) * exp s + (B / c) * (exp (-s / 2) * exp s) := by
          rw [exp_neg]
          field_simp
         _ = _ := by rw [he]
  have hs := (sq_le_sq₀ (div_nonneg hx hd0.le) (by positivity)).2 hdiv
  have hsum : ((A / c * q) * exp s + (B / c) * exp (s / 2)) ^ 2 ≤
      2 * ((A / c * q) * exp s) ^ 2 + 2 * ((B / c) * exp (s / 2)) ^ 2 := by
    nlinarith [sq_nonneg ((A / c * q) * exp s - (B / c) * exp (s / 2))]
  have he₂ : exp s ^ 2 = exp (2 * s) := by rw [← exp_nat_mul]; norm_num
  have he₁ : exp (s / 2) ^ 2 = exp s := by
    rw [← exp_nat_mul]
    congr 1
    ring
  apply hs.trans (hsum.trans_eq ?_)
  simp only [mul_pow, div_pow, he₂, he₁]
  ring

/-- A jointly measurable quarter profile with a controlled homogeneous amplitude
and an exponentially decaying remainder has the first saddle-distance mass gain. -/
theorem memLp_quarter_div_saddleDist_of_exp_bound
    {b c A B : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {Q : ℝ → ℂ} {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (volume.restrict (quarterOrbitStrip b)))
    (hQ : MemLp (fun h ↦ Q h / (√h : ℂ)) 2 (volume.restrict (Ioo 0 b)))
    (hd : ∀ h ∈ Ioo 0 b, ∀ t, |t| ≤ eighthPeriod h →
      c * exp (-|t|) ≤ saddleDist (dipoleOrbit h t))
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
        ‖V (h, t)‖ ≤ A * ‖Q h‖ + B * exp (-|t| / 2)) :
    MemLp (fun q ↦ V q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  let W := fun q ↦ V q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)
  have hdm : Continuous (fun q : ℝ × ℝ ↦
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit)
  have hWm : AEStronglyMeasurable W (volume.restrict (quarterOrbitStrip b)) :=
    hV.div₀ hdm.aestronglyMeasurable
  have hInv : IntegrableOn (fun h : ℝ ↦ 1 / √h) (Ioo 0 b) := by
    have hi : IntegrableOn (fun h : ℝ ↦ h ^ (-(1 / 2 : ℝ))) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).2 (by norm_num)
    apply hi.congr_fun _ measurableSet_Ioo
    intro h hh
    dsimp only
    rw [rpow_neg hh.1.le, ← sqrt_eq_rpow, one_div]
  let G := fun h ↦ (2 * A ^ 2 * exp 4 / c ^ 2) * ‖Q h / (√h : ℂ)‖ ^ 2 +
    (4 * B ^ 2 * exp 2 / c ^ 2) / √h
  have hG : IntegrableOn G (Ioo 0 b) := by
    change Integrable G (volume.restrict (Ioo 0 b))
    convert! ((hQ.integrable_norm_pow (by norm_num)).const_mul
      (2 * A ^ 2 * exp 4 / c ^ 2)).add
      (hInv.const_mul (4 * B ^ 2 * exp 2 / c ^ 2)) using 1
    funext h
    dsimp only [G, Pi.add_apply]
    ring
  apply memLp_quarterStrip_of_integral_bound hWm hG
  filter_upwards [hbound, aestronglyMeasurable_quarterStrip_sections hWm,
    ae_restrict_mem measurableSet_Ioo] with h hv hwm hh
  have hh1 : h < 1 := hh.2.trans hb1
  have hL : 0 ≤ eighthPeriod h := (eighthPeriod_pos hh.1 hh1).le
  have hLL : -eighthPeriod h ≤ eighthPeriod h := by linarith
  let M₁ := fun t ↦ (2 * A ^ 2 * ‖Q h‖ ^ 2 / c ^ 2) * exp (2 * |t|)
  let M₂ := fun t ↦ (2 * B ^ 2 / c ^ 2) * exp |t|
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
    have hdt0 : 0 < saddleDist (dipoleOrbit h t) :=
      (mul_pos hc (exp_pos _)).trans_le hdt
    dsimp only [W]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdt0]
    exact weighted_profile_sq_bound hc hA hB (norm_nonneg _) (norm_nonneg _) hdt ht
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
  have heL : exp (eighthPeriod h) ≤ exp 2 / √h :=
    (le_div_iff₀ (sqrt_pos.2 hh.1)).2 (exp_eighthPeriod_mul_sqrt_le hh.1 hh1)
  have he2L : exp (2 * eighthPeriod h) ≤ exp 4 / h := by
    have hs := pow_le_pow_left₀ (exp_pos _).le heL 2
    norm_num [div_pow, sq_sqrt hh.1.le, ← exp_nat_mul] at hs
    exact hs
  have he₂ : (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), exp (2 * |t|)) ≤
      exp 4 / h := by
    rw [hexp 2 (by norm_num)]
    linarith
  have he₁ : (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), exp |t|) ≤
      2 * exp 2 / √h := by
    have he := hexp 1 (by norm_num)
    simp only [one_mul, div_one] at he
    rw [he]
    calc 2 * (exp (eighthPeriod h) - 1) ≤ 2 * exp (eighthPeriod h) := by linarith
         _ ≤ 2 * (exp 2 / √h) := mul_le_mul_of_nonneg_left heL (by norm_num)
         _ = _ := by ring
  have hqn : ‖Q h / (√h : ℂ)‖ ^ 2 = ‖Q h‖ ^ 2 / h := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sqrt_nonneg _), div_pow, sq_sqrt hh.1.le]
  simp only [Pi.add_apply]
  rw [integral_add hi₁ hi₂]
  dsimp only [M₁, M₂]
  rw [integral_const_mul, integral_const_mul]
  calc _ ≤ (2 * A ^ 2 * ‖Q h‖ ^ 2 / c ^ 2) * (exp 4 / h) +
        (2 * B ^ 2 / c ^ 2) * (2 * exp 2 / √h) :=
      add_le_add (mul_le_mul_of_nonneg_left he₂ (by positivity))
        (mul_le_mul_of_nonneg_left he₁ (by positivity))
       _ = G h := by dsimp only [G]; rw [hqn]; ring

end EulerDipoleEigenvalues
