module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Endpoint estimates for interval H¹ representatives

Blueprint: `lem:h1-endpoint-estimates` and `lem:h1-endpoint-layers`.

The estimates use the canonical extension, not the unrestricted raw endpoint
values. Cauchy–Schwarz bounds endpoint values and rescaled zero-trace layers
using only first-order data; no Hardy inequality or second derivative is needed.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Interval Topology

/-- Cauchy–Schwarz for the integral of a complex L² function on a finite interval. -/
theorem norm_intervalIntegral_sq_le {c d : ℝ} {D : ℝ → ℂ} (hcd : c ≤ d)
    (hD : MemLp D 2 (volume.restrict (Icc c d))) :
    ‖∫ t in c..d, D t‖ ^ 2 ≤ (d - c) * ∫ t in c..d, ‖D t‖ ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp D (ENNReal.ofReal 2) (volume.restrict (Icc c d)) by simpa using hD)
    (memLp_const (1 : ℂ) : MemLp (fun _ : ℝ ↦ (1 : ℂ))
      (ENNReal.ofReal 2) (volume.restrict (Icc c d)))
  simp only [norm_one, mul_one, Real.rpow_two, one_pow] at hh
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hcd), smul_eq_mul, mul_one] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hn := norm_integral_le_integral_norm (f := D) (μ := volume.restrict (Icc c d))
  have hs := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hn.trans hh)
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),
    Real.sq_sqrt (sub_nonneg.mpr hcd)] at hs
  simpa only [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc,
    mul_comm] using hs

/-- The endpoint values of the derivative do not affect its L² membership. -/
theorem HasIntervalH1.memLp_derivative_Icc {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) : MemLp D 2 (volume.restrict (Icc a b)) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact h.memLp_derivative

/-- Square integrability of the derivative on the closed interval. -/
theorem HasIntervalH1.integrableOn_sq_norm_derivative {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) : IntegrableOn (fun t ↦ ‖D t‖ ^ 2) (Icc a b) :=
  h.memLp_derivative_Icc.norm.integrable_sq

/-- The squared H¹ increment is bounded by the length times the local derivative energy. -/
theorem HasIntervalH1.extension_sub_sq_le {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hc : c ∈ Icc a b)
    (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    ‖intervalH1Extension a b F D d - intervalH1Extension a b F D c‖ ^ 2 ≤
      (d - c) * ∫ t in c..d, ‖D t‖ ^ 2 := by
  rw [← h.integral_eq_extension_sub hab hc hd]
  exact norm_intervalIntegral_sq_le hcd
    (h.memLp_derivative_Icc.mono_measure (Measure.restrict_mono
      (Icc_subset_Icc hc.1 hd.2) le_rfl))

/-- Endpoint Cauchy–Schwarz with a zero left trace. -/
theorem HasIntervalH1.extension_sq_le_left {a b x : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0) (hx : x ∈ Icc a b) :
    ‖intervalH1Extension a b F D x‖ ^ 2 ≤ (x - a) * ∫ t in a..x, ‖D t‖ ^ 2 := by
  simpa only [ha, sub_zero] using
    h.extension_sub_sq_le hab ⟨le_rfl, hab.le⟩ hx hx.1

/-- Endpoint Cauchy–Schwarz with a zero right trace. -/
theorem HasIntervalH1.extension_sq_le_right {a b x : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (hb : intervalH1Extension a b F D b = 0) (hx : x ∈ Icc a b) :
    ‖intervalH1Extension a b F D x‖ ^ 2 ≤ (b - x) * ∫ t in x..b, ‖D t‖ ^ 2 := by
  simpa only [hb, zero_sub, norm_neg] using
    h.extension_sub_sq_le hab hx ⟨hab.le, le_rfl⟩ hx.2

/-- The left endpoint layer has a bound uniform in its width, after rescaling. -/
theorem HasIntervalH1.integral_extension_sq_le_left {a b c : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0) (hc : c ∈ Icc a b) :
    (∫ x in a..c, ‖intervalH1Extension a b F D x‖ ^ 2) ≤
      (c - a) ^ 2 * ∫ t in a..c, ‖D t‖ ^ 2 := by
  have hE := (intervalIntegrable_iff_integrableOn_Icc_of_le hc.1).mpr
    (h.integrableOn_sq_norm_derivative.mono_set (Icc_subset_Icc le_rfl hc.2))
  have hG := (((h.continuousOn_extension hab).norm.pow 2).mono
    (Icc_subset_Icc le_rfl hc.2)).intervalIntegrable_of_Icc (μ := volume) hc.1
  have hpoint : ∀ x ∈ Icc a c, ‖intervalH1Extension a b F D x‖ ^ 2 ≤
      (c - a) * ∫ t in a..c, ‖D t‖ ^ 2 := by
    intro x hx
    calc
      _ ≤ (x - a) * ∫ t in a..x, ‖D t‖ ^ 2 :=
        h.extension_sq_le_left hab ha ⟨hx.1, hx.2.trans hc.2⟩
      _ ≤ (c - a) * ∫ t in a..c, ‖D t‖ ^ 2 := by
        apply mul_le_mul (sub_le_sub_right hx.2 a)
          (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
            (Eventually.of_forall (fun _ ↦ sq_nonneg _)) hE)
          (intervalIntegral.integral_nonneg_of_forall hx.1 (fun _ ↦ sq_nonneg _))
          (sub_nonneg.mpr hc.1)
  calc
    _ ≤ ∫ _ in a..c, (c - a) * ∫ t in a..c, ‖D t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hc.1 hG intervalIntegrable_const hpoint
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

/-- The corresponding uniform bound for a right endpoint layer. -/
theorem HasIntervalH1.integral_extension_sq_le_right {a b c : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (hb : intervalH1Extension a b F D b = 0) (hc : c ∈ Icc a b) :
    (∫ x in c..b, ‖intervalH1Extension a b F D x‖ ^ 2) ≤
      (b - c) ^ 2 * ∫ t in c..b, ‖D t‖ ^ 2 := by
  have hE := (intervalIntegrable_iff_integrableOn_Icc_of_le hc.2).mpr
    (h.integrableOn_sq_norm_derivative.mono_set (Icc_subset_Icc hc.1 le_rfl))
  have hG := (((h.continuousOn_extension hab).norm.pow 2).mono
    (Icc_subset_Icc hc.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hc.2
  have hpoint : ∀ x ∈ Icc c b, ‖intervalH1Extension a b F D x‖ ^ 2 ≤
      (b - c) * ∫ t in c..b, ‖D t‖ ^ 2 := by
    intro x hx
    calc
      _ ≤ (b - x) * ∫ t in x..b, ‖D t‖ ^ 2 :=
        h.extension_sq_le_right hab hb ⟨hc.1.trans hx.1, hx.2⟩
      _ ≤ (b - c) * ∫ t in c..b, ‖D t‖ ^ 2 := by
        apply mul_le_mul (sub_le_sub_left hx.1 b)
          (intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
            (Eventually.of_forall (fun _ ↦ sq_nonneg _)) hE)
          (intervalIntegral.integral_nonneg_of_forall hx.2 (fun _ ↦ sq_nonneg _))
          (sub_nonneg.mpr hc.2)
  calc
    _ ≤ ∫ _ in c..b, (b - c) * ∫ t in c..b, ‖D t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hc.2 hG intervalIntegrable_const hpoint
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

/-- Rescaling a left endpoint layer costs at most its local derivative energy. -/
theorem HasIntervalH1.integral_rescaled_left_le {a b c : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0) (hc : c ∈ Ioc a b) :
    (∫ x in a..c, (‖intervalH1Extension a b F D x‖ / (c - a)) ^ 2) ≤
      ∫ t in a..c, ‖D t‖ ^ 2 := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div]
  apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hc.1))).mpr
  simpa only [mul_comm] using h.integral_extension_sq_le_left hab ha ⟨hc.1.le, hc.2⟩

/-- Rescaling a right endpoint layer costs at most its local derivative energy. -/
theorem HasIntervalH1.integral_rescaled_right_le {a b c : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (hb : intervalH1Extension a b F D b = 0) (hc : c ∈ Ico a b) :
    (∫ x in c..b, (‖intervalH1Extension a b F D x‖ / (b - c)) ^ 2) ≤
      ∫ t in c..b, ‖D t‖ ^ 2 := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div]
  apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hc.2))).mpr
  simpa only [mul_comm] using h.integral_extension_sq_le_right hab hb ⟨hc.1, hc.2.le⟩

/-- The rescaled left endpoint layer vanishes as its width goes to zero. -/
theorem HasIntervalH1.tendsto_integral_rescaled_left {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0) :
    Tendsto (fun c ↦ ∫ x in a..c, (‖intervalH1Extension a b F D x‖ / (c - a)) ^ 2)
      (𝓝[Ioc a b] a) (𝓝 0) := by
  have hE : IntegrableOn (fun t ↦ ‖D t‖ ^ 2) (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using h.integrableOn_sq_norm_derivative
  have hcont : ContinuousOn (fun c ↦ ∫ t in a..c, ‖D t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hE.intervalIntegrable
        (show a ∈ uIcc a b from left_mem_uIcc)
  have hlim : Tendsto (fun c ↦ ∫ t in a..c, ‖D t‖ ^ 2) (𝓝[Ioc a b] a) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using
      (hcont a ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
  have hmem : ∀ᶠ c in 𝓝[Ioc a b] a, c ∈ Ioc a b := self_mem_nhdsWithin
  exact squeeze_zero'
    (hmem.mono fun c hc ↦ intervalIntegral.integral_nonneg_of_forall hc.1.le
      (fun _ ↦ sq_nonneg _))
    (hmem.mono fun _ hc ↦ h.integral_rescaled_left_le hab ha hc) hlim

/-- The rescaled right endpoint layer vanishes as its width goes to zero. -/
theorem HasIntervalH1.tendsto_integral_rescaled_right {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (hb : intervalH1Extension a b F D b = 0) :
    Tendsto (fun c ↦ ∫ x in c..b, (‖intervalH1Extension a b F D x‖ / (b - c)) ^ 2)
      (𝓝[Ico a b] b) (𝓝 0) := by
  have hE : IntegrableOn (fun t ↦ ‖D t‖ ^ 2) (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using h.integrableOn_sq_norm_derivative
  have hcont : ContinuousOn (fun c ↦ ∫ t in c..b, ‖D t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval_left hE
  have hlim : Tendsto (fun c ↦ ∫ t in c..b, ‖D t‖ ^ 2) (𝓝[Ico a b] b) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using
      (hcont b ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hmem : ∀ᶠ c in 𝓝[Ico a b] b, c ∈ Ico a b := self_mem_nhdsWithin
  exact squeeze_zero'
    (hmem.mono fun c hc ↦ intervalIntegral.integral_nonneg_of_forall hc.2.le
      (fun _ ↦ sq_nonneg _))
    (hmem.mono fun _ hc ↦ h.integral_rescaled_right_le hab hb hc) hlim

end NoEmbeddedEigenvalues
