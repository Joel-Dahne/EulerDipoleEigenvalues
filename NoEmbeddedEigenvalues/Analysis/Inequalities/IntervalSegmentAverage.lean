import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalZeroExtension
import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1Estimates
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Segment averages of interval H¹ data

Blueprint: `lem:segment-average-h1`.

Averaging a continuous H¹ representative along segments from a fixed point
preserves H¹. The derivative has an extra segment parameter, which compensates
for the inverse dilation Jacobian in the squared integral.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

private theorem weighted_segment_l2 {M : ℝ → ℂ} (hM : Measurable M)
    (hML : MemLp M 2 volume) (a b z : ℝ) :
    let B : ℝ × ℝ → ℂ := fun p ↦ p.2 • M (p.2 * p.1 + (1 - p.2) * z)
    MemLp B 2 ((volume.restrict (Ioo a b)).prod (volume.restrict (Icc (0 : ℝ) 1))) ∧
      (∫ p, ‖B p‖ ^ 2 ∂((volume.restrict (Ioo a b)).prod
        (volume.restrict (Icc (0 : ℝ) 1)))) ≤ ∫ x : ℝ, ‖M x‖ ^ 2 := by
  let B : ℝ × ℝ → ℂ := fun p ↦ p.2 • M (p.2 * p.1 + (1 - p.2) * z)
  have hBm : Measurable B := by dsimp [B]; fun_prop
  have hI : Integrable (fun x ↦ ‖M x‖ ^ 2) := hML.integrable_norm_pow (by norm_num)
  have hI0 : 0 ≤ ∫ x : ℝ, ‖M x‖ ^ 2 := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hslice (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x ↦ ‖B (x, t)‖ ^ 2) ∧
        (∫ x : ℝ, ‖B (x, t)‖ ^ 2) ≤ ∫ x : ℝ, ‖M x‖ ^ 2 := by
    by_cases ht0 : t = 0
    · simp [B, ht0, hI0]
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have he (x : ℝ) : ‖B (x, t)‖ ^ 2 =
        t ^ 2 * ‖M (t * x + (1 - t) * z)‖ ^ 2 := by
      simp only [B, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [he]
    refine ⟨((hI.comp_add_right ((1 - t) * z)).comp_mul_left' ht0).const_mul _, ?_⟩
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun y : ℝ ↦ ‖M (y + (1 - t) * z)‖ ^ 2) t,
      integral_add_right_eq_self (fun x : ℝ ↦ ‖M x‖ ^ 2) ((1 - t) * z),
      abs_of_pos (inv_pos.2 htpos), smul_eq_mul]
    have hc : t ^ 2 * t⁻¹ = t := by field_simp
    rw [← mul_assoc, hc]
    exact mul_le_of_le_one_left hI0 ht.2
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x in Ioo a b, ‖B (x, t)‖ ^ 2) ≤ ∫ x : ℝ, ‖M x‖ ^ 2 :=
    (setIntegral_le_integral (hslice t ht).1
      (Eventually.of_forall fun _ ↦ sq_nonneg _)).trans (hslice t ht).2
  have houter : Integrable (fun t ↦ ∫ x in Ioo a b, ‖B (x, t)‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply (integrable_const (∫ x : ℝ, ‖M x‖ ^ 2)).mono'
      ((hBm.norm.pow_const 2).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
    exact hbound t ht
  have hprod : Integrable (fun p ↦ ‖B p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    apply (integrable_prod_iff' (hBm.norm.pow_const 2).aestronglyMeasurable).2
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (hslice t ht).1.integrableOn
    · simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using houter
  refine ⟨(memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable).2 hprod, ?_⟩
  rw [integral_prod_symm _ hprod]
  have hi := integral_mono_ae houter (integrable_const (∫ x : ℝ, ‖M x‖ ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht ↦ hbound t ht))
  simpa using hi

private theorem segment_mem_Icc {a b z x t : ℝ} (hz : z ∈ Icc a b)
    (hx : x ∈ Icc a b) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x + (1 - t) * z ∈ Icc a b := by
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.2 hx.1),
      mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hz.1)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.2 hx.2),
      mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hz.2)]

private theorem segment_average_h1 {G M : ℝ → ℂ} (hG : Continuous G)
    (hM : Measurable M) (hML : MemLp M 2 volume) {a b z : ℝ} (hab : a < b)
    (hz : z ∈ Icc a b)
    (hFTC : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, (∫ x in c..d, M x) = G d - G c) :
    ∃ Q₁ : ℝ → ℂ,
      HasIntervalH1 a b (fun x ↦ ∫ t in Icc (0 : ℝ) 1,
        G (t * x + (1 - t) * z)) Q₁ ∧
      (∫ x in Ioo a b, ‖Q₁ x‖ ^ 2) ≤ ∫ x : ℝ, ‖M x‖ ^ 2 := by
  let B : ℝ × ℝ → ℂ := fun p ↦ p.2 • M (p.2 * p.1 + (1 - p.2) * z)
  let Q := fun x ↦ ∫ t in Icc (0 : ℝ) 1, G (t * x + (1 - t) * z)
  let Q₁ := fun x ↦ ∫ t in Icc (0 : ℝ) 1, B (x, t)
  have hBm : Measurable B := by dsimp [B]; fun_prop
  obtain ⟨hBL, hBE⟩ := weighted_segment_l2 hM hML a b z
  have hBs : Integrable (fun p ↦ ‖B p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    hBL.integrable_norm_pow (by norm_num)
  have hQ₁m : AEStronglyMeasurable Q₁ (volume.restrict (Ioo a b)) :=
    hBm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ‖Q₁ x‖ ^ 2 ≤ ∫ t in Icc (0 : ℝ) 1, ‖B (x, t)‖ ^ 2 := by
    filter_upwards [hBs.prod_right_ae] with x hx
    have hBt : MemLp (fun t ↦ B (x, t)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLp_two_iff_integrable_sq_norm
        ((hBm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).2 hx
    have hi := norm_intervalIntegral_sq_le zero_le_one hBt
    simpa only [Q₁, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc, sub_zero, one_mul] using hi
  have hQ₁s : IntegrableOn (fun x ↦ ‖Q₁ x‖ ^ 2) (Ioo a b) := by
    apply hBs.integral_prod_left.mono' (hQ₁m.norm.pow 2)
    filter_upwards [hpoint] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hx
  have hQ₁L := (memLp_two_iff_integrable_sq_norm hQ₁m).2 hQ₁s
  have hQm : AEStronglyMeasurable Q (volume.restrict (Ioo a b)) :=
    (show Measurable (fun p : ℝ × ℝ ↦ G (p.2 * p.1 + (1 - p.2) * z)) by
      fun_prop).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hG.continuousOn : ContinuousOn G (Icc a b))
  have hQL : MemLp Q 2 (volume.restrict (Ioo a b)) := by
    apply MemLp.of_bound hQm C
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hn := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦
        hC _ (segment_mem_Icc hz (Ioo_subset_Icc_self hx) ht))
    simpa only [Q, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, mul_one] using hn
  have hinc : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      (∫ s in x..y, Q₁ s) = Q y - Q x := by
    intro x hx y hy
    have hsub : uIoc x y ⊆ Ioo a b :=
      uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hx hy)
    have hi : Integrable B ((volume.restrict (uIoc x y)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) :=
      (hBL.integrable (by norm_num)).mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
    change (∫ s in x..y, ∫ t in Icc (0 : ℝ) 1, B (s, t)) = _
    rw [intervalIntegral_integral_swap hi]
    calc
      _ = ∫ t in Icc (0 : ℝ) 1,
          G (t * y + (1 - t) * z) - G (t * x + (1 - t) * z) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp only [B]
        rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_add]
        exact hFTC _ (segment_mem_Icc hz (Ioo_subset_Icc_self hx) ht)
          _ (segment_mem_Icc hz (Ioo_subset_Icc_self hy) ht)
      _ = _ := integral_sub
        ((hG.comp (by fun_prop)).integrableOn_Icc)
        ((hG.comp (by fun_prop)).integrableOn_Icc)
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq hab hQ₁L hinc
  refine ⟨Q₁, ⟨hQL, hQ₁L, hac, (ae_restrict_iff' measurableSet_Ioo).1 hder⟩, ?_⟩
  exact (integral_mono_ae hQ₁s hBs.integral_prod_left hpoint).trans
    ((integral_prod _ hBs).symm.le.trans hBE)

/-- Segment averaging preserves interval H¹ with a universal derivative-energy bound.
The integrand uses the canonical continuous representative at every point of the segment. -/
theorem HasIntervalH1.segmentAverage {a b z : ℝ} {F D : ℝ → ℂ}
    (hF : HasIntervalH1 a b F D) (hab : a < b) (hz : z ∈ Icc a b) :
    ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 a b Q Q₁ ∧
      (∀ x ∈ Icc a b, Q x = ∫ t in (0 : ℝ)..1,
        intervalH1Extension a b F D (t * x + (1 - t) * z)) ∧
      (∫ x in Ioo a b, ‖Q₁ x‖ ^ 2) ≤ ∫ x in Ioo a b, ‖D x‖ ^ 2 := by
  let E := intervalZeroExtension a b D
  have hEL : MemLp E 2 volume := memLp_intervalZeroExtension hF.memLp_derivative
  let M := hEL.aestronglyMeasurable.mk E
  have hM : Measurable M := hEL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : E =ᵐ[volume] M := hEL.aestronglyMeasurable.ae_eq_mk
  have hML : MemLp M 2 volume := hEL.ae_eq he
  let G := fun x ↦ intervalH1Extension a b F D (max a (min b x))
  have hG : Continuous G := (hF.continuousOn_extension hab).comp_continuous (by fun_prop)
    (fun x ↦ ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩)
  have hGeq (x : ℝ) (hx : x ∈ Icc a b) : G x = intervalH1Extension a b F D x := by
    dsimp only [G]
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hFTC : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, (∫ x in c..d, M x) = G d - G c := by
    intro c hc d hd
    calc
      _ = ∫ x in c..d, E x :=
        intervalIntegral.integral_congr_ae (he.symm.mono (fun _ hx _ ↦ hx))
      _ = _ := by rw [intervalIntegral_intervalZeroExtension D hc hd,
        hF.integral_eq_extension_sub hab hc hd, hGeq c hc, hGeq d hd]
  have henergy : (∫ x : ℝ, ‖M x‖ ^ 2) = ∫ x in Ioo a b, ‖D x‖ ^ 2 := by
    calc
      _ = ∫ x : ℝ, ‖E x‖ ^ 2 := integral_congr_ae (he.symm.fun_comp (fun w ↦ ‖w‖ ^ 2))
      _ = _ := by rw [integral_sq_intervalZeroExtension hab.le,
        intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  obtain ⟨Q₁, hQ, hQE⟩ := segment_average_h1 hG hM hML hab hz hFTC
  refine ⟨(fun x ↦ ∫ t in Icc (0 : ℝ) 1, G (t * x + (1 - t) * z)),
    Q₁, hQ, ?_, hQE.trans_eq henergy⟩
  intro x hx
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact hGeq _ (segment_mem_Icc hz hx ht)

end NoEmbeddedEigenvalues
