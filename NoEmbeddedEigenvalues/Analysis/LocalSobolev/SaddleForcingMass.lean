module

public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.SaddleStreamJet
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleDistanceWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Ordinary forcing mass near quadratic saddles

Blueprint: `lem:saddle-quadratic-forcing-mass`.

The square of the quadratic-gradient weight is bounded by a constant times
inverse Euclidean radius, integrable in two physical dimensions. Remainder
weights can then be weakened without any logarithmic multiplier.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Inverse Euclidean radius is integrable on every bounded disk. -/
theorem integrableOn_inv_localRadius (c : ℝ × ℝ) (ρ : ℝ) :
    IntegrableOn (fun p ↦ (localRadius c p)⁻¹) (localDisk c ρ) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hR : Measurable (localRadius (0 : ℝ × ℝ)) := by unfold localRadius; fun_prop
  have hi : IntegrableOn (fun q : ℝ × ℝ ↦ (localRadius 0 q)⁻¹)
      (Metric.ball 0 ρ) := by
    apply integrableOn_ball_of_norm_le_rpow (E := ℝ × ℝ) (μ := volume)
      (C := 1) (α := 1) (by simp [Module.finrank_prod])
      (by simp [Module.finrank_prod])
      ?_ hR.inv.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    dsimp only [Pi.inv_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (show 0 ≤ localRadius 0 q from Real.sqrt_nonneg _)),
      one_mul, Real.rpow_neg_one]
    by_cases hq : q = 0
    · simp [hq, localRadius]
    · exact inv_anti₀ (norm_pos_iff.mpr hq)
        (by simpa only [dist_zero_right] using dist_le_localRadius 0 q)
  have hi0 := hi.mono_set (show localDisk 0 ρ ⊆ Metric.ball 0 ρ from
    fun q hq ↦ (dist_le_localRadius 0 q).trans_lt hq)
  let e := Homeomorph.addRight c
  have hpre : e ⁻¹' localDisk c ρ = localDisk 0 ρ := by
    ext q
    simp [e, localDisk, localRadius]
  have hcR (q : ℝ × ℝ) : localRadius c (e q) = localRadius 0 q := by
    simp [e, localRadius]
  apply (measurePreserving_add_right volume c).integrableOn_comp_preimage
    e.measurableEmbedding |>.mp
  change IntegrableOn ((fun p ↦ (localRadius c p)⁻¹) ∘ e) (e ⁻¹' localDisk c ρ)
  rw [hpre]
  simpa only [Function.comp_def, hcR] using hi0

/-- The inverse square root is a genuine L² function, not just a finite
expression for its totalized norm. -/
theorem memLp_inv_sqrt_localRadius (c : ℝ × ℝ) (ρ : ℝ) :
    MemLp (fun p ↦ (Real.sqrt (localRadius c p) : ℂ)⁻¹) 2
      (volume.restrict (localDisk c ρ)) := by
  have hm : Measurable (fun p ↦ (Real.sqrt (localRadius c p) : ℂ)⁻¹) := by
    unfold localRadius
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have he : (fun p ↦ ‖(Real.sqrt (localRadius c p) : ℂ)⁻¹‖ ^ 2) =
      (fun p ↦ (localRadius c p)⁻¹) := by
    funext p
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
  rw [he]
  exact integrableOn_inv_localRadius c ρ

/-- Quadratic growth of the value, with its original coefficient. -/
theorem norm_saddleQuadratic_le (c : ℝ × ℝ) (a : ℂ) (p : ℝ × ℝ) :
    ‖saddleQuadratic c a p‖ ≤ ‖a * (Real.cos c.1 : ℂ) / 2‖ * localRadius c p ^ 2 := by
  have hs : localRadius c p ^ 2 = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold saddleQuadratic
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (p.1 - c.1), sq_nonneg (p.2 - c.2)]

/-- Both ordinary forcing weights of a quadratic have finite mass on every
bounded disk. The gradient needs the two-dimensional inverse-radius integral. -/
theorem saddleQuadratic_forcing_mass (c : ℝ × ℝ) (a : ℂ) (ρ : ℝ) :
    MemLp (fun p ↦ saddleQuadratic c a p / (localRadius c p ^ 2 : ℂ)) 2
      (volume.restrict (localDisk c ρ)) ∧
    ∀ j : Fin 2, MemLp (fun p ↦ classicalComplexJet [j] (saddleQuadratic c a) p /
      (Real.rpow (localRadius c p) (3 / 2) : ℂ)) 2
      (volume.restrict (localDisk c ρ)) := by
  have hR : Measurable (localRadius c) := by unfold localRadius; fun_prop
  have : IsFiniteMeasure (volume.restrict (localDisk c ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    exact (Metric.isBounded_ball.subset (show localDisk c ρ ⊆ Metric.ball c ρ from
      fun p hp ↦ (dist_le_localRadius c p).trans_lt hp)).measure_lt_top.ne
  constructor
  · have hm : Measurable (fun p ↦ saddleQuadratic c a p /
        (localRadius c p ^ 2 : ℂ)) := by unfold saddleQuadratic localRadius; fun_prop
    have hb : MemLp (fun _ : ℝ × ℝ ↦ ‖a * (Real.cos c.1 : ℂ) / 2‖) 2
        (volume.restrict (localDisk c ρ)) := memLp_const _
    apply hb.mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
    by_cases hr : localRadius c p = 0
    · simp only [hr, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      exact norm_nonneg (a * (Real.cos c.1 : ℂ) / 2)
    · exact (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr (norm_saddleQuadratic_le c a p)
  · intro j
    have hQ : Measurable (classicalComplexJet [j] (saddleQuadratic c a)) := by
      have he := funext (first_saddleQuadratic c a j)
      rw [he]
      unfold axisCoord
      split_ifs <;> fun_prop
    have hb : MemLp (fun p ↦ classicalComplexJet [j] (saddleQuadratic c a) p /
        (localRadius c p : ℂ)) ⊤ (volume.restrict (localDisk c ρ)) := by
      apply memLp_top_of_bound (hQ.div (Complex.continuous_ofReal.measurable.comp
        hR)).aestronglyMeasurable ‖a * (Real.cos c.1 : ℂ)‖
      apply Filter.Eventually.of_forall
      intro p
      dsimp only [Pi.div_apply, Function.comp_apply]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
      by_cases hr : localRadius c p = 0
      · simp only [hr, div_zero]
        exact norm_nonneg _
      · exact (div_le_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))).mpr
          (norm_first_saddleQuadratic_le c a j p)
    apply (hb.mul (memLp_inv_sqrt_localRadius c ρ)).ae_eq
    apply Filter.Eventually.of_forall
    intro p
    have he : Real.rpow (localRadius c p) (3 / 2) =
        localRadius c p * Real.sqrt (localRadius c p) := by
      by_cases hr : localRadius c p = 0
      · simp [hr, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      · have hrpos : 0 < localRadius c p :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
        rw [Real.sqrt_eq_rpow]
        simp only [Real.rpow_eq_pow]
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add hrpos, Real.rpow_one]
    dsimp only [Pi.mul_apply]
    rw [he]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end NoEmbeddedEigenvalues
