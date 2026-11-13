import NoEmbeddedEigenvalues.SaddleDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Critical inverse-radius nonintegrability

In two physical dimensions inverse squared Euclidean radius is not locally
integrable at its center. This distinguishes a genuine weighted L² condition
from the totalized value of an integral, and detects constant Hessian defects.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The critical inverse-square weight is not integrable on any disk centered
at its singularity. The proof compares the Euclidean and product radii. -/
theorem not_integrableOn_inv_sq_localRadius (c : ℝ × ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ¬IntegrableOn (fun p ↦ (localRadius c p ^ 2)⁻¹) (localDisk c ρ) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  intro hi
  let e := Homeomorph.addRight c
  have hpre : e ⁻¹' localDisk c ρ = localDisk 0 ρ := by
    ext q
    simp [e, localDisk, localRadius]
  have hcR (q : ℝ × ℝ) : localRadius c (e q) = localRadius 0 q := by
    simp [e, localRadius]
  have hi0 := (measurePreserving_add_right volume c).integrableOn_comp_preimage
    e.measurableEmbedding |>.mpr hi
  change IntegrableOn ((fun p ↦ (localRadius c p ^ 2)⁻¹) ∘ e)
    (e ⁻¹' localDisk c ρ) at hi0
  simp only [hpre, Function.comp_def, hcR] at hi0
  have hb : Metric.ball (0 : ℝ × ℝ) (ρ / 2) ⊆ localDisk 0 ρ := by
    intro p hp
    have hr := localRadius_le_two_dist (0 : ℝ × ℝ) p
    exact hr.trans_lt (by linarith [Metric.mem_ball.mp hp])
  have hn : IntegrableOn (fun p : ℝ × ℝ ↦ (‖p‖ ^ 2)⁻¹)
      (Metric.ball 0 (ρ / 2)) := by
    apply ((hi0.mono_set hb).const_mul 4).mono' (by fun_prop)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hp : p = 0
    · simp [hp, localRadius]
    · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
      have hR : 0 < localRadius 0 p := lt_of_lt_of_le hn
        (by simpa only [dist_zero_right] using dist_le_localRadius 0 p)
      have hle : localRadius 0 p ≤ 2 * ‖p‖ := by
        simpa only [dist_zero_right] using localRadius_le_two_dist 0 p
      suffices 1 / ‖p‖ ^ 2 ≤ 4 / localRadius 0 p ^ 2 by
        simpa only [one_div, div_eq_mul_inv, one_mul] using this
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_le_mul hle hle hR.le (by positivity : 0 ≤ 2 * ‖p‖)]
  have hone := (integrableOn_fun_norm_addHaar (volume : Measure (ℝ × ℝ))
    (f := fun r : ℝ ↦ (r ^ 2)⁻¹)).mp hn
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioo 0 (ρ / 2)) := by
    apply hone.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Module.finrank_prod, Module.finrank_self, Nat.add_sub_cancel,
      pow_one, smul_eq_mul]
    field_simp
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo 0 (ρ / 2)) := by
    simpa only [Real.rpow_neg_one] using hinv
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity : 0 < ρ / 2)).mp hpow
  norm_num at this

/-- A nonzero constant divided by radius squared cannot be L² on a disk.
In particular, an admissible weighted Hessian cannot have a constant defect. -/
theorem memLp_const_div_sq_localRadius_iff (c : ℝ × ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) :
    MemLp (fun p ↦ z / (localRadius c p ^ 2 : ℂ)) 2
      (volume.restrict (localDisk c ρ)) ↔ z = 0 := by
  constructor
  · intro hz
    by_contra hne
    have hB : Bornology.IsBounded (localDisk c ρ) :=
      Metric.isBounded_ball.subset fun p hp ↦ (dist_le_localRadius c p).trans_lt hp
    have : IsFiniteMeasure (volume.restrict (localDisk c ρ)) :=
      isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
    have hi : MemLp (fun p ↦ ((localRadius c p : ℂ) ^ 2)⁻¹) 2
        (volume.restrict (localDisk c ρ)) := by
      apply (hz.const_mul z⁻¹).ae_eq
      exact Filter.Eventually.of_forall fun p ↦ by
        dsimp only
        field_simp
    have hint := (hi.integrable (by norm_num)).norm
    have he : (fun p ↦ ‖((localRadius c p : ℂ) ^ 2)⁻¹‖) =
        (fun p ↦ (localRadius c p ^ 2)⁻¹) := by
      funext p
      rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
    rw [he] at hint
    exact not_integrableOn_inv_sq_localRadius c hρ hint
  · rintro rfl
    simp only [zero_div]
    exact MemLp.zero'

end NoEmbeddedEigenvalues
