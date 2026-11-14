import NoEmbeddedEigenvalues.Analysis.CylinderJointSynthesis

/-!
# Finite joint mass of the actual cylinder inverse integral

First reconstruct actual real-line time modes, with their genuine L² norms and
summable masses. Angular coefficient extraction and Parseval then identify the
mass of the bounded integral synthesis. In particular, joint finiteness is not
inferred merely from a totalized integral identity or separate mode finiteness.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual inverse time integrals, still indexed by signed angular degree. -/
def cylinderJointTimeModes (H : ℝ × ℤ → ℂ) (q : ℝ × ℤ) : ℂ :=
  cylinderTimeSynthesis (fun ξ ↦ H (ξ, q.2)) q.1

theorem measurable_cylinderJointTimeModes {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) : Measurable (cylinderJointTimeModes H) := by
  apply measurable_from_prod_countable_left
  intro n
  have hc : Continuous (FourierTransform.fourierInv
      (fun η ↦ H ((2 * Real.pi) * η, n)) : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      (measurePreserving_cylinderAngularFrequency.integrable_comp_of_integrable
        (cylinderFourierMeasure_mode_integrable h1 n))
  simpa only [cylinderJointTimeModes, cylinderTimeSynthesis_eq_fourierInv] using hc.measurable

/-- Actual time modes have genuine joint L², not only separate finite norms. -/
theorem cylinderJointTimeModes_memLp {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    MemLp (cylinderJointTimeModes H) 2 (volume.prod Measure.count) := by
  apply memLp_two_prod_count_of_summable_mass
    (measurable_cylinderJointTimeModes h1).aestronglyMeasurable
    (fun n ↦ cylinderTimeSynthesis_memLp
      (cylinderFourierMeasure_mode_integrable h1 n) (cylinderFourierMeasure_mode_memLp h2 n))
  have hs := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hm (n : ℤ) : (∫ t, ‖cylinderJointTimeModes H (t, n)‖ ^ 2) =
      ∫ ξ, ‖H (ξ, n)‖ ^ 2 ∂cylinderFrequencyMeasure :=
    cylinderTimeSynthesis_sq_mass
      (cylinderFourierMeasure_mode_integrable h1 n) (cylinderFourierMeasure_mode_memLp h2 n)
  simp_rw [hm]
  simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))] using
    integrable_count_iff.mp hs.integral_prod_right

/-- Integrated modewise Plancherel uses the actual time-integral family. -/
theorem cylinderJointTimeModes_sq_mass {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    (∫ q, ‖cylinderJointTimeModes H q‖ ^ 2 ∂(volume.prod Measure.count)) =
      ∫ p, ‖H p‖ ^ 2 ∂cylinderFourierMeasure := by
  have ht := cylinderJointTimeModes_memLp h1 h2
  have hi := (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mp ht
  have hs := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  rw [integral_prod_symm _ hi]
  calc
    _ = ∫ n : ℤ, ∫ ξ, ‖H (ξ, n)‖ ^ 2 ∂cylinderFrequencyMeasure ∂Measure.count := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun n ↦ cylinderTimeSynthesis_sq_mass
        (cylinderFourierMeasure_mode_integrable h1 n) (cylinderFourierMeasure_mode_memLp h2 n)
    _ = _ := (integral_prod_symm _ hs).symm

/-- Parseval identifies every angular slice of the continuous integral synthesis. -/
theorem cylinderJointSynthesis_slice_mass {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (t : ℝ) :
    (∫ θ, ‖cylinderJointSynthesis H (t, θ)‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ n : ℤ, ‖cylinderJointTimeModes H (t, n)‖ ^ 2 ∂Measure.count := by
  have hp := hasSum_sq_circle_fourierCoeff (cylinderJointSynthesis_slice_memLp h1 t)
  change HasSum (fun n ↦ ‖cylinderAngularCoeff (cylinderJointSynthesis H) n t‖ ^ 2) _ at hp
  simp only [cylinderJointSynthesis_coeff h1] at hp
  change HasSum (fun n ↦ ‖cylinderJointTimeModes H (t, n)‖ ^ 2) _ at hp
  have hc : Integrable (fun n : ℤ ↦ ‖cylinderJointTimeModes H (t, n)‖ ^ 2) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp.summable
  exact hp.tsum_eq.symm.trans (by simpa using (integral_countable hc).symm)

/-- The bounded integral is genuinely L² on the whole cylinder. -/
theorem cylinderJointSynthesis_memLp {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    MemLp (cylinderJointSynthesis H) 2 logCylinderMeasure := by
  have hm : AEStronglyMeasurable (cylinderJointSynthesis H) logCylinderMeasure :=
    (continuous_cylinderJointSynthesis h1).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_prod_iff (hm.norm.pow 2)).mpr
  refine ⟨Filter.Eventually.of_forall fun t ↦ ?_, ?_⟩
  · have hs := cylinderJointSynthesis_slice_memLp h1 t
    exact (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  · have ht := cylinderJointTimeModes_memLp h1 h2
    have hi := (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mp ht
    apply hi.integral_prod_left.congr
    exact Filter.Eventually.of_forall fun t ↦ by
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using
        (cylinderJointSynthesis_slice_mass h1 t).symm

/-- Exact joint inverse Plancherel, after establishing both actual finite norms. -/
theorem cylinderJointSynthesis_sq_mass {H : ℝ × ℤ → ℂ}
    (h1 : Integrable H cylinderFourierMeasure) (h2 : MemLp H 2 cylinderFourierMeasure) :
    (∫ q, ‖cylinderJointSynthesis H q‖ ^ 2 ∂logCylinderMeasure) =
      ∫ p, ‖H p‖ ^ 2 ∂cylinderFourierMeasure := by
  have hS := cylinderJointSynthesis_memLp h1 h2
  have hT := cylinderJointTimeModes_memLp h1 h2
  have hiS := (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS
  have hiT := (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mp hT
  rw [logCylinderMeasure, integral_prod _ hiS]
  calc
    _ = ∫ t : ℝ, ∫ n : ℤ, ‖cylinderJointTimeModes H (t, n)‖ ^ 2 ∂Measure.count :=
      integral_congr_ae (Filter.Eventually.of_forall (cylinderJointSynthesis_slice_mass h1))
    _ = ∫ q, ‖cylinderJointTimeModes H q‖ ^ 2 ∂(volume.prod Measure.count) :=
      (integral_prod _ hiT).symm
    _ = _ := cylinderJointTimeModes_sq_mass h1 h2

end NoEmbeddedEigenvalues
