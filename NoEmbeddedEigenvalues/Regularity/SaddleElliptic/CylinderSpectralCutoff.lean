import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderJetCandidates
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Simultaneous finite-mass spectral approximation

A single measurable finite-mass exhaustion gives integrable truncations of
every L² spectrum and every specified derivative spectrum. Inverse isometry
transfers strong L² convergence. Frequency bounds or higher differentiability
of a spectral cutoff are unnecessary: kernel integration by parts only needs
the two actual spectra in each weak pair to be integrable.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology
local instance : SigmaFinite cylinderFourierMeasure := by
  unfold cylinderFourierMeasure
  infer_instance

/-- One common finite-mass cutoff, applied to each ordered derivative spectrum. -/
def cylinderSpectralCutoff (N : ℕ) (H : ℝ × ℤ → ℂ) : ℝ × ℤ → ℂ :=
  (spanningSets cylinderFourierMeasure N).indicator H

theorem cylinderSpectralCutoff_memLp {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) (N : ℕ) :
    MemLp (cylinderSpectralCutoff N H) 2 cylinderFourierMeasure :=
  hH.indicator (measurableSet_spanningSets _ _)

/-- Integrability is derived for the truncation, not assumed of the original spectrum. -/
theorem cylinderSpectralCutoff_integrable {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) (N : ℕ) :
    Integrable (cylinderSpectralCutoff N H) cylinderFourierMeasure := by
  let : IsFiniteMeasure (cylinderFourierMeasure.restrict
      (spanningSets cylinderFourierMeasure N)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top _ _).ne
  apply (integrable_indicator_iff (measurableSet_spanningSets _ _)).mpr
  exact (hH.restrict (spanningSets cylinderFourierMeasure N)).integrable (by norm_num)

/-- Multiplication by any ordered symbol commutes with the very same cutoff. -/
theorem cylinderSpectralJet_cutoff (w : List (Fin 2)) (N : ℕ) (H : ℝ × ℤ → ℂ) :
    cylinderSpectralJet w (cylinderSpectralCutoff N H) =
      cylinderSpectralCutoff N (cylinderSpectralJet w H) := by
  funext p
  by_cases hp : p ∈ spanningSets cylinderFourierMeasure N <;>
    simp [cylinderSpectralJet, cylinderSpectralCutoff, hp]

theorem cylinderSpectralCutoff_tendsto {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) :
    Tendsto (fun N ↦ (cylinderSpectralCutoff_memLp hH N).toLp (cylinderSpectralCutoff N H))
      atTop (𝓝 (hH.toLp H)) := by
  have hi : Tendsto (fun N ↦ ∫ p, ‖cylinderSpectralCutoff N H p - H p‖ ^ 2
      ∂cylinderFourierMeasure) atTop (𝓝 0) := by
    have hb := (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH
    have h := tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ))
      (bound := fun p ↦ ‖H p‖ ^ 2)
      (fun N ↦ ((cylinderSpectralCutoff_memLp hH N).sub hH).aestronglyMeasurable.norm.pow 2)
      hb
      (fun N ↦ Filter.Eventually.of_forall fun p ↦ by
        by_cases hp : p ∈ spanningSets cylinderFourierMeasure N <;>
          simp [cylinderSpectralCutoff, hp])
      (Filter.Eventually.of_forall fun p ↦ by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_mem_spanningSets cylinderFourierMeasure p] with N hN
        simp [cylinderSpectralCutoff, hN])
    simpa using h
  have he (N : ℕ) :
      ‖(cylinderSpectralCutoff_memLp hH N).toLp (cylinderSpectralCutoff N H) -
        hH.toLp H‖ ^ 2 =
        ∫ p, ‖cylinderSpectralCutoff N H p - H p‖ ^ 2 ∂cylinderFourierMeasure := by
    rw [cylinderL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      ((cylinderSpectralCutoff_memLp hH N).toLp (cylinderSpectralCutoff N H)) (hH.toLp H),
      (cylinderSpectralCutoff_memLp hH N).coeFn_toLp, hH.coeFn_toLp] with p hs hN h
    simp only [hs, Pi.sub_apply, hN, h]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hi.sqrt

theorem cylinderJointSynthesis_cutoff_memLp {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) (N : ℕ) :
    MemLp (cylinderJointSynthesis (cylinderSpectralCutoff N H)) 2 logCylinderMeasure :=
  cylinderJointSynthesis_memLp (cylinderSpectralCutoff_integrable hH N)
    (cylinderSpectralCutoff_memLp hH N)

/-- Actual integrable inverse approximants converge to the arbitrary L² inverse class. -/
theorem cylinderJointSynthesis_cutoff_tendsto {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) :
    Tendsto (fun N ↦ (cylinderJointSynthesis_cutoff_memLp hH N).toLp
      (cylinderJointSynthesis (cylinderSpectralCutoff N H))) atTop
      (𝓝 (cylinderInverseL2 (hH.toLp H))) := by
  have he (N : ℕ) : (cylinderJointSynthesis_cutoff_memLp hH N).toLp
      (cylinderJointSynthesis (cylinderSpectralCutoff N H)) =
      cylinderInverseL2 ((cylinderSpectralCutoff_memLp hH N).toLp
        (cylinderSpectralCutoff N H)) := by
    apply Lp.ext
    exact (cylinderJointSynthesis_cutoff_memLp hH N).coeFn_toLp.trans
      (cylinderInverseL2_ae_integral (cylinderSpectralCutoff_integrable hH N)
        (cylinderSpectralCutoff_memLp hH N)).symm
  simp only [he]
  exact (cylinderInverseL2.continuous.tendsto _).comp (cylinderSpectralCutoff_tendsto hH)

end NoEmbeddedEigenvalues
