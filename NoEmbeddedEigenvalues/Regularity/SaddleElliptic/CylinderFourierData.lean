import Mathlib.Analysis.Real.Pi.Bounds
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourier
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Normalized angular-frequency data

The logarithmic derivative has angular-frequency symbol `I * ξ`, while Mathlib
uses cycle frequency `ξ / (2 * π)`. Transporting its L² transform gives the
frequency measure `dξ / (2 * π)`. Signed angular modes retain counting measure.
A jointly measurable representative is chosen explicitly, before product norms
or a.e. spectral support are asserted.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Angular-frequency measure corresponding to the unitary cycle transform. -/
def cylinderFrequencyMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • volume

/-- Full angular-frequency/signed-mode measure. -/
def cylinderFourierMeasure : Measure (ℝ × ℤ) :=
  cylinderFrequencyMeasure.prod Measure.count

/-- Cycle-frequency rescaling is measure preserving with the stated normalization. -/
theorem measurePreserving_cylinderCycleFrequency :
    MeasurePreserving (fun ξ : ℝ ↦ ξ / (2 * Real.pi)) cylinderFrequencyMeasure volume := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hm : Measure.map (fun ξ : ℝ ↦ ξ / (2 * Real.pi)) volume =
      ENNReal.ofReal (2 * Real.pi) • volume := by
    simpa only [div_eq_mul_inv, inv_inv, abs_of_pos hp] using
      Real.map_volume_mul_right (inv_ne_zero hp.ne')
  refine ⟨by fun_prop, ?_⟩
  rw [cylinderFrequencyMeasure, Measure.map_smul _ (by fun_prop), hm, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hp.ne', ENNReal.ofReal_one, one_smul]

/-- Angular frequency is `2 * π` times cycle frequency. -/
theorem measurePreserving_cylinderAngularFrequency :
    MeasurePreserving (fun η : ℝ ↦ (2 * Real.pi) * η) volume cylinderFrequencyMeasure := by
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨by fun_prop, ?_⟩
  simpa only [cylinderFrequencyMeasure, abs_of_pos (inv_pos.mpr hp)] using
    Real.map_volume_mul_left hp.ne'

/-- The same rescaling is a measurable embedding, so actual integrals transport. -/
theorem measurableEmbedding_cylinderCycleFrequency :
    MeasurableEmbedding (fun ξ : ℝ ↦ ξ / (2 * Real.pi)) := by
  have hn : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  simpa only [div_eq_mul_inv, Homeomorph.toMeasurableEquiv_coe,
    Homeomorph.coe_mulRight₀] using
    (Homeomorph.mulRight₀ ((2 * Real.pi)⁻¹) hn).toMeasurableEquiv.measurableEmbedding

/-- This normalized frequency measure is bounded by Lebesgue measure. -/
theorem cylinderFrequencyMeasure_le_volume : cylinderFrequencyMeasure ≤ volume := by
  have hc : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three]))
  intro s
  change ENNReal.ofReal ((2 * Real.pi)⁻¹) * volume s ≤ volume s
  exact mul_le_of_le_one_left' hc

instance : SigmaFinite cylinderFrequencyMeasure :=
  Measure.sigmaFinite_of_le volume cylinderFrequencyMeasure_le_volume

/-- A jointly measurable representative of the transformed, signed-mode data. -/
def cylinderFourierData {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (p : ℝ × ℤ) : ℂ :=
  ((Lp.aestronglyMeasurable (cylinderFourierMode hG p.2)).mk (cylinderFourierMode hG p.2))
    (p.1 / (2 * Real.pi))

/-- Choosing a measurable representative does not alter the frequency L² class. -/
theorem cylinderFourierData_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    (fun ξ ↦ cylinderFourierData hG (ξ, n)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ cylinderFourierMode hG n (ξ / (2 * Real.pi)) :=
  measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae
    (Lp.aestronglyMeasurable (cylinderFourierMode hG n)).ae_eq_mk.symm

/-- The representative is jointly measurable in real frequency and signed index. -/
theorem measurable_cylinderFourierData {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) : Measurable (cylinderFourierData hG) := by
  apply measurable_from_prod_countable_left
  intro n
  exact (Lp.aestronglyMeasurable (cylinderFourierMode hG n)).measurable_mk.comp (by fun_prop)

/-- Each rescaled spectral mode has a genuinely finite norm. -/
theorem cylinderFourierData_mode_memLp {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    MemLp (fun ξ ↦ cylinderFourierData hG (ξ, n)) 2 cylinderFrequencyMeasure :=
  ((Lp.memLp (cylinderFourierMode hG n)).comp_measurePreserving
    measurePreserving_cylinderCycleFrequency).ae_eq (cylinderFourierData_ae hG n).symm

/-- The angular-frequency density cancels the rescaling Jacobian exactly. -/
theorem cylinderFourierData_mode_mass {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    (∫ ξ, ‖cylinderFourierData hG (ξ, n)‖ ^ 2 ∂cylinderFrequencyMeasure) =
      ‖cylinderFourierMode hG n‖ ^ 2 := by
  calc
    _ = ∫ ξ, ‖cylinderFourierMode hG n (ξ / (2 * Real.pi))‖ ^ 2
        ∂cylinderFrequencyMeasure := by
      apply integral_congr_ae
      filter_upwards [cylinderFourierData_ae hG n] with ξ hξ
      rw [hξ]
    _ = ∫ η, ‖cylinderFourierMode hG n η‖ ^ 2 :=
      measurePreserving_cylinderCycleFrequency.integral_comp
        measurableEmbedding_cylinderCycleFrequency
        (fun η : ℝ ↦ ‖cylinderFourierMode hG n η‖ ^ 2)
    _ = ‖cylinderFourierMode hG n‖ ^ 2 := (cylinderRealL2_norm_sq _).symm

/-- Countable mode families with genuine finite mode masses and a finite sum
have finite joint product mass. Measurability is required jointly. -/
theorem memLp_two_prod_count_of_summable_mass
    {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] {μ : Measure α} [SFinite μ]
    {f : α × ι → ℂ} (hf : AEStronglyMeasurable f (μ.prod Measure.count))
    (hModes : ∀ i, MemLp (fun x ↦ f (x, i)) 2 μ)
    (hSum : Summable (fun i ↦ ∫ x, ‖f (x, i)‖ ^ 2 ∂μ)) :
    MemLp f 2 (μ.prod Measure.count) := by
  apply (memLp_two_iff_integrable_sq_norm hf).mpr
  apply (integrable_prod_iff' (hf.norm.pow 2)).mpr
  constructor
  · exact Filter.Eventually.of_forall fun i ↦
      (memLp_two_iff_integrable_sq_norm (hModes i).aestronglyMeasurable).mp (hModes i)
  · apply integrable_count_iff.mpr
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm,
      Real.norm_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))] using hSum

/-- Joint normalized spectral data are genuinely L², not just modewise L². -/
theorem cylinderFourierData_memLp {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    MemLp (cylinderFourierData hG) 2 cylinderFourierMeasure := by
  apply memLp_two_prod_count_of_summable_mass
    (measurable_cylinderFourierData hG).aestronglyMeasurable
    (cylinderFourierData_mode_memLp hG)
  simpa only [cylinderFourierData_mode_mass] using
    (cylinderFourierMode_hasSum_mass hG).summable

/-- Normalized Plancherel for the full real-frequency and signed angular spectrum. -/
theorem cylinderFourierData_sq_mass {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    (∫ p, ‖cylinderFourierData hG p‖ ^ 2 ∂cylinderFourierMeasure) =
      ∫ q, ‖G q‖ ^ 2 ∂logCylinderMeasure := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (cylinderFourierData_memLp hG).aestronglyMeasurable).mp (cylinderFourierData_memLp hG)
  rw [cylinderFourierMeasure, integral_prod_symm _ hi]
  simp_rw [cylinderFourierData_mode_mass]
  have hc : Integrable (fun n : ℤ ↦ ‖cylinderFourierMode hG n‖ ^ 2) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      (cylinderFourierMode_hasSum_mass hG).summable
  simpa only [Measure.count_singleton, measureReal_def, ENNReal.toReal_one, one_smul,
    (cylinderFourierMode_hasSum_mass hG).tsum_eq] using integral_countable hc

/-- Scalar relations between Fourier classes survive representative choice and
frequency rescaling. The resulting identities are a.e., not pointwise. -/
theorem cylinderFourierData_smul_modes {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) {m n : ℤ} {c : ℂ}
    (hc : cylinderFourierMode hG m = c • cylinderFourierMode hG n) :
    (fun ξ ↦ cylinderFourierData hG (ξ, m)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ c * cylinderFourierData hG (ξ, n) := by
  have he : (cylinderFourierMode hG m : ℝ → ℂ) =ᵐ[volume]
      fun η ↦ c * cylinderFourierMode hG n η := by
    rw [hc]
    filter_upwards [Lp.coeFn_smul c (cylinderFourierMode hG n)] with η hη
    simpa only [Pi.smul_apply, smul_eq_mul] using hη
  filter_upwards [cylinderFourierData_ae hG m, cylinderFourierData_ae hG n,
    measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae he] with ξ hm hn hξ
  rw [hm, hn]
  exact hξ

/-- A forbidden time coefficient gives a zero normalized spectral mode. -/
theorem cylinderFourierData_mode_eq_zero {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) {n : ℤ}
    (hn : cylinderAngularCoeff G n =ᵐ[volume] 0) :
    (fun ξ ↦ cylinderFourierData hG (ξ, n)) =ᵐ[cylinderFrequencyMeasure] 0 := by
  have hz := cylinderFourierMode_eq_zero hG hn
  have he : (cylinderFourierMode hG n : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hz]
    exact Lp.coeFn_zero _ _ _
  exact (cylinderFourierData_ae hG n).trans
    (measurePreserving_cylinderCycleFrequency.quasiMeasurePreserving.ae he)

/-- Rescaling the normalized data back to cycles recovers the Fourier class a.e. -/
theorem cylinderFourierData_rescale_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    (fun η ↦ cylinderFourierData hG ((2 * Real.pi) * η, n)) =ᵐ[volume]
      cylinderFourierMode hG n := by
  have hp : 2 * Real.pi ≠ 0 := by positivity
  filter_upwards [measurePreserving_cylinderAngularFrequency.quasiMeasurePreserving.ae
    (cylinderFourierData_ae hG n)] with η hη
  simpa only [mul_div_cancel_left₀ _ hp] using hη

/-- The normalized spectral mode, returned to cycles as an actual L² class. -/
def cylinderFourierDataMode {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((cylinderFourierData_mode_memLp hG n).comp_measurePreserving
    measurePreserving_cylinderAngularFrequency).toLp
      (fun η ↦ cylinderFourierData hG ((2 * Real.pi) * η, n))

/-- The explicitly rescaled normalized data represent the original Fourier mode. -/
theorem cylinderFourierDataMode_eq {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    cylinderFourierDataMode hG n = cylinderFourierMode hG n := by
  apply Lp.ext
  exact (((cylinderFourierData_mode_memLp hG n).comp_measurePreserving
    measurePreserving_cylinderAngularFrequency).coeFn_toLp).trans
      (cylinderFourierData_rescale_ae hG n)

/-- Inverse L² Fourier analysis of the normalized spectral data recovers the
specified time-dependent coefficient, as a representative identity a.e. -/
theorem cylinderFourierData_inverse_ae {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (n : ℤ) :
    (FourierTransform.fourierInv (cylinderFourierDataMode hG n) : ℝ → ℂ) =ᵐ[volume]
      cylinderAngularCoeff G n := by
  rw [cylinderFourierDataMode_eq, cylinderFourierMode_inverse]
  exact cylinderTimeMode_ae hG n

/-- Mode support of the actual coefficients transports jointly to the spectrum. -/
theorem cylinderFourierData_support {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) {M : Set ℤ}
    (hM : ∀ n, n ∉ M → cylinderAngularCoeff G n =ᵐ[volume] 0) :
    ∀ᵐ p ∂cylinderFourierMeasure, p.2 ∉ M → cylinderFourierData hG p = 0 := by
  have hs : ∀ᵐ ξ ∂cylinderFrequencyMeasure,
      ∀ n : ℤ, n ∉ M → cylinderFourierData hG (ξ, n) = 0 := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : n ∈ M
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hn).elim
    · exact (cylinderFourierData_mode_eq_zero hG (hM n hn)).mono fun _ h _ ↦ h
  exact (Measure.quasiMeasurePreserving_fst.ae hs).mono fun p hp ↦ hp p.2

end NoEmbeddedEigenvalues
