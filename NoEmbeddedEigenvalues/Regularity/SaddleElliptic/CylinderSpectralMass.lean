module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderSymbol
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spectral mass for the logarithmic cylinder

The reciprocal order-two weight is genuinely L² for real logarithmic frequency
and counting measure on nonnegative angular modes. A separable integrable
majorant proves this without evaluating an improper integral. Hölder then gives
L¹ spectral data from the weighted L² norm used by the cylinder inverse.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Lebesgue frequency measure times counting measure on angular degrees. -/
def cylinderSpectralMeasure : Measure (ℝ × ℕ) := volume.prod Measure.count

/-- Summable angular mass, including the zero mode. -/
theorem summable_inv_one_add_nat_sq :
    Summable (fun m : ℕ ↦ (1 + (m : ℝ) ^ 2)⁻¹) := by
  have hs : Summable (fun m : ℕ ↦ 1 / ((m : ℝ) + 1) ^ 2) := by
    simpa only [Real.rpow_ofNat, sq_abs] using
      (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun m ↦ by positivity) (fun m ↦ ?_) (hs.mul_left 2)
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have h1 : 0 < 1 + (m : ℝ) ^ 2 := by positivity
  have h2 : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
  rw [show (1 + (m : ℝ) ^ 2)⁻¹ = 1 / (1 + (m : ℝ) ^ 2) from (one_div _).symm,
    ← mul_div_assoc]
  apply (div_le_div_iff₀ h1 h2).mpr
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

/-- Actual integrability of the squared reciprocal spectral Sobolev weight. -/
theorem integrable_sq_inv_cylinderSobolevWeight :
    Integrable (fun p ↦ (cylinderSobolevWeight p)⁻¹ ^ 2) cylinderSpectralMeasure := by
  have hm : Integrable (fun m : ℕ ↦ (1 + (m : ℝ) ^ 2)⁻¹) Measure.count := by
    apply integrable_count_iff.mpr
    exact summable_inv_one_add_nat_sq.congr fun m ↦ (Real.norm_of_nonneg (by positivity)).symm
  have hprod := integrable_inv_one_add_sq.mul_prod hm
  have hmeas : Measurable (fun p ↦ (cylinderSobolevWeight p)⁻¹ ^ 2) :=
    measurable_cylinderSobolevWeight.inv.pow_const 2
  apply hprod.mono' hmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos : 0 < (1 + p.1 ^ 2) * (1 + (p.2 : ℝ) ^ 2) := by positivity
    have hbound : (1 + p.1 ^ 2) * (1 + (p.2 : ℝ) ^ 2) ≤ cylinderSobolevWeight p ^ 2 := by
      dsimp only [cylinderSobolevWeight]
      nlinarith [sq_nonneg p.1, sq_nonneg (p.2 : ℝ),
        mul_nonneg (sq_nonneg p.1) (sq_nonneg (p.2 : ℝ))]
    simpa only [one_div, mul_inv, ← inv_pow] using one_div_le_one_div_of_le hpos hbound

/-- The reciprocal spectral weight belongs to L², not just a totalized energy. -/
theorem memLp_inv_cylinderSobolevWeight :
    MemLp (fun p ↦ (cylinderSobolevWeight p)⁻¹) 2 cylinderSpectralMeasure := by
  exact (memLp_two_iff_integrable_sq
    measurable_cylinderSobolevWeight.inv.aestronglyMeasurable).mpr
      integrable_sq_inv_cylinderSobolevWeight

/-- Weighted L² spectral data are L¹, also after restriction to allowed modes. -/
theorem integrable_of_memLp_cylinderSobolevWeight {μ : Measure (ℝ × ℕ)}
    (hμ : μ ≤ cylinderSpectralMeasure) {V : ℝ × ℕ → ℂ}
    (hV : AEStronglyMeasurable V μ)
    (hWV : MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ) :
    Integrable V μ := by
  have hK := memLp_inv_cylinderSobolevWeight.mono_measure hμ
  have hprod := hK.integrable_mul hWV.norm
  have hnorm : Integrable (fun p ↦ ‖V p‖) μ := by
    apply hprod.congr
    exact Filter.Eventually.of_forall fun p ↦ by
      have hw := one_le_cylinderSobolevWeight p
      dsimp only [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact inv_mul_cancel_left₀ (by linarith : cylinderSobolevWeight p ≠ 0) _
  exact (integrable_norm_iff hV).mp hnorm

end NoEmbeddedEigenvalues
