import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierData
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderSpectralMass

/-!
# Summable mass of the signed cylinder weight

The signed complex basis uses the original normalized measure, with no folding
factors. Splitting integers into natural and strictly negative indices proves the
reciprocal weight has genuine L² mass. Hölder gives actual L¹ of weighted data.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- The order-two weight for signed angular degrees. -/
def cylinderSignedWeight (p : ℝ × ℤ) : ℝ := cylinderSobolevWeight (p.1, p.2.natAbs)

theorem measurable_cylinderAbsModes :
    Measurable (fun p : ℝ × ℤ ↦ (p.1, p.2.natAbs)) :=
  measurable_fst.prodMk ((measurable_of_countable Int.natAbs).comp measurable_snd)

theorem measurable_cylinderSignedWeight : Measurable cylinderSignedWeight :=
  measurable_cylinderSobolevWeight.comp measurable_cylinderAbsModes

theorem one_le_cylinderSignedWeight (p : ℝ × ℤ) : 1 ≤ cylinderSignedWeight p :=
  one_le_cylinderSobolevWeight _

/-- Both signed tails have finite reciprocal quadratic mass. -/
theorem summable_inv_one_add_int_natAbs_sq :
    Summable (fun n : ℤ ↦ (1 + (n.natAbs : ℝ) ^ 2)⁻¹) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa using summable_inv_one_add_nat_sq
  · have he (n : ℕ) : (-(n + 1) : ℤ).natAbs = n + 1 := by
      rw [show -(n + 1 : ℤ) = -((n + 1 : ℕ) : ℤ) by simp]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
    simpa only [he] using (summable_nat_add_iff 1).2 summable_inv_one_add_nat_sq

/-- Genuine reciprocal-weight L² in the normalized signed product measure. -/
theorem memLp_inv_cylinderSignedWeight :
    MemLp (fun p ↦ (cylinderSignedWeight p)⁻¹) 2 cylinderFourierMeasure := by
  apply (memLp_two_iff_integrable_sq
    measurable_cylinderSignedWeight.inv.aestronglyMeasurable).mpr
  have hm : Integrable (fun n : ℤ ↦ (1 + (n.natAbs : ℝ) ^ 2)⁻¹) Measure.count := by
    apply integrable_count_iff.mpr
    exact summable_inv_one_add_int_natAbs_sq.congr fun n ↦
      (Real.norm_of_nonneg (by positivity)).symm
  have hf := integrable_inv_one_add_sq.mono_measure cylinderFrequencyMeasure_le_volume
  have hprod := hf.mul_prod hm
  apply hprod.mono' (measurable_cylinderSignedWeight.inv.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos : 0 < (1 + p.1 ^ 2) * (1 + (p.2.natAbs : ℝ) ^ 2) := by positivity
    have hbound : (1 + p.1 ^ 2) * (1 + (p.2.natAbs : ℝ) ^ 2) ≤
        cylinderSignedWeight p ^ 2 := by
      dsimp only [cylinderSignedWeight, cylinderSobolevWeight]
      nlinarith [sq_nonneg p.1, sq_nonneg (p.2.natAbs : ℝ),
        mul_nonneg (sq_nonneg p.1) (sq_nonneg (p.2.natAbs : ℝ))]
    simpa only [Pi.inv_apply, one_div, mul_inv, ← inv_pow] using
      one_div_le_one_div_of_le hpos hbound

/-- The two-derivative spectral norm supplies actual L¹ of the same data. -/
theorem integrable_of_memLp_cylinderSignedWeight {V : ℝ × ℤ → ℂ}
    (hV : AEStronglyMeasurable V cylinderFourierMeasure)
    (hWV : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * V p) 2 cylinderFourierMeasure) :
    Integrable V cylinderFourierMeasure := by
  have hprod := memLp_inv_cylinderSignedWeight.integrable_mul hWV.norm
  have hnorm : Integrable (fun p ↦ ‖V p‖) cylinderFourierMeasure := by
    apply hprod.congr
    exact Filter.Eventually.of_forall fun p ↦ by
      have hw := one_le_cylinderSignedWeight p
      dsimp only [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact inv_mul_cancel_left₀ (by linarith : cylinderSignedWeight p ≠ 0) _
  exact (integrable_norm_iff hV).mp hnorm

end NoEmbeddedEigenvalues
