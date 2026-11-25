module

public import EulerDipoleEigenvalues.Analysis.Inequalities.CountableCellEnergy

/-!
# Transfer of cell energies to comparable weights

Blueprint: `lem:cell-weight-transfer`.

Only cellwise comparison with constants is used; the weight need not be smooth.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- Removing a weight bounded below by one preserves the raw L² class. -/
theorem memLp_of_sqrt_weight_ge_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ} {F : α → ℂ} (hW : Measurable W) (h1 : ∀ᵐ x ∂μ, 1 ≤ W x)
    (hF : MemLp (fun x ↦ (Real.sqrt (W x) : ℂ) * F x) 2 μ) : MemLp F 2 μ := by
  have hw : Measurable (fun x ↦ (Real.sqrt (W x) : ℂ)) := by fun_prop
  have he : (fun x ↦ ((Real.sqrt (W x) : ℂ) * F x) / (Real.sqrt (W x) : ℂ)) =ᵐ[μ] F := by
    filter_upwards [h1] with x hx
    have hn := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (zero_lt_one.trans_le hx)).ne'
    field_simp
  apply hF.of_le_mul (c := 1) ((hF.aestronglyMeasurable.div₀ hw.aestronglyMeasurable).congr he)
  filter_upwards [h1] with x hx
  rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_mul_of_one_le_left (norm_nonneg _) (by simpa using Real.sqrt_le_sqrt hx)

/-- A cell estimate transfers to a weight between a nonnegative cell constant
and a fixed multiple of that constant. Both weighted energies are genuine integrals. -/
theorem sqrt_weight_cell_energy {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W G : α → ℝ} {F : α → ℂ} {A w K : ℝ} (hW : Measurable W)
    (hw : 0 ≤ w) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hcomp : ∀ᵐ x ∂μ, w ≤ W x ∧ W x ≤ A * w) (hGpos : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hG : Integrable G μ) (hWG : Integrable (fun x ↦ W x * G x) μ) (hF : MemLp F 2 μ)
    (hbound : (∫ x, ‖F x‖ ^ 2 ∂μ) ≤ K * ∫ x, G x ∂μ) :
    MemLp (fun x ↦ (Real.sqrt (W x) : ℂ) * F x) 2 μ ∧
      (∫ x, ‖(Real.sqrt (W x) : ℂ) * F x‖ ^ 2 ∂μ) ≤
        A * K * ∫ x, W x * G x ∂μ := by
  have hFm : AEStronglyMeasurable (fun x ↦ (Real.sqrt (W x) : ℂ) * F x) μ :=
    ((by fun_prop : Measurable (fun x ↦ (Real.sqrt (W x) : ℂ))).aestronglyMeasurable).mul
      hF.aestronglyMeasurable
  have hFn := hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hle : ∀ᵐ x ∂μ, ‖(Real.sqrt (W x) : ℂ) * F x‖ ^ 2 ≤ (A * w) * ‖F x‖ ^ 2 := by
    filter_upwards [hcomp] with x hx
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw.trans hx.1)]
    exact mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)
  have hFI : Integrable (fun x ↦ ‖(Real.sqrt (W x) : ℂ) * F x‖ ^ 2) μ :=
    (hFn.const_mul (A * w)).mono' (hFm.norm.pow 2) (by
      filter_upwards [hle] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(Real.sqrt (W x) : ℂ) * F x‖)]
      exact hx)
  refine ⟨(memLp_two_iff_integrable_sq_norm hFm).2 hFI, ?_⟩
  have hGI : w * (∫ x, G x ∂μ) ≤ ∫ x, W x * G x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hG.const_mul _) hWG
    filter_upwards [hcomp, hGpos] with x hx hg
    exact mul_le_mul_of_nonneg_right hx.1 hg
  calc
    _ ≤ ∫ x, (A * w) * ‖F x‖ ^ 2 ∂μ := integral_mono_ae hFI (hFn.const_mul _) hle
    _ = (A * w) * ∫ x, ‖F x‖ ^ 2 ∂μ := integral_const_mul ..
    _ ≤ (A * w) * (K * ∫ x, G x ∂μ) := mul_le_mul_of_nonneg_left hbound (mul_nonneg hA hw)
    _ = (A * K) * (w * ∫ x, G x ∂μ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hGI (mul_nonneg hA hK)

end EulerDipoleEigenvalues
