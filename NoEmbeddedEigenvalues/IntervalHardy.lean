import NoEmbeddedEigenvalues.HardyAverage
import NoEmbeddedEigenvalues.IntervalZeroExtension

/-!
# Hardy division for interval Sobolev representatives

Blueprint: `lem:hardy-endpoint`.

The endpoint fundamental theorem identifies a zero-trace H¹ representative with
an integral primitive of its zero-extended derivative. The half-line primitive
Hardy inequality supplies finite squared quotient energy with constant four.
Endpoint values throughout are canonical traces, not raw assignments.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ENNReal

private theorem HasIntervalH1.lintegral_hardy_endpoint {η : ℝ} (hη : 0 < η)
    {F D : ℝ → ℂ} (hF : HasIntervalH1 0 η F D)
    (h0 : intervalH1Extension 0 η F D 0 = 0) :
    (∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖F x / (x : ℂ)‖ ^ 2)) ≤
      4 * ∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖D x‖ ^ 2) := by
  let E := intervalZeroExtension 0 η D
  have hEi : Integrable E := integrable_intervalZeroExtension hF.memLp_derivative
  have hprim (x : ℝ) (hx : x ∈ Ioo 0 η) : (∫ t in (0 : ℝ)..x, E t) = F x := by
    rw [intervalIntegral_intervalZeroExtension D ⟨le_rfl, hη.le⟩
      (Ioo_subset_Icc_self hx), hF.integral_eq_extension_sub hη ⟨le_rfl, hη.le⟩
        (Ioo_subset_Icc_self hx), h0, sub_zero, hF.extension_eq hη hx]
  have henergy : (∫⁻ x, ENNReal.ofReal (‖E x‖ ^ 2)) =
      ∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖D x‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo 0 η <;> simp [E, intervalZeroExtension, hx]
  calc
    _ = ∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖∫ t in (0 : ℝ)..x, E t‖ ^ 2 / x ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [hprim x hx, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (‖∫ t in (0 : ℝ)..x, E t‖ ^ 2 / x ^ 2) :=
      lintegral_mono_set (fun _ hx ↦ hx.1)
    _ ≤ 4 * ∫⁻ x in Ioi 0, ENNReal.ofReal (‖E x‖ ^ 2) :=
      lintegral_sq_primitive_div_sq_le_of_integrable hEi
    _ ≤ 4 * ∫⁻ x, ENNReal.ofReal (‖E x‖ ^ 2) := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by rw [henergy]

/-- Endpoint Hardy with an explicit integrability conclusion (`lem:hardy-endpoint`). -/
theorem HasIntervalH1.hardy_endpoint {η : ℝ} (hη : 0 < η) {F D : ℝ → ℂ}
    (hF : HasIntervalH1 0 η F D) (h0 : intervalH1Extension 0 η F D 0 = 0) :
    MemLp (fun x ↦ F x / (x : ℂ)) 2 (volume.restrict (Ioo 0 η)) ∧
      (∫ x in Ioo 0 η, ‖F x / (x : ℂ)‖ ^ 2) ≤
        4 * ∫ x in Ioo 0 η, ‖D x‖ ^ 2 := by
  have hbound := hF.lintegral_hardy_endpoint hη h0
  have hDm : IntegrableOn (fun x ↦ ‖D x‖ ^ 2) (Ioo 0 η) :=
    hF.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hDnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 η)] (fun x ↦ ‖D x‖ ^ 2) :=
    Eventually.of_forall (fun _ ↦ sq_nonneg _)
  have hfiniteD : (∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖D x‖ ^ 2)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hDnonneg).1 hDm.hasFiniteIntegral
  have hfiniteQ : (∫⁻ x in Ioo 0 η, ENNReal.ofReal (‖F x / (x : ℂ)‖ ^ 2)) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top (by norm_num) hfiniteD)
  have hQmeas : AEStronglyMeasurable (fun x ↦ F x / (x : ℂ))
      (volume.restrict (Ioo 0 η)) :=
    hF.memLp_value.aestronglyMeasurable.div₀ (by fun_prop)
  have hQnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 η)] (fun x ↦ ‖F x / (x : ℂ)‖ ^ 2) :=
    Eventually.of_forall (fun _ ↦ sq_nonneg _)
  have hQint : IntegrableOn (fun x ↦ ‖F x / (x : ℂ)‖ ^ 2) (Ioo 0 η) :=
    ⟨hQmeas.norm.pow 2, (hasFiniteIntegral_iff_ofReal hQnonneg).2 hfiniteQ⟩
  refine ⟨(memLp_two_iff_integrable_sq_norm hQmeas).2 hQint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hQint hQnonneg,
    ← ofReal_integral_eq_lintegral_ofReal hDm hDnonneg,
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

end NoEmbeddedEigenvalues
