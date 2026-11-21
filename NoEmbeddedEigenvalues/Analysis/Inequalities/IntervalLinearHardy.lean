import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalHardy
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Energy of division at an interior zero

Blueprint: `lem:hardy-interior-linear`.

The two orientations of the primitive Hardy inequality control division by
`x - z`. Values at the single zero are immaterial for the energy estimate.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ENNReal

/-- Split at the interior zero and use only the derivative energy on each side. -/
theorem HasIntervalH1.lintegral_hardy_interior {a b z : ℝ} {N D U : ℝ → ℂ}
    (hN : HasIntervalH1 a b N D) (hz : z ∈ Ioo a b) (hzero : N z = 0)
    (hfactor : ∀ x ∈ Ioo a b, N x = ((x - z : ℝ) : ℂ) * U x) :
    (∫⁻ x in Ioo a b, ENNReal.ofReal (‖U x‖ ^ 2)) ≤
      4 * ∫⁻ x in Ioo a b, ENNReal.ofReal (‖D x‖ ^ 2) := by
  have hhalf (σ L c d : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (hsub : Ioo c d ⊆ Ioo a b) (hc : z ∈ Icc c d)
      (hseg : ∀ t ∈ Ioo 0 L, σ * t + z ∈ Ioo c d) :
      (∫⁻ t in Ioo 0 L, ENNReal.ofReal (‖U (σ * t + z)‖ ^ 2)) ≤
        4 * ∫⁻ x in Ioo c d, ENNReal.ofReal (‖D x‖ ^ 2) := by
    let E := intervalZeroExtension c d D
    have hEi : Integrable E :=
      integrable_intervalZeroExtension (hN.memLp_derivative.mono_measure
        (Measure.restrict_mono hsub le_rfl))
    have henergy : (∫⁻ x, ENNReal.ofReal (‖E x‖ ^ 2)) =
        ∫⁻ x in Ioo c d, ENNReal.ofReal (‖D x‖ ^ 2) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      congr 1
      funext x
      by_cases hx : x ∈ Ioo c d <;> simp [E, intervalZeroExtension, hx]
    have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    let V := fun t ↦ σ • E (σ * t + z)
    have hVi : Integrable V :=
      (((hEi.comp_add_right z).comp_mul_left' hσne).smul σ)
    have hVE : (∫⁻ t, ENNReal.ofReal (‖V t‖ ^ 2)) =
        ∫⁻ x in Ioo c d, ENNReal.ofReal (‖D x‖ ^ 2) := by
      simp only [V, norm_smul, Real.norm_eq_abs, hσabs, one_mul]
      rcases hσ with rfl | rfl
      · simp only [one_mul]
        rw [lintegral_add_right_eq_self (fun t ↦ ENNReal.ofReal (‖E t‖ ^ 2)) z]
        exact henergy
      · simp only [neg_one_mul]
        rw [lintegral_neg_eq_self (fun t ↦ ENNReal.ofReal (‖E (t + z)‖ ^ 2)),
          lintegral_add_right_eq_self (fun t ↦ ENNReal.ofReal (‖E t‖ ^ 2)) z]
        exact henergy
    have hprim (t : ℝ) (ht : t ∈ Ioo 0 L) :
        (∫ s in (0 : ℝ)..t, V s) = N (σ * t + z) := by
      simp only [V, intervalIntegral.integral_smul]
      rw [intervalIntegral.smul_integral_comp_mul_add, mul_zero, zero_add,
        intervalIntegral_intervalZeroExtension D hc
          (Ioo_subset_Icc_self (hseg t ht)),
        hN.integral_eq_sub hz (hsub (hseg t ht)), hzero, sub_zero]
    calc
      _ = ∫⁻ t in Ioo 0 L,
          ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, V s‖ ^ 2 / t ^ 2) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only
        rw [hprim t ht, hfactor _ (hsub (hseg t ht)), add_sub_cancel_right,
          ← Complex.real_smul, norm_smul, Real.norm_eq_abs, abs_mul,
          hσabs, one_mul, mul_pow, sq_abs]
        rw [mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos ht.1))]
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, V s‖ ^ 2 / t ^ 2) :=
        lintegral_mono_set (fun _ ht ↦ ht.1)
      _ ≤ 4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (‖V t‖ ^ 2) :=
        lintegral_sq_primitive_div_sq_le_of_integrable hVi
      _ ≤ 4 * ∫⁻ t, ENNReal.ofReal (‖V t‖ ^ 2) := by
        gcongr
        exact Measure.restrict_le_self
      _ = _ := by rw [hVE]
  have hp := hhalf 1 (b - z) z b (Or.inl rfl) (Ioo_subset_Ioo hz.1.le le_rfl)
    ⟨le_rfl, hz.2.le⟩ (fun t ht ↦ by
      simp only [one_mul]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hm := hhalf (-1) (z - a) a z (Or.inr rfl) (Ioo_subset_Ioo le_rfl hz.2.le)
    ⟨hz.1.le, le_rfl⟩ (fun t ht ↦ by
      simp only [neg_one_mul]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hplus : (∫⁻ x in Ioo z b, ENNReal.ofReal (‖U x‖ ^ 2)) ≤
      4 * ∫⁻ x in Ioo z b, ENNReal.ofReal (‖D x‖ ^ 2) := by
    have he := setLIntegral_Ioo_comp_add_right (fun x ↦ ENNReal.ofReal (‖U x‖ ^ 2)) z z b
    rw [sub_self] at he
    rw [← he]
    simpa only [one_mul] using hp
  have hminus : (∫⁻ x in Ioo a z, ENNReal.ofReal (‖U x‖ ^ 2)) ≤
      4 * ∫⁻ x in Ioo a z, ENNReal.ofReal (‖D x‖ ^ 2) := by
    have he := setLIntegral_Ioo_comp_sub_left (fun x ↦ ENNReal.ofReal (‖U x‖ ^ 2)) z a z
    rw [sub_self] at he
    rw [← he]
    simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using hm
  have hμ : volume.restrict (Ioo a b) =
      volume.restrict (Ioo a z) + volume.restrict (Ioo z b) := by
    rw [← Measure.restrict_union (by
      apply disjoint_left.2
      intro x hx hy
      linarith [hx.2, hy.1]) measurableSet_Ioo]
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne z] with x hx
    simp only [mem_Ioo, mem_union]
    apply propext
    constructor <;> intro h
    · rcases lt_or_gt_of_ne hx with hlt | hgt
      · exact Or.inl ⟨h.1, hlt⟩
      · exact Or.inr ⟨hgt, h.2⟩
    · rcases h with h | h <;> constructor <;> linarith [h.1, h.2, hz.1, hz.2]
  rw [hμ, lintegral_add_measure, lintegral_add_measure, mul_add]
  exact add_le_add hminus hplus

/-- A measurable linear quotient at an interior zero has genuine L² energy,
without assuming its integrability in advance. -/
theorem HasIntervalH1.hardy_interior {a b z : ℝ} {N D U : ℝ → ℂ}
    (hN : HasIntervalH1 a b N D) (hz : z ∈ Ioo a b) (hzero : N z = 0)
    (hUm : AEStronglyMeasurable U (volume.restrict (Ioo a b)))
    (hfactor : ∀ x ∈ Ioo a b, N x = ((x - z : ℝ) : ℂ) * U x) :
    MemLp U 2 (volume.restrict (Ioo a b)) ∧
      (∫ x in Ioo a b, ‖U x‖ ^ 2) ≤ 8 * ∫ x in Ioo a b, ‖D x‖ ^ 2 := by
  let I := ∫⁻ x in Ioo a b, ENNReal.ofReal (‖D x‖ ^ 2)
  have hb : (∫⁻ x in Ioo a b, ENNReal.ofReal (‖U x‖ ^ 2)) ≤ 8 * I :=
    (hN.lintegral_hardy_interior hz hzero hfactor).trans
      (mul_le_mul_left (by norm_num : (4 : ℝ≥0∞) ≤ 8) I)
  have hDi := hN.memLp_derivative.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hDf : I < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)).1 hDi.2
  have hUi : IntegrableOn (fun x ↦ ‖U x‖ ^ 2) (Ioo a b) :=
    ⟨hUm.norm.pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun _ ↦ sq_nonneg _)).2
        (hb.trans_lt (ENNReal.mul_lt_top (by norm_num) hDf))⟩
  refine ⟨(memLp_two_iff_integrable_sq_norm hUm).2 hUi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hUi
      (Eventually.of_forall fun _ ↦ sq_nonneg _),
    show I = ∫⁻ x in Ioo a b, ENNReal.ofReal (‖D x‖ ^ 2) from rfl,
    ← ofReal_integral_eq_lintegral_ofReal hDi
      (Eventually.of_forall fun _ ↦ sq_nonneg _),
    show (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (8 : ℝ))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb

/-- A prescribed linear quotient of an interval H¹ function vanishing at an
interior point has energy bounded uniformly in the interval and the zero. -/
theorem HasIntervalH1.integral_sq_linear_quotient_le {a b z : ℝ} {N D U : ℝ → ℂ}
    (hN : HasIntervalH1 a b N D) (hz : z ∈ Ioo a b) (hzero : N z = 0)
    (hU : MemLp U 2 (volume.restrict (Ioo a b)))
    (hfactor : ∀ x ∈ Ioo a b, N x = ((x - z : ℝ) : ℂ) * U x) :
    (∫ x in Ioo a b, ‖U x‖ ^ 2) ≤ 8 * ∫ x in Ioo a b, ‖D x‖ ^ 2 :=
  (hN.hardy_interior hz hzero hU.aestronglyMeasurable hfactor).2

end NoEmbeddedEigenvalues
