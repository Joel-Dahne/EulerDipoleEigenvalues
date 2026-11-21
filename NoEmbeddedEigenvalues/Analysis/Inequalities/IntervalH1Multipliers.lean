import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth bounded multipliers on interval H¹

Blueprint: `lem:h1-smooth-multiplier`.

Both multiplier coefficients are bounded only on the interval in question.
The specified derivative and the original pointwise representative are retained.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff

/-- The interval H¹ product rule for a smooth multiplier with bounded value and
bounded specified derivative. -/
theorem HasIntervalH1.mul_smooth {a b B H : ℝ} {U U₁ R R₁ : ℝ → ℂ}
    (hU : HasIntervalH1 a b U U₁) (hR : ContDiffOn ℝ ∞ R (Icc a b))
    (hdR : ∀ x ∈ Ioo a b, HasDerivAt R (R₁ x) x)
    (hB : ∀ x ∈ Ioo a b, ‖R x‖ ≤ B) (hH : ∀ x ∈ Ioo a b, ‖R₁ x‖ ≤ H) :
    HasIntervalH1 a b (fun x ↦ R x * U x) (fun x ↦ R₁ x * U x + R x * U₁ x) := by
  have hRm : AEStronglyMeasurable R (volume.restrict (Ioo a b)) :=
    (hR.continuousOn.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hR₁m : AEStronglyMeasurable R₁ (volume.restrict (Ioo a b)) := by
    have hc := ((hR.mono Ioo_subset_Icc_self).deriv_of_isOpen
      (m := ∞) isOpen_Ioo (by simp)).continuousOn
    exact (hc.congr (fun x hx ↦ (hdR x hx).deriv.symm)).aestronglyMeasurable measurableSet_Ioo
  have hmul (F : ℝ → ℂ) (hF : MemLp F 2 (volume.restrict (Ioo a b))) :
      MemLp (fun x ↦ R x * F x) 2 (volume.restrict (Ioo a b)) := by
    apply hF.of_le_mul (c := B) (hRm.mul hF.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Pi.mul_apply, norm_mul] using
      mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg (F x))
  have hmul₁ : MemLp (fun x ↦ R₁ x * U x) 2 (volume.restrict (Ioo a b)) := by
    apply hU.memLp_value.of_le_mul (c := H) (hR₁m.mul hU.memLp_value.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Pi.mul_apply, norm_mul] using
      mul_le_mul_of_nonneg_right (hH x hx) (norm_nonneg (U x))
  refine ⟨hmul U hU.memLp_value, hmul₁.add (hmul U₁ hU.memLp_derivative), ?_, ?_⟩
  · intro c d hc hcd hd
    have hsub : uIcc c d ⊆ Icc a b := by
      rw [uIcc_of_le hcd]
      exact Icc_subset_Icc hc.le hd.le
    have hac : AbsolutelyContinuousOnInterval R c d :=
      ((hR.mono hsub).of_le (by simp)).absolutelyContinuousOnInterval
    simpa only [smul_eq_mul] using hac.fun_smul (hU.locally_absolutelyContinuous c d hc hcd hd)
  · filter_upwards [hU.hasDerivAt_ae] with x hx hxI
    exact (hdR x hxI).mul (hx hxI)

/-- A smooth coefficient on an open neighborhood of the closed interval is an
H¹ multiplier; compactness supplies the coefficient and derivative bounds. -/
theorem HasIntervalH1.mul_contDiffOn_open {a b : ℝ} {U U₁ R : ℝ → ℂ}
    (hU : HasIntervalH1 a b U U₁) {S : Set ℝ} (hS : IsOpen S)
    (hR : ContDiffOn ℝ ∞ R S) (hsub : Icc a b ⊆ S) :
    HasIntervalH1 a b (fun x ↦ R x * U x)
      (fun x ↦ deriv R x * U x + R x * U₁ x) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hR.continuousOn.mono hsub)
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hR.continuousOn_deriv_of_isOpen hS (by simp)).mono hsub)
  apply hU.mul_smooth (hR.mono hsub) ?_
    (fun x hx ↦ hB x (Ioo_subset_Icc_self hx))
    (fun x hx ↦ hH x (Ioo_subset_Icc_self hx))
  intro x hx
  exact ((hR.contDiffAt (hS.mem_nhds (hsub (Ioo_subset_Icc_self hx)))).differentiableAt
    (by simp)).hasDerivAt

end NoEmbeddedEigenvalues
