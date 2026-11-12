import NoEmbeddedEigenvalues.SobolevGluing

/-!
# Multipliers for local L²

Blueprint: `lem:local-l2-multiplier`.

At order zero no derivatives of the coefficient are needed. Measurable bounded
coefficients preserve L²; continuous coefficients are bounded on each compact
localization. Neither assertion gives finite norms on the whole periodic lift.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A measurable coefficient bounded on the domain preserves local L². -/
theorem MemSobolevLocOn.zero_mul_bounded {U : Set (ℝ × ℝ)} {F G : ℝ × ℝ → ℂ}
    (hF : MemSobolevLocOn 0 U F) (hG : Measurable G) {C : ℝ}
    (hb : ∀ p ∈ U, ‖G p‖ ≤ C) : MemSobolevLocOn 0 U (fun p ↦ G p * F p) := by
  intro V hV hc hVU
  have hBV : MemLp G ⊤ (volume.restrict V) := by
    apply memLp_top_of_bound hG.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
    exact hb p (hVU (subset_closure hp))
  exact hBV.mul (hF V hV hc hVU)

/-- A coefficient continuous on the domain preserves local L², with only compact
bounds and no global boundedness premise. -/
theorem MemSobolevLocOn.zero_mul_continuousOn {U : Set (ℝ × ℝ)}
    {F G : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 0 U F) (hG : ContinuousOn G U) :
    MemSobolevLocOn 0 U (fun p ↦ G p * F p) := by
  intro V hV hc hVU
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hG.mono hVU)
  have hBV : MemLp G ⊤ (volume.restrict V) := by
    apply memLp_top_of_bound
      ((hG.mono (subset_closure.trans hVU)).aestronglyMeasurable hV.measurableSet) C
    filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
    exact hC p (subset_closure hp)
  exact hBV.mul (hF V hV hc hVU)

end NoEmbeddedEigenvalues
