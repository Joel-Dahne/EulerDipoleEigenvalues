import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1WeakLift
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ACLSlicing

/-!
# Weak time derivatives from orbitwise absolute continuity

Blueprint: `lem:acl-weak-converse`.

Integration by parts is performed separately on almost every time fiber.
Only the raw functions must be jointly integrable; no measurable selection of
the one-dimensional absolutely continuous representatives is needed.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Integrable raw data and almost-everywhere ACL sections give the specified
second weak partial derivative on a bounded rectangle. -/
theorem hasWeakPartialOn_snd_of_ae_ac {a b c d : ℝ} (hcd : c < d)
    {F D : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F (Ioo a b ×ˢ Ioo c d))
    (hD : IntegrableOn D (Ioo a b ×ˢ Ioo c d))
    (hsec : ∀ᵐ h ∂(volume.restrict (Ioo a b)), ∃ G : ℝ → ℂ,
      (∀ᵐ t, G t = F (h, t)) ∧
      (∀ s t, AbsolutelyContinuousOnInterval G s t) ∧
      ∀ᵐ t, HasDerivAt G (D (h, t)) t) :
    HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 F D := by
  have hFl := hF.locallyIntegrableOn
  have hDl := hD.locallyIntegrableOn
  refine ⟨hFl, hDl, fun φ hφ ↦ ?_⟩
  have hiF := integrable_mul_of_tsupport_subset hFl (hφ.continuous_coordPartial 1)
    (hφ.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 φ).trans hφ.tsupport_subset)
  have hiD := integrable_mul_of_tsupport_subset hDl hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have heq {V : ℝ × ℝ → ℂ} (hi : Integrable V)
      (hz : ∀ p ∉ Ioo a b ×ˢ Ioo c d, V p = 0) :
      (∫ p, V p) = ∫ h in Ioo a b, ∫ t in Ioo c d, V (h, t) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod _ (by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hi.integrableOn)
  rw [heq hiF (fun p hp ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp
      (hφ.tsupport_subset (tsupport_coordPartial_subset 1 φ ht))), mul_zero]),
    heq hiD (fun p hp ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφ.tsupport_subset ht)), mul_zero]),
    ← integral_neg]
  have hDp : Integrable D ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hD
  apply integral_congr_ae
  filter_upwards [hsec, hDp.prod_right_ae] with h hh hDi
  obtain ⟨G, hGF, hAC, hder⟩ := hh
  have hβ : ContDiff ℝ 1 (fun t ↦ φ (h, t)) :=
    (hφ.contDiff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hβc : φ (h, c) = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht ↦ (lt_irrefl c) (hφ.tsupport_subset ht).2.1)
  have hβd : φ (h, d) = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht ↦ (lt_irrefl d) (hφ.tsupport_subset ht).2.2)
  have hFTC := integral_mul_deriv_of_ac_zero_test hcd.le (hAC c d)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd.le).2
      (by rwa [integrableOn_Icc_iff_integrableOn_Ioo]))
    (hder.mono fun _ ht _ ↦ ht) hβ hβc hβd
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo] at hFTC
  calc
    _ = ∫ t in Ioo c d, G t * deriv (fun t ↦ φ (h, t)) t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hGF] with t ht
      change F (h, t) * deriv (fun t ↦ φ (h, t)) t = _
      rw [ht]
    _ = -(∫ t in Ioo c d, D (h, t) * φ (h, t)) := hFTC

end NoEmbeddedEigenvalues
