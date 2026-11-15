import NoEmbeddedEigenvalues.TraceH2

/-!
# Interval H¹ regularity of fixed-window parameter integrals

Blueprint: `lem:fixed-window-h1`.

An L² weak level derivative can be integrated over a fixed transverse window.
The horizontal ACL fundamental theorem and Fubini give the increment identity;
continuity retains the original pointwise parameter integral.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Integration over a finite transverse interval preserves square integrability. -/
theorem memLp_setIntegral_Icc {I : Set ℝ} [IsFiniteMeasure (volume.restrict I)]
    {c d : ℝ} (hcd : c ≤ d) {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (I ×ˢ Icc c d))) :
    MemLp (fun x ↦ ∫ t in Icc c d, F (x, t)) 2 (volume.restrict I) := by
  have hp : MemLp F 2 ((volume.restrict I).prod (volume.restrict (Icc c d))) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hF
  have hm := (hp.integrable (by norm_num)).integral_prod_left.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hi := hp.norm.integrable_sq.integral_prod_left.const_mul (d - c)
  apply hi.mono' (hm.norm.pow 2)
  filter_upwards [ae_memLp_sections hF] with x hx
  have hh := norm_intervalIntegral_sq_le hcd hx
  change |‖∫ t in Icc c d, F (x, t)‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc] using hh

/-- A continuous rectangle function with a square-integrable weak level derivative
has its original fixed-window integral in interval H¹. -/
theorem HasWeakPartialOn.setIntegral_h1 {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D : ℝ × ℝ → ℂ}
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D) :
    HasIntervalH1 a b (fun x ↦ ∫ t in Icc l r, F (x, t))
      (fun x ↦ ∫ t in Icc l r, D (x, t)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    isFiniteMeasure_restrict.2 ((measure_mono
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).trans_lt
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hsub : Icc l r ⊆ Ioo c d := Icc_subset_Ioo hl hr
  have hFs := hF.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hsub) le_rfl)
  have hDs := hD.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hsub) le_rfl)
  have hDL := memLp_setIntegral_Icc hlr hDs
  have hFTC : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      (∫ s in x..y, ∫ t in Icc l r, D (s, t)) =
        (∫ t in Icc l r, F (y, t)) - ∫ t in Icc l r, F (x, t) := by
    intro x hx y hy
    have hi : Integrable (Function.uncurry (fun s t ↦ D (s, t)))
        ((volume.restrict (uIoc x y)).prod (volume.restrict (Icc l r))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact (hD.integrable (by norm_num)).mono_measure (Measure.restrict_mono
        (prod_mono (uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hx hy)) hsub) le_rfl)
    rw [intervalIntegral_integral_swap hi]
    calc
      _ = ∫ t in Icc l r, F (y, t) - F (x, t) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
          (hd.ae_horizontal_integral_eq hab hcd hFc hF hD Filter.EventuallyEq.rfl)]
          with t ht
        exact ht x hx y hy
      _ = _ := integral_sub
        ((hFc.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht ↦ ⟨hy, hsub ht⟩)).integrableOn_Icc)
        ((hFc.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht ↦ ⟨hx, hsub ht⟩)).integrableOn_Icc)
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq hab hDL hFTC
  exact ⟨memLp_setIntegral_Icc hlr hFs, hDL, hac,
    (ae_restrict_iff' measurableSet_Ioo).1 hder⟩

end NoEmbeddedEigenvalues
