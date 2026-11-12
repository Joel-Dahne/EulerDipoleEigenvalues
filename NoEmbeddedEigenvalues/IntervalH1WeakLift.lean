import NoEmbeddedEigenvalues.IntervalH1
import NoEmbeddedEigenvalues.WeakPartialLocality

/-!
# Weak planar derivatives of interval H¹ representatives

Blueprint: `lem:ac-integration-by-parts`, `lem:interval-h1-weak-lift`.

Absolute continuity and the complex FTC give integration by parts on compact
intervals. Fubini then lifts a specified interval derivative to the first
coordinate of the plane. No endpoint trace convention is used in this lift.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Compact-interval integration by parts with the actual boundary values. -/
theorem integral_mul_deriv_of_ac {a b : ℝ} (hab : a ≤ b)
    {A D β : ℝ → ℂ} (hA : AbsolutelyContinuousOnInterval A a b)
    (hD : IntervalIntegrable D volume a b)
    (hder : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt A (D x) x)
    (hβ : ContDiff ℝ 1 β) :
    (∫ x in Icc a b, A x * deriv β x) =
      A b * β b - A a * β a - ∫ x in Icc a b, D x * β x := by
  obtain ⟨K, hK⟩ := hβ.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc a b) isCompact_Icc
  have hβac : AbsolutelyContinuousOnInterval β a b := by
    rw [← uIcc_of_le hab] at hK
    exact hK.absolutelyContinuousOnInterval
  have hDb := hD.mul_continuousOn hβ.continuous.continuousOn
  have hAb : IntervalIntegrable (fun x ↦ A x * deriv β x) volume a b := by
    have hc := hA.continuousOn.mul (hβ.continuous_deriv (by norm_num)).continuousOn
    exact hc.intervalIntegrable
  have hFTC := complex_integral_eq_sub_of_ac (hβac.smul hA) (hDb.add hAb) (by
    filter_upwards [hder] with x hx hxI
    have hh := ((hβ.differentiable (by norm_num) x).hasDerivAt).mul (hx hxI)
    convert hh using 1
    ring)
  simp only [smul_eq_mul, Pi.mul_apply] at hFTC
  rw [intervalIntegral.integral_add hDb hAb,
    intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hFTC
  linear_combination hFTC

/-- Compact-interval integration by parts for a specified a.e. complex derivative. -/
theorem integral_mul_deriv_of_ac_zero_test {a b : ℝ} (hab : a ≤ b)
    {A D β : ℝ → ℂ} (hA : AbsolutelyContinuousOnInterval A a b)
    (hD : IntervalIntegrable D volume a b)
    (hder : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt A (D x) x)
    (hβ : ContDiff ℝ 1 β) (hβa : β a = 0) (hβb : β b = 0) :
    (∫ x in Icc a b, A x * deriv β x) = -(∫ x in Icc a b, D x * β x) := by
  simpa only [hβa, hβb, mul_zero, sub_self, zero_sub] using
    integral_mul_deriv_of_ac hab hA hD hder hβ

/-- Interval H¹ supplies the first planar weak derivative of its level pullback. -/
theorem HasIntervalH1.weak_fst {a b : ℝ} {A D : ℝ → ℂ} (h : HasIntervalH1 a b A D) :
    HasWeakPartialOn (Ioo a b ×ˢ (univ : Set ℝ)) 0
      (fun q ↦ A q.1) (fun q ↦ D q.1) := by
  apply hasWeakPartialOn_of_locally
  intro q hq
  let c := (a + q.1) / 2
  let d := (q.1 + b) / 2
  let m := |q.2| + 1
  have hac : a < c := by dsimp [c]; linarith [hq.1.1]
  have hcq : c < q.1 := by dsimp [c]; linarith [hq.1.1]
  have hqd : q.1 < d := by dsimp [d]; linarith [hq.1.2]
  have hdb : d < b := by dsimp [d]; linarith [hq.1.2]
  have hcd : c < d := hcq.trans hqd
  have hsub : Icc c d ⊆ Ioo a b := Icc_subset_Ioo hac hdb
  have hAc := h.absolutelyContinuous (hsub ⟨le_rfl, hcd.le⟩) (hsub ⟨hcd.le, le_rfl⟩)
  have hAi : IntegrableOn A (Icc c d) :=
    (show IntegrableOn A (Ioo a b) volume from
      h.memLp_value.integrable (by norm_num)).mono_set hsub
  have hDi : IntegrableOn D (Icc c d) :=
    h.integrableOn_derivative.mono_set (hsub.trans Ioo_subset_Icc_self)
  have hAp := hAi.comp_fst (volume.restrict (Icc (-m) m))
  have hDp := hDi.comp_fst (volume.restrict (Icc (-m) m))
  have hAloc : LocallyIntegrableOn (fun p : ℝ × ℝ ↦ A p.1) (Ioo c d ×ˢ Ioo (-m) m) := by
    have hi : IntegrableOn (fun p : ℝ × ℝ ↦ A p.1) (Icc c d ×ˢ Icc (-m) m) := by
      simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hAp
    exact hi.locallyIntegrableOn.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hDloc : LocallyIntegrableOn (fun p : ℝ × ℝ ↦ D p.1) (Ioo c d ×ˢ Ioo (-m) m) := by
    have hi : IntegrableOn (fun p : ℝ × ℝ ↦ D p.1) (Icc c d ×ˢ Icc (-m) m) := by
      simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hDp
    exact hi.locallyIntegrableOn.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  refine ⟨Ioo c d ×ˢ Ioo (-m) m, isOpen_Ioo.prod isOpen_Ioo,
    ⟨⟨hcq, hqd⟩, abs_lt.1 (by dsimp [m]; linarith : |q.2| < m)⟩,
    hAloc, hDloc, ?_⟩
  intro φ hφ
  have hs : tsupport φ ⊆ Icc c d ×ˢ Icc (-m) m :=
    hφ.tsupport_subset.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hiF := integrable_mul_of_tsupport_subset hAloc (hφ.continuous_coordPartial 0)
    (hφ.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 φ).trans hφ.tsupport_subset)
  have hiD := integrable_mul_of_tsupport_subset hDloc hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have heq {V : ℝ × ℝ → ℂ} (hi : Integrable V)
      (hz : ∀ p ∉ Icc c d ×ˢ Icc (-m) m, V p = 0) :
      (∫ p, V p) = ∫ t in Icc (-m) m, ∫ x in Icc c d, V (x, t) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ (by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hi.integrableOn)
  rw [heq hiF (fun p hp ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hs
      (tsupport_coordPartial_subset 0 φ ht))), mul_zero]),
    heq hiD (fun p hp ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hs ht)), mul_zero])]
  simp only [coordPartial, ite_true]
  rw [← integral_neg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  apply integral_mul_deriv_of_ac_zero_test (β := fun x ↦ φ (x, t))
    hcd.le hAc ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd.le).2 hDi)
  · filter_upwards [h.hasDerivAt_ae] with x hx hxI
    exact hx (hsub (by simpa only [uIcc_of_le hcd.le] using hxI))
  · exact (hφ.contDiff.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  · exact image_eq_zero_of_notMem_tsupport (fun ht ↦
      (lt_irrefl c) (hφ.tsupport_subset ht).1.1)
  · exact image_eq_zero_of_notMem_tsupport (fun ht ↦
      (lt_irrefl d) (hφ.tsupport_subset ht).1.2)

end NoEmbeddedEigenvalues
