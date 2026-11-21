import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceL2

/-!
# Strong one-sided continuity of canonical rectangle traces

Blueprint: `lem:interval-trace-increment`, `lem:l2-trace-continuity`.

The interval Cauchy–Schwarz estimate keeps the actual distance between the
trace lines. Integrating the section estimate yields an L² increment bound,
including normal endpoints. The traces belong to one supplied joint ACL field;
no raw boundary values or measurable choice of fibre representatives is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology Interval

/-- The increment bound retains the distance between the two trace points. -/
theorem HasIntervalH1.extension_sub_sq_le_distance {a b x y : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖intervalH1Extension a b F D y - intervalH1Extension a b F D x‖ ^ 2 ≤
      |y - x| * ∫ t in Ioo a b, ‖D t‖ ^ 2 := by
  have hi := h.integrableOn_sq_norm_derivative
  have hord : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, c ≤ d →
      ‖intervalH1Extension a b F D d - intervalH1Extension a b F D c‖ ^ 2 ≤
        (d - c) * ∫ t in Ioo a b, ‖D t‖ ^ 2 := by
    intro c hc d hd hcd
    apply (h.extension_sub_sq_le hab hc hd hcd).trans
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hcd)
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioo]
    exact setIntegral_mono_set hi (Eventually.of_forall fun t ↦ sq_nonneg _)
      (Eventually.of_forall fun t ht ↦ Icc_subset_Icc hc.1 hd.2 ht)
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hord x hx y hy hxy
  · simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using
      hord y hy x hx hyx

/-- Canonical traces have genuine L² differences and an explicit endpoint-safe
increment bound. -/
theorem HasACLSectionsOn.trace_sub_sq_le {I : Set ℝ} {a b s t : ℝ}
    {G D : ℝ × ℝ → ℂ} (h : HasACLSectionsOn I (Ioo a b) G D)
    (hab : a < b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo a b))) :
    MemLp (fun r ↦ aclTrace a b G D t r - aclTrace a b G D s r) 2
      (volume.restrict I) ∧
    (∫ r in I, ‖aclTrace a b G D t r - aclTrace a b G D s r‖ ^ 2) ≤
      |t - s| * ∫ q in I ×ˢ Ioo a b, ‖D q‖ ^ 2 := by
  have hL := ((h.l2_trace hab hGm hG hD t ht).1).sub
    ((h.l2_trace hab hGm hG hD s hs).1)
  have hDp : MemLp D 2 ((volume.restrict I).prod (volume.restrict (Ioo a b))) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hD
  have iD := hDp.norm.integrable_sq
  have hpt : ∀ᵐ r ∂(volume.restrict I),
      ‖aclTrace a b G D t r - aclTrace a b G D s r‖ ^ 2 ≤
        |t - s| * ∫ u in Ioo a b, ‖D (r, u)‖ ^ 2 := by
    filter_upwards [h.ae_hasIntervalH1 hG hD] with r hr
    exact hr.extension_sub_sq_le_distance hab hs ht
  refine ⟨hL, ?_⟩
  have hi := integral_mono_ae (hL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (iD.integral_prod_left.const_mul |t - s|) hpt
  rw [integral_const_mul, ← integral_prod _ iD] at hi
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Pi.sub_apply] using hi

/-- Strong L² trace convergence reaches either normal endpoint. -/
theorem HasACLSectionsOn.tendsto_trace_sq {I : Set ℝ} {a b s : ℝ}
    {G D : ℝ × ℝ → ℂ} (h : HasACLSectionsOn I (Ioo a b) G D)
    (hab : a < b) (hs : s ∈ Icc a b) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo a b))) :
    Tendsto (fun t ↦ ∫ r in I, ‖aclTrace a b G D t r - aclTrace a b G D s r‖ ^ 2)
      (𝓝[Icc a b] s) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ ↦ |t - s| * ∫ q in I ×ˢ Ioo a b, ‖D q‖ ^ 2) := by
    fun_prop
  have hz : Tendsto (fun t : ℝ ↦ |t - s| * ∫ q in I ×ˢ Ioo a b, ‖D q‖ ^ 2)
      (𝓝[Icc a b] s) (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      (hc.tendsto s).mono_left (nhdsWithin_le_nhds : 𝓝[Icc a b] s ≤ 𝓝 s)
  apply squeeze_zero' (Eventually.of_forall fun t ↦ integral_nonneg fun r ↦ sq_nonneg _) ?_ hz
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h.trace_sub_sq_le hab hs ht hGm hG hD).2

end NoEmbeddedEigenvalues
