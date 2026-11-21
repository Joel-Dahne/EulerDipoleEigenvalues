import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeightedTraces
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalTraceIntegration
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakPartialLocality

/-!
# Specified weak derivatives across a matching-trace line

Blueprint: `lem:transverse-trace-window-consistency`,
`lem:transverse-trace-weak-gluing`.

Canonical one-sided ACL traces supply the boundary terms in integration by
parts. Their equality cancels the normal jump. The tangential derivative is
extended by cutoffs constant in the tested coordinate. All candidates have
actual whole-rectangle L² norms before either weak identity is extended.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Replace a trace construction's derivative witness by the specified weak
normal derivative, preserving its canonical trace. -/
theorem HasTransverseH1Trace.with_weak_snd {l r a b t : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t chart F T)
    (hd : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 (F ∘ chart) D)
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    ∃ G : ℝ × ℝ → ℂ, Measurable G ∧
      G =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo a b)] (F ∘ chart) ∧
      MemLp G 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) ∧
      HasACLSectionsOn (Ioo l r) (Ioo a b) G D ∧
      T =ᵐ[volume.restrict (Ioo l r)] aclTrace a b G D t := by
  obtain ⟨hlr, hab, ht, H, E, _, hHF, hH, hE, hHE, hT⟩ := h
  have hFL : MemLp (F ∘ chart) 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) :=
    hH.ae_eq hHF
  obtain ⟨G, hGm, hGF, hGD, _, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hlr) hab hFL hD
  have hGL := hFL.ae_eq hGF.symm
  refine ⟨G, hGm, hGF, hGL, hGD, ?_⟩
  filter_upwards [hT, hGD.ae_trace_independent hab hHE hGF hHF hGL hH hD hE]
    with x hx he
  exact hx.trans (he t ht).symm

/-- A trace on a smaller normal window determines the trace on every larger
H¹ window, including when the prescribed point is an endpoint of either. -/
theorem HasTransverseH1Trace.extend_normal {l r a c d b t : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r c d t chart F T)
    (hac : a ≤ c) (hdb : d ≤ b)
    (hd : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 (F ∘ chart) D)
    (hF : MemLp (F ∘ chart) 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    HasTransverseH1Trace l r a b t chart F T := by
  obtain ⟨hlr, hcd, ht, H, E, _, hHF, hH, hE, hHE, hT⟩ := h
  have hab : a < b := hac.trans_lt (hcd.trans_le hdb)
  have hcc : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hoo : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  have hp : Ioo l r ×ˢ Ioo c d ⊆ Ioo l r ×ˢ Ioo a b := prod_mono Subset.rfl hoo
  obtain ⟨G, hGm, hGF, hGD, hGH1, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hlr) hab hF hD
  have hGL := hF.ae_eq hGF.symm
  have hGsub := hGL.mono_measure (Measure.restrict_mono hp le_rfl)
  have hDsub := hD.mono_measure (Measure.restrict_mono hp le_rfl)
  have hGFsub : G =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo c d)] (F ∘ chart) :=
    ae_restrict_of_ae_restrict_of_subset hp hGF
  have hACLsub : HasACLSectionsOn (Ioo l r) (Ioo c d) G D := by
    filter_upwards [hGD] with x hx
    exact ⟨fun u v huv ↦ hx.1 u v (huv.trans hoo),
      ae_restrict_of_ae_restrict_of_subset hoo hx.2⟩
  refine ⟨hlr, hab, hcc ht, G, D, hGm, hGF, hGL, hD, hGD, ?_⟩
  filter_upwards [hT, hGH1, hACLsub.ae_hasIntervalH1 hGsub hDsub,
    hACLsub.ae_trace_independent hcd hHE hGFsub hHF hGsub hH hDsub hE]
      with x hxT hxFull hxSub hxEq
  have he := hxSub.extension_unique hcd ((hxFull.continuousOn_extension hab).mono hcc)
    (fun y hy ↦ hxFull.extension_eq hab (hoo hy)) ht
  exact hxT.trans ((hxEq t ht).symm.trans he.symm)

/-- Equal canonical one-sided traces remove the normal jump while retaining
the same specified derivative. Raw values on the joining line are unused. -/
theorem HasTransverseH1Trace.weak_snd_glue {l r a t b : ℝ}
    {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hL : HasTransverseH1Trace l r a t t id F T)
    (hR : HasTransverseH1Trace l r t b t id F T)
    (hdL : HasWeakPartialOn (Ioo l r ×ˢ Ioo a t) 1 F D)
    (hdR : HasWeakPartialOn (Ioo l r ×ˢ Ioo t b) 1 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 F D := by
  have hat := hL.2.1
  have htb := hR.2.1
  have hsubL : Ioo l r ×ˢ Ioo a t ⊆ Ioo l r ×ˢ Ioo a b :=
    prod_mono Subset.rfl (Ioo_subset_Ioo le_rfl htb.le)
  have hsubR : Ioo l r ×ˢ Ioo t b ⊆ Ioo l r ×ˢ Ioo a b :=
    prod_mono Subset.rfl (Ioo_subset_Ioo hat.le le_rfl)
  have hDL := hD.mono_measure (Measure.restrict_mono hsubL le_rfl)
  have hDR := hD.mono_measure (Measure.restrict_mono hsubR le_rfl)
  obtain ⟨Gleft, _, hGLF, hGL, hACL, hTL⟩ := hL.with_weak_snd hdL hDL
  obtain ⟨Gright, _, hGRF, hGR, hACR, hTR⟩ := hR.with_weak_snd hdR hDR
  have hFl : LocallyIntegrableOn F (Ioo l r ×ˢ Ioo a b) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have hDl : LocallyIntegrableOn D (Ioo l r ×ˢ Ioo a b) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hD.locallyIntegrable (by norm_num))
  refine ⟨hFl, hDl, fun φ hφ ↦ ?_⟩
  have hiF := integrable_mul_of_tsupport_subset hFl (hφ.continuous_coordPartial 1)
    (hφ.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 φ).trans hφ.tsupport_subset)
  have hiD := integrable_mul_of_tsupport_subset hDl hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have heq {V : ℝ × ℝ → ℂ} (hi : Integrable V)
      (hz : ∀ p ∉ Ioo l r ×ˢ Ioo a b, V p = 0) :
      (∫ p, V p) = ∫ x in Ioo l r, ∫ y in Ioo a b, V (x, y) := by
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
  have hslice {c d : ℝ} {G : ℝ × ℝ → ℂ}
      (he : G =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo c d)] F) :
      ∀ᵐ x ∂(volume.restrict (Ioo l r)),
        ∀ᵐ y ∂(volume.restrict (Ioo c d)), G (x, y) = F (x, y) := by
    have hp : ∀ᵐ q ∂((volume.restrict (Ioo l r)).prod (volume.restrict (Ioo c d))),
        G q = F q := by
      simpa only [Filter.EventuallyEq, Measure.prod_restrict, ← Measure.volume_eq_prod] using he
    exact Measure.ae_ae_of_ae_prod hp
  apply integral_congr_ae
  filter_upwards [hACL.ae_hasIntervalH1 hGL hDL, hACR.ae_hasIntervalH1 hGR hDR,
    hslice hGLF, hslice hGRF, hTL, hTR, ae_memLp_sections hF, ae_memLp_sections hD]
      with x hxL hxR hxGL hxGR hxTL hxTR hxF hxD
  let β : ℝ → ℂ := fun y ↦ φ (x, y)
  have hβ : ContDiff ℝ 1 β :=
    (hφ.contDiff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hβa : β a = 0 := by
    change φ (x, a) = 0
    exact image_eq_zero_of_notMem_tsupport
      (fun ht ↦ (lt_irrefl a) (hφ.tsupport_subset ht).2.1)
  have hβb : β b = 0 := by
    change φ (x, b) = 0
    exact image_eq_zero_of_notMem_tsupport
      (fun ht ↦ (lt_irrefl b) (hφ.tsupport_subset ht).2.2)
  have hFi : IntegrableOn (fun y ↦ F (x, y)) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hxF.integrable (by norm_num)
  have hDi : IntegrableOn (fun y ↦ D (x, y)) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hxD.integrable (by norm_num)
  have hsplit {V : ℝ → ℂ} (hi : IntegrableOn V (Icc a b)) :
      (∫ y in Ioo a b, V y) =
        (∫ y in Ioo a t, V y) + ∫ y in Ioo t b, V y := by
    have hiL : IntervalIntegrable V volume a t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hat.le).2
        (hi.mono_set (Icc_subset_Icc le_rfl htb.le))
    have hiR : IntervalIntegrable V volume t b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le htb.le).2
        (hi.mono_set (Icc_subset_Icc hat.le le_rfl))
    simpa only [intervalIntegral.integral_of_le hat.le,
      intervalIntegral.integral_of_le htb.le,
      intervalIntegral.integral_of_le (hat.trans htb).le,
      integral_Ioc_eq_integral_Ioo] using
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
  have heL : (∫ y in Ioo a t, F (x, y) * deriv β y) =
      ∫ y in Ioo a t, Gleft (x, y) * deriv β y :=
    integral_congr_ae (hxGL.mono fun y hy ↦ congrArg (fun z : ℂ ↦ z * deriv β y) hy.symm)
  have heR : (∫ y in Ioo t b, F (x, y) * deriv β y) =
      ∫ y in Ioo t b, Gright (x, y) * deriv β y :=
    integral_congr_ae (hxGR.mono fun y hy ↦ congrArg (fun z : ℂ ↦ z * deriv β y) hy.symm)
  change T x = intervalH1Extension a t (fun y ↦ Gleft (x, y)) (fun y ↦ D (x, y)) t at hxTL
  change T x = intervalH1Extension t b (fun y ↦ Gright (x, y)) (fun y ↦ D (x, y)) t at hxTR
  change (∫ y in Ioo a b, F (x, y) * deriv β y) =
    -(∫ y in Ioo a b, D (x, y) * β y)
  rw [hsplit (hFi.mul_continuousOn (hβ.continuous_deriv (by simp)).continuousOn isCompact_Icc),
    hsplit (hDi.mul_continuousOn hβ.continuous.continuousOn isCompact_Icc),
    heL, heR, hxL.integral_mul_deriv hat hβ, hxR.integral_mul_deriv htb hβ]
  simp only [hβa, hβb, mul_zero, sub_zero, zero_sub]
  rw [← hxTL, ← hxTR]
  ring

/-- The canonical trace of the glued rectangle is the original common trace,
not a new boundary assignment. This also works for a supplied physical chart. -/
theorem HasTransverseH1Trace.glue_trace {l r a t b : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hL : HasTransverseH1Trace l r a t t chart F T)
    (hR : HasTransverseH1Trace l r t b t chart F T)
    (hdL : HasWeakPartialOn (Ioo l r ×ˢ Ioo a t) 1 (F ∘ chart) D)
    (hdR : HasWeakPartialOn (Ioo l r ×ˢ Ioo t b) 1 (F ∘ chart) D)
    (hF : MemLp (F ∘ chart) 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    HasTransverseH1Trace l r a b t chart F T := by
  have hleft : HasTransverseH1Trace l r a t t id (F ∘ chart) T := hL
  have hright : HasTransverseH1Trace l r t b t id (F ∘ chart) T := hR
  exact hL.extend_normal le_rfl hR.2.1.le
    (hleft.weak_snd_glue hright hdL hdR hF hD) hF hD

/-- Tangential weak identities cross a horizontal line without any trace
hypothesis: the testing cutoff has zero tangential derivative. -/
theorem HasWeakPartialOn.glue_fst_across_snd {l r a t b : ℝ} {F D : ℝ × ℝ → ℂ}
    (hdL : HasWeakPartialOn (Ioo l r ×ˢ Ioo a t) 0 F D)
    (hdR : HasWeakPartialOn (Ioo l r ×ˢ Ioo t b) 0 F D)
    (hF : LocallyIntegrableOn F (Ioo l r ×ˢ Ioo a b))
    (hD : LocallyIntegrableOn D (Ioo l r ×ˢ Ioo a b)) :
    HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 0 F D := by
  apply HasWeakPartialOn.remove_transverse_line (t := t) ?_ hF hD
  apply hasWeakPartialOn_of_locally
  intro p hp
  by_cases hpt : p.2 < t
  · exact ⟨Ioo l r ×ˢ Ioo a t, isOpen_Ioo.prod isOpen_Ioo,
      ⟨hp.1.1, hp.1.2.1, hpt⟩, hdL⟩
  · have hne : p.2 ≠ t := hp.2
    have htp : t < p.2 := lt_of_le_of_ne (le_of_not_gt hpt) hne.symm
    exact ⟨Ioo l r ×ˢ Ioo t b, isOpen_Ioo.prod isOpen_Ioo,
      ⟨hp.1.1, htp, hp.1.2.2⟩, hdR⟩

/-- Matching canonical traces and finite whole-rectangle norms give ordinary H¹
with both original specified derivative candidates. -/
theorem HasTransverseH1Trace.h1_glue {l r a t b : ℝ}
    {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hL : HasTransverseH1Trace l r a t t id F T)
    (hR : HasTransverseH1Trace l r t b t id F T)
    (hdL : ∀ j, HasWeakPartialOn (Ioo l r ×ˢ Ioo a t) j F (D j))
    (hdR : ∀ j, HasWeakPartialOn (Ioo l r ×ˢ Ioo t b) j F (D j))
    (hF : MemLp F 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hD : ∀ j, MemLp (D j) 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) F ∧
      ∀ j, HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) j F (D j) := by
  have hder (j : Fin 2) : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) j F (D j) := by
    fin_cases j
    · exact (hdL 0).glue_fst_across_snd (hdR 0)
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num)))
        (locallyIntegrableOn_of_locallyIntegrable_restrict ((hD 0).locallyIntegrable (by norm_num)))
    · exact hL.weak_snd_glue hR (hdL 1) (hdR 1) hF (hD 1)
  exact ⟨⟨hF, fun j ↦ ⟨D j, hder j, hD j⟩⟩, hder⟩

end NoEmbeddedEigenvalues
