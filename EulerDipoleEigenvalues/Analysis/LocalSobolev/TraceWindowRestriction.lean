module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWeakGluing

/-!
# Restriction of canonical transverse traces

Blueprint: `lem:transverse-trace-window-consistency`.

Restrict the existing ACL data and identify the continuous interval extensions
on the entire smaller closed interval, including either normal endpoint.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Restriction to a nested nonempty normal window retains the same canonical
trace, including when the trace point becomes an endpoint. -/
theorem HasTransverseH1Trace.restrict_normal {l r a c d b t : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t chart F T)
    (hac : a ≤ c) (hdb : d ≤ b) (hcd : c < d) (ht : t ∈ Icc c d) :
    HasTransverseH1Trace l r c d t chart F T := by
  obtain ⟨hlr, hab, _, G, D, hm, hGF, hG, hD, hGD, hT⟩ := h
  have hcc : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hoo : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  have hp : Ioo l r ×ˢ Ioo c d ⊆ Ioo l r ×ˢ Ioo a b := prod_mono Subset.rfl hoo
  have hGs := hG.mono_measure (Measure.restrict_mono hp le_rfl)
  have hDs := hD.mono_measure (Measure.restrict_mono hp le_rfl)
  have hACL : HasACLSectionsOn (Ioo l r) (Ioo c d) G D := by
    filter_upwards [hGD] with x hx
    exact ⟨fun u v huv ↦ hx.1 u v (huv.trans hoo),
      ae_restrict_of_ae_restrict_of_subset hoo hx.2⟩
  refine ⟨hlr, hcd, ht, G, D, hm,
    ae_restrict_of_ae_restrict_of_subset hp hGF, hGs, hDs, hACL, ?_⟩
  filter_upwards [hT, hGD.ae_hasIntervalH1 hG hD, hACL.ae_hasIntervalH1 hGs hDs]
    with x hxT hxFull hxSub
  have he := hxSub.extension_unique hcd ((hxFull.continuousOn_extension hab).mono hcc)
    (fun y hy ↦ hxFull.extension_eq hab (hoo hy)) ht
  exact hxT.trans he

end EulerDipoleEigenvalues
