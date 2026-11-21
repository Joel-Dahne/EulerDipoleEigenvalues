module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTrace
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalParameterH2

/-!
# Weak parameter flux with canonical traces

Blueprint: `lem:interior-trace-at`, `lem:canonical-transverse-trace`,
`lem:rough-window-flux`, `lem:second-window-flux`.

Translate each interior transverse point to zero and use the continuous-section
trace, rather than evaluating the raw weak potential on a null line. The same
trace works on every containing rectangle. Rough fixed-window averages retain
their raw a.e. class, and second differentiation keeps the original continuous
value function.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Translate a continuous section representative to an interior point. -/
theorem interiorSectionTrace_eq_at {f g : ℝ → ℂ} {c d t : ℝ}
    (ht : t ∈ Ioo c d) (hg : ContinuousOn g (Ioo c d))
    (he : g =ᵐ[volume.restrict (Ioo c d)] f) :
    interiorSectionTrace (fun s ↦ f (t + s)) = g t := by
  have hge : (fun s ↦ g (t + s)) =ᵐ[volume.restrict (Ioo (c - t) (d - t))]
      (fun s ↦ f (t + s)) := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [(measurePreserving_add_left volume t).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 he)] with s hs hsI
    exact hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  have hgc : ContinuousOn (fun s ↦ g (t + s)) (Ioo (c - t) (d - t)) :=
    hg.comp (continuous_const.add continuous_id).continuousOn
      (fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  simpa only [add_zero] using interiorSectionTrace_eq (by linarith [ht.1])
    (by linarith [ht.2]) hgc hge

/-- One ACL field identifies all its interior canonical transverse traces on
one good-level set; no raw values of the original planar field are used. -/
theorem HasACLSectionsOn.ae_interiorSectionTrace_eq {a b c d : ℝ}
    {F G D : ℝ × ℝ → ℂ} (h : HasACLSectionsOn (Ioo a b) (Ioo c d) G D)
    (he : G =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo c d)] F) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ t ∈ Ioo c d,
      interiorSectionTrace (fun s ↦ F (x, t + s)) = G (x, t) := by
  filter_upwards [h.ae_continuousOn isOpen_Ioo, ae_sections_eq_of_rectangle he]
    with x hc hx
  exact fun t ht ↦ interiorSectionTrace_eq_at ht hc hx

/-- A rough weak transverse potential has actual L² canonical traces at every
interior point, not necessarily its arbitrary raw line values. -/
theorem HasWeakPartialOn.memLp_interiorSectionTrace {a b c d t : ℝ}
    {F D : ℝ × ℝ → ℂ} (hab : a < b) (hcd : c < d) (ht : t ∈ Ioo c d)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 F D) :
    MemLp (fun x ↦ interiorSectionTrace (fun s ↦ F (x, t + s))) 2
      (volume.restrict (Ioo a b)) := by
  obtain ⟨G, hGm, hGF, hG⟩ := hd.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hcd)
  have hGL := hF.ae_eq hGF.symm
  apply ((hG.l2_trace hcd hGm hGL hD t (Ioo_subset_Icc_self ht)).1).ae_eq
  filter_upwards [hG.ae_trace_eq hcd hGL hD, hG.ae_interiorSectionTrace_eq hGF] with x hx he
  exact (hx t ht).trans (he t ht).symm

/-- The weak transverse FTC uses the canonical traces of a rough potential,
simultaneously for every pair of interior endpoints on one good-level set. -/
theorem HasWeakPartialOn.ae_vertical_integral_eq_trace {a b c d : ℝ}
    {F D : ℝ × ℝ → ℂ} (hab : a < b) (hcd : c < d)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 F D) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ l ∈ Ioo c d, ∀ r ∈ Ioo c d,
      (∫ t in l..r, D (x, t)) =
        interiorSectionTrace (fun s ↦ F (x, r + s)) -
        interiorSectionTrace (fun s ↦ F (x, l + s)) := by
  obtain ⟨G, -, hGF, hG⟩ := hd.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hcd)
  filter_upwards [hG.ae_hasIntervalH1 (hF.ae_eq hGF.symm) hD,
    hG.ae_interiorSectionTrace_eq hGF] with x hx he
  intro l hl r hr
  rw [he r hr, he l hl]
  exact hx.integral_eq_sub hl hr

/-- An a.e. divergence decomposition gives a genuine flux derivative of an
H¹ representative of a rough fixed-window average. No planar continuity or
measurability of the separate scalar coefficient is assumed. -/
theorem HasWeakPartialOn.exists_setIntegral_h1_flux_rep {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D H P B : ℝ × ℝ → ℂ} {β : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hH : MemLp H 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hP : MemLp P 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (ht : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 P B)
    (hflux : D =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo c d)]
      (fun q ↦ H q + β q.1 * B q)) :
    ∃ A : ℝ → ℂ, A =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ ∫ t in Icc l r, F (x, t)) ∧
      HasIntervalH1 a b A (fun x ↦ (∫ t in Icc l r, H (x, t)) + β x *
        (interiorSectionTrace (fun s ↦ P (x, r + s)) -
          interiorSectionTrace (fun s ↦ P (x, l + s)))) := by
  obtain ⟨A, hAeq, hA⟩ := hx.exists_setIntegral_h1_rep hab hcd hl hlr hr hF hD
  refine ⟨A, hAeq, hA.congr_derivative ?_⟩
  have hsub : Icc l r ⊆ Ioo c d := Icc_subset_Ioo hl hr
  filter_upwards [ht.ae_vertical_integral_eq_trace hab hcd hP hB,
    ae_memLp_sections hH, ae_memLp_sections hB, ae_sections_eq_of_rectangle hflux]
    with x hFTC hHx hBx hxe
  have hHi : IntegrableOn (fun t ↦ H (x, t)) (Icc l r) :=
    (hHx.mono_measure (Measure.restrict_mono_set _ hsub)).integrable (by norm_num)
  have hBi : IntegrableOn (fun t ↦ B (x, t)) (Icc l r) :=
    (hBx.mono_measure (Measure.restrict_mono_set _ hsub)).integrable (by norm_num)
  calc
    _ = ∫ t in Icc l r, H (x, t) + β x * B (x, t) :=
      integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hxe)
    _ = (∫ t in Icc l r, H (x, t)) + β x * ∫ t in Icc l r, B (x, t) := by
      rw [integral_add hHi (hBi.const_mul _), integral_const_mul]
    _ = _ := by
      have he : (∫ t in Icc l r, B (x, t)) =
          interiorSectionTrace (fun s ↦ P (x, r + s)) -
            interiorSectionTrace (fun s ↦ P (x, l + s)) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
        exact hFTC l ⟨hl, hlr.trans_lt hr⟩ r ⟨hl.trans_le hlr, hr⟩
      rw [he]

/-- Keep any supplied continuous scalar representative of the raw average.
Only the scalar a.e. identity is needed, not continuity of the planar field. -/
theorem HasWeakPartialOn.setIntegral_h1_flux_of_ae_eq {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D H P B : ℝ × ℝ → ℂ} {β A : ℝ → ℂ}
    (hAc : ContinuousOn A (Ioo a b))
    (hAeq : A =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ ∫ t in Icc l r, F (x, t)))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hH : MemLp H 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hP : MemLp P 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (ht : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 P B)
    (hflux : D =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo c d)]
      (fun q ↦ H q + β q.1 * B q)) :
    HasIntervalH1 a b A (fun x ↦ (∫ t in Icc l r, H (x, t)) + β x *
      (interiorSectionTrace (fun s ↦ P (x, r + s)) -
        interiorSectionTrace (fun s ↦ P (x, l + s)))) := by
  obtain ⟨K, hKeq, hK⟩ := hx.exists_setIntegral_h1_flux_rep hab hcd hl hlr hr
    hF hD hH hP hB ht hflux
  exact hK.congr_Ioo (Measure.eqOn_open_of_ae_eq (hKeq.trans hAeq.symm)
    isOpen_Ioo (hK.continuousOn_Ioo hab) hAc)

/-- Two weak parameter derivatives with a divergence decomposition of the
second give the actual second scalar derivative in boundary-flux form. -/
theorem HasWeakPartialOn.setIntegral_h2_flux {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D E H P B : ℝ × ℝ → ℂ} {β : ℝ → ℂ}
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hE : MemLp E 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hH : MemLp H 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hP : MemLp P 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (hxx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 D E)
    (ht : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 P B)
    (hflux : E =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo c d)]
      (fun q ↦ H q + β q.1 * B q)) :
    HasIntervalH2 a b (fun x ↦ ∫ t in Icc l r, F (x, t))
      (deriv (fun x ↦ ∫ t in Icc l r, F (x, t)))
      (fun x ↦ (∫ t in Icc l r, H (x, t)) + β x *
        (interiorSectionTrace (fun s ↦ P (x, r + s)) -
          interiorSectionTrace (fun s ↦ P (x, l + s)))) := by
  let N := fun x ↦ ∫ t in Icc l r, F (x, t)
  have hN := hx.setIntegral_h1 hab hcd hl hlr hr hFc hF hD
  obtain ⟨A, C, hAC⟩ := hx.setIntegral_h2 hab hcd hl hlr hr hFc hF hD hE hxx
  have hNc := hAC.with_deriv hab
  refine ⟨hN.with_deriv, hxx.setIntegral_h1_flux_of_ae_eq hab hcd hl hlr hr
    (hNc.2.continuousOn_Ioo hab) ?_ hD hE hH hP hB ht hflux⟩
  filter_upwards [ae_restrict_of_ae hN.hasDerivAt_ae, ae_restrict_mem measurableSet_Ioo]
    with x hx hxI
  exact (hx hxI).deriv

end NoEmbeddedEigenvalues
