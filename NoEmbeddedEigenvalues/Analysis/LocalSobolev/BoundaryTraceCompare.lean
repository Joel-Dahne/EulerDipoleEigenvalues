module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceWeakGluing

/-!
# Comparison of one-sided canonical boundary traces

Blueprint: `lem:one-sided-trace-comparison`.

Restrict to a common inward interval and compare the continuous sections
before taking their endpoint limits. The map can translate the tangential
parameter and reverse or translate the normal parameter.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Canonical traces agree under a compatible product reparametrization on
any common inward subwindow. -/
theorem HasTransverseH1Trace.ae_eq_inward {a b w l r c d t δ : ℝ}
    {V W : ℝ × ℝ → ℂ} {T S : ℝ → ℂ}
    (hT : HasTransverseH1Trace a b 0 w 0 id V T)
    (hS : HasTransverseH1Trace l r c d t id W S)
    {k φ : ℝ → ℝ} (hδ : 0 < δ) (hδw : δ ≤ w)
    (hk : MapsTo k (Ioo a b) (Ioo l r)) (hφ : MapsTo φ (Ioo 0 δ) (Ioo c d))
    (hkm : MeasurePreserving k volume volume) (hφm : MeasurePreserving φ volume volume)
    (hφc : Continuous φ) (hφ0 : φ 0 = t)
    (he : ∀ s ∈ Ioo a b, ∀ u ∈ Ioo 0 δ, V (s, u) = W (k s, φ u)) :
    T =ᵐ[volume.restrict (Ioo a b)] S ∘ k := by
  obtain ⟨_, hw, h0, G, D, _, hGV, hG, hD, hGD, hTG⟩ := hT
  obtain ⟨_, hcd, ht, H, E, _, hHW, hH, hE, hHE, hSH⟩ := hS
  let Q := Ioo a b ×ˢ Ioo (0 : ℝ) δ
  have hsub : Q ⊆ Ioo a b ×ˢ Ioo 0 w :=
    prod_mono subset_rfl (Ioo_subset_Ioo_right hδw)
  have hmap : MapsTo (Prod.map k φ) Q (Ioo l r ×ˢ Ioo c d) :=
    fun _ hq ↦ ⟨hk hq.1, hφ hq.2⟩
  have hm : MeasurePreserving (Prod.map k φ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact hkm.prod hφm
  have hkm' := hkm.quasiMeasurePreserving.restrict hk
  have hH' := (hm.quasiMeasurePreserving.restrict hmap).ae hHW
  have hGH : G =ᵐ[volume.restrict Q] (H ∘ Prod.map k φ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hGV, hH',
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo : MeasurableSet Q)]
      with q h1 h2 hq
    exact h1.trans ((he q.1 hq.1 q.2 hq.2).trans h2.symm)
  have hGcont : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ContinuousOn (fun u ↦ G (s,u)) (Ioo 0 δ) :=
    (hGD.ae_continuousOn isOpen_Ioo).mono fun _ hs ↦ hs.mono (Ioo_subset_Ioo_right hδw)
  have hHcont : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ContinuousOn (fun u ↦ H (k s,φ u)) (Ioo 0 δ) := by
    filter_upwards [hkm'.ae (hHE.ae_continuousOn isOpen_Ioo)] with s hs
    exact hs.comp hφc.continuousOn hφ
  have hψ : Tendsto φ (𝓝[Ioo 0 δ] 0) (𝓝[Ioo c d] t) := by
    rw [← hφ0]
    exact hφc.continuousWithinAt.tendsto_nhdsWithin hφ
  have : (𝓝[Ioo 0 δ] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hδ
  have hJ : ∀ᶠ u in 𝓝[Ioo 0 δ] (0 : ℝ), u ∈ Ioo 0 δ := self_mem_nhdsWithin
  filter_upwards [hTG, hkm'.ae hSH, hGD.ae_tendsto_trace hw hG hD,
    hkm'.ae (hHE.ae_tendsto_trace hcd hH hE),
    ae_eqOn_sections_of_ae_eq isOpen_Ioo hGH hGcont hHcont] with s hs1 hs2 hg hh heq
  have hleft := (hg 0 h0).mono_left (nhdsWithin_mono 0 (Ioo_subset_Ioo_right hδw))
  have hright := (hh t ht).comp hψ
  have hEq : ∀ᶠ u in 𝓝[Ioo 0 δ] (0 : ℝ), H (k s,φ u) = G (s,u) :=
    hJ.mono fun u hu ↦ (heq u hu).symm
  exact hs1.trans ((tendsto_nhds_unique hleft (hright.congr' hEq)).trans hs2.symm)

/-- Replace a canonical trace by the same a.e. tangential class. -/
theorem HasTransverseH1Trace.congr_trace {l r a b t : ℝ} {C : ℝ × ℝ → ℝ × ℝ}
    {F : ℝ × ℝ → ℂ} {T S : ℝ → ℂ} (h : HasTransverseH1Trace l r a b t C F T)
    (he : S =ᵐ[volume.restrict (Ioo l r)] T) : HasTransverseH1Trace l r a b t C F S := by
  obtain ⟨hl, hn, ht, G, D, hm, heG, hG, hD, ha, htG⟩ := h
  exact ⟨hl, hn, ht, G, D, hm, heG, hG, hD, ha, he.trans htG⟩

/-- The weak normal derivative gives a canonical trace at any point of the
closed normal interval, with no choice of raw boundary values. -/
theorem HasWeakPartialOn.exists_transverse_trace {a b l r t : ℝ} (hlr : l < r)
    (hab : a < b) (ht : t ∈ Icc a b) {V D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 V D)
    (hV : MemLp V 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    ∃ T, HasTransverseH1Trace l r a b t id V T := by
  obtain ⟨G, hm, he, ha, _, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hlr) hab hV hD
  exact ⟨_, hlr, hab, ht, G, D, hm, he, hV.ae_eq he.symm, hD, ha, EventuallyEq.rfl⟩

end NoEmbeddedEigenvalues
