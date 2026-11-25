module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.WeightedTraces

/-!
# Consistent interior traces from continuous section germs

Blueprint: `def:interior-section-trace`, `lem:interior-section-trace`.

A locally continuous representative of a one-dimensional a.e. class has a unique
value at zero. Choosing that value gives a single interior trace independent of
all transverse windows. Its agreement with the existing ACL trace is proved;
no value of an arbitrary raw planar representative on a null line is used.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- A continuous representative on some interval around zero, in the a.e. sense. -/
def HasContinuousSectionGerm (f : ℝ → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ ContinuousOn g (Ioo a b) ∧
    g =ᵐ[volume.restrict (Ioo a b)] f

/-- The representative-independent interior value when a continuous germ exists.
The fallback on exceptional sections is irrelevant to all trace assertions. -/
def interiorSectionTrace (f : ℝ → ℂ) : ℂ := by
  classical
  exact if h : HasContinuousSectionGerm f then h.choose 0 else 0

/-- One consistent choice on all transverse windows in the same planar chart. -/
def interiorChartTrace (chart : ℝ × ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℂ) (r : ℝ) : ℂ :=
  interiorSectionTrace (fun t ↦ F (chart (r, t)))

theorem interiorSectionTrace_eq {f g : ℝ → ℂ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hg : ContinuousOn g (Ioo a b))
    (hgf : g =ᵐ[volume.restrict (Ioo a b)] f) : interiorSectionTrace f = g 0 := by
  classical
  have hf : HasContinuousSectionGerm f := ⟨g, a, b, ha, hb, hg, hgf⟩
  rw [interiorSectionTrace, dite_eq_left hf]
  obtain ⟨a', b', ha', hb', hg', hgf'⟩ := hf.choose_spec
  have hsub : Ioo (max a a') (min b b') ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hsub' : Ioo (max a a') (min b b') ⊆ Ioo a' b' :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have he := (hgf'.filter_mono (ae_mono (Measure.restrict_mono hsub' le_rfl))).trans
    (hgf.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))).symm
  exact Measure.eqOn_open_of_ae_eq he isOpen_Ioo (hg'.mono hsub') (hg.mono hsub)
    ⟨max_lt ha ha', lt_min hb hb'⟩

theorem interiorSectionTrace_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    interiorSectionTrace f = f 0 :=
  interiorSectionTrace_eq (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)
    hf.continuousOn EventuallyEq.rfl

/-- An a.e. change on a neighbourhood does not change an existing trace germ. -/
theorem interiorSectionTrace_congr {f f' : ℝ → ℂ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hf : HasContinuousSectionGerm f)
    (he : f =ᵐ[volume.restrict (Ioo a b)] f') :
    interiorSectionTrace f = interiorSectionTrace f' := by
  obtain ⟨g, c, d, hc, hd, hg, hgf⟩ := hf
  have hs : Ioo (max a c) (min b d) ⊆ Ioo c d :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hs' : Ioo (max a c) (min b d) ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  rw [interiorSectionTrace_eq hc hd hg hgf]
  exact (interiorSectionTrace_eq (max_lt ha hc) (lt_min hb hd) (hg.mono hs)
    ((hgf.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))).trans
      (he.filter_mono (ae_mono (Measure.restrict_mono hs' le_rfl))))).symm

theorem HasContinuousSectionGerm.mul_continuous {f g : ℝ → ℂ}
    (hf : HasContinuousSectionGerm f) (hg : Continuous g) :
    HasContinuousSectionGerm (fun t ↦ g t * f t) := by
  obtain ⟨h, a, b, ha, hb, hh, hhe⟩ := hf
  exact ⟨fun t ↦ g t * h t, a, b, ha, hb, hg.continuousOn.mul hh,
    hhe.mono fun t ht ↦ congrArg (g t * ·) ht⟩

theorem interiorSectionTrace_mul_continuous {f g : ℝ → ℂ}
    (hf : HasContinuousSectionGerm f) (hg : Continuous g) :
    interiorSectionTrace (fun t ↦ g t * f t) = g 0 * interiorSectionTrace f := by
  obtain ⟨h, a, b, ha, hb, hh, hhe⟩ := hf
  rw [interiorSectionTrace_eq ha hb hh hhe]
  exact interiorSectionTrace_eq ha hb (hg.continuousOn.mul hh)
    (hhe.mono fun t ht ↦ congrArg (g t * ·) ht)

theorem interiorSectionTrace_add_continuous {f g : ℝ → ℂ}
    (hf : HasContinuousSectionGerm f) (hg : Continuous g) :
    interiorSectionTrace (fun t ↦ f t + g t) = interiorSectionTrace f + g 0 := by
  obtain ⟨h, a, b, ha, hb, hh, hhe⟩ := hf
  rw [interiorSectionTrace_eq ha hb hh hhe]
  exact interiorSectionTrace_eq ha hb (hh.add hg.continuousOn)
    (hhe.mono fun t ht ↦ congrArg (· + g t) ht)

theorem interiorSectionTrace_eq_sub_add {f g : ℝ → ℂ}
    (hf : HasContinuousSectionGerm (fun t ↦ f t - g t)) (hg : Continuous g) :
    interiorSectionTrace f = interiorSectionTrace (fun t ↦ f t - g t) + g 0 := by
  simpa only [sub_add_cancel] using interiorSectionTrace_add_continuous hf hg

/-- The planar a.e. equality used by a trace supplies genuine a.e. section equality. -/
theorem ae_sections_eq_of_rectangle {l r a b : ℝ} {F G : ℝ × ℝ → ℂ}
    (he : F =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo a b)] G) :
    ∀ᵐ x ∂volume.restrict (Ioo l r),
      (fun t ↦ F (x, t)) =ᵐ[volume.restrict (Ioo a b)] (fun t ↦ G (x, t)) := by
  apply Measure.ae_ae_of_ae_prod (p := fun q ↦ F q = G q)
  simpa only [Filter.EventuallyEq, Measure.prod_restrict, Measure.volume_eq_prod] using he

/-- Every interior ACL trace agrees with the single continuous-germ choice. -/
theorem HasTransverseH1Trace.ae_eq_interiorChartTrace {l r a b : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b 0 chart F T) (ha : a < 0) (hb : 0 < b) :
    T =ᵐ[volume.restrict (Ioo l r)] interiorChartTrace chart F := by
  obtain ⟨_, hab, _, G, D, _, hGF, hG, hD, hACL, hT⟩ := h
  filter_upwards [hT, hACL.ae_trace_eq hab hG hD,
    hACL.ae_continuousOn isOpen_Ioo, ae_sections_eq_of_rectangle hGF]
    with x hx htrace hc he
  exact hx.trans ((htrace 0 ⟨ha, hb⟩).trans
    (interiorSectionTrace_eq ha hb hc he).symm)

theorem HasTransverseH1Trace.ae_hasContinuousSectionGerm {l r a b : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b 0 chart F T) (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ x ∂volume.restrict (Ioo l r),
      HasContinuousSectionGerm (fun t ↦ F (chart (x, t))) := by
  obtain ⟨_, _, _, G, D, _, hGF, _, _, hACL, _⟩ := h
  filter_upwards [hACL.ae_continuousOn isOpen_Ioo, ae_sections_eq_of_rectangle hGF]
    with x hc he
  exact ⟨fun t ↦ G (x, t), a, b, ha, hb, hc, he⟩

/-- An H¹ pullback produces the same canonical trace on every interior window,
with actual L² membership rather than only a totalized integral bound. -/
theorem MemSobolevOn.hasInteriorChartTrace {l r a b : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ}
    (hlr : l < r) (ha : a < 0) (hb : 0 < b)
    (hF : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) (fun q ↦ F (chart q))) :
    HasTransverseH1Trace l r a b 0 chart F (interiorChartTrace chart F) ∧
    MemLp (interiorChartTrace chart F) 2 (volume.restrict (Ioo l r)) := by
  obtain ⟨D, hd, hD⟩ := hF.2 1
  obtain ⟨G, hGm, hGF, hACL, _, htrace⟩ := hd.exists_l2_trace
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr hlr) (ha.trans hb) hF.1 hD
  have h : HasTransverseH1Trace l r a b 0 chart F (aclTrace a b G D 0) :=
    ⟨hlr, ha.trans hb, ⟨ha.le, hb.le⟩, G, D, hGm, hGF,
      hF.1.ae_eq hGF.symm, hD, hACL, EventuallyEq.rfl⟩
  have he := h.ae_eq_interiorChartTrace ha hb
  refine ⟨?_, (htrace 0 ⟨ha.le, hb.le⟩).1.ae_eq he⟩
  exact ⟨hlr, ha.trans hb, ⟨ha.le, hb.le⟩, G, D, hGm, hGF,
    hF.1.ae_eq hGF.symm, hD, hACL, he.symm⟩

end EulerDipoleEigenvalues
