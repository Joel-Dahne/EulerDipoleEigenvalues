module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalIntegralFlux

/-!
# Second regularity of fixed-window parameter integrals

Blueprint: `lem:fixed-window-h1-rough`, `lem:fixed-window-h2`,
`lem:interval-h1-continuous-derivative`, `lem:interval-h2-canonical-derivatives`.

A rough weak parameter derivative is replaced by an ACL integral representative,
not by its arbitrary values on exceptional parameter lines. This gives interval
H² for the original integral whenever its continuous potential has two L² weak
parameter derivatives. The ordinary first and second derivatives provide
compatible representatives on overlapping intervals.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- A weak parameter integral has an interval H¹ representative even when the
original planar field is not continuous. Its averaged derivative is retained. -/
theorem HasWeakPartialOn.exists_setIntegral_h1_rep {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D) :
    ∃ A : ℝ → ℂ, A =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ ∫ t in Icc l r, F (x, t)) ∧
      HasIntervalH1 a b A (fun x ↦ ∫ t in Icc l r, D (x, t)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    isFiniteMeasure_restrict.2 ((measure_mono
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).trans_lt
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  let R := Ioo a b ×ˢ Ioo c d
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hs : Prod.swap ⁻¹' R = Ioo c d ×ˢ Ioo a b := by
    ext p
    simp only [R, mem_preimage, mem_prod, Prod.fst_swap, Prod.snd_swap, and_comm]
  have hFs := memLp_comp_swap hRo.measurableSet hF
  have hDs := memLp_comp_swap hRo.measurableSet hD
  have hds := hd.comp_swap_fst hRo
  rw [hs] at hFs hDs hds
  obtain ⟨G, hGm, hGF, hG⟩ := hds.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hcd) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hab)
  have hGL := hFs.ae_eq hGF.symm
  have hsub : Icc l r ⊆ Ioo c d := Icc_subset_Ioo hl hr
  have hGsub : HasACLSectionsOn (Icc l r) (Ioo a b) G (D ∘ Prod.swap) :=
    ae_restrict_of_ae_restrict_of_subset hsub hG
  have hGLsub := hGL.mono_measure (Measure.restrict_mono_set _ (prod_mono hsub subset_rfl))
  have hDLsub := hDs.mono_measure (Measure.restrict_mono_set _ (prod_mono hsub subset_rfl))
  have htrace (x : ℝ) (hx : x ∈ Ioo a b) :
      MemLp (fun t ↦ G (t, x)) 2 (volume.restrict (Icc l r)) := by
    apply ((hGsub.l2_trace hab hGm hGLsub hDLsub x (Ioo_subset_Icc_self hx)).1).ae_eq
    filter_upwards [hGsub.ae_trace_eq hab hGLsub hDLsub] with t ht
    exact ht x hx
  let A := fun x ↦ ∫ t in Icc l r, G (t, x)
  have hmeanEq : A =ᵐ[volume.restrict (Ioo a b)]
      (fun x ↦ ∫ t in Icc l r, F (x, t)) := by
    have hprod : G =ᵐ[(volume.restrict (Ioo c d)).prod (volume.restrict (Ioo a b))]
        (F ∘ Prod.swap) := by
      simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hGF
    have heq : ∀ᵐ p ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))),
        G p.swap = F p := by
      simpa only [Function.comp_apply, Prod.swap_swap] using
        Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
    filter_upwards [Measure.ae_ae_of_ae_prod heq] with x hx
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hx)
  have hFs' := hF.mono_measure (Measure.restrict_mono_set _ (prod_mono subset_rfl hsub))
  have hDs' := hD.mono_measure (Measure.restrict_mono_set _ (prod_mono subset_rfl hsub))
  have hDL := memLp_setIntegral_Icc hlr hDs'
  have hFTC : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      (∫ s in x..y, ∫ t in Icc l r, D (s, t)) = A y - A x := by
    intro x hx y hy
    have hi : Integrable (Function.uncurry (fun s t ↦ D (s, t)))
        ((volume.restrict (uIoc x y)).prod (volume.restrict (Icc l r))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact (hD.integrable (by norm_num)).mono_measure (Measure.restrict_mono_set _
        (prod_mono (uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hx hy)) hsub))
    rw [intervalIntegral_integral_swap hi]
    calc
      _ = ∫ t in Icc l r, G (t, y) - G (t, x) := by
        apply integral_congr_ae
        filter_upwards [hGsub.ae_hasIntervalH1 hGLsub hDLsub] with t ht
        exact ht.integral_eq_sub hx hy
      _ = _ := integral_sub ((htrace y hy).integrable (by norm_num))
        ((htrace x hx).integrable (by norm_num))
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq hab hDL hFTC
  exact ⟨A, hmeanEq, ⟨(memLp_setIntegral_Icc hlr hFs').ae_eq hmeanEq.symm,
    hDL, hac, (ae_restrict_iff' measurableSet_Ioo).1 hder⟩⟩

/-- The original continuous potential has H² fixed-window integrals when its
first and second weak parameter derivatives are square integrable. -/
theorem HasWeakPartialOn.setIntegral_h2 {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D E : ℝ × ℝ → ℂ}
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hE : MemLp E 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (hxx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 D E) :
    MemIntervalH2 a b (fun x ↦ ∫ t in Icc l r, F (x, t)) := by
  obtain ⟨A, hAeq, hA⟩ := hxx.exists_setIntegral_h1_rep hab hcd hl hlr hr hD hE
  exact ⟨A, _, (hx.setIntegral_h1 hab hcd hl hlr hr hFc hF hD).congr_derivative hAeq.symm, hA⟩

/-- Interval H¹ retains its original continuous representative in the interior. -/
theorem HasIntervalH1.continuousOn_Ioo {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) : ContinuousOn F (Ioo a b) :=
  ((h.continuousOn_extension hab).mono Ioo_subset_Icc_self).congr (h.extension_eq hab).symm

/-- A continuous specified derivative upgrades the a.e. FTC to an actual
pointwise derivative at every interior point. -/
theorem HasIntervalH1.hasDerivAt_of_continuous {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hDc : ContinuousOn D (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt F (D x) x := by
  have hm := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo hDc x hx
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl : IntervalIntegrable D volume x x) hm
    (hDc.continuousAt (isOpen_Ioo.mem_nhds hx))).const_add (F x)
  apply hp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [h.integral_eq_sub hx hy]
  abel

/-- The ordinary first and second derivatives supply one compatible interval
H² pair, without replacing the original value representative. -/
theorem HasIntervalH2.with_deriv {a b : ℝ} {F D E : ℝ → ℂ}
    (h : HasIntervalH2 a b F D E) (hab : a < b) :
    HasIntervalH2 a b F (deriv F) (deriv (deriv F)) := by
  have he : EqOn D (deriv F) (Ioo a b) := fun x hx ↦
    (h.1.hasDerivAt_of_continuous (h.2.continuousOn_Ioo hab) hx).deriv.symm
  exact ⟨h.1.with_deriv, (h.2.congr_Ioo he).with_deriv⟩

end NoEmbeddedEigenvalues
