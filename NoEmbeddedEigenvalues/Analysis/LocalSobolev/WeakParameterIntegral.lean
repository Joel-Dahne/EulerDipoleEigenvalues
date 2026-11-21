module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ACLSlicing
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceH2

/-!
# Weak differentiation under a signed parameter integral

Blueprint: `lem:weak-parameter-integral`.

Coordinate swapping and complex-valued sliced tests provide the distributional
identities used to commute level differentiation with a midpoint integral.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Complex-valued version of the fixed-test sliced weak identity. -/
theorem ae_sliced_test_complex {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U 1 F D) {a b c d : ℝ}
    (hrect : Icc a b ×ˢ Icc c d ⊆ U) {β : ℝ → ℂ}
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hβJ : tsupport β ⊆ Ioo c d) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      (∫ t in Icc c d, F (x, t) * deriv β t) =
        -(∫ t in Icc c d, D (x, t) * β t) := by
  let r : ℝ → ℝ := fun t ↦ (β t).re
  let i : ℝ → ℝ := fun t ↦ (β t).im
  have hr : ContDiff ℝ ∞ r := Complex.reCLM.contDiff.comp hβ
  have hi : ContDiff ℝ ∞ i := Complex.imCLM.contDiff.comp hβ
  have hrder (t : ℝ) : deriv r t = (deriv β t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hβ.differentiable (by simp) t).hasDerivAt)).deriv
  have hinder (t : ℝ) : deriv i t = (deriv β t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hβ.differentiable (by simp) t).hasDerivAt)).deriv
  have hsR : tsupport r ⊆ tsupport β := tsupport_comp_subset rfl β
  have hsI : tsupport i ⊆ tsupport β := tsupport_comp_subset rfl β
  have hwR := ACLSlicing.ae_sliced_test hd hrect hr
    (hβs.comp_left rfl) (hsR.trans hβJ)
  have hwI := ACLSlicing.ae_sliced_test hd hrect hi
    (hβs.comp_left rfl) (hsI.trans hβJ)
  have hFp : Integrable F ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hd.1.integrableOn_compact_subset hrect (isCompact_Icc.prod isCompact_Icc)
  have hDp : Integrable D ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hd.2.1.integrableOn_compact_subset hrect (isCompact_Icc.prod isCompact_Icc)
  filter_upwards [hwR, hwI,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hFp.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hDp.prod_right_ae]
      with x hxR hxI hxF hxD
  have hsplit {V R J : ℝ → ℂ} (hV : IntegrableOn V (Icc c d))
      (hR : Continuous R) (hJ : Continuous J) :
      (∫ t in Icc c d, V t * (R t + Complex.I * J t)) =
        (∫ t in Icc c d, V t * R t) + Complex.I * ∫ t in Icc c d, V t * J t := by
    have hVR := hV.mul_continuousOn hR.continuousOn isCompact_Icc
    have hVJ := hV.mul_continuousOn hJ.continuousOn isCompact_Icc
    rw [← integral_const_mul, ← integral_add hVR (hVJ.const_mul Complex.I)]
    congr 1
    funext t
    ring
  have hleft : (∫ t in Icc c d, F (x, t) * deriv β t) =
      (∫ t in Icc c d, F (x, t) * ((deriv r t : ℝ) : ℂ)) +
        Complex.I * ∫ t in Icc c d, F (x, t) * ((deriv i t : ℝ) : ℂ) := by
    calc
      _ = ∫ t in Icc c d, F (x, t) *
          (((deriv r t : ℝ) : ℂ) + Complex.I * ((deriv i t : ℝ) : ℂ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t ↦ by
          dsimp only
          rw [hrder, hinder, mul_comm Complex.I, Complex.re_add_im]
      _ = _ := hsplit hxF (Complex.continuous_ofReal.comp (hr.continuous_deriv (by simp)))
        (Complex.continuous_ofReal.comp (hi.continuous_deriv (by simp)))
  have hright : (∫ t in Icc c d, D (x, t) * β t) =
      (∫ t in Icc c d, D (x, t) * (r t : ℂ)) +
        Complex.I * ∫ t in Icc c d, D (x, t) * (i t : ℂ) := by
    calc
      _ = ∫ t in Icc c d, D (x, t) * ((r t : ℂ) + Complex.I * (i t : ℂ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t ↦ by
          dsimp only [r, i]
          rw [mul_comm Complex.I, Complex.re_add_im]
      _ = _ := hsplit hxD (Complex.continuous_ofReal.comp hr.continuous)
        (Complex.continuous_ofReal.comp hi.continuous)
  rw [hleft, hright, hxR, hxI]
  ring

/-- A compact level test can be passed through the signed midpoint integral.
This is a distributional identity, with no pointwise differentiability of `F`. -/
theorem integral_parameterPrimitive_mul_deriv {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F D : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn U 0 F D) {a b c d t : ℝ}
    (hrect : Icc a b ×ˢ Icc c d ⊆ U) (hzero : (0 : ℝ) ∈ Icc c d) (ht : t ∈ Icc c d)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hβJ : tsupport β ⊆ Ioo a b) :
    (∫ x in Icc a b, (∫ u in 0..t, F (x, u)) * deriv β x) =
      -(∫ x in Icc a b, (∫ u in 0..t, D (x, u)) * β x) := by
  have hs := HasWeakPartialOn.comp_swap_fst hU hd
  have hrect' : Icc c d ×ˢ Icc a b ⊆ Prod.swap ⁻¹' U :=
    fun _ hp ↦ hrect ⟨hp.2, hp.1⟩
  have hw := ae_sliced_test_complex hs hrect' hβ hβs hβJ
  have hw' : ∀ᵐ u ∂(volume.restrict (Icc c d)),
      (∫ x in Icc a b, F (x, u) * deriv β x) =
        -(∫ x in Icc a b, D (x, u) * β x) := by
    rw [← Measure.restrict_congr_set
      (Ioo_ae_eq_Icc : Ioo c d =ᵐ[volume] Icc c d)]
    exact hw
  have hsub : uIoc 0 t ⊆ Icc c d := uIoc_subset_uIcc.trans (uIcc_subset_Icc hzero ht)
  have hi {V : ℝ × ℝ → ℂ} (hV : LocallyIntegrableOn V U) {k : ℝ → ℂ}
      (hk : Continuous k) :
      Integrable (fun p : ℝ × ℝ ↦ V (p.2, p.1) * k p.2)
        ((volume.restrict (uIoc 0 t)).prod (volume.restrict (Icc a b))) := by
    have hVk : IntegrableOn (fun p : ℝ × ℝ ↦ (V ∘ Prod.swap) p * k p.2)
        (Icc c d ×ˢ Icc a b) :=
      ((locallyIntegrableOn_comp_swap hV hU).integrableOn_compact_subset hrect'
        (isCompact_Icc.prod isCompact_Icc)).mul_continuousOn
          (hk.comp continuous_snd).continuousOn (isCompact_Icc.prod isCompact_Icc)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hVk.mono_set (prod_mono hsub subset_rfl)
  have heF := intervalIntegral_integral_swap (f := fun u x ↦ F (x, u) * deriv β x)
    (hi hd.1 (hβ.continuous_deriv (by simp)))
  have heD := intervalIntegral_integral_swap (f := fun u x ↦ D (x, u) * β x)
    (hi hd.2.1 hβ.continuous)
  calc
    _ = ∫ u in 0..t, ∫ x in Icc a b, F (x, u) * deriv β x := by
      simpa only [intervalIntegral.integral_mul_const] using heF.symm
    _ = ∫ u in 0..t, -(∫ x in Icc a b, D (x, u) * β x) := by
      apply intervalIntegral.integral_congr_ae_restrict
      exact hw'.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    _ = _ := by
      rw [intervalIntegral.integral_neg, heD]
      simp only [intervalIntegral.integral_mul_const]

/-- A signed primitive of a rectangle-integrable function is rectangle-integrable.
The rectangle's time interval contains the fixed midpoint. -/
theorem integrableOn_parameterPrimitive_rectangle {a b c d : ℝ}
    {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F (Icc a b ×ˢ Icc c d))
    (hzero : (0 : ℝ) ∈ Icc c d) :
    IntegrableOn (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, F (q.1, u)) (Icc a b ×ˢ Icc c d) := by
  let K := Icc a b ×ˢ Icc c d
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hm : AEStronglyMeasurable (K.indicator F) (volume : Measure (ℝ × ℝ)) :=
    (aestronglyMeasurable_indicator_iff hKm).2 hF.aestronglyMeasurable
  let G := hm.mk (K.indicator F)
  have hGeq : K.indicator F =ᵐ[(volume : Measure ℝ).prod volume] G := by
    simpa only [Measure.volume_eq_prod] using hm.ae_eq_mk
  have hgood : ∀ᵐ q : ℝ × ℝ, ∀ᵐ u : ℝ,
      K.indicator F (q.1, u) = G (q.1, u) := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ae_of_ae_prod hGeq)
  have hPm : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, F (q.1, u))
      (volume.restrict K) := by
    have hGm : Measurable G := hm.stronglyMeasurable_mk.measurable
    have hp := (ACLSlicing.measurable_sectionPrimitive hGm 0).aestronglyMeasurable
      (μ := volume.restrict K)
    apply hp.congr
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hKm] with q hq hqK
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hq] with u hu huI
    have huK : (q.1, u) ∈ K :=
      ⟨hqK.1, uIcc_subset_Icc hzero hqK.2 (uIoc_subset_uIcc huI)⟩
    simpa only [indicator_of_mem huK] using hu.symm
  have hFp : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hJ := hFp.norm.integral_prod_left.comp_fst (volume.restrict (Icc c d))
  have hPmp : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, F (q.1, u))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hPi := hJ.mono' hPmp (by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFp.prod_right_ae,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)] with q hq ht
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_mono_set hq.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Eventually.of_forall fun _ hu ↦
          uIcc_subset_Icc hzero ht (uIoc_subset_uIcc hu))))
  simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hPi

private theorem compact_inner_rectangle {a b c d : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ Ioo a b ×ˢ Ioo c d) (hc : c < 0) (hd : 0 < d) :
    ∃ A B C D : ℝ, a < A ∧ B < b ∧ c < C ∧ D < d ∧ C < 0 ∧ 0 < D ∧
      K ⊆ Ioo A B ×ˢ Ioo C D := by
  obtain ⟨l, hl, hlo⟩ := hK.exists_forall_le'
    (continuous_fst.sub continuous_const).continuousOn
    (fun p hp ↦ sub_pos.2 (hKU hp).1.1)
  obtain ⟨r, hr, hhi⟩ := hK.exists_forall_le'
    (continuous_const.sub continuous_fst).continuousOn
    (fun p hp ↦ sub_pos.2 (hKU hp).1.2)
  obtain ⟨s, hs, hbot⟩ := hK.exists_forall_le'
    (continuous_snd.sub continuous_const).continuousOn
    (fun p hp ↦ sub_pos.2 (hKU hp).2.1)
  obtain ⟨v, hv, htop⟩ := hK.exists_forall_le'
    (continuous_const.sub continuous_snd).continuousOn
    (fun p hp ↦ sub_pos.2 (hKU hp).2.2)
  refine ⟨a + l / 2, b - r / 2, min (c + s / 2) (c / 2),
    max (d - v / 2) (d / 2), by linarith, by linarith,
    lt_min (by linarith) (by linarith), max_lt (by linarith) (by linarith),
    (min_le_right _ _).trans_lt (by linarith),
    (show 0 < d / 2 by linarith).trans_le (le_max_right _ _), ?_⟩
  intro p hp
  have h1 := hlo p hp
  have h2 := hhi p hp
  have h3 := hbot p hp
  have h4 := htop p hp
  dsimp only [Pi.sub_apply] at h1 h2 h3 h4
  exact ⟨⟨by linarith, by linarith⟩,
    ⟨(min_le_left _ _).trans_lt (by linarith),
      (show p.2 < d - v / 2 by linarith).trans_le (le_max_left _ _)⟩⟩

/-- On a rectangle containing the midpoint, weak level differentiation commutes
with the signed time primitive. Local integrability of both primitives is explicit. -/
private theorem parameterPrimitive_rectangle_of_locallyIntegrable {a b c d : ℝ}
    (hc : c < 0) (hd : 0 < d) {F D : ℝ × ℝ → ℂ}
    (hFD : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (hP : LocallyIntegrableOn (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, F (q.1, u))
      (Ioo a b ×ˢ Ioo c d))
    (hQ : LocallyIntegrableOn (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, D (q.1, u))
      (Ioo a b ×ˢ Ioo c d)) :
    HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0
      (fun q ↦ ∫ u in 0..q.2, F (q.1, u)) (fun q ↦ ∫ u in 0..q.2, D (q.1, u)) := by
  refine ⟨hP, hQ, ?_⟩
  intro φ hφ
  obtain ⟨A, B, C, E, hA, hB, hC, hE, hC0, hE0, hs⟩ :=
    compact_inner_rectangle hφ.hasCompactSupport hφ.tsupport_subset hc hd
  let K := Icc A B ×ˢ Icc C E
  have hKU : K ⊆ Ioo a b ×ˢ Ioo c d :=
    prod_mono (Icc_subset_Ioo hA hB) (Icc_subset_Ioo hC hE)
  have hφK : tsupport φ ⊆ K := hs.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hslice (t : ℝ) :
      (∫ x in Icc A B, (∫ u in 0..t, F (x, u)) * partialX φ (x, t)) =
        -(∫ x in Icc A B, (∫ u in 0..t, D (x, u)) * φ (x, t)) := by
    by_cases ht : t ∈ Icc C E
    · have hβ : ContDiff ℝ ∞ (fun x ↦ φ (x, t)) :=
        hφ.contDiff.comp (contDiff_id.prodMk contDiff_const)
      have hpre : tsupport (fun x ↦ φ (x, t)) ⊆
          (fun x : ℝ ↦ (x, t)) ⁻¹' tsupport φ :=
        closure_minimal (fun _ hx ↦ subset_tsupport φ hx)
          ((isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const))
      have hβsub : tsupport (fun x ↦ φ (x, t)) ⊆ Ioo A B :=
        fun x hx ↦ (hs (hpre hx)).1
      have hβs : HasCompactSupport (fun x ↦ φ (x, t)) :=
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
          (hβsub.trans Ioo_subset_Icc_self)
      exact integral_parameterPrimitive_mul_deriv (isOpen_Ioo.prod isOpen_Ioo) hFD hKU
        ⟨hC0.le, hE0.le⟩ ht hβ hβs hβsub
    · have hval (x : ℝ) : φ (x, t) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hp ↦ ht (Ioo_subset_Icc_self (hs hp).2))
      have hder (x : ℝ) : partialX φ (x, t) = 0 := by
        change deriv (fun s ↦ φ (s, t)) x = 0
        simp_rw [hval]
        exact deriv_const x (0 : ℂ)
      simp_rw [hval, hder, mul_zero, integral_zero, neg_zero]
  have hFint := integrable_mul_of_tsupport_subset hP (hφ.continuous_coordPartial 0)
    (hφ.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 φ).trans hφ.tsupport_subset)
  have hDint := integrable_mul_of_tsupport_subset hQ hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have heq {V : ℝ × ℝ → ℂ} (hi : Integrable V) (hz : ∀ p ∉ K, V p = 0) :
      (∫ p, V p) = ∫ t in Icc C E, ∫ x in Icc A B, V (x, t) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ (by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hi.integrableOn)
  rw [heq hFint (fun p hp ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφK
      (tsupport_coordPartial_subset 0 φ ht))), mul_zero]),
    heq hDint (fun p hp ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφK ht)), mul_zero])]
  simp only [coordPartial, ite_true]
  calc
    _ = ∫ t in Icc C E, -(∫ x in Icc A B, (∫ u in 0..t, D (x, u)) * φ (x, t)) :=
      integral_congr_ae (Eventually.of_forall hslice)
    _ = _ := integral_neg _

/-- Local integrability is preserved by a signed midpoint primitive on an open
rectangle whose time interval contains zero. -/
theorem locallyIntegrableOn_parameterPrimitive_rectangle {a b c d : ℝ}
    (hc : c < 0) (hd : 0 < d) {F : ℝ × ℝ → ℂ}
    (hF : LocallyIntegrableOn F (Ioo a b ×ˢ Ioo c d)) :
    LocallyIntegrableOn (fun q : ℝ × ℝ ↦ ∫ u in 0..q.2, F (q.1, u))
      (Ioo a b ×ˢ Ioo c d) := by
  apply (locallyIntegrableOn_iff (isOpen_Ioo.prod isOpen_Ioo).isLocallyClosed).2
  intro K hKU hK
  obtain ⟨A, B, C, E, hA, hB, hC, hE, hC0, hE0, hs⟩ :=
    compact_inner_rectangle hK hKU hc hd
  have hrect : Icc A B ×ˢ Icc C E ⊆ Ioo a b ×ˢ Ioo c d :=
    prod_mono (Icc_subset_Ioo hA hB) (Icc_subset_Ioo hC hE)
  exact (integrableOn_parameterPrimitive_rectangle
    (hF.integrableOn_compact_subset hrect (isCompact_Icc.prod isCompact_Icc))
    ⟨hC0.le, hE0.le⟩).mono_set
      (hs.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))

/-- Weak level differentiation commutes with the signed midpoint primitive on
rectangles. All local integrability conclusions follow from the weak input. -/
theorem HasWeakPartialOn.parameterPrimitive_rectangle {a b c d : ℝ}
    (hc : c < 0) (hd : 0 < d) {F D : ℝ × ℝ → ℂ}
    (hFD : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D) :
    HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0
      (fun q ↦ ∫ u in 0..q.2, F (q.1, u)) (fun q ↦ ∫ u in 0..q.2, D (q.1, u)) :=
  parameterPrimitive_rectangle_of_locallyIntegrable hc hd hFD
    (locallyIntegrableOn_parameterPrimitive_rectangle hc hd hFD.1)
    (locallyIntegrableOn_parameterPrimitive_rectangle hc hd hFD.2.1)

end NoEmbeddedEigenvalues
