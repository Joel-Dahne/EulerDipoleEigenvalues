import NoEmbeddedEigenvalues.IntervalH1WeakLift
import NoEmbeddedEigenvalues.WeakParameterIntegral
import NoEmbeddedEigenvalues.WeakPartialLocality
import NoEmbeddedEigenvalues.QuarterReconstruction

/-!
# Weak level differentiation on moving quarter strips

Blueprint: `lem:quarter-primitive-weak`, `lem:quarter-reconstruction-weak`,
`lem:quarter-profile-ae`.

Every interior point has a rectangular neighbourhood whose time interval
contains the midpoint and whose whole rectangle stays inside the strip.
Rectangular weak primitive identities therefore glue without differentiating
the moving endpoints or choosing pointwise orbit representatives.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Midpoint-containing rectangles form neighbourhoods inside the quarter strip. -/
theorem quarterStrip_midpoint_rectangle {b : ℝ} (hb : b ≤ 1)
    {q : ℝ × ℝ} (hq : q ∈ quarterOrbitStrip b) :
    ∃ a c m : ℝ, 0 < m ∧ q ∈ Ioo a c ×ˢ Ioo (-m) m ∧
      Ioo a c ×ˢ Ioo (-m) m ⊆ quarterOrbitStrip b := by
  have hq1 : q.1 ∈ Ioo (0 : ℝ) 1 := ⟨hq.1, hq.2.1.trans_le hb⟩
  have ht : |q.2| < eighthPeriod q.1 := abs_lt.2 hq.2.2
  let m := (|q.2| + eighthPeriod q.1) / 2
  have hm : 0 < m := by dsimp [m]; linarith [abs_nonneg q.2]
  have htm : |q.2| < m := by dsimp [m]; linarith
  have hmL : m < eighthPeriod q.1 := by dsimp [m]; linarith
  have hLc : ContinuousAt eighthPeriod q.1 :=
    continuousOn_eighthPeriod.continuousAt (Ioo_mem_nhds hq1.1 hq1.2)
  have hn' : Ioo 0 b ∩ eighthPeriod ⁻¹' Ioi m ∈ 𝓝 q.1 :=
    inter_mem (Ioo_mem_nhds hq.1 hq.2.1) (hLc.preimage_mem_nhds (Ioi_mem_nhds hmL))
  have hn : {h : ℝ | 0 < h ∧ h < b ∧ m < eighthPeriod h} ∈ 𝓝 q.1 := by
    convert hn' using 1
    ext h
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Ioo, mem_preimage, mem_Ioi, and_assoc]
  obtain ⟨a, c, _, hac, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  refine ⟨a, c, m, hm, ⟨Icc_mem_nhds_iff.1 hac, abs_lt.1 htm⟩, ?_⟩
  intro p hp
  obtain ⟨hp0, hpb, hpL⟩ := hsub (Ioo_subset_Icc_self hp.1)
  exact ⟨hp0, hpb, by linarith [hp.2.1], hp.2.2.trans hpL⟩

/-- Weak level differentiation commutes with a signed midpoint integral on the
moving quarter strip. Local integrability of both primitives is a conclusion. -/
theorem HasWeakPartialOn.quarterPrimitive {b : ℝ} (hb : b ≤ 1)
    {F D : ℝ × ℝ → ℂ} (hFD : HasWeakPartialOn (quarterOrbitStrip b) 0 F D) :
    HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ ∫ u in 0..q.2, F (q.1, u)) (fun q ↦ ∫ u in 0..q.2, D (q.1, u)) := by
  apply hasWeakPartialOn_of_locally
  intro q hq
  obtain ⟨a, c, m, hm, hqR, hRS⟩ := quarterStrip_midpoint_rectangle hb hq
  exact ⟨Ioo a c ×ˢ Ioo (-m) m, isOpen_Ioo.prod isOpen_Ioo, hqR,
    HasWeakPartialOn.parameterPrimitive_rectangle (by linarith) hm (hFD.mono hRS)⟩

/-- The moving strip is open on the physical level range. -/
theorem isOpen_quarterOrbitStrip {b : ℝ} (hb : b ≤ 1) : IsOpen (quarterOrbitStrip b) := by
  apply isOpen_iff_mem_nhds.2
  intro q hq
  obtain ⟨a, c, m, _, hqR, hRS⟩ := quarterStrip_midpoint_rectangle hb hq
  exact mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hqR) hRS

private theorem mul_time_phase {b : ℝ} (hb : b ≤ 1) {F D : ℝ × ℝ → ℂ}
    (hFD : HasWeakPartialOn (quarterOrbitStrip b) 0 F D) (c : ℝ) :
    HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ F q * Complex.exp (Complex.I * ((c * q.2 : ℝ) : ℂ)))
      (fun q ↦ D q * Complex.exp (Complex.I * ((c * q.2 : ℝ) : ℂ))) := by
  let M : ℝ × ℝ → ℂ := fun q ↦ Complex.exp (Complex.I * ((c * q.2 : ℝ) : ℂ))
  have hM : ContDiff ℝ ∞ M :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_snd))).cexp
  have hzero (q : ℝ × ℝ) : coordPartial 0 M q = 0 := by
    change deriv (fun _ : ℝ ↦ Complex.exp (Complex.I * ((c * q.2 : ℝ) : ℂ))) q.1 = 0
    exact deriv_const _ _
  apply (hFD.mul_smooth (isOpen_quarterOrbitStrip hb) hM).congr_ae_on
    (measurableSet_quarterOrbitStrip b)
  · exact Eventually.of_forall fun _ _ ↦ mul_comm _ _
  · exact Eventually.of_forall fun q _ ↦ by rw [hzero, zero_mul, zero_add]; exact mul_comm _ _

/-- The midpoint forcing contribution, written with factored phases. -/
def quarterDuhamel (lam : ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  Complex.I * ((∫ u in 0..q.2,
    F (q.1, u) * Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))) *
      Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)))

/-- The level derivative of the Duhamel term uses the specified weak level
forcing derivative, with no derivative of the moving time endpoints. -/
theorem HasWeakPartialOn.quarterDuhamel {b : ℝ} (hb : b ≤ 1)
    {F D : ℝ × ℝ → ℂ} (hFD : HasWeakPartialOn (quarterOrbitStrip b) 0 F D)
    (lam : ℝ) : HasWeakPartialOn (quarterOrbitStrip b) 0
      (quarterDuhamel lam F) (quarterDuhamel lam D) := by
  have hminus := mul_time_phase hb hFD (-lam)
  have hprimitive := HasWeakPartialOn.quarterPrimitive hb hminus
  have hplus := mul_time_phase hb hprimitive lam
  unfold NoEmbeddedEigenvalues.quarterDuhamel
  simpa only [neg_mul, Complex.ofReal_neg, mul_neg] using hplus.const_mul Complex.I

/-- Full midpoint reconstruction as a sum of its amplitude and forcing parts. -/
def quarterReconstruction (lam : ℝ) (A : ℝ → ℂ) (F : ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) : ℂ :=
  A q.1 * Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)) + quarterDuhamel lam F q

/-- The reconstruction has the orbitwise variation-of-constants formula. -/
theorem quarterReconstruction_eq (lam : ℝ) (A : ℝ → ℂ) (F : ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) :
    quarterReconstruction lam A F q =
      Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)) * A q.1 +
        Complex.I * ∫ u in 0..q.2,
          Complex.exp (Complex.I * ((lam * (q.2 - u) : ℝ) : ℂ)) * F (q.1, u) := by
  calc
    _ = quarterReconstructionLevel lam A F q := by
      dsimp [quarterReconstruction, quarterDuhamel, quarterReconstructionLevel]
      ring
    _ = _ := quarterReconstructionLevel_eq lam A F q

/-- Product and primitive rules identify the joint candidate as a weak derivative,
provided the amplitude's weak level derivative is specified. -/
theorem quarterReconstruction_weak {b : ℝ} (hb : b ≤ 1)
    {A A₁ : ℝ → ℂ} {F D : ℝ × ℝ → ℂ}
    (hA : HasWeakPartialOn (quarterOrbitStrip b) 0 (fun q ↦ A q.1) (fun q ↦ A₁ q.1))
    (hF : HasWeakPartialOn (quarterOrbitStrip b) 0 F D) (lam : ℝ) :
    HasWeakPartialOn (quarterOrbitStrip b) 0 (quarterReconstruction lam A F)
      (quarterReconstructionLevel lam A₁ D) := by
  have h := (mul_time_phase hb hA lam).add (HasWeakPartialOn.quarterDuhamel hb hF lam)
  apply h.congr_ae_on (measurableSet_quarterOrbitStrip b)
  · exact Eventually.of_forall fun _ _ ↦ rfl
  · exact Eventually.of_forall fun q _ ↦ by
      dsimp [quarterDuhamel, quarterReconstructionLevel]
      ring

/-- A compatible local interval derivative lifts to a planar weak derivative. -/
theorem HasIntervalH1Loc.weak_fst {a b : ℝ} {A A₁ : ℝ → ℂ}
    (hA : HasIntervalH1Loc a b A A₁) :
    HasWeakPartialOn (Ioo a b ×ˢ (univ : Set ℝ)) 0
      (fun q ↦ A q.1) (fun q ↦ A₁ q.1) := by
  apply hasWeakPartialOn_of_locally
  intro q hq
  let c := (a + q.1) / 2
  let d := (q.1 + b) / 2
  have hc : a < c := by dsimp [c]; linarith [hq.1.1]
  have hcq : c < q.1 := by dsimp [c]; linarith [hq.1.1]
  have hqd : q.1 < d := by dsimp [d]; linarith [hq.1.2]
  have hd : d < b := by dsimp [d]; linarith [hq.1.2]
  exact ⟨Ioo c d ×ˢ univ, isOpen_Ioo.prod isOpen_univ, ⟨⟨hcq, hqd⟩, mem_univ _⟩,
    HasIntervalH1.weak_fst (hA c d hc (hcq.trans hqd) hd)⟩

/-- Local interval H¹ midpoint data and the specified forcing derivative identify
the full joint level-reconstruction candidate as a weak derivative. -/
theorem quarterReconstruction_weak_of_intervalH1Loc {b : ℝ} (hb : b ≤ 1)
    {A A₁ : ℝ → ℂ} {F D : ℝ × ℝ → ℂ} (hA : HasIntervalH1Loc 0 b A A₁)
    (hF : HasWeakPartialOn (quarterOrbitStrip b) 0 F D) (lam : ℝ) :
    HasWeakPartialOn (quarterOrbitStrip b) 0 (quarterReconstruction lam A F)
      (quarterReconstructionLevel lam A₁ D) := by
  apply quarterReconstruction_weak hb _ hF lam
  exact (HasIntervalH1Loc.weak_fst hA).mono (fun q hq ↦ ⟨⟨hq.1, hq.2.1⟩, mem_univ _⟩)

/-- For a.e. measurable quarter profiles, a.e. equality on a.e. time fiber
implies joint a.e. equality. Measurability is essential in this direction. -/
theorem ae_eq_quarterStrip_of_ae_sections {b : ℝ} {F G : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b)))
    (hG : AEStronglyMeasurable G (volume.restrict (quarterOrbitStrip b)))
    (heq : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
        F (h, t) = G (h, t)) :
    F =ᵐ[volume.restrict (quarterOrbitStrip b)] G := by
  let S := quarterOrbitStrip b
  have hS := measurableSet_quarterOrbitStrip b
  have hmF : AEStronglyMeasurable (S.indicator F) (volume : Measure (ℝ × ℝ)) :=
    (aestronglyMeasurable_indicator_iff hS).2 hF
  have hmG : AEStronglyMeasurable (S.indicator G) (volume : Measure (ℝ × ℝ)) :=
    (aestronglyMeasurable_indicator_iff hS).2 hG
  let f := hmF.mk (S.indicator F)
  let g := hmG.mk (S.indicator G)
  have hfeq : S.indicator F =ᵐ[(volume : Measure ℝ).prod volume] f := by
    simpa only [Measure.volume_eq_prod] using hmF.ae_eq_mk
  have hgeq : S.indicator G =ᵐ[(volume : Measure ℝ).prod volume] g := by
    simpa only [Measure.volume_eq_prod] using hmG.ae_eq_mk
  have hi : ∀ᵐ h : ℝ, ∀ᵐ t : ℝ, S.indicator F (h, t) = S.indicator G (h, t) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 heq] with h hh
    by_cases hI : h ∈ Ioo 0 b
    · filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (hh hI)] with t ht
      by_cases htI : t ∈ Ioo (-eighthPeriod h) (eighthPeriod h)
      · have hq : (h, t) ∈ S := ⟨hI.1, hI.2, htI⟩
        simpa only [indicator_of_mem hq] using ht htI
      · have hq : (h, t) ∉ S := fun hq ↦ htI hq.2.2
        simp only [indicator_of_notMem hq]
    · exact Eventually.of_forall fun t ↦ by
        have hq : (h, t) ∉ S := fun hq ↦ hI ⟨hq.1, hq.2.1⟩
        simp only [indicator_of_notMem hq]
  have hfg : ∀ᵐ h : ℝ, ∀ᵐ t : ℝ, f (h, t) = g (h, t) := by
    filter_upwards [hi, Measure.ae_ae_of_ae_prod hfeq,
      Measure.ae_ae_of_ae_prod hgeq] with h hh hf hg
    filter_upwards [hh, hf, hg] with t ht htF htG
    exact htF.symm.trans (ht.trans htG)
  have hjoint : f =ᵐ[(volume : Measure ℝ).prod volume] g :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmF.stronglyMeasurable_mk.measurable
      hmG.stronglyMeasurable_mk.measurable)).2 hfg
  have hind : S.indicator F =ᵐ[volume] S.indicator G := by
    rw [Measure.volume_eq_prod]
    exact hfeq.trans (hjoint.trans hgeq.symm)
  filter_upwards [ae_restrict_of_ae hind, ae_restrict_mem hS] with q hq hqS
  have hqS' : q ∈ S := hqS
  rw [indicator_of_mem hqS', indicator_of_mem hqS'] at hq
  exact hq

end NoEmbeddedEigenvalues
