import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.DuBoisReymond
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Directional absolute continuity on almost every section

Blueprint: `lem:acl-slicing`.

`HasACLSectionsOn I J G D` records local absolute continuity and the specified a.e.
derivative on almost every vertical section. It requires neither an `x` derivative
nor square integrability. Open order-connected sets cover bounded and unbounded
open intervals without choosing endpoints in the extended reals.

The existence and whole-section uniqueness theorems are proved without admissions.
The proof first slices each fixed time test by Fubini and the fundamental lemma.
The topology induced by `(β, β')` on smooth time tests is second countable, so the
closed sliced identities hold on one common full-measure set. The one-dimensional
weak FTC supplies AC representatives on rational compact rectangles. A fixed
primitive-and-average formula identifies all these representatives and is jointly
measurable; rational windows cover every compact subinterval, also for unbounded
intervals. Finally, measurable versions of the data remove any extra measurability
assumption on the original representatives. Uniqueness only needs continuity of sections.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ContDiff

/-- Almost every vertical section is locally absolutely continuous on `J`, with
specified derivative `D`. The values outside `I ×ˢ J` are unconstrained. -/
def HasACLSectionsOn (I J : Set ℝ) (G D : ℝ × ℝ → ℂ) : Prop :=
  ∀ᵐ a ∂(volume.restrict I),
    (∀ c d, uIcc c d ⊆ J → AbsolutelyContinuousOnInterval (fun t ↦ G (a, t)) c d) ∧
    ∀ᵐ t ∂(volume.restrict J), HasDerivAt (fun t ↦ G (a, t)) (D (a, t)) t

/-- Local absolute continuity gives continuous sections on an arbitrary open set. -/
theorem HasACLSectionsOn.ae_continuousOn {I J : Set ℝ} {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I J G D) (hJ : IsOpen J) :
    ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun t ↦ G (a, t)) J := by
  filter_upwards [h] with a ha
  intro t ht
  obtain ⟨c, d, htc, hnhds, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have hcd : c ≤ d := htc.1.trans htc.2
  have hc := (ha.1 c d (by simpa only [uIcc_of_le hcd] using hsub)).continuousOn
  rw [uIcc_of_le hcd] at hc
  exact (hc.continuousAt hnhds).continuousWithinAt

/-- Equality a.e. on a product and continuity on almost every section imply equality
on almost every *whole* section. No derivative or measurability assumption on the raw
functions is needed. -/
theorem ae_eqOn_sections_of_ae_eq {I J : Set ℝ} (hJ : IsOpen J)
    {G H : ℝ × ℝ → ℂ} (heq : G =ᵐ[volume.restrict (I ×ˢ J)] H)
    (hG : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun t ↦ G (a, t)) J)
    (hH : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun t ↦ H (a, t)) J) :
    ∀ᵐ a ∂(volume.restrict I), ∀ t ∈ J, G (a, t) = H (a, t) := by
  have hp : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict J)), G p = H p := by
    simpa only [Filter.EventuallyEq, Measure.prod_restrict, Measure.volume_eq_prod] using heq
  filter_upwards [Measure.ae_ae_of_ae_prod hp, hG, hH] with a ha hc hd
  exact Measure.eqOn_open_of_ae_eq ha hJ hc hd

/-- Directional ACL representatives are unique on almost every entire section,
including any prescribed interior trace point. -/
theorem HasACLSectionsOn.ae_eqOn {I J : Set ℝ} (hJ : IsOpen J)
    {F G H D E : ℝ × ℝ → ℂ}
    (hG : HasACLSectionsOn I J G D) (hH : HasACLSectionsOn I J H E)
    (hGF : G =ᵐ[volume.restrict (I ×ˢ J)] F)
    (hHF : H =ᵐ[volume.restrict (I ×ˢ J)] F) :
    ∀ᵐ a ∂(volume.restrict I), ∀ t ∈ J, G (a, t) = H (a, t) :=
  ae_eqOn_sections_of_ae_eq hJ (hGF.trans hHF.symm)
    (hG.ae_continuousOn hJ) (hH.ae_continuousOn hJ)

namespace ACLSlicing

/-- A separable family of closed conditions has one common exceptional null set.
For slicing, apply this to smooth time tests supported in a fixed compact interval,
with the topology induced by the pair `(β, β')` of continuous functions there. -/
theorem ae_forall_of_isClosed {A T : Type*} [MeasurableSpace A] {μ : Measure A}
    [TopologicalSpace T] [SeparableSpace T] {P : A → T → Prop}
    (hclosed : ∀ᵐ a ∂μ, IsClosed {t | P a t})
    (h : ∀ t, ∀ᵐ a ∂μ, P a t) :
    ∀ᵐ a ∂μ, ∀ t, P a t := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense T
  have hall : ∀ᵐ a ∂μ, ∀ t ∈ s, P a t := (ae_ball_iff hs).2 fun t _ ↦ h t
  filter_upwards [hclosed, hall] with a hc ha
  have hsub : closure s ⊆ {t | P a t} := closure_minimal ha hc
  intro t
  exact hsub (hd.closure_eq ▸ mem_univ t)

/-- The real one-dimensional weak FTC on a bounded interval. The representative
extends absolutely continuously to the endpoints when the data are integrable on the
whole interval. For locally integrable sections this is applied on compact windows;
complex sections are handled by their real and imaginary parts. -/
theorem exists_ac_rep_Ioo {a b : ℝ} (hab : a < b) {F D : ℝ → ℝ}
    (hF : IntegrableOn F (Ioo a b)) (hD : IntegrableOn D (Ioo a b))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t, φ t * D t = -(∫ t, deriv φ t * F t)) :
    ∃ G : ℝ → ℝ, G =ᵐ[volume.restrict (Ioo a b)] F ∧
      AbsolutelyContinuousOnInterval G a b ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), HasDerivAt G (D t) t := by
  have hFi : IntegrableOn F (Icc a b) := by rwa [integrableOn_Icc_iff_integrableOn_Ioo]
  have hDi : IntegrableOn D (Icc a b) := by rwa [integrableOn_Icc_iff_integrableOn_Ioo]
  obtain ⟨N, hN, hFTC⟩ := exists_null_sub_eq_intervalIntegral
    (m := fun t ↦ -D t) (G := F) (α := a) (β := b)
    (fun c d hc hd ↦ hDi.neg.mono_set (Icc_subset_Icc hc.le hd.le))
    (fun c d hc hd ↦ hFi.mono_set (Icc_subset_Icc hc.le hd.le)) (by
      intro φ hφ c d hc hd hs
      have ht : tsupport φ ⊆ Icc c d :=
        closure_minimal (fun t ht ↦ hs t ht) isClosed_Icc
      have hw := hweak φ hφ (isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) ht)
        (ht.trans (Icc_subset_Ioo hc hd))
      simpa only [mul_neg, integral_neg, neg_neg] using congrArg Neg.neg hw)
  have hnotN : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ N := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hN
  obtain ⟨c, hc, hcN⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by simp [Real.volume_Ioo, hab])
    (ae_restrict_of_ae hnotN)
  let G : ℝ → ℝ := fun t ↦ F c + ∫ s in c..t, D s
  have hDc : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 hDi
  have hc' : c ∈ uIcc a b := by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hc
  refine ⟨G, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hnotN, ae_restrict_mem measurableSet_Ioo] with t htN ht
    change F c + (∫ s in c..t, D s) = F t
    rcases lt_trichotomy c t with hct | rfl | htc
    · have hh := hFTC c t hc.1 hct ht.2 hcN htN
      rw [intervalIntegral.integral_neg] at hh
      linarith
    · simp
    · have hh := hFTC t c ht.1 htc hc.2 htN hcN
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm] at hh
      linarith
  · exact (LipschitzWith.const (F c)).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (hDc.absolutelyContinuousOnInterval_intervalIntegral hc')
  · filter_upwards [ae_restrict_of_ae hDc.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    exact (ht (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self htI)
      c hc').const_add (F c)

/-- A fixed time test satisfies the sliced weak identity almost everywhere in the
transverse variable. This is Fubini followed by the fundamental lemma, not an
intersection over an uncountable family of tests. -/
theorem ae_sliced_test {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U 1 F D) {a b c d : ℝ}
    (hrect : Icc a b ×ˢ Icc c d ⊆ U) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hβJ : tsupport β ⊆ Ioo c d) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      (∫ t in Icc c d, F (x, t) * ((deriv β t : ℝ) : ℂ)) =
        -(∫ t in Icc c d, D (x, t) * (β t : ℂ)) := by
  let K := Icc a b ×ˢ Icc c d
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hF := hd.1.integrableOn_compact_subset hrect hK
  have hD := hd.2.1.integrableOn_compact_subset hrect hK
  let R : ℝ × ℝ → ℂ := fun p ↦
    F p * ((deriv β p.2 : ℝ) : ℂ) + D p * (β p.2 : ℂ)
  have hdc : Continuous (deriv β) := hβ.continuous_deriv (by simp)
  have hbc : Continuous (fun t ↦ (β t : ℂ)) := Complex.continuous_ofReal.comp hβ.continuous
  have hdcc : Continuous (fun t ↦ ((deriv β t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hdc
  have hRi : IntegrableOn R K :=
    (hF.mul_continuousOn (hdcc.comp continuous_snd).continuousOn hK).add
      (hD.mul_continuousOn (hbc.comp continuous_snd).continuousOn hK)
  have hRip : Integrable R ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, K, Measure.prod_restrict, ← Measure.volume_eq_prod] using hRi
  let r : ℝ → ℂ := fun x ↦ ∫ t in Icc c d, R (x, t)
  have hri : IntegrableOn r (Icc a b) := hRip.integral_prod_left
  have hr0 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hri.locallyIntegrableOn.mono_set Ioo_subset_Icc_self) (by
      intro α hα hαs hαI
      let φ : ℝ × ℝ → ℂ := fun p ↦ (α p.1 : ℂ) * (β p.2 : ℂ)
      have hts : tsupport φ ⊆ tsupport α ×ˢ tsupport β := by
        apply closure_minimal _ ((isClosed_tsupport α).prod (isClosed_tsupport β))
        intro p hp
        have hne : α p.1 ≠ 0 ∧ β p.2 ≠ 0 := by
          simpa only [φ, Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
            not_or] using hp
        exact ⟨subset_tsupport α hne.1, subset_tsupport β hne.2⟩
      have hφ : IsTestFunctionOn U φ :=
        ⟨(Complex.ofRealCLM.contDiff.comp (hα.comp contDiff_fst)).mul
            (Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_snd)),
          (hαs.isCompact.prod hβs.isCompact).of_isClosed_subset (isClosed_tsupport φ) hts,
          hts.trans ((Set.prod_mono (hαI.trans Ioo_subset_Icc_self)
            (hβJ.trans Ioo_subset_Icc_self)).trans hrect)⟩
      have he : coordPartial 1 φ = fun p ↦ (α p.1 : ℂ) * ((deriv β p.2 : ℝ) : ℂ) := by
        funext p
        simp only [coordPartial, show (1 : Fin 2) ≠ 0 by decide, ite_false, partialY, φ]
        exact (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt p.2
          ((hβ.differentiable (by simp) p.2).hasDerivAt)).const_mul (α p.1 : ℂ))).deriv
      have hw := hd.2.2 φ hφ
      rw [he] at hw
      have hiF := integrable_mul_of_tsupport_subset hd.1
        (hφ.continuous_coordPartial 1) (hφ.hasCompactSupport_coordPartial 1)
        ((tsupport_coordPartial_subset 1 φ).trans hφ.tsupport_subset)
      have hiD := integrable_mul_of_tsupport_subset hd.2.1 hφ.contDiff.continuous
        hφ.hasCompactSupport hφ.tsupport_subset
      rw [he] at hiF
      have hi : Integrable (fun p ↦ (α p.1 : ℂ) * R p) := by
        convert hiF.add hiD using 1
        ext p
        dsimp [R, φ]
        ring
      have hs : ∫ p, (α p.1 : ℂ) * R p = 0 := by
        have hh : (fun p ↦ (α p.1 : ℂ) * R p) =
            (fun p ↦ F p * ((α p.1 : ℂ) * ((deriv β p.2 : ℝ) : ℂ))) +
            (fun p ↦ D p * φ p) := by ext p; dsimp [R, φ]; ring
        rw [hh]
        change (∫ p, F p * ((α p.1 : ℂ) * ((deriv β p.2 : ℝ) : ℂ)) + D p * φ p) = 0
        rw [integral_add hiF hiD, hw, neg_add_cancel]
      have hz : ∀ p ∉ K, (α p.1 : ℂ) * R p = 0 := by
        intro p hp
        by_cases hx : p.1 ∈ Icc a b
        · have hy : p.2 ∉ tsupport β := fun h ↦ hp ⟨hx, Ioo_subset_Icc_self (hβJ h)⟩
          simp [R, image_eq_zero_of_notMem_tsupport hy, deriv_of_notMem_tsupport hy]
        · have hx' : p.1 ∉ tsupport α := fun h ↦ hx (Ioo_subset_Icc_self (hαI h))
          simp [image_eq_zero_of_notMem_tsupport hx']
      have hbase : ∫ x, α x • r x = ∫ x in Icc a b, (α x : ℂ) * r x := by
        simp only [Complex.real_smul]
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hx' : x ∉ tsupport α := fun h ↦ hx (Ioo_subset_Icc_self (hαI h))
        simp [image_eq_zero_of_notMem_tsupport hx']
      rw [hbase]
      have hip : Integrable (fun p ↦ (α p.1 : ℂ) * R p)
          ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
        simpa only [IntegrableOn, K, Measure.prod_restrict, ← Measure.volume_eq_prod] using
          (hi.integrableOn : IntegrableOn (fun p ↦ (α p.1 : ℂ) * R p) K)
      have heq : (∫ x in Icc a b, (α x : ℂ) * r x) = ∫ p in K, (α p.1 : ℂ) * R p := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hip]
        simp only [r, integral_const_mul]
      rw [heq, setIntegral_eq_integral_of_forall_compl_eq_zero hz, hs])
  have hFp : Integrable F ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hF
  have hDp : Integrable D ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hD
  have hr0' : ∀ᵐ x ∂(volume.restrict (Ioo a b)), r x = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).2 hr0
  filter_upwards [hr0', ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hFp.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hDp.prod_right_ae] with x hx hxF hxD
  have hxFi : IntegrableOn (fun t ↦ F (x, t)) (Icc c d) := hxF
  have hxDi : IntegrableOn (fun t ↦ D (x, t)) (Icc c d) := hxD
  have iF := hxFi.mul_continuousOn hdcc.continuousOn isCompact_Icc
  have iD := hxDi.mul_continuousOn hbc.continuousOn isCompact_Icc
  change (∫ t in Icc c d, F (x, t) * ((deriv β t : ℝ) : ℂ) +
    D (x, t) * (β t : ℂ)) = 0 at hx
  rw [integral_add iF iD] at hx
  exact eq_neg_iff_add_eq_zero.2 hx

/-- Extend a continuous compact-window test by zero. Only its values on the window
are used, so no endpoint matching is required. -/
def windowExtend {c d : ℝ} (g : C(Icc c d, ℝ)) (t : ℝ) : ℝ :=
  if ht : t ∈ Icc c d then g ⟨t, ht⟩ else 0

private theorem continuousOn_windowExtend {c d : ℝ} (g : C(Icc c d, ℝ)) :
    ContinuousOn (windowExtend g) (Icc c d) := by
  apply continuousOn_iff_continuous_domRestrict.2
  have he : (Icc c d).domRestrict (windowExtend g) = g := by
    funext t
    simp [windowExtend, Set.domRestrict]
  rw [he]
  exact g.continuous

/-- Integration against locally integrable data is continuous in the uniform norm
on a fixed compact window. This makes the sliced weak identity a closed condition
in the topology of test values and first derivatives. -/
theorem continuous_windowPairing {c d : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc c d)) :
    Continuous (fun g : C(Icc c d, ℝ) ↦ ∫ t in Icc c d, f t * (windowExtend g t : ℂ)) := by
  have hi (g : C(Icc c d, ℝ)) : IntegrableOn
      (fun t ↦ f t * (windowExtend g t : ℂ)) (Icc c d) :=
    hf.mul_continuousOn (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_windowExtend g)) isCompact_Icc
  rw [continuous_iff_continuousAt]
  intro g
  have hn : ∀ᶠ g' : C(Icc c d, ℝ) in 𝓝 g, ‖g'‖ < ‖g‖ + 1 :=
    (continuous_norm : Continuous (fun g' : C(Icc c d, ℝ) ↦ ‖g'‖)).continuousAt.eventually
      (gt_mem_nhds (lt_add_one ‖g‖))
  apply continuousAt_of_dominated (bound := fun t ↦ ‖f t‖ * (‖g‖ + 1))
  · exact Eventually.of_forall fun g' ↦ (hi g').aestronglyMeasurable
  · filter_upwards [hn] with g' hg'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [norm_mul, Complex.norm_real, windowExtend, dite_eq_left ht]
    exact mul_le_mul_of_nonneg_left ((g'.norm_coe_le_norm ⟨t, ht⟩).trans hg'.le)
      (norm_nonneg _)
  · exact hf.norm.mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : (fun g' : C(Icc c d, ℝ) ↦ f t * (windowExtend g' t : ℂ)) =
        (fun g' : C(Icc c d, ℝ) ↦ f t * (g' ⟨t, ht⟩ : ℂ)) := by
      funext g'; simp only [windowExtend, dite_eq_left ht]
    rw [he]
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_eval_const (⟨t, ht⟩ : Icc c d)))).continuousAt

/-- One common exceptional set works for *all* time tests on a compact rectangle.
The test topology is induced by `(β, β')` in two spaces of continuous functions;
it is second countable, without a smooth approximation theorem. -/
theorem ae_all_sliced_tests {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U 1 F D) {a b c d : ℝ}
    (hrect : Icc a b ×ˢ Icc c d ⊆ U) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioo c d →
      (∫ t in Icc c d, F (x, t) * ((deriv β t : ℝ) : ℂ)) =
        -(∫ t in Icc c d, D (x, t) * (β t : ℂ)) := by
  let T := {β : ℝ → ℝ // ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ Ioo c d}
  let jet : T → C(Icc c d, ℝ) × C(Icc c d, ℝ) := fun β ↦
    (⟨fun t ↦ β.1 t, β.2.1.continuous.comp continuous_subtype_val⟩,
      ⟨fun t ↦ deriv β.1 t, (β.2.1.continuous_deriv (by simp)).comp continuous_subtype_val⟩)
  let : TopologicalSpace T := TopologicalSpace.induced jet inferInstance
  let : SecondCountableTopology T := secondCountableTopology_induced _ _ _
  have hj : Continuous jet := continuous_induced_dom
  let P : ℝ → T → Prop := fun x β ↦
    (∫ t in Icc c d, F (x, t) * ((deriv β.1 t : ℝ) : ℂ)) =
      -(∫ t in Icc c d, D (x, t) * (β.1 t : ℂ))
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hiF : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (hd.1.integrableOn_compact_subset hrect hK : IntegrableOn F (Icc a b ×ˢ Icc c d))
  have hiD : Integrable D ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (hd.2.1.integrableOn_compact_subset hrect hK : IntegrableOn D (Icc a b ×ˢ Icc c d))
  have hc : ∀ᵐ x ∂(volume.restrict (Ioo a b)), IsClosed {β | P x β} := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hiF.prod_right_ae,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hiD.prod_right_ae] with x hxF hxD
    have hF := (continuous_windowPairing hxF).comp hj.snd
    have hD := ((continuous_windowPairing hxD).comp hj.fst).neg
    have eF : (fun β : T ↦ ∫ t in Icc c d, F (x, t) * ((deriv β.1 t : ℝ) : ℂ)) =
        (fun g ↦ ∫ t in Icc c d, F (x, t) * (windowExtend g t : ℂ)) ∘ (fun β ↦ (jet β).2) := by
      funext β
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp [windowExtend, ht, jet]
    have eD : (fun β : T ↦ -(∫ t in Icc c d, D (x, t) * (β.1 t : ℂ))) =
        -(fun g ↦ ∫ t in Icc c d, D (x, t) * (windowExtend g t : ℂ)) ∘ (fun β ↦ (jet β).1) := by
      funext β
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp [windowExtend, ht, jet]
    exact isClosed_eq (eF ▸ hF) (eD ▸ hD)
  have hall : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ β, P x β :=
    ae_forall_of_isClosed hc fun β ↦ ae_sliced_test hd hrect β.2.1 β.2.2.1 β.2.2.2
  filter_upwards [hall] with x hx β hβ hβs hβJ
  exact hx ⟨β, hβ, hβs, hβJ⟩

/-- Complex weak FTC on a compact window, with real scalar tests. -/
theorem exists_ac_rep_Icc_complex {c d : ℝ} (hcd : c < d) {F D : ℝ → ℂ}
    (hF : IntegrableOn F (Icc c d)) (hD : IntegrableOn D (Icc c d))
    (hw : ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioo c d →
      (∫ t in Icc c d, F t * ((deriv β t : ℝ) : ℂ)) =
        -(∫ t in Icc c d, D t * (β t : ℂ))) :
    ∃ G : ℝ → ℂ, G =ᵐ[volume.restrict (Ioo c d)] F ∧
      AbsolutelyContinuousOnInterval G c d ∧
      ∀ᵐ t ∂(volume.restrict (Ioo c d)), HasDerivAt G (D t) t := by
  have hreal (L : ℂ →L[ℝ] ℝ) : ∃ G : ℝ → ℝ,
      G =ᵐ[volume.restrict (Ioo c d)] (fun t ↦ L (F t)) ∧
      AbsolutelyContinuousOnInterval G c d ∧
      ∀ᵐ t ∂(volume.restrict (Ioo c d)), HasDerivAt G (L (D t)) t := by
    have hFr : IntegrableOn (fun t ↦ L (F t)) (Icc c d) := L.integrable_comp hF
    have hDr : IntegrableOn (fun t ↦ L (D t)) (Icc c d) := L.integrable_comp hD
    apply exists_ac_rep_Ioo hcd
      (hFr.mono_set Ioo_subset_Icc_self) (hDr.mono_set Ioo_subset_Icc_self)
    intro β hβ hβs hβJ
    have hdb : Continuous (deriv β) := hβ.continuous_deriv (by simp)
    have iF := hF.mul_continuousOn
      (Complex.continuous_ofReal.comp hdb).continuousOn isCompact_Icc
    have iD := hD.mul_continuousOn
      (Complex.continuous_ofReal.comp hβ.continuous).continuousOn isCompact_Icc
    simp only [Function.comp_apply] at iF iD
    have hh := congrArg L (hw β hβ hβs hβJ)
    rw [map_neg, ← L.integral_comp_comm iF, ← L.integral_comp_comm iD] at hh
    have hm (z : ℂ) (r : ℝ) : L (z * (r : ℂ)) = r * L z := by
      rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul]
    simp_rw [hm] at hh
    have eD : (∫ t, β t * L (D t)) = ∫ t in Icc c d, β t * L (D t) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have ht' : t ∉ tsupport β := fun h ↦ ht (Ioo_subset_Icc_self (hβJ h))
      simp [image_eq_zero_of_notMem_tsupport ht']
    have eF : (∫ t, deriv β t * L (F t)) = ∫ t in Icc c d, deriv β t * L (F t) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have ht' : t ∉ tsupport β := fun h ↦ ht (Ioo_subset_Icc_self (hβJ h))
      simp [deriv_of_notMem_tsupport ht']
    rw [eD, eF]
    linarith
  obtain ⟨R, hRF, hR, hRD⟩ := hreal Complex.reCLM
  obtain ⟨S, hSF, hS, hSD⟩ := hreal Complex.imCLM
  let G : ℝ → ℂ := fun t ↦ (R t : ℂ) + Complex.I * (S t : ℂ)
  refine ⟨G, ?_, ?_, ?_⟩
  · filter_upwards [hRF, hSF] with t htR htS
    dsimp [G]
    rw [htR, htS]
    simpa [mul_comm] using Complex.re_add_im (F t)
  · exact (Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hR).add
      ((Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hS).const_smul
        Complex.I)
  · filter_upwards [hRD, hSD] with t htR htS
    have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t htR
    have hs := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t htS).const_mul Complex.I
    convert hr.add hs using 1
    · rfl
    · simpa [mul_comm] using (Complex.re_add_im (D t)).symm

/-- The interval primitive of a jointly measurable function is jointly measurable,
even on sections on which the defining integral is not integrable (the Bochner integral
is total). -/
theorem measurable_sectionPrimitive {D : ℝ × ℝ → ℂ} (hD : Measurable D) (c : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ ∫ s in c..p.2, D (p.1, s)) := by
  let f : (ℝ × ℝ) × ℝ → ℂ := fun q ↦
    if c < q.2 ∧ q.2 ≤ q.1.2 then D (q.1.1, q.2) else 0
  let g : (ℝ × ℝ) × ℝ → ℂ := fun q ↦
    if q.1.2 < q.2 ∧ q.2 ≤ c then D (q.1.1, q.2) else 0
  have hf : Measurable f := by
    apply Measurable.ite (by measurability) (hD.comp (by fun_prop)) measurable_const
  have hg : Measurable g := by
    apply Measurable.ite (by measurability) (hD.comp (by fun_prop)) measurable_const
  have hfm := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hgm := (hg.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  convert hfm.sub hgm using 1
  funext p
  rw [intervalIntegral]
  congr 1 <;> rw [← integral_indicator measurableSet_Ioc] <;>
    simp only [f, g, Set.indicator, mem_Ioc]

/-- A canonical representative: primitive in the time variable, with the additive
constant chosen by averaging on a fixed nondegenerate window. -/
def windowRepresentative (c d : ℝ) (F D : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((d - c : ℝ) : ℂ)⁻¹ *
    (∫ s in Icc c d, F (p.1, s) - ∫ t in c..s, D (p.1, t)) +
    ∫ t in c..p.2, D (p.1, t)

theorem measurable_windowRepresentative {F D : ℝ × ℝ → ℂ}
    (hF : Measurable F) (hD : Measurable D) (c d : ℝ) :
    Measurable (windowRepresentative c d F D) := by
  have hA := measurable_sectionPrimitive hD c
  have hC := ((hF.sub hA).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc c d))).measurable
  exact (measurable_const.mul (hC.comp measurable_fst)).add hA

/-- On every good section the primitive-and-average formula agrees everywhere
with any AC representative, even on a larger window than the averaging interval. -/
theorem windowRepresentative_eq {c d e f x : ℝ} {F D : ℝ × ℝ → ℂ} {H : ℝ → ℂ}
    (hcd : c < d) (hc : c ∈ Icc e f) (hd : d ∈ Icc e f)
    (hD : IntegrableOn (fun t ↦ D (x, t)) (Icc e f))
    (hH : AbsolutelyContinuousOnInterval H e f)
    (hHF : H =ᵐ[volume.restrict (Ioo e f)] (fun t ↦ F (x, t)))
    (hHD : ∀ᵐ t ∂(volume.restrict (Ioo e f)), HasDerivAt H (D (x, t)) t) :
    EqOn (fun t ↦ windowRepresentative c d F D (x, t)) H (Icc e f) := by
  have hef : e ≤ f := hc.1.trans hc.2
  have hder : ∀ᵐ t, t ∈ Icc e f → HasDerivAt H (D (x, t)) t := by
    apply (ae_restrict_iff' measurableSet_Icc).1
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hFTC (t : ℝ) (ht : t ∈ Icc e f) :
      (∫ s in c..t, D (x, s)) = H t - H c := by
    have hsub : uIcc c t ⊆ Icc e f := uIcc_subset_Icc hc ht
    apply complex_integral_eq_sub_of_ac
      (hH.mono (by simpa only [uIcc_of_le hef] using hsub))
      ((hD.mono_set hsub).intervalIntegrable)
    filter_upwards [hder] with s hs hsI
    exact hs (hsub hsI)
  have hHF' : H =ᵐ[volume.restrict (Icc e f)] (fun t ↦ F (x, t)) := by
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hsub : Icc c d ⊆ Icc e f := Icc_subset_Icc hc.1 hd.2
  have havg : (∫ s in Icc c d, F (x, s) - ∫ t in c..s, D (x, t)) =
      ((d - c : ℝ) : ℂ) * H c := by
    calc
      _ = ∫ s in Icc c d, H c := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hHF',
          ae_restrict_mem measurableSet_Icc] with s hs hsI
        rw [← hs, hFTC s (hsub hsI)]
        abel
      _ = _ := by
        simp [hcd.le, Complex.real_smul]
  intro t ht
  change ((d - c : ℝ) : ℂ)⁻¹ * _ + _ = H t
  rw [havg, hFTC t ht, inv_mul_cancel_left₀ (by exact_mod_cast sub_ne_zero.mpr hcd.ne')]
  abel

/-- Every compact subset of an open interval lies strictly inside a rational
compact window contained in that interval. -/
theorem exists_rat_window {J K : Set ℝ} (hJ : IsOpen J) (hJc : OrdConnected J)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKJ : K ⊆ J) :
    ∃ c d : ℚ, (c : ℝ) < d ∧ Icc (c : ℝ) d ⊆ J ∧ K ⊆ Ioo (c : ℝ) d := by
  have hlJ := hKJ (hK.sInf_mem hKn)
  have hrJ := hKJ (hK.sSup_mem hKn)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hJ.mem_nhds hlJ)
  obtain ⟨l', r', ⟨hl', hr'⟩, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hJ.mem_nhds hrJ)
  obtain ⟨c, hc₁, hc₂⟩ := exists_rat_btwn hl
  obtain ⟨d, hd₁, hd₂⟩ := exists_rat_btwn hr'
  have hcJ : (c : ℝ) ∈ J := hsub ⟨hc₁, hc₂.trans hr⟩
  have hdJ : (d : ℝ) ∈ J := hsub' ⟨hl'.trans hd₁, hd₂⟩
  have hcd : (c : ℝ) < d := hc₂.trans_le (csInf_le_csSup hKn hK.bddBelow hK.bddAbove) |>.trans hd₁
  refine ⟨c, d, hcd, ?_, ?_⟩
  · simpa only [uIcc_of_le hcd.le] using hJc.uIcc_subset hcJ hdJ
  · intro t ht
    exact ⟨hc₂.trans_le (csInf_le hK.bddBelow ht), (le_csSup hK.bddAbove ht).trans_lt hd₁⟩

/-- The data needed for constructing a representative are available simultaneously
on almost every section of a compact rectangle. -/
theorem ae_ac_rep_on_rectangle {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U 1 F D) {a b c d : ℝ} (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ U) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      IntegrableOn (fun t ↦ D (x, t)) (Icc c d) ∧ ∃ H : ℝ → ℂ,
      H =ᵐ[volume.restrict (Ioo c d)] (fun t ↦ F (x, t)) ∧
      AbsolutelyContinuousOnInterval H c d ∧
      ∀ᵐ t ∂(volume.restrict (Ioo c d)), HasDerivAt H (D (x, t)) t := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hiF : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (hd.1.integrableOn_compact_subset hrect hK)
  have hiD : Integrable D ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (hd.2.1.integrableOn_compact_subset hrect hK)
  filter_upwards [ae_all_sliced_tests hd hrect,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hiF.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hiD.prod_right_ae] with x hx hxF hxD
  exact ⟨hxD, exists_ac_rep_Icc_complex hcd hxF hxD hx⟩

/-- Construction for jointly measurable data. Rational compact rectangles give
one common exceptional set; the averaging window is fixed before choosing a section. -/
theorem exists_acl_sections_measurable {I J : Set ℝ} {F D : ℝ × ℝ → ℂ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hJ : IsOpen J) (hJc : OrdConnected J)
    (hJn : J.Nonempty) (hd : HasWeakPartialOn (I ×ˢ J) 1 F D)
    (hFm : Measurable F) (hDm : Measurable D) :
    ∃ G : ℝ × ℝ → ℂ, Measurable G ∧
      G =ᵐ[volume.restrict (I ×ˢ J)] F ∧ HasACLSectionsOn I J G D := by
  obtain ⟨t₀, ht₀⟩ := hJn
  obtain ⟨c₀, d₀, h₀, h₀J, -⟩ := exists_rat_window hJ hJc
    isCompact_singleton (singleton_nonempty t₀) (singleton_subset_iff.2 ht₀)
  let G := windowRepresentative c₀ d₀ F D
  have hGm : Measurable G := measurable_windowRepresentative hFm hDm c₀ d₀
  have hc₀ : (c₀ : ℝ) ∈ J := h₀J ⟨le_rfl, h₀.le⟩
  have hd₀ : (d₀ : ℝ) ∈ J := h₀J ⟨h₀.le, le_rfl⟩
  let Q (x : ℝ) (c d : ℚ) : Prop :=
    IntegrableOn (fun t ↦ D (x, t)) (Icc (c : ℝ) d) ∧ ∃ H : ℝ → ℂ,
      H =ᵐ[volume.restrict (Ioo (c : ℝ) d)] (fun t ↦ F (x, t)) ∧
      AbsolutelyContinuousOnInterval H c d ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (c : ℝ) d)), HasDerivAt H (D (x, t)) t
  have hrat : ∀ᵐ x ∂(volume : Measure ℝ), ∀ a b c d : ℚ,
      (c : ℝ) < d → Icc (a : ℝ) b ×ˢ Icc (c : ℝ) d ⊆ I ×ˢ J →
      x ∈ Ioo (a : ℝ) b → Q x c d := by
    refine ae_all_iff.2 fun a ↦ ae_all_iff.2 fun b ↦
      ae_all_iff.2 fun c ↦ ae_all_iff.2 fun d ↦ ?_
    by_cases hcd : (c : ℝ) < d
    · by_cases hrect : Icc (a : ℝ) b ×ˢ Icc (c : ℝ) d ⊆ I ×ˢ J
      · have hh := (ae_restrict_iff' measurableSet_Ioo).1
          (ae_ac_rep_on_rectangle hd hcd hrect)
        filter_upwards [hh] with x hx _ _ hxI
        exact hx hxI
      · exact Eventually.of_forall fun _ _ h ↦ (hrect h).elim
    · exact Eventually.of_forall fun _ h ↦ (hcd h).elim
  have hsections : ∀ᵐ x ∂(volume.restrict I),
      (∀ u v, uIcc u v ⊆ J → AbsolutelyContinuousOnInterval (fun t ↦ G (x, t)) u v) ∧
      ∀ᵐ t ∂(volume.restrict J), G (x, t) = F (x, t) ∧
        HasDerivAt (fun s ↦ G (x, s)) (D (x, t)) t := by
    filter_upwards [ae_restrict_of_ae hrat, ae_restrict_mem hI.measurableSet] with x hx hxI
    obtain ⟨a, b, hab, habI, hxAB⟩ := exists_rat_window hI hIc
      isCompact_singleton (singleton_nonempty x) (singleton_subset_iff.2 hxI)
    have hxAB' : x ∈ Ioo (a : ℝ) b := hxAB (mem_singleton x)
    have get (c d : ℚ) (hcd : (c : ℝ) < d) (hcdJ : Icc (c : ℝ) d ⊆ J)
        (hc : (c₀ : ℝ) ∈ Icc (c : ℝ) d) (hd' : (d₀ : ℝ) ∈ Icc (c : ℝ) d) :
        ∃ H : ℝ → ℂ, EqOn (fun t ↦ G (x, t)) H (Icc (c : ℝ) d) ∧
          H =ᵐ[volume.restrict (Ioo (c : ℝ) d)] (fun t ↦ F (x, t)) ∧
          AbsolutelyContinuousOnInterval H c d ∧
          ∀ᵐ t ∂(volume.restrict (Ioo (c : ℝ) d)), HasDerivAt H (D (x, t)) t := by
      obtain ⟨hiD, H, hHF, hH, hHD⟩ := hx a b c d hcd (Set.prod_mono habI hcdJ) hxAB'
      exact ⟨H, windowRepresentative_eq h₀ hc hd' hiD hH hHF hHD, hHF, hH, hHD⟩
    constructor
    · intro u v huvJ
      let K : Set ℝ := {↑c₀, ↑d₀, u, v}
      have hKJ : K ⊆ J := by
        simp only [K, insert_subset_iff, singleton_subset_iff]
        exact ⟨hc₀, hd₀, huvJ left_mem_uIcc, huvJ right_mem_uIcc⟩
      obtain ⟨c, d, hcd, hcdJ, hKcd⟩ := exists_rat_window (K := K) hJ hJc
        (by exact (((isCompact_singleton : IsCompact ({v} : Set ℝ)).insert u).insert
          (d₀ : ℝ)).insert (c₀ : ℝ)) ⟨c₀, by simp [K]⟩ hKJ
      have hc := Ioo_subset_Icc_self (hKcd (show (c₀ : ℝ) ∈ K by simp [K]))
      have hd' := Ioo_subset_Icc_self (hKcd (show (d₀ : ℝ) ∈ K by simp [K]))
      obtain ⟨H, heq, _, hH, _⟩ := get c d hcd hcdJ hc hd'
      have hsub : uIcc u v ⊆ Icc (c : ℝ) d := uIcc_subset_Icc
        (Ioo_subset_Icc_self (hKcd (show u ∈ K by simp [K])))
        (Ioo_subset_Icc_self (hKcd (show v ∈ K by simp [K])))
      exact (hH.mono (by simpa only [uIcc_of_le hcd.le] using hsub)).congr
        (fun t ht ↦ (heq (hsub ht)).symm)
    · let P (t : ℝ) := G (x, t) = F (x, t) ∧ HasDerivAt (fun s ↦ G (x, s)) (D (x, t)) t
      have hlocal (c d : ℚ) : ∀ᵐ t ∂(volume : Measure ℝ),
          ((c : ℝ) < d ∧ Icc (c : ℝ) d ⊆ J ∧
            (c₀ : ℝ) ∈ Icc (c : ℝ) d ∧ (d₀ : ℝ) ∈ Icc (c : ℝ) d) →
          t ∈ Ioo (c : ℝ) d → P t := by
        by_cases hcond : (c : ℝ) < d ∧ Icc (c : ℝ) d ⊆ J ∧
            (c₀ : ℝ) ∈ Icc (c : ℝ) d ∧ (d₀ : ℝ) ∈ Icc (c : ℝ) d
        · obtain ⟨H, heq, hHF, _, hHD⟩ := get c d hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          simp only [hcond, true_and, true_implies]
          apply (ae_restrict_iff' measurableSet_Ioo).1
          filter_upwards [hHF, hHD, ae_restrict_mem measurableSet_Ioo] with t htF htD ht
          refine ⟨(heq (Ioo_subset_Icc_self ht)).trans htF, htD.congr_of_eventuallyEq ?_⟩
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact heq (Ioo_subset_Icc_self hs)
        · exact Eventually.of_forall fun _ h ↦ (hcond h).elim
      have htall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ c d : ℚ,
          ((c : ℝ) < d ∧ Icc (c : ℝ) d ⊆ J ∧
            (c₀ : ℝ) ∈ Icc (c : ℝ) d ∧ (d₀ : ℝ) ∈ Icc (c : ℝ) d) →
          t ∈ Ioo (c : ℝ) d → P t :=
        ae_all_iff.2 fun c ↦ ae_all_iff.2 fun d ↦ hlocal c d
      filter_upwards [ae_restrict_of_ae htall, ae_restrict_mem hJ.measurableSet] with t ht htJ
      let K : Set ℝ := {↑c₀, ↑d₀, t}
      have hKJ : K ⊆ J := by
        simp only [K, insert_subset_iff, singleton_subset_iff]
        exact ⟨hc₀, hd₀, htJ⟩
      obtain ⟨c, d, hcd, hcdJ, hKcd⟩ := exists_rat_window (K := K) hJ hJc
        (by exact ((isCompact_singleton : IsCompact ({t} : Set ℝ)).insert
          (d₀ : ℝ)).insert (c₀ : ℝ))
        ⟨c₀, by simp [K]⟩ hKJ
      exact ht c d ⟨hcd, hcdJ,
        Ioo_subset_Icc_self (hKcd (show (c₀ : ℝ) ∈ K by simp [K])),
        Ioo_subset_Icc_self (hKcd (show (d₀ : ℝ) ∈ K by simp [K]))⟩
        (hKcd (show t ∈ K by simp [K]))
  refine ⟨G, hGm, ?_, ?_⟩
  · have hp : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict J)), G p = F p := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hGm hFm)).2
      filter_upwards [hsections] with x hx
      exact hx.2.mono fun t ht ↦ ht.1
    simpa only [Filter.EventuallyEq, Measure.prod_restrict, Measure.volume_eq_prod] using hp
  · filter_upwards [hsections] with x hx
    exact ⟨hx.1, hx.2.mono fun t ht ↦ ht.2⟩

end ACLSlicing

/-- Directional ACL slicing (`lem:acl-slicing`). Only the second weak partial
is assumed. The representative is jointly measurable, not just measurable sectionwise.
The intervals may be unbounded; all regularity and derivative conclusions are local
in the time variable. Uniqueness is `HasACLSectionsOn.ae_eqOn`. -/
theorem HasWeakPartialOn.exists_acl_sections {I J : Set ℝ} {F D : ℝ × ℝ → ℂ}
    (hI : IsOpen I) (hIc : OrdConnected I) (_hIn : I.Nonempty)
    (hJ : IsOpen J) (hJc : OrdConnected J) (hJn : J.Nonempty)
    (hd : HasWeakPartialOn (I ×ˢ J) 1 F D) :
    ∃ G : ℝ × ℝ → ℂ, Measurable G ∧
      G =ᵐ[volume.restrict (I ×ˢ J)] F ∧ HasACLSectionsOn I J G D := by
  have hU : MeasurableSet (I ×ˢ J) := hI.measurableSet.prod hJ.measurableSet
  have hFm := hd.1.aestronglyMeasurable
  have hDm := hd.2.1.aestronglyMeasurable
  let Fm := hFm.mk F
  let Dm := hDm.mk D
  have hFeq : F =ᵐ[volume.restrict (I ×ˢ J)] Fm := hFm.ae_eq_mk
  have hDeq : D =ᵐ[volume.restrict (I ×ˢ J)] Dm := hDm.ae_eq_mk
  have hm {f g : ℝ × ℝ → ℂ} (heq : f =ᵐ[volume.restrict (I ×ˢ J)] g)
      {φ : ℝ × ℝ → ℂ} (hφ : tsupport φ ⊆ I ×ˢ J) :
      (fun p ↦ g p * φ p) =ᵐ[volume] (fun p ↦ f p * φ p) := by
    filter_upwards [(ae_restrict_iff' hU).1 heq] with p hp
    by_cases hpU : p ∈ I ×ˢ J
    · rw [hp hpU]
    · have hpφ : p ∉ tsupport φ := fun h ↦ hpU (hφ h)
      simp [image_eq_zero_of_notMem_tsupport hpφ]
  have hdm : HasWeakPartialOn (I ×ˢ J) 1 Fm Dm := by
    refine ⟨hd.1.congr hFeq, hd.2.1.congr hDeq, fun φ hφ ↦ ?_⟩
    rw [integral_congr_ae (hm hFeq
      ((tsupport_coordPartial_subset 1 φ).trans hφ.tsupport_subset)),
      integral_congr_ae (hm hDeq hφ.tsupport_subset), hd.2.2 φ hφ]
  obtain ⟨G, hGm, hGF, hG⟩ := ACLSlicing.exists_acl_sections_measurable
    hI hIc hJ hJc hJn hdm hFm.stronglyMeasurable_mk.measurable
      hDm.stronglyMeasurable_mk.measurable
  refine ⟨G, hGm, hGF.trans hFeq.symm, ?_⟩
  have hDp : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict J)), D p = Dm p := by
    simpa only [Filter.EventuallyEq, Measure.prod_restrict, Measure.volume_eq_prod] using hDeq
  filter_upwards [hG, Measure.ae_ae_of_ae_prod hDp] with x hx hxeq
  refine ⟨hx.1, ?_⟩
  filter_upwards [hx.2, hxeq] with t ht hteq
  rwa [hteq]

end NoEmbeddedEigenvalues
