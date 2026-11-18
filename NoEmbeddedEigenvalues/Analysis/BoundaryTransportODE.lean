import NoEmbeddedEigenvalues.Analysis.BoundaryTraceContinuity
import NoEmbeddedEigenvalues.TraceWeakGluing
import NoEmbeddedEigenvalues.TraceH2
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Boundary weak equations for tangential transport

Blueprint: `lem:boundary-transport-ode`.

Tangential test pairings of the value and right-hand side converge strongly
at the normal endpoint. The remaining normal flux is the distance to the
boundary times an integrable pairing; it can have no nonzero endpoint limit.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem ae_horizontal_of_ae {P : ℝ × ℝ → Prop} {a b w : ℝ}
    (h : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)), P q) :
    ∀ᵐ u ∂(volume.restrict (Ioo 0 w)), ∀ᵐ s ∂(volume.restrict (Ioo a b)), P (s, u) := by
  have hs : Prod.swap ⁻¹' (Ioo a b ×ˢ Ioo 0 w) = Ioo 0 w ×ˢ Ioo a b := by
    ext q
    simp [and_comm]
  have h' := (Measure.measurePreserving_swap.restrict_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo)).quasiMeasurePreserving.ae h
  rw [hs, ← Measure.prod_restrict] at h'
  exact Measure.ae_ae_of_ae_prod (p := fun q ↦ P q.swap) h'

private theorem HasACLSectionsOn.ae_horizontal_trace_eq {a b w : ℝ}
    {G D F : ℝ × ℝ → ℂ} (hw : 0 < w) (h : HasACLSectionsOn (Ioo a b) (Ioo 0 w) G D)
    (hG : MemLp G 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (he : G =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)] F) :
    ∀ᵐ u ∂(volume.restrict (Ioo 0 w)), aclTrace 0 w G D u =ᵐ[volume.restrict (Ioo a b)]
      fun s ↦ F (s, u) := by
  have hprod : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)),
      aclTrace 0 w G D q.2 q.1 = G q := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (h.ae_trace_eq hw hG hD),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)] with q hq hu
    exact hq q.2 hu
  exact ae_horizontal_of_ae (hprod.mp (he.mono fun _ h₁ h₂ ↦ h₂.trans h₁))

private theorem HasWeakPartialOn.ae_horizontal_test {a b w : ℝ}
    {F A : ℝ × ℝ → ℂ} (hab : a < b) (hw : 0 < w)
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 0 F A)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hA : MemLp A 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 1 β) (hβa : β a = 0) (hβb : β b = 0) :
    ∀ᵐ u ∂(volume.restrict (Ioo 0 w)), (∫ s in Ioo a b, F (s, u) * deriv β s) =
      -(∫ s in Ioo a b, A (s, u) * β s) := by
  let Q := Ioo a b ×ˢ Ioo (0 : ℝ) w
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have he : Prod.swap ⁻¹' Q = Ioo 0 w ×ˢ Ioo a b := by ext p; simp [Q, and_comm]
  have hs := hd.comp_swap_fst hQ
  have hFs := memLp_comp_swap hQ.measurableSet hF
  have hAs := memLp_comp_swap hQ.measurableSet hA
  rw [he] at hs hFs hAs
  obtain ⟨G, _, hGF, hG⟩ := hs.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hw) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hab)
  have hGFp : G =ᵐ[(volume.restrict (Ioo 0 w)).prod (volume.restrict (Ioo a b))]
      (F ∘ Prod.swap) := by simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hGF
  filter_upwards [hG.ae_hasIntervalH1 (hFs.ae_eq hGF.symm) hAs,
    Measure.ae_ae_of_ae_prod hGFp] with u hu heu
  simpa only [hβa, hβb, mul_zero, sub_self, zero_sub, Function.comp_apply, Prod.swap_prod_mk] using
    calc
      (∫ s in Ioo a b, F (s, u) * deriv β s) = ∫ s in Ioo a b, G (u, s) * deriv β s :=
        integral_congr_ae (heu.mono fun s h ↦ congrArg (· * deriv β s) h.symm)
      _ = _ := hu.integral_mul_deriv hab hβ

/-- A vanishing normal coefficient can leave no nonzero residual in the
one-sided limit of the tangential equation. -/
private theorem eq_zero_of_tendsto_of_linear_bound {w : ℝ} (hw : 0 < w)
    {E : ℝ → ℂ} {M : ℝ → ℝ} {z : ℂ}
    (hE : Tendsto E (𝓝[Ioo 0 w] 0) (𝓝 z))
    (hM : IntegrableOn M (Ioo 0 w))
    (hb : ∀ᵐ u ∂(volume.restrict (Ioo 0 w)), ‖E u‖ ≤ u * M u) : z = 0 := by
  by_contra hz
  have hc : 0 < ‖z‖ / 2 := half_pos (norm_pos_iff.2 hz)
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.1
    (hE.norm.eventually (lt_mem_nhds (by linarith : ‖z‖ / 2 < ‖z‖)))
  let δ := min ε w
  have hδ : 0 < δ := lt_min hε hw
  have hsub : Ioo 0 δ ⊆ Ioo 0 w := Ioo_subset_Ioo_right (min_le_right _ _)
  have hi : IntegrableOn (fun u : ℝ ↦ u ^ (-1 : ℝ)) (Ioo 0 δ) := by
    apply ((hM.mono_set hsub).const_mul (‖z‖ / 2)⁻¹).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hb] with u hu hub
    have huε : u ∈ Metric.ball 0 ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hu.1] using
        (hu.2.trans_le (min_le_left ε w))
    have hul : ‖z‖ / 2 < ‖E u‖ := he ⟨huε, hsub hu⟩
    rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_inv, abs_of_pos hu.1]
    apply (le_inv_mul_iff₀ hc).2
    simpa only [div_eq_mul_inv] using
      (div_le_iff₀ hu.1).2 (hul.le.trans (by simpa only [mul_comm u] using hub))
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hi
  norm_num at this

/-- Trace pairings against a fixed L² test converge, including at the boundary. -/
theorem HasACLSectionsOn.tendsto_trace_pairing {I : Set ℝ} {a b t : ℝ}
    {G D : ℝ × ℝ → ℂ} (h : HasACLSectionsOn I (Ioo a b) G D)
    (hab : a < b) (ht : t ∈ Icc a b) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo a b)))
    {β : ℝ → ℂ} (hβ : MemLp β 2 (volume.restrict I)) :
    Tendsto (fun u ↦ ∫ s in I, aclTrace a b G D u s * β s)
      (𝓝[Icc a b] t) (𝓝 (∫ s in I, aclTrace a b G D t s * β s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsmall := ((h.tendsto_trace_sq hab ht hGm hG hD).sqrt).mul_const
    (Real.sqrt (∫ s in I, ‖β s‖ ^ 2))
  simp only [Real.sqrt_zero, zero_mul] at hsmall
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hsmall
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hU := (h.l2_trace hab hGm hG hD u hu).1
  have hT := (h.l2_trace hab hGm hG hD t ht).1
  have iU : Integrable (fun s ↦ aclTrace a b G D u s * β s) (volume.restrict I) :=
    hU.integrable_mul hβ
  have iT : Integrable (fun s ↦ aclTrace a b G D t s * β s) (volume.restrict I) :=
    hT.integrable_mul hβ
  rw [← integral_sub iU iT]
  have he : (fun s ↦ aclTrace a b G D u s * β s - aclTrace a b G D t s * β s) =
      fun s ↦ (aclTrace a b G D u s - aclTrace a b G D t s) * β s := by
    funext s; rw [sub_mul]
  rw [he]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [norm_mul]
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp _ (ENNReal.ofReal 2) _ by simpa using hU.sub hT)
    (show MemLp _ (ENNReal.ofReal 2) _ by simpa using hβ)
  simpa only [Pi.sub_apply, Real.rpow_two, ← Real.sqrt_eq_rpow] using hh

/-- A tangential weak equation descends to the canonical left-normal traces
when the error is a distance factor times an integrable normal flux. -/
theorem HasTransverseH1Trace.boundary_weak_tangent {a b w : ℝ}
    {F R A N DF DR : ℝ × ℝ → ℂ} {TF TR : ℝ → ℂ} {c : ℝ → ℂ}
    (hF : HasTransverseH1Trace a b 0 w 0 id F TF)
    (hR : HasTransverseH1Trace a b 0 w 0 id R TR)
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 0 F A)
    (hDF : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 F DF)
    (hDR : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 R DR)
    (hAL : MemLp A 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hNL : IntegrableOn N (Ioo a b ×ˢ Ioo 0 w))
    (hDFL : MemLp DF 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hDRL : MemLp DR 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hc : ContinuousAt c 0) (hc0 : c 0 = 1)
    (he : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)),
      c q.2 * A q = R q + (q.2 : ℂ) * N q) :
    ∃ T : ℝ → ℂ, T =ᵐ[volume.restrict (Ioo a b)] TF ∧ HasIntervalH1 a b T TR := by
  have hab := hF.1
  have hw := hF.2.1
  obtain ⟨G, hGm, hGF, hGL, hG, hTF⟩ := hF.with_weak_snd hDF hDFL
  obtain ⟨K, hKm, hKR, hKL, hK, hTR⟩ := hR.with_weak_snd hDR hDRL
  simp only [Function.comp_id] at hGF hKR
  have ht : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw.le⟩
  have hTFL := ((hG.l2_trace hw hGm hGL hDFL 0 ht).1).ae_eq hTF.symm
  have hTRL := ((hK.l2_trace hw hKm hKL hDRL 0 ht).1).ae_eq hTR.symm
  have hL (β : ℝ → ℂ) (hβ : Continuous β) :
      MemLp β 2 (volume.restrict (Ioo a b)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := β) hβ.continuousOn
    exact MemLp.of_bound hβ.aestronglyMeasurable C
      ((ae_restrict_mem measurableSet_Ioo).mono fun s hs ↦ hC s (Ioo_subset_Icc_self hs))
  have hTest (β : ℝ → ℂ) (hβ : ContDiff ℝ 1 β) (hβa : β a = 0) (hβb : β b = 0) :
      (∫ s in Ioo a b, TF s * deriv β s) = -(∫ s in Ioo a b, TR s * β s) := by
    let E := fun u ↦ c u * (∫ s in Ioo a b, aclTrace 0 w G DF u s * deriv β s) +
      ∫ s in Ioo a b, aclTrace 0 w K DR u s * β s
    let z := (∫ s in Ioo a b, TF s * deriv β s) + ∫ s in Ioo a b, TR s * β s
    have hE : Tendsto E (𝓝[Ioo 0 w] 0) (𝓝 z) := by
      have hsub : 𝓝[Ioo 0 w] (0 : ℝ) ≤ 𝓝[Icc 0 w] 0 :=
        nhdsWithin_mono _ Ioo_subset_Icc_self
      have hh := ((hc.mono_left nhdsWithin_le_nhds).mul
        ((hG.tendsto_trace_pairing hw ht hGm hGL hDFL
          (hL _ (hβ.continuous_deriv le_rfl))).mono_left hsub)).add
        ((hK.tendsto_trace_pairing hw ht hKm hKL hDRL (hL _ hβ.continuous)).mono_left hsub)
      simpa only [E, z, hc0, one_mul, integral_congr_ae (hTF.mono
        fun s hs ↦ congrArg (· * deriv β s) hs.symm),
        integral_congr_ae (hTR.mono fun s hs ↦ congrArg (· * β s) hs.symm)] using hh
    have hProd (P : ℝ × ℝ → ℂ)
        (hP : IntegrableOn P (Ioo a b ×ˢ Ioo 0 w)) :
        Integrable (fun q : ℝ × ℝ ↦ P q.swap * β q.2)
          ((volume.restrict (Ioo 0 w)).prod (volume.restrict (Ioo a b))) := by
      have hPi : Integrable P ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo 0 w))) := by
        simpa only [IntegrableOn, Measure.prod_restrict, Measure.volume_eq_prod] using hP
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := β) hβ.continuous.continuousOn
      apply (hPi.swap.norm.const_mul C).mono'
        (hPi.swap.aestronglyMeasurable.mul (hβ.continuous.comp continuous_snd).aestronglyMeasurable)
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := volume) (s := Ioo a b) measurableSet_Ioo)] with q hq
      change ‖P q.swap * β q.2‖ ≤ C * ‖P q.swap‖
      rw [norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC q.2 (Ioo_subset_Icc_self hq)) (norm_nonneg _)
    have iN := hProd N hNL
    have hfin : IsFiniteMeasure (volume.restrict (Ioo a b ×ˢ Ioo 0 w)) :=
      isFiniteMeasure_restrict.2 ((measure_mono
        (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).trans_lt
          (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
    have iR := hProd R ((hKL.ae_eq hKR).integrable (by norm_num))
    have hbnd : ∀ᵐ u ∂(volume.restrict (Ioo 0 w)),
        ‖E u‖ ≤ u * ∫ s in Ioo a b, ‖N (s, u) * β s‖ := by
      filter_upwards [hd.ae_horizontal_test hab hw (hGL.ae_eq hGF) hAL hβ hβa hβb,
        hG.ae_horizontal_trace_eq hw hGL hDFL hGF,
        hK.ae_horizontal_trace_eq hw hKL hDRL hKR, ae_horizontal_of_ae he,
        iR.prod_right_ae, iN.prod_right_ae,
        ae_restrict_mem measurableSet_Ioo] with u hu hGu hKu heu hiR hiN huI
      change Integrable (fun s ↦ R (s, u) * β s) (volume.restrict (Ioo a b)) at hiR
      change Integrable (fun s ↦ N (s, u) * β s) (volume.restrict (Ioo a b)) at hiN
      have heq : c u * (∫ s in Ioo a b, A (s, u) * β s) =
          (∫ s in Ioo a b, R (s, u) * β s) + (u : ℂ) * ∫ s in Ioo a b, N (s, u) * β s := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add hiR (hiN.const_mul _)]
        exact integral_congr_ae (heu.mono fun s hs ↦ by
          simp only [← mul_assoc, hs, add_mul])
      dsimp only [E]
      rw [integral_congr_ae (hGu.mono fun s hs ↦ congrArg (· * deriv β s) hs),
        integral_congr_ae (hKu.mono fun s hs ↦ congrArg (· * β s) hs), hu,
        mul_neg, heq, neg_add_rev, neg_add_cancel_right, norm_neg, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos huI.1]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) huI.1.le
    exact eq_neg_of_add_eq_zero_left (eq_zero_of_tendsto_of_linear_bound hw hE
      iN.norm.integral_prod_left hbnd)
  have iTF : IntegrableOn TF (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hTFL.integrable (by norm_num)
  have iTR : IntegrableOn TR (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hTRL.integrable (by norm_num)
  obtain ⟨T, hT, hTac, hTd⟩ := ACLSlicing.exists_ac_rep_Icc_complex hab iTF iTR (by
      intro β hβ hβs hβI
      rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
      have hβc := Complex.ofRealCLM.contDiff.comp (hβ.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      have hz (s : ℝ) (hs : s ∉ Ioo a b) : β s = 0 := by
        by_contra hs'
        exact hs (hβI (subset_tsupport _ hs'))
      have heβ (s : ℝ) : deriv (fun x ↦ (β x : ℂ)) s = ((deriv β s : ℝ) : ℂ) :=
        (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
          ((hβ.differentiable (by simp) s).hasDerivAt)).deriv
      simpa only [heβ] using hTest (fun s ↦ (β s : ℂ)) hβc
        (by simp [hz a (by simp)]) (by simp [hz b (by simp)]))
  refine ⟨T, hT, hTFL.ae_eq hT.symm, hTRL, ?_, (ae_restrict_iff' measurableSet_Ioo).1 hTd⟩
  intro x y hx hxy hy
  exact hTac.mono (by rw [uIcc_of_le hab.le, uIcc_of_le hxy]; exact Icc_subset_Icc hx.le hy.le)

/-- The homogeneous boundary equation with a real phase coefficient preserves
modulus, even if the coefficient is only specified almost everywhere. -/
theorem HasIntervalH1.norm_eq_of_imaginary_derivative {a b : ℝ} {T D : ℝ → ℂ}
    {α : ℝ → ℝ} (h : HasIntervalH1 a b T D)
    (hD : D =ᵐ[volume.restrict (Ioo a b)] fun s ↦ Complex.I * (α s : ℂ) * T s)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    ‖T x‖ = ‖T y‖ := by
  have hord (c d : ℝ) (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) :
      ‖T c‖ = ‖T d‖ := by
    have hac := h.absolutelyContinuous hc hd
    have hconj := Complex.conjLIE.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hac
    have hprod : AbsolutelyContinuousOnInterval (fun s ↦ T s * star (T s)) c d := by
      simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Complex.conjLIE_apply,
        Complex.star_def] using hac.fun_smul hconj
    have hder : ∀ᵐ s, s ∈ uIcc c d → HasDerivAt (fun s ↦ T s * star (T s)) 0 s := by
      filter_upwards [h.hasDerivAt_ae, (ae_restrict_iff' measurableSet_Ioo).1 hD] with s hs he hsI
      have hs' := ordConnected_Ioo.uIcc_subset hc hd hsI
      have h1 := hs hs'
      rw [he hs'] at h1
      have h2 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt s h1
      have hh := h1.mul h2
      change HasDerivAt (fun t ↦ T t * Complex.conjCLE (T t)) _ s at hh
      simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
        Function.comp_apply, map_mul, Complex.conj_I, Complex.conj_ofReal] at hh
      convert hh using 1 <;> first | rfl | ring
    have eq := complex_integral_eq_sub_of_ac hprod (intervalIntegrable_const (c := (0 : ℂ))) hder
    simp only [intervalIntegral.integral_zero] at eq
    have heq := sub_eq_zero.mp eq.symm
    change T d * (starRingEnd ℂ) (T d) = T c * (starRingEnd ℂ) (T c) at heq
    rw [Complex.mul_conj', Complex.mul_conj'] at heq
    have hn := congrArg Complex.re heq
    simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hn
    nlinarith [norm_nonneg (T c), norm_nonneg (T d)]
  exact hord x y hx hy

/-- Identify the traces in the homogeneous boundary equation using only the
bulk a.e. relations and the continuous zero boundary values of the forcing. -/
theorem HasTransverseH1Trace.boundary_mode {a b w : ℝ}
    {F V R g : ℝ × ℝ → ℂ} {TF TV TR : ℝ → ℂ} {α : ℝ → ℝ}
    (hF : HasTransverseH1Trace a b 0 w 0 id F TF)
    (hV : HasTransverseH1Trace a b 0 w 0 id V TV)
    (hR : HasTransverseH1Trace a b 0 w 0 id R TR)
    (hg : ∀ s ∈ Ioo a b, ContinuousOn (fun u ↦ g (s, u)) (Icc 0 w))
    (hg0 : ∀ s ∈ Ioo a b, g (s, 0) = 0)
    (heF : F =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)] fun q ↦ V q + g q)
    (heR : R =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)]
      fun q ↦ Complex.I * (α q.1 : ℂ) * V q) :
    TF =ᵐ[volume.restrict (Ioo a b)] TV ∧
      TR =ᵐ[volume.restrict (Ioo a b)] fun s ↦ Complex.I * (α s : ℂ) * TV s := by
  obtain ⟨hab, hw, ht, GF, DF, _, heGF, hGFL, hDFL, hGF, hTF⟩ := hF
  obtain ⟨_, _, _, GV, DV, _, heGV, hGVL, hDVL, hGV, hTV⟩ := hV
  obtain ⟨_, _, _, GR, DR, _, heGR, hGRL, hDRL, hGR, hTR⟩ := hR
  simp only [id_eq] at heGF heGV heGR
  have : (𝓝[Ioo 0 w] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hw
  have hJ : ∀ᶠ u in 𝓝[Ioo 0 w] (0 : ℝ), u ∈ Ioo 0 w := self_mem_nhdsWithin
  have hGg : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ContinuousOn (fun u ↦ GV (s, u) + g (s, u)) (Ioo 0 w) := by
    filter_upwards [hGV.ae_continuousOn isOpen_Ioo, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    exact hs.add ((hg s hsI).mono Ioo_subset_Icc_self)
  have hGc : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ContinuousOn (fun u ↦ Complex.I * (α s : ℂ) * GV (s, u)) (Ioo 0 w) :=
    (hGV.ae_continuousOn isOpen_Ioo).mono fun s hs ↦ continuousOn_const.mul hs
  have heqF : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)), GF q = GV q + g q := by
    filter_upwards [heGF, heGV, heF] with q h1 h2 h3
    rw [h1, h2, h3]
  have heqR : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)),
      GR q = Complex.I * (α q.1 : ℂ) * GV q := by
    filter_upwards [heGR, heGV, heR] with q h1 h2 h3
    rw [h1, h2, h3]
  constructor
  · filter_upwards [hTF, hTV, hGF.ae_tendsto_trace hw hGFL hDFL,
      hGV.ae_tendsto_trace hw hGVL hDVL, ae_restrict_mem measurableSet_Ioo,
      ae_eqOn_sections_of_ae_eq isOpen_Ioo heqF (hGF.ae_continuousOn isOpen_Ioo) hGg]
      with s h1 h2 h3 h4 hs he
    have hg' := (hg s hs 0 ht).mono Ioo_subset_Icc_self
    have hlim := (h4 0 ht).add hg'
    dsimp only at hlim
    rw [hg0 s hs, add_zero] at hlim
    have he' : ∀ᶠ u in 𝓝[Ioo 0 w] (0 : ℝ), GV (s, u) + g (s, u) = GF (s, u) :=
      hJ.mono fun u hu ↦ (he u hu).symm
    exact h1.trans ((tendsto_nhds_unique (h3 0 ht) (hlim.congr' he')).trans h2.symm)
  · filter_upwards [hTR, hTV, hGR.ae_tendsto_trace hw hGRL hDRL,
      hGV.ae_tendsto_trace hw hGVL hDVL,
      ae_eqOn_sections_of_ae_eq isOpen_Ioo heqR (hGR.ae_continuousOn isOpen_Ioo) hGc]
      with s h1 h2 h3 h4 he
    have he' : ∀ᶠ u in 𝓝[Ioo 0 w] (0 : ℝ), Complex.I * (α s : ℂ) * GV (s, u) = GR (s, u) :=
      hJ.mono fun u hu ↦ (he u hu).symm
    change TR s = Complex.I * (α s : ℂ) * TV s
    rw [h1, h2]
    exact tendsto_nhds_unique (h3 0 ht) (((h4 0 ht).const_mul _).congr' he')

/-- Local homogeneous boundary transport gives a single constant modulus on
the full tangential interval of the input canonical trace. -/
theorem HasTransverseH1Trace.exists_norm_eq_of_boundary_mode {a b w : ℝ}
    {F V R g : ℝ × ℝ → ℂ} {TF TV TR : ℝ → ℂ} {α : ℝ → ℝ}
    (hF : HasTransverseH1Trace a b 0 w 0 id F TF)
    (hV : HasTransverseH1Trace a b 0 w 0 id V TV)
    (hR : HasTransverseH1Trace a b 0 w 0 id R TR)
    (hg : ∀ s ∈ Ioo a b, ContinuousOn (fun u ↦ g (s, u)) (Icc 0 w))
    (hg0 : ∀ s ∈ Ioo a b, g (s, 0) = 0)
    (heF : F =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)] fun q ↦ V q + g q)
    (heR : R =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)]
      fun q ↦ Complex.I * (α q.1 : ℂ) * V q)
    (hT : ∃ T : ℝ → ℂ, T =ᵐ[volume.restrict (Ioo a b)] TF ∧ HasIntervalH1 a b T TR) :
    ∃ z : ℂ, ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖TV s‖ = ‖z‖ := by
  obtain ⟨T, heT, hTd⟩ := hT
  have ⟨hTV, hTR⟩ := hF.boundary_mode hV hR hg hg0 heF heR
  have he := heT.trans hTV
  have hD : TR =ᵐ[volume.restrict (Ioo a b)] fun s ↦ Complex.I * (α s : ℂ) * T s := by
    filter_upwards [hTR, he] with s h1 h2
    rw [h1, h2]
  have hm : (a + b) / 2 ∈ Ioo a b := by
    have := hF.1
    constructor <;> linarith
  refine ⟨T ((a + b) / 2), ?_⟩
  filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with s hs hsI
  rw [← hs]
  exact hTd.norm_eq_of_imaginary_derivative hD hsI hm

end NoEmbeddedEigenvalues
