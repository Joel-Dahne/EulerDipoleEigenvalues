module

public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedTangentialCurrent

/-! # Smooth annular cutoff for the difference of the virial fields -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real ComplexConjugate
open scoped Topology

local notation "smoothOrder" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "Plane" => ℝ × ℝ

private def cartCoeff (p : Plane) : ℝ := (mixedFieldX p ^ 2 + mixedFieldY p ^ 2) / 2
private def diffX (p : Plane) : ℝ := mixedFieldX p - normalField₁ p
private def diffY (p : Plane) : ℝ := mixedFieldY p - normalField₂ p
private def diffCoeff (p : Plane) : ℝ := cartCoeff p - normalCoeff p

private theorem cosHalf_ne {p : Plane} (hp : 0 < dipoleLift p) :
    cos (p.1 / 2) ≠ 0 ∧ cos (p.2 / 2) ≠ 0 := by
  have hc (x : ℝ) (hx : -1 < cos x) : cos (x / 2) ≠ 0 := by
    have he := cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at he
    intro h
    simp only [h, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_sub] at he
    linarith
  unfold dipoleLift at hp
  exact ⟨hc _ (by linarith [cos_le_one p.2]), hc _ (by linarith [cos_le_one p.1])⟩

private theorem mixed_at_regular {p : Plane} (h0 : 0 < dipoleLift p) :
    ContDiffAt ℝ smoothOrder mixedFieldX p ∧ ContDiffAt ℝ smoothOrder mixedFieldY p ∧
    IsAdaptedOn mixedFieldX mixedFieldY cartCoeff {p} ∧
    divergence mixedFieldX mixedFieldY p = cartCoeff p + 1 ∧
    fieldDeriv mixedFieldX mixedFieldY dipoleLift p = dipoleLift p - 2 := by
  obtain ⟨hx, hy⟩ := cosHalf_ne h0
  obtain ⟨dx, dy, cx, cy⟩ := mixed_field_cartesian_partials_of_cos_ne hx hy
  obtain ⟨hx', hsx, htx⟩ := mixed_field_trig hx
  obtain ⟨hy', hsy, hty⟩ := mixed_field_trig hy
  refine ⟨(contDiffAt_tan.2 hx).comp p (by fun_prop),
    (contDiffAt_tan.2 hy).comp p (by fun_prop), ?_, ?_, ?_⟩
  · intro q hq
    have hqp : q = p := hq
    subst q
    simp only [classicalL0, smul_eq_mul, dx, dy, cx, cy, mul_zero, sub_zero, zero_sub,
      cartCoeff, mixedFieldX, mixedFieldY]
    rw [← one_div, ← one_div, hx', hy', htx, hty]
    constructor <;> ring
  · simp only [divergence, dx, dy, cartCoeff, mixedFieldX, mixedFieldY]
    rw [← one_div, ← one_div, hx', hy']
    ring
  · simp only [fieldDeriv, smul_eq_mul, partialX_dipoleLift, partialY_dipoleLift,
      mixedFieldX, mixedFieldY, dipoleLift]
    linear_combination -hsx - hsy

private theorem cutoff_partials {χ : ℝ → ℝ} (hc : Differentiable ℝ χ)
    {p : Plane} {F : Plane → ℝ} (hF : DifferentiableAt ℝ F p) :
    partialX (fun r ↦ χ (dipoleLift r) * F r) p =
      χ (dipoleLift p) * partialX F p - deriv χ (dipoleLift p) * sin p.1 * F p ∧
    partialY (fun r ↦ χ (dipoleLift r) * F r) p =
      χ (dipoleLift p) * partialY F p - deriv χ (dipoleLift p) * sin p.2 * F p := by
  have hcd : DifferentiableAt ℝ (χ ∘ dipoleLift) p :=
    (hc _).comp _ (by unfold dipoleLift; fun_prop)
  have hx : partialX (χ ∘ dipoleLift) p = deriv χ (dipoleLift p) * -sin p.1 :=
    ((hc _).hasDerivAt.comp p.1 ((hasDerivAt_cos p.1).add_const (cos p.2))).deriv
  have hy : partialY (χ ∘ dipoleLift) p = deriv χ (dipoleLift p) * -sin p.2 :=
    ((hc _).hasDerivAt.comp p.2 ((hasDerivAt_cos p.2).const_add (cos p.1))).deriv
  change partialX (fun r ↦ (χ ∘ dipoleLift) r • F r) p = _ ∧
    partialY (fun r ↦ (χ ∘ dipoleLift) r • F r) p = _
  rw [partialX_smul hcd hF, partialY_smul hcd hF, hx, hy]
  simp only [Function.comp_apply, smul_eq_mul]
  constructor <;> ring

private theorem periodic_mixedX : IsPeriodicLift mixedFieldX := fun p ↦ by
  simp only [mixedFieldX, show (p.1 + 2 * π) / 2 = p.1 / 2 + π by ring, tan_add_pi, and_self]

private theorem periodic_mixedY : IsPeriodicLift mixedFieldY := fun p ↦ by
  simp only [mixedFieldY, show (p.2 + 2 * π) / 2 = p.2 / 2 + π by ring, tan_add_pi, and_self]

private theorem cutoff_mixedField {χ : ℝ → ℝ} (hχ : ContDiff ℝ smoothOrder χ) {a b : ℝ}
    (ha : 0 < a) (hs : ∀ s, χ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    ContDiff ℝ smoothOrder (fun p ↦ χ (dipoleLift p) * mixedFieldX p) ∧
    ContDiff ℝ smoothOrder (fun p ↦ χ (dipoleLift p) * mixedFieldY p) ∧
    ContDiff ℝ smoothOrder (fun p ↦ χ (dipoleLift p) * cartCoeff p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * mixedFieldX p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * mixedFieldY p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * cartCoeff p) ∧
    IsAdaptedOn (fun p ↦ χ (dipoleLift p) * mixedFieldX p)
      (fun p ↦ χ (dipoleLift p) * mixedFieldY p) (fun p ↦ χ (dipoleLift p) * cartCoeff p) univ := by
  have hΨ : ContDiff ℝ smoothOrder dipoleLift := by unfold dipoleLift; fun_prop
  have hcs := hχ.comp hΨ
  have hvan (p : Plane) (hp : dipoleLift p ∉ Icc a b) :
      ∀ᶠ q in 𝓝 p, χ (dipoleLift q) = 0 := by
    filter_upwards [hΨ.continuous.continuousAt.eventually
      (isClosed_Icc.isOpen_compl.mem_nhds hp)] with q hq
    by_contra hn
    exact hq (hs _ hn)
  have hsmooth {F : Plane → ℝ} (hF : ∀ p, 0 < dipoleLift p → ContDiffAt ℝ smoothOrder F p) :
      ContDiff ℝ smoothOrder (fun p ↦ χ (dipoleLift p) * F p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : dipoleLift p ∈ Icc a b
    · exact hcs.contDiffAt.mul (hF p (ha.trans_le hp.1))
    · apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hvan p hp] with q hq
      simp only [hq, zero_mul]
  have hper {F : Plane → ℝ} (hF : IsPeriodicLift F) :
      IsPeriodicLift (fun p ↦ χ (dipoleLift p) * F p) := fun p ↦ by
    simp only [dipoleLift, cos_add_two_pi, (hF p).1, (hF p).2, and_self]
  refine ⟨hsmooth fun p h ↦ (mixed_at_regular h).1,
    hsmooth fun p h ↦ (mixed_at_regular h).2.1, hsmooth fun p h ↦ ?_,
    hper periodic_mixedX, hper periodic_mixedY, hper fun p ↦ ?_, ?_⟩
  · have h := mixed_at_regular h
    exact ((h.1.pow 2).add (h.2.1.pow 2)).div_const 2
  · simp only [cartCoeff, (periodic_mixedX p).1, (periodic_mixedX p).2,
      (periodic_mixedY p).1, (periodic_mixedY p).2, and_self]
  · intro p _
    by_cases hp : dipoleLift p ∈ Icc a b
    · obtain ⟨hx, hy, had, _, _⟩ := mixed_at_regular (ha.trans_le hp.1)
      have hχd := hχ.differentiable (by simp)
      rw [classicalL0_cutoff_mul hχd (hx.differentiableAt (by simp)),
        classicalL0_cutoff_mul hχd (hy.differentiableAt (by simp))]
      have h := had p (mem_singleton p)
      exact ⟨by linear_combination χ (dipoleLift p) * h.1,
        by linear_combination χ (dipoleLift p) * h.2⟩
    · have hz := hvan p hp
      have z {F : Plane → ℝ} : (fun q ↦ χ (dipoleLift q) * F q) =ᶠ[𝓝 p] fun _ ↦ 0 :=
        hz.mono fun q hq ↦ by simp only [hq, zero_mul]
      simp only [classicalL0, partialX_eq_zero_of_eventually z,
        partialY_eq_zero_of_eventually z, sub_zero, hz.self_of_nhds, zero_mul,
        smul_eq_mul, mul_zero, add_zero, neg_zero, and_self]

private def quad (U V f : Plane → ℝ) (ω : L2) (p : Plane) : ℝ :=
  let X := streamLiftX ω p
  let Y := streamLiftY ω p
  f p * ‖liftL2 ω p‖ ^ 2 +
    2 * (partialX U p * ‖X‖ ^ 2 + partialX V p * (Y * conj X).re +
      partialY U p * (X * conj Y).re + partialY V p * ‖Y‖ ^ 2) -
    f p * (‖X‖ ^ 2 + ‖Y‖ ^ 2)

private theorem quad_integral {U V f : Plane → ℝ} (hU : ContDiff ℝ smoothOrder U)
    (hV : ContDiff ℝ smoothOrder V) (hf : ContDiff ℝ smoothOrder f)
    (hpU : IsPeriodicLift U) (hpV : IsPeriodicLift V) (hpf : IsPeriodicLift f)
    (had : IsAdaptedOn U V f univ) (hdiv : divergence U V = f) {a b : ℝ} (ha : 0 < a)
    (hb : b < 1)
    (hs : ∀ p, U p ≠ 0 ∨ V p ≠ 0 ∨ f p ≠ 0 → 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b)
    {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) :
    IntegrableOn (quad U V f ω) cellSquare ∧ (∫ p in cellSquare, quad U V f ω p) = 0 := by
  have hle (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 le_top
  have V₀ := (virial_l2 had (hU.of_le (hle 3)) (hV.of_le (hle 3)) (hf.of_le (hle 2))
    hpU hpV hpf ha hb hs hlam hω).2
  have hz : (fun p ↦ laplacian (fun q ↦ f q - divergence U V q) p) = 0 := by
    have he : (fun q ↦ f q - divergence U V q) = 0 := by ext p; simp [hdiv]
    rw [he]
    ext p
    simp [laplacian, partialX, partialY]
  have hcX {g : Plane → ℝ} (hg : ContDiff ℝ smoothOrder g) : Continuous (partialX g) :=
    (contDiff_partialX (n := 0) (by simpa using hg.of_le (hle 1))).continuous
  have hcY {g : Plane → ℝ} (hg : ContDiff ℝ smoothOrder g) : Continuous (partialY g) :=
    (contDiff_partialY (n := 0) (by simpa using hg.of_le (hle 1))).continuous
  have hz' : squarePairing (fun _ ↦ 0) (streamLift ω) = 0 := by
    simp [squarePairing, squareIntegral]
  simp only [hz, Pi.zero_apply, zero_smul, hz', Complex.zero_re, mul_zero, add_zero] at V₀
  let F : Fin 7 → Plane → ℝ :=
    ![rePair f ω ω, rePair (partialX U) (streamPartial 0 ω) (streamPartial 0 ω),
      rePair (partialX V) (streamPartial 1 ω) (streamPartial 0 ω),
      rePair (partialY U) (streamPartial 0 ω) (streamPartial 1 ω),
      rePair (partialY V) (streamPartial 1 ω) (streamPartial 1 ω),
      rePair f (streamPartial 0 ω) (streamPartial 0 ω),
      rePair f (streamPartial 1 ω) (streamPartial 1 ω)]
  have hi : ∀ i, IntegrableOn (F i) periodSquare := by
    intro i
    fin_cases i
    · exact integrableOn_rePair hf.continuous _ _
    · exact integrableOn_rePair (hcX hU) _ _
    · exact integrableOn_rePair (hcX hV) _ _
    · exact integrableOn_rePair (hcY hU) _ _
    · exact integrableOn_rePair (hcY hV) _ _
    · exact integrableOn_rePair hf.continuous _ _
    · exact integrableOn_rePair hf.continuous _ _
  let c : Fin 7 → ℝ := ![1, 2, 2, 2, 2, -1, -1]
  have hQ : quad U V f ω = fun p ↦ ∑ i, c i * F i p := by
    funext p
    simp only [quad, c, F, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, rePair, streamLiftX, streamLiftY, re_mul_conj_self]
    ring
  have hI : squareIntegral (quad U V f ω) = 0 := by
    rw [hQ, squareIntegral_weighted_sum _ _ hi]
    simp only [streamLiftX, streamLiftY] at V₀
    rw [re_squarePairing_smul hf.continuous ω ω,
      re_squarePairing_smul (hcX hU) (streamPartial 0 ω) (streamPartial 0 ω),
      re_squarePairing_smul (hcX hV) (streamPartial 1 ω) (streamPartial 0 ω),
      re_squarePairing_smul (hcY hU) (streamPartial 0 ω) (streamPartial 1 ω),
      re_squarePairing_smul (hcY hV) (streamPartial 1 ω) (streamPartial 1 ω),
      re_squarePairing_smul hf.continuous (streamPartial 0 ω) (streamPartial 0 ω),
      re_squarePairing_smul hf.continuous (streamPartial 1 ω) (streamPartial 1 ω)] at V₀
    simp only [c, F, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    linarith only [V₀]
  have hp : IsPeriodicLift (quad U V f ω) := by
    intro p
    have hω' := isPeriodicLift_liftL2 ω p
    have hx := isPeriodicLift_liftL2 (streamPartial 0 ω) p
    have hy := isPeriodicLift_liftL2 (streamPartial 1 ω) p
    constructor <;> simp only [quad, (hpf p).1, (hpf p).2, hω'.1, hω'.2, streamLiftX,
      streamLiftY, hx.1, hx.2, hy.1, hy.2, (hpU.partialX p).1, (hpU.partialX p).2,
      (hpU.partialY p).1, (hpU.partialY p).2, (hpV.partialX p).1, (hpV.partialX p).2,
      (hpV.partialY p).1, (hpV.partialY p).2]
  have hm : Measurable (quad U V f ω) := by
    have h₁ := (hcX hU).measurable
    have h₂ := (hcX hV).measurable
    have h₃ := (hcY hU).measurable
    have h₄ := (hcY hV).measurable
    have h₅ := hf.continuous.measurable
    have h₆ := measurable_liftL2 ω
    have h₇ : Measurable (streamLiftX ω) := measurable_liftL2 _
    have h₈ : Measurable (streamLiftY ω) := measurable_liftL2 _
    unfold quad
    fun_prop
  have hvan (p : Plane) (hp : dipoleLift p ≤ 0) : quad U V f ω p = 0 := by
    have hloc : ∀ᶠ q in 𝓝 p, dipoleLift q < 2 * a :=
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt.eventually
        (gt_mem_nhds (show dipoleLift p < 2 * a by linarith))
    have hv : ∀ᶠ q in 𝓝 p, U q = 0 ∧ V q = 0 ∧ f q = 0 := hloc.mono fun q hq ↦ by
      exact ⟨by_contra fun h ↦ hq.not_ge (hs q (.inl h)).1,
        by_contra fun h ↦ hq.not_ge (hs q (.inr (.inl h))).1,
        by_contra fun h ↦ hq.not_ge (hs q (.inr (.inr h))).1⟩
    have hu : U =ᶠ[𝓝 p] fun _ ↦ 0 := hv.mono fun _ h ↦ h.1
    have hv' : V =ᶠ[𝓝 p] fun _ ↦ 0 := hv.mono fun _ h ↦ h.2.1
    simp only [quad, partialX_eq_zero_of_eventually hu, partialY_eq_zero_of_eventually hu,
      partialX_eq_zero_of_eventually hv', partialY_eq_zero_of_eventually hv',
      hv.self_of_nhds.2.2, zero_mul, mul_zero, add_zero, sub_zero]
  refine ⟨?_, (squareIntegral_eq_setIntegral_cellSquare hp hm hvan).symm.trans hI⟩
  have hpair {g : Plane → ℝ} (hg : Continuous g) (u v : L2) :
      IntegrableOn (rePair g u v) cellSquare := by
    let B : Set Plane := Icc (-π) (-π + 2 * π) ×ˢ Icc (-π) (-π + 2 * π)
    have hsub : periodBox ⊆ B := fun _ h ↦ ⟨⟨h.1.1.le, h.1.2⟩, ⟨h.2.1.le, h.2.2⟩⟩
    have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hB.exists_bound_of_continuousOn hg.continuousOn
    have hv : MemLp (fun p ↦ conj (liftL2 v p)) 2 (volume.restrict periodBox) :=
      (memLp_liftL2_periodBox v).congr_norm
        (Complex.continuous_conj.comp_aestronglyMeasurable
          (memLp_liftL2_periodBox v).aestronglyMeasurable)
        (.of_forall fun p ↦ (Complex.norm_conj _).symm)
    have hi := Complex.reCLM.integrable_comp ((memLp_liftL2_periodBox u).integrable_mul hv)
    have hb : IntegrableOn (rePair g u v) periodBox :=
      hi.bdd_mul hg.aestronglyMeasurable
        ((ae_restrict_mem measurableSet_periodBox).mono fun p hp ↦ hM p (hsub hp))
    exact hb.mono_set cellSquare_subset_periodBox
  have hiC : ∀ i, IntegrableOn (F i) cellSquare := by
    intro i
    fin_cases i
    · exact hpair hf.continuous _ _
    · exact hpair (hcX hU) _ _
    · exact hpair (hcX hV) _ _
    · exact hpair (hcY hU) _ _
    · exact hpair (hcY hV) _ _
    · exact hpair hf.continuous _ _
    · exact hpair hf.continuous _ _
  rw [hQ]
  exact integrable_finsetSum _ fun i _ ↦ (hiC i).const_mul (c i)

private theorem cutoff_difference {χ : ℝ → ℝ} (hχ : ContDiff ℝ smoothOrder χ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hs : ∀ s, χ s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b)
    {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) :
    IntegrableOn (quad (fun p ↦ χ (dipoleLift p) * diffX p)
      (fun p ↦ χ (dipoleLift p) * diffY p) (fun p ↦ χ (dipoleLift p) * diffCoeff p) ω) cellSquare ∧
    (∫ p in cellSquare, quad (fun r ↦ χ (dipoleLift r) * diffX r)
      (fun r ↦ χ (dipoleLift r) * diffY r) (fun r ↦ χ (dipoleLift r) * diffCoeff r) ω p) = 0 := by
  have h0 : 0 < 2 * a := by linarith
  have h2 : 2 * b < 2 := by linarith
  obtain ⟨hX, hY, hC, hpX, hpY, hpC, hm⟩ := cutoff_mixedField hχ h0 hs
  obtain ⟨hN₁, hN₂, hNf, hpN₁, hpN₂, hpNf, hn⟩ := annularCutoff_normalField hχ h0 h2 hs
  let U := fun p ↦ χ (dipoleLift p) * diffX p
  let V := fun p ↦ χ (dipoleLift p) * diffY p
  let f := fun p ↦ χ (dipoleLift p) * diffCoeff p
  have hU : U = (fun p ↦ χ (dipoleLift p) * mixedFieldX p) -
      (fun p ↦ χ (dipoleLift p) * normalField₁ p) := funext fun p ↦ mul_sub _ _ _
  have hV : V = (fun p ↦ χ (dipoleLift p) * mixedFieldY p) -
      (fun p ↦ χ (dipoleLift p) * normalField₂ p) := funext fun p ↦ mul_sub _ _ _
  have hf : f = (fun p ↦ χ (dipoleLift p) * cartCoeff p) -
      (fun p ↦ χ (dipoleLift p) * normalCoeff p) := funext fun p ↦ mul_sub _ _ _
  have hx : ContDiff ℝ smoothOrder U := hU ▸ hX.sub hN₁
  have hy : ContDiff ℝ smoothOrder V := hV ▸ hY.sub hN₂
  have hz : ContDiff ℝ smoothOrder f := hf ▸ hC.sub hNf
  have hX' (p : Plane) : partialX U p =
      partialX (fun r ↦ χ (dipoleLift r) * mixedFieldX r) p -
      partialX (fun r ↦ χ (dipoleLift r) * normalField₁ r) p := by
    rw [hU]
    exact partialX_sub (hX.differentiable (by simp) p) (hN₁.differentiable (by simp) p)
  have hY' (p : Plane) : partialY V p =
      partialY (fun r ↦ χ (dipoleLift r) * mixedFieldY r) p -
      partialY (fun r ↦ χ (dipoleLift r) * normalField₂ r) p := by
    rw [hV]
    exact partialY_sub (hY.differentiable (by simp) p) (hN₂.differentiable (by simp) p)
  have had : IsAdaptedOn U V f univ := by
    intro p hp
    obtain ⟨hm₁, hm₂⟩ := hm p hp
    obtain ⟨hn₁, hn₂⟩ := hn p hp
    have hL {g k : Plane → ℝ} (hg : DifferentiableAt ℝ g p) (hk : DifferentiableAt ℝ k p) :
        classicalL0 (g - k) p = classicalL0 g p - classicalL0 k p := by
      have hx : partialX (g - k) p = _ := partialX_sub hg hk
      have hy : partialY (g - k) p = _ := partialY_sub hg hk
      simp only [classicalL0, hx, hy, smul_eq_mul]
      ring
    rw [hU, hV, hf, hL (hX.differentiable (by simp) p) (hN₁.differentiable (by simp) p),
      hL (hY.differentiable (by simp) p) (hN₂.differentiable (by simp) p)]
    simp only [Pi.sub_apply] at *
    exact ⟨by linear_combination hm₁ - hn₁, by linear_combination hm₂ - hn₂⟩
  have hdiv : divergence U V = f := by
    funext p
    have hn := (cutoff_normalField_algebra hχ h0 h2 hs p).1
    have hmix : χ (dipoleLift p) * cartCoeff p -
        divergence (fun r ↦ χ (dipoleLift r) * mixedFieldX r)
          (fun r ↦ χ (dipoleLift r) * mixedFieldY r) p =
      -χ (dipoleLift p) - (dipoleLift p - 2) * deriv χ (dipoleLift p) := by
      by_cases hp : dipoleLift p ∈ Icc (2 * a) (2 * b)
      · obtain ⟨h₁, h₂, _, hd, hw⟩ := mixed_at_regular (h0.trans_le hp.1)
        have hχd := hχ.differentiable (by simp)
        unfold divergence at hd ⊢
        rw [(cutoff_partials hχd (h₁.differentiableAt (by simp))).1,
          (cutoff_partials hχd (h₂.differentiableAt (by simp))).2]
        simp only [fieldDeriv, partialX_dipoleLift, partialY_dipoleLift, smul_eq_mul] at hw
        linear_combination -χ (dipoleLift p) * hd - deriv χ (dipoleLift p) * hw
      · have hvan : χ =ᶠ[𝓝 (dipoleLift p)] fun _ ↦ 0 := by
          filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hp] with s hss
          by_contra h
          exact hss (hs s h)
        have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
        have hvan' {F : Plane → ℝ} :
            (fun r ↦ χ (dipoleLift r) * F r) =ᶠ[𝓝 p] fun _ ↦ 0 :=
          (hc.continuousAt.eventually hvan).mono fun r h ↦ by simp only [h, zero_mul]
        rw [divergence, partialX_eq_zero_of_eventually hvan', partialY_eq_zero_of_eventually hvan',
          hvan.self_of_nhds, hvan.deriv_eq, deriv_const]
        simp
    unfold divergence at hn hmix ⊢
    rw [hX', hY', hf, Pi.sub_apply]
    linear_combination -hmix + hn
  refine quad_integral hx hy hz (hU ▸ hpX.sub hpN₁) (hV ▸ hpY.sub hpN₂) (hf ▸ hpC.sub hpNf)
    had hdiv ha hb (fun p hp ↦ hs _ ?_) hlam hω
  rcases hp with h | h | h <;> exact left_ne_zero_of_mul h

private theorem cart_mixed_form {p : Plane} (hp : p ∈ cellSquare) (X Y : ℂ) :
    cartCoeff p = mixedFieldCoeff (diagCoord p) ∧
    (2 * partialX mixedFieldX p - cartCoeff p) * ‖X‖ ^ 2 +
      (2 * partialY mixedFieldY p - cartCoeff p) * ‖Y‖ ^ 2 =
      (1 / 2) * mixedGradientForm 1 (mixedFieldMatrixOffDiagonal (diagCoord p))
        (X + Y) (X - Y) := by
  obtain ⟨A, B, _, hdiv, _, _, _, _, _, dx, dy⟩ := mixed_field_algebra.2 p hp
  have h0 : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  obtain ⟨hx, hy⟩ := cosHalf_ne h0
  have hc := (mixed_at_regular h0).2.2.2.1
  have he : cartCoeff p = mixedFieldCoeff (diagCoord p) := by linarith
  refine ⟨he, ?_⟩
  have hM : mixedFieldMatrixOffDiagonal (diagCoord p) =
      (mixedFieldX p ^ 2 - mixedFieldY p ^ 2) / 2 := by
    have hm : mixedFieldMatrixOffDiagonal (diagCoord p) =
        2 * mixedFieldA (diagCoord p) * mixedFieldB (diagCoord p) := by
      simp only [mixedFieldMatrixOffDiagonal, mixedFieldA, mixedFieldB, div_eq_mul_inv, pow_two,
        mul_inv_rev]
      ring
    rw [hm, A, B]
    ring
  obtain ⟨dX, dY, _, _⟩ := mixed_field_cartesian_partials_of_cos_ne hx hy
  have hX := (mixed_field_trig hx).1
  have hY := (mixed_field_trig hy).1
  rw [dX, dY, ← one_div, ← one_div, hX, hY, hM]
  simp only [mixedGradientForm, cartCoeff, mixedFieldX, mixedFieldY, Complex.sq_norm,
    Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem normal_pair {p : Plane} (hg : gradSq dipoleLift p ≠ 0) (X Y : ℂ) :
    ((normalField₁ p • X + normalField₂ p • Y) *
      conj (sin p.1 • X + sin p.2 • Y)).re =
      -(dipoleLift p - 2) *
        ‖((sin p.1 : ℂ) * X + (sin p.2 : ℂ) * Y) / (√(sin p.1 ^ 2 + sin p.2 ^ 2) : ℂ)‖ ^ 2 := by
  let S : ℂ := sin p.1 • X + sin p.2 • Y
  let G : ℝ := sin p.1 ^ 2 + sin p.2 ^ 2
  have hG : 0 < G := lt_of_le_of_ne (by unfold G; positivity) (by
    rw [gradSq_dipoleLift] at hg
    exact Ne.symm hg)
  have h : normalField₁ p • X + normalField₂ p • Y = (-(dipoleLift p - 2) / G) • S := by
    simp only [normalField₁, normalField₂, partialX_dipoleLift, partialY_dipoleLift,
      gradSq_dipoleLift, S, G, Complex.real_smul, div_eq_mul_inv]
    push_cast
    ring
  change ((normalField₁ p • X + normalField₂ p • Y) * conj S).re =
    -(dipoleLift p - 2) * ‖S / (√G : ℂ)‖ ^ 2
  rw [h, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul, re_mul_conj_self,
    norm_div, Complex.norm_real, Real.norm_of_nonneg (sqrt_nonneg _), div_pow, sq_sqrt hG.le]
  ring

private theorem cutoff_quad_eq {χ : ℝ → ℝ} (hχ : ContDiff ℝ smoothOrder χ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hs : ∀ s, χ s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b)
    {ω : L2} (d : MixedQuotientData ω)
    {q : Plane} (hq : q ∈ mixedOpenCell) (hp : diagInv q ∈ cellSquare)
    (h2 : dipoleLift (diagInv q) < 2)
    (hx : d.streamA q = streamLiftX ω (diagInv q) + streamLiftY ω (diagInv q))
    (hy : d.streamB q = streamLiftX ω (diagInv q) - streamLiftY ω (diagInv q)) :
    let p := diagInv q
    2 * quad (fun r ↦ χ (dipoleLift r) * diffX r) (fun r ↦ χ (dipoleLift r) * diffY r)
        (fun r ↦ χ (dipoleLift r) * diffCoeff r) ω p =
      χ (dipoleLift p) * (mixedVirialDensity d q - mixedNormalVirialDensity d q) -
        2 * deriv χ (dipoleLift p) * mixedTangentialCurrent d q := by
  let p := diagInv q
  let X := streamLiftX ω p
  let Y := streamLiftY ω p
  let S : ℂ := sin p.1 • X + sin p.2 • Y
  let W : ℂ := diffX p • X + diffY p • Y
  have h0 : 0 < dipoleLift p := by
    change 0 < dipoleLift (diagInv q)
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hg := (gradSq_dipoleLift_pos h0 h2).ne'
  have ha' : 0 < 2 * a := by linarith
  have hb' : 2 * b < 2 := by linarith
  obtain ⟨hMX, hMY, _, _, _, _, _⟩ := cutoff_mixedField hχ ha' hs
  obtain ⟨hNX, hNY, _, _, _, _, _⟩ := annularCutoff_normalField hχ ha' hb' hs
  obtain ⟨hmX, hmY, _, _, _⟩ := mixed_at_regular h0
  have hχd := hχ.differentiable (by simp)
  have dsX {g k : Plane → ℝ} (h₁ : DifferentiableAt ℝ g p) (h₂ : DifferentiableAt ℝ k p) :
      partialX (fun r ↦ g r - k r) p = partialX g p - partialX k p := partialX_sub h₁ h₂
  have dsY {g k : Plane → ℝ} (h₁ : DifferentiableAt ℝ g p) (h₂ : DifferentiableAt ℝ k p) :
      partialY (fun r ↦ g r - k r) p = partialY g p - partialY k p := partialY_sub h₁ h₂
  have hU : (fun r ↦ χ (dipoleLift r) * diffX r) =
      fun r ↦ χ (dipoleLift r) * mixedFieldX r - χ (dipoleLift r) * normalField₁ r :=
    funext fun r ↦ mul_sub _ _ _
  have hV : (fun r ↦ χ (dipoleLift r) * diffY r) =
      fun r ↦ χ (dipoleLift r) * mixedFieldY r - χ (dipoleLift r) * normalField₂ r :=
    funext fun r ↦ mul_sub _ _ _
  have eX : (d.streamA q + d.streamB q) / 2 = X := by rw [hx, hy]; ring
  have eY : (d.streamA q - d.streamB q) / 2 = Y := by rw [hx, hy]; ring
  have hN : mixedNormalVirialDensity d q = 2 * eeBulkDensity ω p := by
    simp only [mixedNormalVirialDensity, eeBulkDensity, eeDensity, streamNormal, streamTangent,
      normalDeriv, tangentDeriv, diagCoord_diagInv, p, eX, eY, X, Y]
  obtain ⟨hA, hB, _, _, _, _, _, hcx, hcy, _, _⟩ := mixed_field_algebra.2 p hp
  rw [show diagCoord p = q from diagCoord_diagInv q] at hA hB
  have eW : (mixedFieldA q - (normalField₁ p + normalField₂ p) / 2) • d.streamA q +
      (mixedFieldB q - (normalField₁ p - normalField₂ p) / 2) • d.streamB q = W := by
    rw [hA, hB, hx, hy]
    simp only [W, diffX, diffY, Complex.real_smul, p, X, Y]
    push_cast
    ring
  have eS : (cos q.2 * sin q.1) • d.streamA q +
      (cos q.1 * sin q.2) • d.streamB q = S := by
    rw [hx, hy]
    simp only [S, p, diagInv_apply, sin_add, sin_sub, Complex.real_smul, X, Y]
    push_cast
    ring
  have hCur : mixedTangentialCurrent d q = 2 * (W * conj S).re := by
    rw [mixed_tangential_current_eq d hq hg]
    rw [eW, eS]
    rfl
  have hm := cart_mixed_form hp X Y
  rw [show diagCoord p = q from diagCoord_diagInv q] at hm
  have hn := (cutoff_normalField_algebra hχ ha' hb' hs p).2 X Y
  have hpair := normal_pair hg X Y
  have hw : (W * conj S).re =
      ((mixedFieldX p • X + mixedFieldY p • Y) * conj S).re -
        ((normalField₁ p • X + normalField₂ p • Y) * conj S).re := by
    have he : W = (mixedFieldX p • X + mixedFieldY p • Y) -
          (normalField₁ p • X + normalField₂ p • Y) := by
      simp only [W, diffX, diffY, sub_smul]
      abel
    rw [he, sub_mul, Complex.sub_re]
  change 2 * quad _ _ _ ω p = _
  rw [hN, hCur, hw]
  simp only [quad, hU, hV, dsX (hMX.differentiable (by simp) p) (hNX.differentiable (by simp) p),
    dsX (hMY.differentiable (by simp) p) (hNY.differentiable (by simp) p),
    dsY (hMX.differentiable (by simp) p) (hNX.differentiable (by simp) p),
    dsY (hMY.differentiable (by simp) p) (hNY.differentiable (by simp) p)]
  rw [(cutoff_partials hχd (hmX.differentiableAt (by simp))).1,
    (cutoff_partials hχd (hmY.differentiableAt (by simp))).1,
    (cutoff_partials hχd (hmX.differentiableAt (by simp))).2,
    (cutoff_partials hχd (hmY.differentiableAt (by simp))).2, hcx, hcy]
  change _ = χ (dipoleLift p) * (_ - 2 * eeBulkDensity ω p) - _
  simp only [diffCoeff, mixedVirialDensity, ← hm.1, hx, hy, eeBulkDensity, eeDensity,
    streamNormal, streamTangent, normalDeriv, tangentDeriv, gradNorm]
  have he' : ((mixedFieldX p • X + mixedFieldY p • Y) * conj S).re =
      mixedFieldX p * sin p.1 * ‖X‖ ^ 2 + mixedFieldX p * sin p.2 * (X * conj Y).re +
      mixedFieldY p * sin p.1 * (Y * conj X).re + mixedFieldY p * sin p.2 * ‖Y‖ ^ 2 := by
    rw [show S = sin p.1 • X + sin p.2 • Y from rfl, add_mul, Complex.add_re]
    rw [re_mul_conj_smul_add, re_mul_conj_smul_add]
    simp only [Complex.real_smul, mul_assoc, Complex.re_ofReal_mul, re_mul_conj_self]
    ring
  rw [he', hpair]
  linear_combination 2 * χ (dipoleLift p) * hm.2 - 2 * hn

/-- The maximum level is attained only at the center of the open cell. -/
theorem mixed_level_lt_one_ae :
    ∀ᵐ q : Plane ∂volume.restrict mixedOpenCell, cos q.1 * cos q.2 < 1 := by
  have hne : ∀ᵐ q : Plane ∂volume, q ≠ 0 := by
    rw [ae_iff]
    rw [Measure.volume_eq_prod]
    simpa only [not_not, ofPred_eq_eq_singleton] using
      (measure_singleton (μ := (volume : Measure ℝ).prod volume) (0 : Plane))
  filter_upwards [ae_restrict_of_ae (s := mixedOpenCell) hne,
    ae_restrict_mem (μ := volume) (measurableSet_Ioo.prod measurableSet_Ioo :
      MeasurableSet mixedOpenCell)] with q hn hq
  have hc (x : ℝ) (hx : x ∈ Ioo (-π / 2) (π / 2)) (hn : x ≠ 0) : cos x < 1 := by
    have hab : |x| < π := by
      have := (abs_lt.mpr ⟨by simpa only [neg_div] using hx.1, hx.2⟩ : |x| < π / 2)
      linarith [pi_pos]
    have ht := strictAntiOn_cos (show 0 ∈ Icc (0 : ℝ) π from ⟨le_rfl, pi_pos.le⟩)
      (show |x| ∈ Icc (0 : ℝ) π from ⟨abs_nonneg _, hab.le⟩) (abs_pos.mpr hn)
    simpa only [cos_abs, cos_zero] using ht
  have ha : 0 < cos q.1 := cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)
  have hb : 0 < cos q.2 := cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)
  by_cases ha' : q.1 = 0
  · have hb' : q.2 ≠ 0 := fun hz ↦ hn (Prod.ext ha' hz)
    simpa only [ha', cos_zero, one_mul] using hc _ hq.2 hb'
  · exact ((mul_lt_mul_of_pos_right (hc _ hq.1 ha') hb).trans_le (by simpa using cos_le_one q.2))

/-- Sobolev virial identity for the tangential difference, cut off in the
regular level variable. The zeroth order stream term of the quadratic
virial drops out because the cutoff preserves `div(W - W₀) = f - f₀`. -/
theorem mixed_tangential_cutoff_identity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (d : MixedQuotientData ω)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ smoothOrder φ) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hs : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    IntegrableOn (fun q ↦ deriv φ (cos q.1 * cos q.2) * mixedTangentialCurrent d q) mixedOpenCell ∧
    (∫ q in mixedOpenCell, φ (cos q.1 * cos q.2) *
        (mixedVirialDensity d q - mixedNormalVirialDensity d q)) =
      ∫ q in mixedOpenCell, deriv φ (cos q.1 * cos q.2) * mixedTangentialCurrent d q := by
  let χ := fun s : ℝ ↦ φ (s / 2)
  have hχ : ContDiff ℝ smoothOrder χ := hφ.comp (contDiff_id.div_const 2)
  have hχ' (s : ℝ) : 2 * deriv χ s = deriv φ (s / 2) := by
    have hd := ((hφ.differentiable (by simp) (s / 2)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2)).deriv
    change deriv χ s = _ at hd
    rw [hd]
    ring
  have hχS (s : ℝ) (hn : χ s ≠ 0) : 2 * a ≤ s ∧ s ≤ 2 * b := by
    obtain ⟨hl, hr⟩ := hs _ hn
    constructor <;> linarith
  obtain ⟨hi, hI⟩ := cutoff_difference hχ ha hb hχS hlam hω
  let D := quad (fun p ↦ χ (dipoleLift p) * diffX p) (fun p ↦ χ (dipoleLift p) * diffY p)
      (fun p ↦ χ (dipoleLift p) * diffCoeff p) ω
  let μ := volume.restrict mixedOpenCell
  have hpre : diagInv ⁻¹' cellSquare = mixedOpenCell := by
    ext q
    simp only [mixedOpenCell, cellSquare, mem_preimage, mem_ofPred_eq, diagCoord_diagInv,
      mem_prod, mem_Ioo, abs_lt, neg_div]
  let E := diagInv.toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map diagInv μ = ENNReal.ofReal (2⁻¹ : ℝ) • volume.restrict cellSquare := by
    change Measure.map diagInv (volume.restrict mixedOpenCell) = _
    rw [← hpre, ← Measure.restrict_map diagInv.continuous.measurable
      isOpen_cellSquare.measurableSet, map_diagInv_volume, Measure.restrict_smul]
    norm_num
  have hd : Integrable (D ∘ diagInv) μ := by
    apply E.measurableEmbedding.integrable_map_iff.1
    change Integrable D (Measure.map diagInv μ)
    rw [hmap]
    exact hi.smul_measure (by finiteness)
  have hd₀ : (∫ q, D (diagInv q) ∂μ) = 0 := by
    have he := E.measurableEmbedding.integral_map D (μ := μ)
    change (∫ p, D p ∂Measure.map diagInv μ) = ∫ q, D (diagInv q) ∂μ at he
    rw [← he, hmap, integral_smul_measure]
    change _ • (∫ p in cellSquare, D p) = 0
    rw [show (∫ p in cellSquare, D p) = 0 from hI, smul_zero]
  let B := fun q : Plane ↦ φ (cos q.1 * cos q.2) *
    (mixedVirialDensity d q - mixedNormalVirialDensity d q)
  let C := fun q : Plane ↦ deriv φ (cos q.1 * cos q.2) * mixedTangentialCurrent d q
  have he : (fun q ↦ 2 * D (diagInv q)) =ᵐ[μ] fun q ↦ B q - C q := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo.prod measurableSet_Ioo :
      MeasurableSet mixedOpenCell), mixed_level_lt_one_ae, d.stream_partials_ae] with q hq htop hs
    have hp : diagInv q ∈ cellSquare := by rwa [← hpre] at hq
    have hΨ : dipoleLift (diagInv q) = 2 * (cos q.1 * cos q.2) := by
      rw [dipoleLift_eq_diag, diagCoord_diagInv]
      ring
    have h := cutoff_quad_eq hχ ha hb hχS d hq hp (by rw [hΨ]; linarith) hs.1 hs.2
    dsimp only at h
    have htwo (t : ℝ) : 2 * t / 2 = t := by ring
    rw [hχ', hΨ] at h
    simp only [χ, htwo] at h
    change _ = B q - C q
    exact h
  have hφcpt : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun s hs' ↦
    by_contra fun hn ↦ hs' (hs _ hn)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφcpt
  have hiB : Integrable B μ :=
    ((mixed_rellich_volume_integrable d).1.sub (mixed_normal_virial_integrable d)).bdd_mul
      ((hφ.continuous.comp (by fun_prop :
        Continuous (fun q : Plane ↦ cos q.1 * cos q.2))).aestronglyMeasurable)
        (.of_forall fun q ↦ hM _)
  have hBC := (hd.const_mul (2 : ℝ)).congr he
  have hiC : Integrable C μ := (hiB.sub hBC).congr (.of_forall fun q ↦ by
    change B q - (B q - C q) = C q
    ring)
  refine ⟨hiC, ?_⟩
  change (∫ q, B q ∂μ) = ∫ q, C q ∂μ
  have hE := integral_congr_ae he
  rw [integral_const_mul, hd₀, mul_zero, integral_sub hiB hiC] at hE
  linarith

end NoEmbeddedEigenvalues
