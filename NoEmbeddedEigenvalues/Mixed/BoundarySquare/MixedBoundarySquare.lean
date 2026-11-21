import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.BoundaryForm
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The mixed Neumann-edge square

The boundary variable is `x = tanh t`; all integrals are on the open interval.
The weighted identity does not impose any endpoint values or boundary conditions.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory ComplexConjugate Filter
open scoped ContDiff Topology

/-- The transformed transport operator after factoring out `sech t`. -/
def mixedBoundaryTransport (lam : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * ((boundaryWeight x : ℂ) * deriv F x - (x : ℂ) * F x) -
    (lam : ℂ) * F x

/-- Second-order expression in the boundary square. -/
def mixedBoundarySquare (lam : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  (boundaryWeight x : ℂ) * deriv (deriv F) x -
    (3 * (x : ℂ) + Complex.I * (lam : ℂ)) * deriv F x

/-- Compact-subinterval absolute continuity on `(-1,1)`. -/
def MixedBoundaryLocAC (F : ℝ → ℂ) : Prop :=
  ∀ c d : ℝ, -1 < c → c < d → d < 1 → AbsolutelyContinuousOnInterval F c d

private theorem mixedLocAC_continuous {F : ℝ → ℂ} (h : MixedBoundaryLocAC F) :
    ContinuousOn F (Ioo (-1) 1) := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := exists_between hx.1
  obtain ⟨b, hxb, hb⟩ := exists_between hx.2
  have hc := (h a b ha (hax.trans hxb) hb).continuousOn
  rw [uIcc_of_le (hax.trans hxb).le] at hc
  exact (hc.continuousAt (Icc_mem_nhds hax hxb)).continuousWithinAt

theorem MixedBoundaryLocAC.ae_differentiableAt {F : ℝ → ℂ} (h : MixedBoundaryLocAC F) :
    ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → DifferentiableAt ℝ F x := by
  have hq (a b : ℚ) : ∀ᵐ x : ℝ, -1 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      x ∈ Icc (a : ℝ) (b : ℝ) → DifferentiableAt ℝ F x := by
    by_cases hab : -1 < (a : ℝ) ∧ (a : ℝ) < b ∧ (b : ℝ) < 1
    · filter_upwards [(h a b hab.1 hab.2.1 hab.2.2).boundedVariationOn
        |>.ae_differentiableAt_of_mem_uIcc] with x hx _ _ _ hm
      exact hx (Icc_subset_uIcc hm)
    · exact Eventually.of_forall fun _ ha hab' hb _ ↦ (hab ⟨ha, hab', hb⟩).elim
  filter_upwards [ae_all_iff.2 fun a ↦ ae_all_iff.2 (hq a)] with x hx hm
  obtain ⟨a, ha, hax⟩ := exists_rat_btwn hm.1
  obtain ⟨b, hxb, hb⟩ := exists_rat_btwn hm.2
  exact hx a b ha (hax.trans hxb) hb ⟨hax.le, hxb.le⟩

private theorem mixedLocAC_hasDerivAt {F D : ℝ → ℂ} (hF : MixedBoundaryLocAC F)
    (hD : ContinuousOn D (Ioo (-1 : ℝ) 1))
    (he : ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1), HasDerivAt F (D x) x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt F (D x) x := by
  have hm := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo hD x hx
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl : IntervalIntegrable D volume x x) hm
    (hD.continuousAt (isOpen_Ioo.mem_nhds hx))).const_add (F x)
  apply hp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  have hs : uIcc x y ⊆ Ioo (-1 : ℝ) 1 := by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h]
      exact fun t ht ↦ ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    · rw [uIcc_comm, uIcc_of_le h]
      exact fun t ht ↦ ⟨hy.1.trans_le ht.1, ht.2.trans_lt hx.2⟩
  have hac : AbsolutelyContinuousOnInterval F x y := by
    rcases lt_trichotomy x y with h | rfl | h
    · exact hF x y hx.1 h hy.2
    · obtain ⟨b, hxb, hb⟩ := exists_between hx.2
      exact (hF x b hx.1 hxb hb).mono (uIcc_subset_uIcc left_mem_uIcc left_mem_uIcc)
    · exact (hF y x hy.1 h hx.2).symm
  have he' := (ae_restrict_iff' measurableSet_Ioo).1 he
  have h := complex_integral_eq_sub_of_ac hac (hD.mono hs).intervalIntegrable
    (he'.mono fun t ht htx ↦ ht (hs htx))
  rw [h]
  abel

private theorem mixed_weight_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < boundaryWeight x := by
  unfold boundaryWeight
  have hp : 0 < x + 1 := by linarith [hx.1]
  nlinarith [mul_pos (sub_pos.mpr hx.2) hp]

private theorem mixed_transport_coeff (lam : ℝ) (F G : ℝ → ℂ) (x : ℝ) :
    G x = mixedBoundaryTransport lam F x →
    (boundaryWeight x : ℂ) * deriv F x = ((x : ℂ) + Complex.I * lam) * F x + Complex.I * G x := by
  intro h
  unfold mixedBoundaryTransport at h
  linear_combination -Complex.I * h + Complex.I_sq *
    ((boundaryWeight x : ℂ) * deriv F x - (x : ℂ) * F x)

private theorem mixed_transport_regular (lam : ℝ) {F G : ℝ → ℂ}
    (hF : MixedBoundaryLocAC F) (hG : MixedBoundaryLocAC G)
    (he : G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F) :
    MixedBoundaryLocAC (deriv F) ∧ ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt F (deriv F x) x ∧
      (boundaryWeight x : ℂ) * deriv F x = ((x : ℂ) + Complex.I * lam) * F x + Complex.I * G x := by
  let X : ℝ → ℂ := fun x ↦ (x : ℂ) + Complex.I * lam
  let W : ℝ → ℂ := fun x ↦ (boundaryWeight x : ℂ)
  let P : ℝ → ℂ := fun x ↦ (W x)⁻¹ * (X x * F x + Complex.I * G x)
  have hw : ∀ x ∈ Ioo (-1 : ℝ) 1, W x ≠ 0 :=
    fun _ hx ↦ Complex.ofReal_ne_zero.mpr (mixed_weight_pos hx).ne'
  have hW : ContDiff ℝ 1 W := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hX : ContDiff ℝ 1 X := by
    exact (Complex.ofRealCLM.contDiff.add contDiff_const : _)
  have hWi := hW.contDiffOn.inv hw
  have hPC : ContinuousOn P (Ioo (-1 : ℝ) 1) :=
    hWi.continuousOn.mul ((hX.continuous.continuousOn.mul (mixedLocAC_continuous hF)).add
      (continuous_const.continuousOn.mul (mixedLocAC_continuous hG)))
  have hp : ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1), HasDerivAt F (P x) x := by
    filter_upwards [he, ae_restrict_of_ae hF.ae_differentiableAt,
      ae_restrict_mem measurableSet_Ioo] with x hx hd hm
    have h := (hd hm).hasDerivAt
    rw [show P x = deriv F x by
      dsimp only [P, X]
      rw [← mixed_transport_coeff lam F G x hx, ← mul_assoc, inv_mul_cancel₀ (hw x hm), one_mul]]
    exact h
  have hPD (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) := mixedLocAC_hasDerivAt hF hPC hp hx
  have hEq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : deriv F x = P x := (hPD x hx).deriv
  constructor
  · intro c d hc hcd hd
    have hs : uIcc c d ⊆ Ioo (-1 : ℝ) 1 := by
      rw [uIcc_of_le hcd.le]
      exact fun _ hx ↦ ⟨hc.trans_le hx.1, hx.2.trans_lt hd⟩
    exact (((hWi.mono hs).absolutelyContinuousOnInterval).smul
      ((hX.contDiffOn.absolutelyContinuousOnInterval.smul (hF c d hc hcd hd)).add
        ((hG c d hc hcd hd).const_smul Complex.I))).congr (fun x hx ↦ (hEq x (hs hx)).symm)
  · intro x hx
    rw [hEq x hx]
    refine ⟨hPD x hx, ?_⟩
    change W x * P x = _
    simp [P, X, ← mul_assoc, mul_inv_cancel₀ (hw x hx)]

private theorem mixed_square_from_transport (lam : ℝ) {F G : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hd : HasDerivAt F (deriv F x) x)
    (hdd : DifferentiableAt ℝ (deriv F) x) (hg : DifferentiableAt ℝ G x)
    (htr : ∀ y ∈ Ioo (-1 : ℝ) 1, (boundaryWeight y : ℂ) * deriv F y =
      ((y : ℂ) + Complex.I * lam) * F y + Complex.I * G y) :
    mixedBoundarySquare lam F x = Complex.I * deriv G x + F x := by
  have hw : HasDerivAt (fun y ↦ (boundaryWeight y : ℂ)) (-(2 : ℂ) * (x : ℂ)) x := by
    have h := ((hasDerivAt_id x).pow 2).const_sub 1
    have h' := h.ofReal_comp
    convert h' using 1 <;> simp [boundaryWeight]
  have hX : HasDerivAt (fun y : ℝ ↦ (y : ℂ) + Complex.I * lam) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.const_add (Complex.I * lam))
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ add_comm _ _)
  have h := (hw.mul hdd.hasDerivAt).unique
    (((hX.mul hd).add (hg.hasDerivAt.const_mul Complex.I)).congr_of_eventuallyEq
      (show _ =ᶠ[𝓝 x] _ from by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using htr y hy))
  unfold mixedBoundarySquare
  linear_combination h

private theorem mixed_square_current_algebra (x lam : ℝ) (f g p b : ℂ)
    (hp : (boundaryWeight x : ℂ) * p = ((x : ℂ) + Complex.I * lam) * f + Complex.I * g) :
    2 * x * (x * ‖f‖ ^ 2 + 2 * (Complex.I * g * conj f).re) -
      boundaryWeight x * (‖f‖ ^ 2 + x * (2 * (p * conj f).re) +
        2 * (Complex.I * b * conj f + Complex.I * g * conj p).re) =
    boundaryWeight x * ‖b‖ ^ 2 - 2 * ((g + (lam : ℂ) * f) * conj g).re -
      boundaryWeight x * ‖Complex.I * b + f‖ ^ 2 := by
  have hr := congrArg Complex.re hp
  have hi := congrArg Complex.im hp
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul,
    zero_sub, sub_zero, zero_add, add_zero] at hr hi
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, sub_zero, zero_add, add_zero]
  linear_combination (2 * g.im - 2 * x * f.re) * hr + (-(2 * x * f.im) - 2 * g.re) * hi

private def mixedSquareCurrent (F G : ℝ → ℂ) (x : ℝ) : ℝ :=
  -boundaryWeight x * (x * ‖F x‖ ^ 2 + 2 * (Complex.I * G x * conj (F x)).re)

private theorem mixedSquareCurrent_ac {F G : ℝ → ℂ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (mixedSquareCurrent F G) a b := by
  have hi : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x) a b :=
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  have hw : ContDiff ℝ 1 (fun x ↦ -boundaryWeight x) :=
    (contDiff_const.sub (contDiff_id.pow 2)).neg
  have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval hF
  have hc := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    ((hG.const_smul Complex.I).smul
      (Complex.conjLIE.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hF))
  refine (hw.contDiffOn.absolutelyContinuousOnInterval.fun_mul
    ((hi.fun_mul (hn.fun_mul hn)).add (hc.const_mul 2))).congr fun x _ ↦ ?_
  simp only [mixedSquareCurrent, pow_two, Function.comp_apply, Complex.reCLM_apply,
    Complex.conjLIE_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply]

private theorem mixed_norm_sq_hasDerivAt {F : ℝ → ℂ} {x : ℝ} {p : ℂ}
    (h : HasDerivAt F p x) :
    HasDerivAt (fun y ↦ ‖F y‖ ^ 2) (2 * (p * conj (F x)).re) x := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  convert (hr.mul hr).add (hi.mul hi) using 1
  · funext y
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Pi.add_apply, Pi.mul_apply, Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  · simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

private theorem mixedSquareCurrent_deriv {lam : ℝ} {F G : ℝ → ℂ} {x : ℝ}
    (hF : HasDerivAt F (deriv F x) x) (hG : DifferentiableAt ℝ G x)
    (htr : (boundaryWeight x : ℂ) * deriv F x =
      ((x : ℂ) + Complex.I * lam) * F x + Complex.I * G x) :
    deriv (mixedSquareCurrent F G) x =
      boundaryWeight x * ‖deriv G x‖ ^ 2 -
        2 * ((G x + (lam : ℂ) * F x) * conj (G x)).re -
        boundaryWeight x * ‖Complex.I * deriv G x + F x‖ ^ 2 := by
  have hw : HasDerivAt (fun y ↦ -boundaryWeight y) (2 * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_sub 1).neg using 1
    · rfl
    · simp
  have hconj := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hF
  have hc := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    ((hG.hasDerivAt.const_mul Complex.I).mul hconj)
  have h := hw.mul (((hasDerivAt_id x).mul (mixed_norm_sq_hasDerivAt hF)).add (hc.const_mul 2))
  have he : deriv (mixedSquareCurrent F G) x = _ := h.deriv
  rw [he]
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq, Complex.reCLM_apply,
    Complex.conjCLE_apply, one_mul]
  change _ = _
  have hconj' : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (deriv F x) = conj (deriv F x) := rfl
  rw [hconj']
  simpa only [sub_eq_add_neg, neg_mul, Complex.add_re] using
    mixed_square_current_algebra x lam (F x) (G x) (deriv F x) (deriv G x) htr

private theorem mixed_current_integral_zero {J : ℝ → ℝ}
    (hac : ∀ a b : ℝ, -1 < a → a < b → b < 1 → AbsolutelyContinuousOnInterval J a b)
    (hi : IntegrableOn (deriv J) (Ioo (-1 : ℝ) 1))
    {C : ℝ} (hb : ∀ x ∈ Ioo (-1 : ℝ) 1, |J x| ≤ C * boundaryWeight x) :
    ∫ x in Ioo (-1 : ℝ) 1, deriv J x = 0 := by
  let r (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)
  have hr (n : ℕ) : r n ∈ Ioo (0 : ℝ) 1 := by
    have h : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    exact ⟨sub_pos.mpr ((div_lt_one (by positivity)).2 (by linarith)),
      sub_lt_self _ (by positivity)⟩
  have hm : Monotone r := by
    intro m n h
    change 1 - 1 / ((m : ℝ) + 2) ≤ 1 - 1 / ((n : ℝ) + 2)
    exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
      (add_le_add (Nat.cast_le.mpr h) (le_refl (2 : ℝ)))) _
  have hlim : Tendsto r atTop (𝓝 1) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have he : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
      tendsto_add_atTop_nat 1
    simpa [r, Nat.cast_add, add_assoc, one_add_one_eq_two] using (h.comp he).const_sub (1 : ℝ)
  let s (n : ℕ) := Ioo (-r n) (r n)
  have hs : ∀ n x, x ∈ s n → x ∈ Ioo (-1 : ℝ) 1 :=
    fun n _ hx ↦ ⟨(neg_lt_neg (hr n).2).trans hx.1, hx.2.trans (hr n).2⟩
  have hUnion : ⋃ n, s n = Ioo (-1 : ℝ) 1 := by
    ext x
    rw [mem_iUnion]
    refine ⟨fun ⟨n, hn⟩ ↦ hs n x hn, fun hx ↦ ?_⟩
    obtain ⟨n, hn⟩ := (hlim.eventually_const_lt (show max (-x) x < 1 by
      exact max_lt (by linarith [hx.1]) hx.2)).exists
    exact ⟨n, ⟨neg_lt.mp ((le_max_left _ _).trans_lt hn), (le_max_right _ _).trans_lt hn⟩⟩
  have hI := tendsto_setIntegral_of_monotone (f := deriv J) (μ := volume)
    (s := s) (fun _ ↦ measurableSet_Ioo) (fun _ _ h ↦
      Ioo_subset_Ioo (neg_le_neg (hm h)) (hm h)) (by rw [hUnion]; exact hi)
  rw [hUnion] at hI
  have hb' (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : ‖J x‖ ≤ C * boundaryWeight x := by
    simpa only [Real.norm_eq_abs] using hb x hx
  have hwl : Continuous fun x : ℝ ↦ C * boundaryWeight x :=
    continuous_const.mul (continuous_const.sub (continuous_id.pow 2))
  have hends : Tendsto (fun n ↦ J (r n) - J (-r n)) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n ↦ J (r n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall fun n ↦
        hb' _ ⟨by linarith [(hr n).1], (hr n).2⟩)
      simpa [boundaryWeight, Function.comp_def] using (hwl.tendsto 1).comp hlim
    have h₂ : Tendsto (fun n ↦ J (-r n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall fun n ↦
        hb' _ ⟨by linarith [(hr n).2], by linarith [(hr n).1]⟩)
      simpa [boundaryWeight, Function.comp_def] using (hwl.tendsto (-1)).comp hlim.neg
    simpa only [sub_zero] using h₁.sub h₂
  refine tendsto_nhds_unique (hI.congr fun n ↦ ?_) hends
  have hn : -r n < r n := by linarith [(hr n).1]
  change (∫ x in Ioo (-r n) (r n), deriv J x) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hn.le]
  exact (hac _ _ (by linarith [(hr n).2]) hn (hr n).2).integral_deriv_eq_sub

/-- Weighted boundary square (`lem:mixed-boundary-square-weighted`). The continuous
right side of the first-order equation gives an AC representative of `F'` on
every compact subinterval; in fact it equals the classical derivative there. -/
theorem mixed_boundary_square_weighted (lam : ℝ) {F G : ℝ → ℂ}
    (hF : MixedBoundaryLocAC F) (hG : MixedBoundaryLocAC G)
    (htransport : G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F)
    (hbF : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖F x‖ ≤ C)
    (hbG : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖G x‖ ≤ C)
    (henergy : IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) (Ioo (-1) 1)) :
    MixedBoundaryLocAC (deriv F) ∧
    (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖(boundaryWeight x : ℂ) * deriv F x‖ ≤ C) ∧
    IntegrableOn (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) (Ioo (-1) 1) ∧
    (∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
      ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2 := by
  let S := Ioo (-1 : ℝ) 1
  let e := fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2
  let c := fun x ↦ ((G x + (lam : ℂ) * F x) * conj (G x)).re
  let s := fun x ↦ boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2
  let J := mixedSquareCurrent F G
  obtain ⟨hdF, hdiff⟩ := mixed_transport_regular lam hF hG htransport
  have htr := fun x hx ↦ (hdiff x hx).2
  obtain ⟨A, hA⟩ := hbF
  obtain ⟨B, hB⟩ := hbG
  have h0 : (0 : ℝ) ∈ S := by norm_num [S]
  have hA0 := (norm_nonneg _).trans (hA _ h0)
  have hB0 := (norm_nonneg _).trans (hB _ h0)
  have hxabs (x : ℝ) (hx : x ∈ S) : |x| ≤ 1 :=
    abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hbound : ∃ C : ℝ, ∀ x ∈ S, ‖(boundaryWeight x : ℂ) * deriv F x‖ ≤ C := by
    refine ⟨(1 + |lam|) * A + B, fun x hx ↦ ?_⟩
    rw [htr x hx]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, one_mul]
    apply add_le_add _ (hB x hx)
    apply mul_le_mul _ (hA x hx) (norm_nonneg _) (by positivity)
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hxabs x hx) |lam|)
  have hceq : EqOn (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) c S := by
    intro x hx
    have ht : mixedBoundaryTransport 0 F x = G x + (lam : ℂ) * F x := by
      unfold mixedBoundaryTransport
      simp only [Complex.ofReal_zero, zero_mul, sub_zero]
      linear_combination -Complex.I * htr x hx - Complex.I_sq * ((lam : ℂ) * F x + G x)
    simp only [ht, c]
  have hcCont : ContinuousOn c S := by
    have hf := mixedLocAC_continuous hF
    have hg := mixedLocAC_continuous hG
    exact Complex.continuous_re.comp_continuousOn
      ((hg.add (continuous_const.continuousOn.mul hf)).mul
        (Complex.continuous_conj.comp_continuousOn hg))
  have hc : IntegrableOn c S := by
    refine (integrable_const ((B + |lam| * A) * B)).mono'
      (hcCont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [norm_mul, Complex.norm_conj]
    refine mul_le_mul ((norm_add_le _ _).trans ?_) (hB x hx) (norm_nonneg _) (by positivity)
    simpa [norm_mul] using add_le_add (hB x hx)
      (mul_le_mul_of_nonneg_left (hA x hx) (abs_nonneg lam))
  have hsquare : ∀ᵐ x ∂volume.restrict S,
      mixedBoundarySquare lam F x = Complex.I * deriv G x + F x := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo,
      ae_restrict_of_ae hdF.ae_differentiableAt, ae_restrict_of_ae hG.ae_differentiableAt]
      with x hx hdd hg
    exact mixed_square_from_transport lam hx (hdiff x hx).1 (hdd hx) (hg hx) htr
  have hS : IntegrableOn s S := by
    have hi : IntegrableOn (fun x ↦ 2 * e x + 2 * A ^ 2) S :=
      (henergy.const_mul 2).add (integrable_const _)
    refine hi.mono' (by
      apply AEStronglyMeasurable.congr (f := fun x ↦
        boundaryWeight x * ‖Complex.I * deriv G x + F x‖ ^ 2)
      · exact (continuous_const.sub (continuous_id.pow 2)).aestronglyMeasurable.mul
          ((((measurable_deriv G).aestronglyMeasurable.const_mul Complex.I).add
            ((mixedLocAC_continuous hF).aestronglyMeasurable measurableSet_Ioo)).norm.pow 2)
      · filter_upwards [hsquare] with x hx
        simp only [s, hx]) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo, hsquare] with x hx hr
    have hw := (mixed_weight_pos hx).le
    have hw1 : boundaryWeight x ≤ 1 := by unfold boundaryWeight; linarith [sq_nonneg x]
    dsimp only [s]
    rw [hr, Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    have hn : ‖Complex.I * deriv G x + F x‖ ≤ ‖deriv G x‖ + ‖F x‖ := by
      simpa [norm_mul] using norm_add_le (Complex.I * deriv G x) (F x)
    have hn2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
    have hb2 : ‖F x‖ ^ 2 ≤ A ^ 2 := (sq_le_sq₀ (norm_nonneg _) hA0).2 (hA x hx)
    calc
      _ ≤ boundaryWeight x * (2 * ‖deriv G x‖ ^ 2 + 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hw
        nlinarith only [hn2, hb2, sq_nonneg (‖deriv G x‖ - ‖F x‖)]
      _ ≤ _ := by
        dsimp only [e]
        nlinarith only [mul_le_mul_of_nonneg_right hw1 (sq_nonneg A)]
  have hJd : deriv J =ᵐ[volume.restrict S] fun x ↦ e x - 2 * c x - s x := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo,
      ae_restrict_of_ae hG.ae_differentiableAt, hsquare] with x hx hd hs
    simpa only [J, s, e, c, hs] using mixedSquareCurrent_deriv (hdiff x hx).1 (hd hx) (htr x hx)
  have hJint : IntegrableOn (deriv J) S :=
    ((henergy.sub (hc.const_mul 2)).sub hS).congr hJd.symm
  have hJb (x : ℝ) (hx : x ∈ S) : |J x| ≤ (A ^ 2 + 2 * B * A) * boundaryWeight x := by
    have hw := (mixed_weight_pos hx).le
    change |mixedSquareCurrent F G x| ≤ _
    rw [mixedSquareCurrent, abs_mul, abs_neg, abs_of_nonneg hw]
    rw [mul_comm (A ^ 2 + 2 * B * A)]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hw
    simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖F x‖), abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    apply add_le_add
    · exact (mul_le_mul (hxabs x hx) ((sq_le_sq₀ (norm_nonneg _) hA0).2 (hA x hx))
        (sq_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [mul_assoc (2 : ℝ) B A]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (Complex.abs_re_le_norm _).trans ?_
      simpa [norm_mul] using mul_le_mul (hB x hx) (hA x hx) (norm_nonneg _) hB0
  have hzero := mixed_current_integral_zero
    (fun a b ha hab hb ↦ mixedSquareCurrent_ac (hF a b ha hab hb) (hG a b ha hab hb)) hJint hJb
  have hEi : IntegrableOn e S := henergy
  have hCi : IntegrableOn (fun x ↦ 2 * c x) S := hc.const_mul 2
  have hcalc : (∫ x in S, e x - 2 * c x - s x) =
      (∫ x in S, e x) - 2 * (∫ x in S, c x) - ∫ x in S, s x := by
    calc
      _ = (∫ x in S, (e - (fun x ↦ 2 * c x)) x) - ∫ x in S, s x :=
        integral_sub (hEi.sub hCi) hS
      _ = _ := by
        simp only [Pi.sub_apply]
        rw [integral_sub hEi hCi, integral_const_mul]
  rw [integral_congr_ae hJd, hcalc] at hzero
  have hcae : (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) =ᵐ[volume.restrict S] c :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ hx ↦ hceq hx
  refine ⟨hdF, hbound, hc.congr hcae.symm, hS, ?_⟩
  rw [integral_congr_ae hcae]
  exact sub_eq_zero.mp hzero

/-- The mixed boundary square for smooth data (`lem:mixed-boundary-square`).
Use derivatives within the closed interval to bound the weighted energy;
they agree with ordinary derivatives on the open interval of integration. -/
theorem mixed_boundary_square (lam : ℝ) {F : ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (Icc (-1) 1)) :
    let G := mixedBoundaryTransport lam F
    (∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
      ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2 := by
  let K := Icc (-1 : ℝ) 1
  let S := Ioo (-1 : ℝ) 1
  let G := mixedBoundaryTransport lam F
  let H : ℝ → ℂ := fun x ↦ -Complex.I *
    ((boundaryWeight x : ℂ) * derivWithin F K x - (x : ℂ) * F x) - (lam : ℂ) * F x
  have hK : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (by norm_num)
  have hW : ContDiff ℝ 1 (fun x ↦ (boundaryWeight x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hX : ContDiff ℝ 1 (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hH : ContDiffOn ℝ 1 H K :=
    (contDiffOn_const.mul ((hW.contDiffOn.mul (hF.derivWithin hK (by simp))).sub
      (hX.contDiffOn.mul (hF.of_le (by simp))))).sub (contDiffOn_const.mul (hF.of_le (by simp)))
  have he : EqOn G H S := by
    intro x hx
    have h := derivWithin_of_mem_nhds (f := F) (mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (show S ⊆ K from Ioo_subset_Icc_self))
    simp only [G, H, mixedBoundaryTransport, h]
  have hloc {u : ℝ → ℂ} (hu : ContDiffOn ℝ 1 u S) : MixedBoundaryLocAC u := by
    intro a b ha hab hb
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hab.le]
    exact hu.mono fun x hx ↦ ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hGS := hH.congr_mono he (show S ⊆ K from Ioo_subset_Icc_self)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  have hd (x : ℝ) (hx : x ∈ S) : derivWithin H K x = deriv G x :=
    (derivWithin_of_mem_nhds (mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (show S ⊆ K from Ioo_subset_Icc_self))).trans
      (he.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)).deriv_eq.symm
  have hEnergy : IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) S := by
    have hc : ContinuousOn (fun x ↦ boundaryWeight x * ‖derivWithin H K x‖ ^ 2) K :=
      (show Continuous boundaryWeight by unfold boundaryWeight; fun_prop).continuousOn.mul
        ((hH.continuousOn_derivWithin hK le_rfl).norm.pow 2)
    exact (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr
      ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦
        congrArg (fun D : ℂ ↦ boundaryWeight x * ‖D‖ ^ 2) (hd x hx))
  exact (mixed_boundary_square_weighted lam
    (hloc ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).mono Ioo_subset_Icc_self)) (hloc hGS)
    EventuallyEq.rfl ⟨A, fun x hx ↦ hA x (Ioo_subset_Icc_self hx)⟩
    ⟨B, fun x hx ↦ (he hx).symm ▸ hB x (Ioo_subset_Icc_self hx)⟩ hEnergy).2.2.2.2

end NoEmbeddedEigenvalues
