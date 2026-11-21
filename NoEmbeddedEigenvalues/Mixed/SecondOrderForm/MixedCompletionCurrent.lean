import NoEmbeddedEigenvalues.Mixed.SecondOrderForm.MixedRellich

/-! # The combined current for mixed square completion

Integrate the weighted Rellich term and the scalar drift together. The current
uses the coefficients `cos²(a) W`, whose first derivatives are bounded even
at the corners. The normal flux is evaluated on closed ACL sections.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open Set Filter MeasureTheory Real ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ
local notation "H" => (π / 2)
local notation "I" => (Ioo (-H) H)
local notation "ν" => (volume.restrict I)
local notation "μ" => (volume.restrict mixedOpenCell)

private def h (q : Plane) := cos q.1
private def k (q : Plane) := cos q.2
private def u (q : Plane) := sin q.1
private def v (q : Plane) := sin q.2
private def p (q : Plane) := h q + k q
private def r (q : Plane) := h q / p q
private def sinsSq (q : Plane) := u q ^ 2 + v q ^ 2

private theorem cell_cos {q : Plane} (hq : q ∈ mixedOpenCell) : 0 < h q ∧ 0 < k q :=
  ⟨cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1),
    cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)⟩

private theorem cell_ae : ∀ᵐ q ∂μ, q ∈ mixedOpenCell :=
  ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

private def X (q : Plane) := h q ^ 2 * mixedFieldA q
private def Y (q : Plane) := h q ^ 2 * mixedFieldB q
private def Z (q : Plane) := h q * u q
private def Xa (q : Plane) := h q ^ 2 / p q * h q + u q ^ 2 * (r q ^ 2 - 2 * r q)
private def Xb (q : Plane) := u q * v q * r q ^ 2
private def Ya (q : Plane) := u q * v q * (r q ^ 2 - 2 * r q)
private def Yb (q : Plane) := h q ^ 2 / p q * k q + v q ^ 2 * r q ^ 2
private def Za (q : Plane) := h q ^ 2 - u q ^ 2

private def pair (a b : ℂ) : ℝ := (a * conj b).re
private def sq (a : ℂ) : ℝ := ‖a‖ ^ 2

private def S (j : Fin 2) (q : Plane) := if j = 0 then -X q else Y q
private def T (j : Fin 2) (q : Plane) := if j = 0 then -Y q else -X q
private def M (j : Fin 2) (q : Plane) := if j = 0 then X q - Z q else Y q
private def Sd (j : Fin 2) (q : Plane) := if j = 0 then -Xa q else Yb q
private def Td (j : Fin 2) (q : Plane) := if j = 0 then -Ya q else -Xb q
private def Md (j : Fin 2) (q : Plane) := if j = 0 then Xa q - Za q else Yb q

private def normal (j : Fin 2) (q : Plane) (z a b : ℂ) : ℝ :=
  S j q * (sq a - sq b) + T j q * (2 * pair a b) + M j q * sq z

private def bulk (j : Fin 2) (q : Plane) (z a b da db : ℂ) : ℝ :=
  Sd j q * (sq a - sq b) + S j q * (2 * pair da a - 2 * pair db b) +
    Td j q * (2 * pair a b) + T j q * (2 * (pair da b + pair a db)) +
    Md j q * sq z + M j q * (2 * pair (if j = 0 then a else b) z)

private def bulkJet {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (q : Plane) :=
  bulk j q (d.phi q) (d.jet [0] q) (d.jet [1] q) (d.jet [j, 0] q) (d.jet [j, 1] q)

private theorem coeff_deriv (j : Fin 2) (x t : ℝ)
    (hp : p (axisTraceChart j (x, t)) ≠ 0) :
    let C := fun s ↦ axisTraceChart j (x, s)
    HasDerivAt (S j ∘ C) (Sd j (C t)) t ∧
    HasDerivAt (T j ∘ C) (Td j (C t)) t ∧
    HasDerivAt (M j ∘ C) (Md j (C t)) t := by
  fin_cases j
  · change cos t + cos x ≠ 0 at hp
    have ha : HasDerivAt (fun s ↦ X (s, x)) (Xa (t, x)) t := by
      apply (((hasDerivAt_cos t).pow 2).mul
        ((hasDerivAt_sin t).div ((hasDerivAt_cos t).add_const (cos x)) hp)).congr_deriv
      dsimp [Xa, h, p, k, u, r]
      field_simp
      ring
    have hb : HasDerivAt (fun s ↦ Y (s, x)) (Ya (t, x)) t := by
      apply (((hasDerivAt_cos t).pow 2).mul
        ((hasDerivAt_const t (sin x)).div ((hasDerivAt_cos t).add_const (cos x)) hp)).congr_deriv
      dsimp [Ya, h, p, k, u, v, r]
      field_simp
      ring
    have hz : HasDerivAt (fun s ↦ Z (s, x)) (Za (t, x)) t := by
      apply ((hasDerivAt_cos t).mul (hasDerivAt_sin t)).congr_deriv
      dsimp [Za, h, u]
      ring
    exact ⟨ha.neg, hb.neg, ha.sub hz⟩
  · change cos x + cos t ≠ 0 at hp
    have ha : HasDerivAt (fun s ↦ X (x, s)) (Xb (x, t)) t := by
      apply (((hasDerivAt_const t (cos x ^ 2))).mul
        ((hasDerivAt_const t (sin x)).div ((hasDerivAt_cos t).const_add (cos x)) hp)).congr_deriv
      dsimp [Xb, h, p, k, u, v, r]
      field_simp
      ring
    have hb : HasDerivAt (fun s ↦ Y (x, s)) (Yb (x, t)) t := by
      apply ((hasDerivAt_const t (cos x ^ 2)).mul
        ((hasDerivAt_sin t).div ((hasDerivAt_cos t).const_add (cos x)) hp)).congr_deriv
      dsimp [Yb, h, p, k, v, r]
      field_simp
      ring
    exact ⟨hb, ha.neg, hb⟩

private theorem pair_deriv {a b : ℝ → ℂ} {da db : ℂ} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s ↦ pair (a s) (b s)) (pair da (b t) + pair (a t) db) t := by
  have hd : HasDerivAt (fun s ↦ (a s * conj (b s)).re)
      (da * conj (b t) + a t * conj db).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (ha.mul (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hb))
  simpa only [pair, Complex.add_re] using hd

private theorem sq_deriv {a : ℝ → ℂ} {da : ℂ} {t : ℝ} (ha : HasDerivAt a da t) :
    HasDerivAt (fun s ↦ sq (a s)) (2 * pair da (a t)) t := by
  simpa only [sq, pair, real_inner_eq_re_inner, RCLike.inner_apply,
    show (RCLike.re : ℂ → ℝ) = Complex.re from rfl] using ha.norm_sq

private theorem normal_deriv (j : Fin 2) (x t : ℝ) {z a b : ℝ → ℂ} {da db : ℂ}
    (hp : p (axisTraceChart j (x, t)) ≠ 0)
    (hz : HasDerivAt z (if j = 0 then a t else b t) t)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s ↦ normal j (axisTraceChart j (x, s)) (z s) (a s) (b s))
      (bulk j (axisTraceChart j (x, t)) (z t) (a t) (b t) da db) t := by
  obtain ⟨hs, ht, hm⟩ := coeff_deriv j x t hp
  apply (((hs.mul ((sq_deriv ha).sub (sq_deriv hb))).add
    (ht.mul ((pair_deriv ha hb).const_mul 2))).add (hm.mul (sq_deriv hz))).congr_deriv
  simp only [bulk, Function.comp_apply, Pi.sub_apply]
  ring

private theorem coeff_bounds (j : Fin 2) {q : Plane} (hq : q ∈ mixedOpenCell) :
    ‖S j q‖ ≤ 2 ∧ ‖T j q‖ ≤ 2 ∧ ‖M j q‖ ≤ 2 ∧
      ‖Sd j q‖ ≤ 6 ∧ ‖Td j q‖ ≤ 6 ∧ ‖Md j q‖ ≤ 6 := by
  obtain ⟨hh, hk⟩ := cell_cos hq
  have hp : 0 < p q := add_pos hh hk
  have hr : |r q| ≤ 1 := by
    rw [r, abs_of_nonneg (div_nonneg hh.le hp.le)]
    exact (div_le_one hp).2 (le_add_of_nonneg_right hk.le)
  have ha : |h q| ≤ 1 := abs_cos_le_one _
  have hb : |k q| ≤ 1 := abs_cos_le_one _
  have hu : |u q| ≤ 1 := abs_sin_le_one _
  have hv : |v q| ≤ 1 := abs_sin_le_one _
  have E : h q ^ 2 / p q = h q * r q := by unfold r; ring
  have eX : X q = h q * r q * u q := by simp only [X, mixedFieldA, r, p, h, k, u]; ring
  have eY : Y q = h q * r q * v q := by simp only [Y, mixedFieldB, r, p, h, k, v]; ring
  have A (x y : ℝ) {a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have B (x y : ℝ) {a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x + y| ≤ a + b :=
    (abs_add_le x y).trans (add_le_add hx hy)
  have C (x y : ℝ) {a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x - y| ≤ a + b :=
    (abs_sub x y).trans (add_le_add hx hy)
  have sqBound (x : ℝ) (hx : |x| ≤ 1) : |x ^ 2| ≤ 1 := by
    simpa only [pow_two, one_mul] using A x x hx hx
  have e : |r q ^ 2 - 2 * r q| ≤ 3 := by
    have he := C _ _ (sqBound _ hr) (A 2 _ (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).le hr)
    norm_num at he ⊢
    exact he
  have hX : |X q| ≤ 1 := by
    rw [eX]
    simpa only [one_mul] using A _ _ (A _ _ ha hr) hu
  have hY : |Y q| ≤ 1 := by
    rw [eY]
    simpa only [one_mul] using A _ _ (A _ _ ha hr) hv
  have hZ : |Z q| ≤ 1 := by simpa only [Z, one_mul] using A _ _ ha hu
  have hXa : |Xa q| ≤ 4 := by
    rw [Xa, E]
    have he := B _ _ (A _ _ (A _ _ ha hr) ha) (A _ _ (sqBound _ hu) e)
    norm_num at he
    exact he
  have hYa : |Ya q| ≤ 3 := by
    simpa only [Ya, one_mul] using A _ _ (A _ _ hu hv) e
  have hXb : |Xb q| ≤ 1 := by
    simpa only [Xb, one_mul] using A _ _ (A _ _ hu hv) (sqBound _ hr)
  have hYb : |Yb q| ≤ 2 := by
    rw [Yb, E]
    have he := B _ _ (A _ _ (A _ _ ha hr) hb) (A _ _ (sqBound _ hv) (sqBound _ hr))
    norm_num at he
    exact he
  have hZa : |Za q| ≤ 1 + 1 := C _ _ (sqBound _ ha) (sqBound _ hu)
  have hM := C _ _ hX hZ
  have hMd := C _ _ hXa hZa
  fin_cases j <;> simp only [S, T, M, Sd, Td, Md, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    one_ne_zero, ite_true, ite_false, Real.norm_eq_abs, abs_neg]
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

private theorem coeff_meas (j : Fin 2) :
    Measurable (S j) ∧ Measurable (T j) ∧ Measurable (M j) ∧
      Measurable (Sd j) ∧ Measurable (Td j) ∧ Measurable (Md j) := by
  fin_cases j <;>
    first
    | change Measurable (fun q ↦ S 0 q) ∧
        Measurable (fun q ↦ T 0 q) ∧
        Measurable (fun q ↦ M 0 q) ∧
        Measurable (fun q ↦ Sd 0 q) ∧
        Measurable (fun q ↦ Td 0 q) ∧
        Measurable (fun q ↦ Md 0 q)
    | change Measurable (fun q ↦ S 1 q) ∧
        Measurable (fun q ↦ T 1 q) ∧
        Measurable (fun q ↦ M 1 q) ∧
        Measurable (fun q ↦ Sd 1 q) ∧
        Measurable (fun q ↦ Td 1 q) ∧
        Measurable (fun q ↦ Md 1 q)
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [S, T, M, Sd, Td, Md, X, Y, Z, Xa, Xb, Ya, Yb, Za, r, p, h, k, u, v,
      mixedFieldA, mixedFieldB, one_ne_zero, ite_true, ite_false]
    fun_prop

private theorem pair_integrable {f g : Plane → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun q ↦ pair (f q) (g q)) μ := by
  have hc := hg.congr_norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ (Complex.norm_conj (g x)).symm)
  exact Complex.reCLM.integrable_comp (hf.integrable_mul hc)

private theorem bulk_integrable {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) :
    Integrable (bulkJet d j) μ := by
  have L := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo) d.weakJet
  have ha := L [0] (by decide)
  have hb := L [1] (by decide)
  have hda := L [j, 0] (by simp)
  have hdb := L [j, 1] (by simp)
  have hz := d.h2.memLp
  have hgrad : MemLp (fun q ↦ if j = 0 then d.jet [0] q else d.jet [1] q) 2 μ := by
    split_ifs <;> assumption
  obtain ⟨hs, ht, hm, hsd, htd, hmd⟩ := coeff_meas j
  have bound {F : Plane → ℝ} (hF : Measurable F) {c : ℝ}
      (hC : ∀ q ∈ mixedOpenCell, ‖F q‖ ≤ c) {G : Plane → ℝ} (hG : Integrable G μ) :
      Integrable (fun q ↦ F q * G q) μ :=
    hG.bdd_mul hF.aestronglyMeasurable (cell_ae.mono hC)
  have i1 := bound hsd (fun _ hq ↦ (coeff_bounds j hq).2.2.2.1)
    (ha.norm.integrable_sq.sub hb.norm.integrable_sq)
  have i2 := bound hs (fun _ hq ↦ (coeff_bounds j hq).1)
    (((pair_integrable hda ha).const_mul 2).sub ((pair_integrable hdb hb).const_mul 2))
  have i3 := bound htd (fun _ hq ↦ (coeff_bounds j hq).2.2.2.2.1)
    ((pair_integrable ha hb).const_mul 2)
  have i4 := bound ht (fun _ hq ↦ (coeff_bounds j hq).2.1)
    (((pair_integrable hda hb).add (pair_integrable ha hdb)).const_mul 2)
  have i5 := bound hmd (fun _ hq ↦ (coeff_bounds j hq).2.2.2.2.2) hz.norm.integrable_sq
  have i6 := bound hm (fun _ hq ↦ (coeff_bounds j hq).2.2.1)
    ((pair_integrable hgrad hz).const_mul 2)
  exact ((((i1.add i2).add i3).add i4).add i5).add i6

private theorem normal_ac (j : Fin 2) {x : ℝ} (hx : x ∈ I) {z a b : ℝ → ℂ}
    (hz : AbsolutelyContinuousOnInterval z (-H) H)
    (ha : AbsolutelyContinuousOnInterval a (-H) H)
    (hb : AbsolutelyContinuousOnInterval b (-H) H) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ normal j (axisTraceChart j (x, t)) (z t) (a t) (b t)) (-H) H := by
  have hlr : -H ≤ H := by linarith [pi_pos]
  have hden (t : ℝ) (ht : t ∈ uIcc (-H) H) : 0 < p (axisTraceChart j (x, t)) := by
    rw [uIcc_of_le hlr] at ht
    have h₁ := cos_pos_of_mem_Ioo hx
    have h₂ := cos_nonneg_of_mem_Icc ht
    fin_cases j
    · exact add_pos_of_nonneg_of_pos h₂ h₁
    · exact add_pos_of_pos_of_nonneg h₁ h₂
  let C := fun t ↦ axisTraceChart j (x, t)
  have hC : ContDiff ℝ 1 C := by
    fin_cases j
    · exact contDiff_id.prodMk contDiff_const
    · exact contDiff_const.prodMk contDiff_id
  have hh : ContDiff ℝ 1 (fun t ↦ h (C t)) := contDiff_cos.comp (contDiff_fst.comp hC)
  have hk : ContDiff ℝ 1 (fun t ↦ k (C t)) := contDiff_cos.comp (contDiff_snd.comp hC)
  have hu : ContDiff ℝ 1 (fun t ↦ u (C t)) := contDiff_sin.comp (contDiff_fst.comp hC)
  have hv : ContDiff ℝ 1 (fun t ↦ v (C t)) := contDiff_sin.comp (contDiff_snd.comp hC)
  have hd := (hh.add hk).contDiffOn (s := uIcc (-H) H)
  have haX : AbsolutelyContinuousOnInterval (X ∘ C) (-H) H :=
    ((hh.pow 2).contDiffOn.mul (hu.contDiffOn.div hd
      (fun t ht ↦ (hden t ht).ne'))).absolutelyContinuousOnInterval
  have haY : AbsolutelyContinuousOnInterval (Y ∘ C) (-H) H :=
    ((hh.pow 2).contDiffOn.mul (hv.contDiffOn.div hd
      (fun t ht ↦ (hden t ht).ne'))).absolutelyContinuousOnInterval
  have haZ : AbsolutelyContinuousOnInterval (Z ∘ C) (-H) H :=
    (hh.mul hu).contDiffOn.absolutelyContinuousOnInterval
  have haS : AbsolutelyContinuousOnInterval (S j ∘ C) (-H) H := by
    fin_cases j
    · exact haX.neg
    · exact haY
  have haT : AbsolutelyContinuousOnInterval (T j ∘ C) (-H) H := by
    fin_cases j
    · exact haY.neg
    · exact haX.neg
  have haM : AbsolutelyContinuousOnInterval (M j ∘ C) (-H) H := by
    fin_cases j
    · exact haX.sub haZ
    · exact haY
  have abs_sq {F : ℝ → ℂ} (hF : AbsolutelyContinuousOnInterval F (-H) H) :
      AbsolutelyContinuousOnInterval (fun t ↦ sq (F t)) (-H) H := by
    have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval hF
    rw [show (fun t ↦ sq (F t)) = (fun t ↦ (Norm.norm ∘ F) t * (Norm.norm ∘ F) t) from
      funext (fun t ↦ pow_two ‖F t‖)]
    exact hn.fun_mul hn
  have pa := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval ha
  have qa := Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval ha
  have pb := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hb
  have qb := Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hb
  have hc : AbsolutelyContinuousOnInterval (fun t ↦ pair (a t) (b t)) (-H) H := by
    apply ((pa.fun_mul pb).add (qa.fun_mul qb)).congr
    intro t _
    simp only [Pi.add_apply, Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      pair, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  have hc' : AbsolutelyContinuousOnInterval (fun t ↦ 2 * pair (a t) (b t)) (-H) H :=
    (LipschitzWith.const (2 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.fun_mul hc
  exact ((haS.fun_mul ((abs_sq ha).sub (abs_sq hb))).add (haT.fun_mul hc')).add
    (haM.fun_mul (abs_sq hz))

private theorem edge_normal (j : Fin 2) (σ : Bool) {x : ℝ} (hx : x ∈ I) (z a b : ℂ)
    (hb : j = 1 → b = 0) :
    normal j (axisTraceChart j (x, cellEdgeNormal σ)) z a b =
      if j = 0 then 0 else (if σ then 1 else -1) * cos x * (sq a + sq z) := by
  have hx' := (cos_pos_of_mem_Ioo hx).ne'
  fin_cases j
  · cases σ <;>
      simp [normal, S, T, M, X, Y, Z, h, u, axisTraceChart, cellEdgeNormal, neg_div]
  · rw [hb rfl]
    cases σ <;>
      simp [normal, S, T, M, X, Y, h, axisTraceChart, cellEdgeNormal, mixedFieldA,
        mixedFieldB, neg_div, sq, pair, pow_two, hx'] <;> ring

private theorem normal_section {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) :
    ∀ᵐ x ∂ν, (∫ t in I, bulkJet d j (axisTraceChart j (x, t))) =
      if j = 0 then 0 else ∑ σ : Bool, cos x *
        (sq (deriv (mixedEdgeValue 1 σ d.phi) x) + sq (mixedEdgeValue 1 σ d.phi x)) := by
  have L := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo) d.weakJet
  have hW := d.weakJet.2 [] (by decide) j
  rw [d.weakJet.1] at hW
  have hz := rellich_acl_sections j hW d.h2.memLp (L [j] (by simp))
    (fun σ ↦ mixedEdgeValue 1 σ d.phi) (fun _ σ ↦ (mixed_quotient_neumann_traces d σ).2.2.1)
  have ha := rellich_acl_sections j (d.weakJet.2 [0] (by simp) j)
    (L [0] (by decide)) (L [j, 0] (by simp))
    (fun σ ↦ deriv (mixedEdgeValue 1 σ d.phi)) (fun _ σ ↦ (mixed_quotient_neumann_traces d σ).2.2.2)
  have hb := rellich_acl_sections j (d.weakJet.2 [1] (by simp) j)
    (L [1] (by decide)) (L [j, 1] (by simp)) (fun _ _ ↦ 0) (fun _ σ ↦ d.normal_zero 1 σ)
  rw [neg_div] at hz ha hb
  filter_upwards [hz, ha, hb, ae_restrict_mem (s := I) measurableSet_Ioo]
    with x hz ha hb hx
  obtain ⟨F, hF, hFt, hFd⟩ := hz
  obtain ⟨A, hA, hAt, hAd⟩ := ha
  obtain ⟨B, hB, hBt, hBd⟩ := hb
  let C := fun t ↦ axisTraceChart j (x, t)
  let N := fun t ↦ normal j (C t) (F t) (A t) (B t)
  have hac : AbsolutelyContinuousOnInterval N (-H) H := normal_ac j hx hF hA hB
  have he : (fun t ↦ bulkJet d j (C t)) =ᵐ[ν] deriv N := by
    filter_upwards [hFd, hAd, hBd, ae_restrict_mem (s := I) measurableSet_Ioo]
      with t ⟨hFv, hFd⟩ ⟨hAv, hAd⟩ ⟨hBv, hBd⟩ ht
    have hq : C t ∈ mixedOpenCell := by
      rw [mixedOpenCell, neg_div]
      fin_cases j
      · exact ⟨ht, hx⟩
      · exact ⟨hx, ht⟩
    obtain ⟨hh, hk⟩ := cell_cos hq
    have hFd' : HasDerivAt F (if j = 0 then A t else B t) t := by
      rw [hAv, hBv]
      fin_cases j <;> exact hFd
    have hd := (normal_deriv j x t (add_pos hh hk).ne' hFd' hAd hBd).deriv
    change bulkJet d j (C t) = deriv N t
    rw [hd, hFv, hAv, hBv]
    rfl
  have hlr : -H ≤ H := by linarith [pi_pos]
  change (∫ t in I, bulkJet d j (C t)) = _
  rw [integral_congr_ae he, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlr,
    hac.integral_deriv_eq_sub]
  have endpoint (σ : Bool) := edge_normal j σ hx (F (cellEdgeNormal σ))
    (A (cellEdgeNormal σ)) (B (cellEdgeNormal σ)) (fun hj ↦ hBt hj σ)
  have hep := congrArg₂ (fun t s ↦ N t - N s)
    (show H = cellEdgeNormal true from rfl)
    (show -H = cellEdgeNormal false by simp [cellEdgeNormal, neg_div])
  rw [hep]
  change normal j (C (cellEdgeNormal true)) _ _ _ - normal j (C (cellEdgeNormal false)) _ _ _ = _
  rw [endpoint true, endpoint false]
  by_cases hj : j = 0
  · simp only [hj, ite_true, sub_self]
  · have h1 : j = 1 := by fin_cases j <;> simp_all
    simp only [hj, ite_false, ite_true, Bool.false_eq_true, hFt h1, hAt h1, Fintype.sum_bool]
    ring

private theorem current_integral {ω : L2} (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, bulkJet d 0 q + bulkJet d 1 q) =
      ∑ σ : Bool, ∫ x in I, cos x *
        (sq (deriv (mixedEdgeValue 1 σ d.phi) x) + sq (mixedEdgeValue 1 σ d.phi x)) := by
  have hprod : Measure.prod ν ν = μ := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, mixedOpenCell, neg_div]
  have h0 := bulk_integrable d 0
  have h1 := bulk_integrable d 1
  change (∫ q, (bulkJet d 0 + bulkJet d 1) q ∂μ) = _
  rw [show (∫ q, (bulkJet d 0 + bulkJet d 1) q ∂μ) = _ from integral_add h0 h1,
    ← hprod, integral_prod_symm _ (hprod.symm ▸ h0),
    integral_prod _ (hprod.symm ▸ h1)]
  change ((∫ x in I, ∫ t in I, bulkJet d 0 (axisTraceChart 0 (x, t))) +
    ∫ x in I, ∫ t in I, bulkJet d 1 (axisTraceChart 1 (x, t))) = _
  rw [integral_congr_ae (normal_section d 0), integral_congr_ae (normal_section d 1)]
  simp only [one_ne_zero, ite_true, ite_false, integral_zero, zero_add]
  apply integral_finsetSum
  intro σ _
  rw [show (fun x ↦ cos x * (sq (deriv (mixedEdgeValue 1 σ d.phi) x) +
        sq (mixedEdgeValue 1 σ d.phi x))) =
      (fun x ↦ cos x * ‖deriv (mixedEdgeValue 1 σ d.phi) x‖ ^ 2) +
        (fun x ↦ cos x * ‖mixedEdgeValue 1 σ d.phi x‖ ^ 2) by
    funext x
    simp only [sq, Pi.add_apply, mul_add]]
  simpa only [IntegrableOn, neg_div] using ((mixed_rellich d).2.2.1 σ).add
    (mixed_edge_integrable d.continuous σ)

private theorem coefficient_identities {q : Plane} (hq : q ∈ mixedOpenCell) :
    let A := mixedFieldA q
    let B := mixedFieldB q
    mixedComparisonDiagonal q = h q ^ 2 + 2 * Z q * A ∧
    Xa q + Yb q = h q ^ 2 * (1 - mixedC₀ q) ∧
    Yb q - Xa q = 2 * Z q * A ∧
    Ya q + Xb q = mixedComparisonOffDiagonal q - 2 * Z q * B := by
  obtain ⟨hh, hk⟩ := cell_cos hq
  have hp : p q ≠ 0 := (add_pos hh hk).ne'
  have e₁ : u q ^ 2 + h q ^ 2 = 1 := sin_sq_add_cos_sq q.1
  have e₂ : v q ^ 2 + k q ^ 2 = 1 := sin_sq_add_cos_sq q.2
  have a : mixedFieldA q = u q / p q := rfl
  have b : mixedFieldB q = v q / p q := rfl
  have f : mixedFieldCoeff q = sinsSq q / p q ^ 2 := rfl
  have G : mixedComparisonOffDiagonal q = 2 * h q ^ 2 / p q ^ 2 * u q * v q := rfl
  have D : mixedComparisonDiagonal q = h q ^ 2 + 2 * h q * (1 - h q ^ 2) / p q := rfl
  dsimp only
  rw [D, G, a, b]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Z, show 1 - h q ^ 2 = u q ^ 2 by linarith only [e₁]]
    ring
  · change Xa q + Yb q =
      h q ^ 2 * (1 - (-mixedFieldCoeff q + 2 * u q ^ 2 / (h q * p q)))
    rw [f]
    unfold Xa Yb r sinsSq
    field_simp [hh.ne', hp]
    unfold p
    ring
  · unfold Xa Yb Z r
    field_simp [hp]
    unfold p
    linear_combination h q * (e₂ - e₁)
  · unfold Ya Xb Z r
    field_simp [hp]
    ring

private theorem potential_identity {q : Plane} (hq : q ∈ mixedOpenCell)
    (hR : sinsSq q ≠ 0) :
    mixedComparisonPotential q +
      h q ^ 2 * mixedFieldCoeff q / 2 * (mixedC₀ q / mixedFieldCoeff q) ^ 2 =
        -(h q ^ 2 * mixedFieldCoeff q / 2) := by
  obtain ⟨hh, hk⟩ := cell_cos hq
  have hp : p q ≠ 0 := (add_pos hh hk).ne'
  have e₁ : 1 - h q ^ 2 = u q ^ 2 := by
    have := sin_sq_add_cos_sq q.1
    change u q ^ 2 + h q ^ 2 = 1 at this
    linarith
  have e₂ : 2 - h q ^ 2 - k q ^ 2 = sinsSq q := by
    unfold sinsSq
    have H₁ : u q ^ 2 + h q ^ 2 = 1 := sin_sq_add_cos_sq q.1
    have H₂ : v q ^ 2 + k q ^ 2 = 1 := sin_sq_add_cos_sq q.2
    linarith
  change (-h q ^ 2 * (2 - h q ^ 2 - k q ^ 2) / p q ^ 2 +
      2 * h q * (1 - h q ^ 2) / p q - 2 * (1 - h q ^ 2) ^ 2 / (2 - h q ^ 2 - k q ^ 2)) +
      h q ^ 2 * (sinsSq q / p q ^ 2) / 2 *
        ((-(sinsSq q / p q ^ 2) + 2 * u q ^ 2 / (h q * p q)) /
          (sinsSq q / p q ^ 2)) ^ 2 = _
  rw [e₁, e₂, show mixedFieldCoeff q = sinsSq q / p q ^ 2 from rfl]
  field_simp [hh.ne', hp, hR]
  ring

private theorem nonzero_ae : ∀ᵐ q ∂μ, sinsSq q ≠ 0 := by
  have h : ∀ᵐ q : Plane ∂volume, q ∉ ({(0, 0)} : Set Plane) :=
    measure_eq_zero_iff_ae_notMem.1 (by
      rw [← singleton_prod_singleton, Measure.volume_eq_prod, Measure.prod_prod]
      simp)
  filter_upwards [cell_ae, ae_restrict_of_ae h] with q hq hq'
  intro he
  have ha : sin q.1 = 0 := by unfold sinsSq u v at he; nlinarith
  have hb : sin q.2 = 0 := by unfold sinsSq u v at he; nlinarith
  have eq₀ {x : ℝ} (hx : x ∈ I) (hs : sin x = 0) : x = 0 := by
    apply strictMonoOn_sin.injOn (Ioo_subset_Icc_self hx)
      (show (0 : ℝ) ∈ Icc (-H) H from ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)
    simpa only [sin_zero] using hs
  apply hq'
  rw [mem_singleton_iff]
  exact Prod.ext (eq₀ (by simpa only [neg_div] using hq.1) ha)
    (eq₀ (by simpa only [neg_div] using hq.2) hb)

private theorem sq_smul (c : ℝ) (z : ℂ) : sq (c • z) = c ^ 2 * sq z := by
  simp only [sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

private theorem sq_add (z w : ℂ) : sq (z + w) = sq z + 2 * pair z w + sq w := by
  simp only [sq, pair, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem square_expand {q : Plane} (hf : mixedFieldCoeff q ≠ 0) (L z : ℂ) :
    h q ^ 2 * mixedFieldCoeff q / 2 * sq (L + (mixedC₀ q / mixedFieldCoeff q) • z) =
      h q ^ 2 * mixedFieldCoeff q / 2 * sq L + h q ^ 2 * mixedC₀ q * pair L z +
      (h q ^ 2 * mixedFieldCoeff q / 2 * (mixedC₀ q / mixedFieldCoeff q) ^ 2) * sq z := by
  rw [sq_add, sq_smul]
  have hp (c : ℝ) : pair L (c • z) = c * pair L z := by
    simp only [pair, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hp]
  field_simp

private theorem div_algebra {q : Plane} (hq : q ∈ mixedOpenCell) (hR : sinsSq q ≠ 0)
    (z a b aa ab bb : ℂ) :
    let ℓ := aa + bb - (2 * tan q.1 : ℝ) • a
    let ω := (h q / 2 : ℝ) • (ℓ - z)
    let U := h q • a - u q • z
    let V := h q • b
    2 * mixedFieldCoeff q * sq ω + sq U + sq V -
        4 * pair (mixedFieldA q • U + mixedFieldB q • V) ω =
      h q ^ 2 * mixedFieldCoeff q / 2 *
        sq (ℓ + (mixedC₀ q / mixedFieldCoeff q) • z) +
      (mixedGradientForm (mixedComparisonDiagonal q) (mixedComparisonOffDiagonal q) a b +
        mixedComparisonPotential q * sq z) +
      (bulk 0 q z a b aa ab + bulk 1 q z a b ab bb) := by
  obtain ⟨hh, hk⟩ := cell_cos hq
  have hp : p q ≠ 0 := (add_pos hh hk).ne'
  have hf : mixedFieldCoeff q ≠ 0 := div_ne_zero hR (pow_ne_zero _ hp)
  obtain ⟨hD, hsum, hdif, hoff⟩ := coefficient_identities hq
  have hP := potential_identity hq hR
  let ℓ := aa + bb - (2 * tan q.1 : ℝ) • a
  let w := (h q / 2 : ℝ) • (ℓ - z)
  let U := h q • a - u q • z
  let V := h q • b
  let f := mixedFieldCoeff q
  let C := mixedC₀ q
  let A := mixedFieldA q
  let B := mixedFieldB q
  change 2 * f * sq w + sq U + sq V - 4 * pair (A • U + B • V) w =
    h q ^ 2 * f / 2 * sq (ℓ + (C / f) • z) +
      (mixedGradientForm (mixedComparisonDiagonal q) (mixedComparisonOffDiagonal q) a b +
        mixedComparisonPotential q * sq z) +
      (bulk 0 q z a b aa ab + bulk 1 q z a b ab bb)
  rw [square_expand hf]
  have hsum' : Xa q + Yb q = h q ^ 2 * (1 - C) := hsum
  have Hd : Yb q - Xa q = 2 * Z q * A := hdif
  have Hc : Ya q + Xb q = mixedComparisonOffDiagonal q - 2 * Z q * B := hoff
  have Hc₀ : h q ^ 2 * C = -h q ^ 2 * f + 2 * Z q * A := by
    change h q ^ 2 * (-f + 2 * u q ^ 2 / (h q * p q)) = _
    rw [show A = u q / p q from rfl, Z]
    field_simp [hh.ne', hp]
  have htX : X q * (2 * tan q.1) = 2 * Z q * A := by
    rw [X, Z, tan_eq_sin_div_cos]
    change h q ^ 2 * A * (2 * (u q / h q)) = _
    field_simp [hh.ne']
  have htY : Y q * (2 * tan q.1) = 2 * Z q * B := by
    rw [Y, Z, tan_eq_sin_div_cos]
    change h q ^ 2 * B * (2 * (u q / h q)) = _
    field_simp [hh.ne']
  -- Keep the rational coefficients opaque in the quadratic algebra.
  have eRel : 2 * f * sq w + sq U + sq V - 4 * pair (A • U + B • V) w =
      h q ^ 2 * f / 2 * sq ℓ + h q ^ 2 * C * pair ℓ z -
        2 * X q * pair a ℓ - 2 * Y q * pair b ℓ +
        h q ^ 2 * (sq a + sq b) + 2 * (X q - Z q) * pair a z + 2 * Y q * pair b z +
        (u q ^ 2 - h q ^ 2 * C - h q ^ 2 * f / 2) * sq z := by
    rw [Hc₀]
    simp only [w, U, V, X, Y, Z, pair, sq, Complex.sq_norm, Complex.normSq_apply,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [eRel]
  have eDiv : bulk 0 q z a b aa ab + bulk 1 q z a b ab bb =
      -2 * X q * pair a ℓ - 2 * Y q * pair b ℓ +
        (h q ^ 2 - mixedComparisonDiagonal q) * (sq a + sq b) -
        2 * mixedComparisonOffDiagonal q * pair a b +
        2 * (X q - Z q) * pair a z + 2 * Y q * pair b z +
        (u q ^ 2 - h q ^ 2 * C) * sq z := by
    have ha : Xa q = (h q ^ 2 * (1 - C) - 2 * Z q * A) / 2 := by linarith only [hsum', Hd]
    have hb : Yb q = (h q ^ 2 * (1 - C) + 2 * Z q * A) / 2 := by linarith only [hsum', Hd]
    have hc : Ya q = mixedComparisonOffDiagonal q - 2 * Z q * B - Xb q := by linarith only [Hc]
    have hD' : mixedComparisonDiagonal q = h q ^ 2 + X q * (2 * tan q.1) := by
      rw [htX]
      exact hD
    simp only [bulk, S, T, M, Sd, Td, Md, one_ne_zero, ite_true, ite_false, Za, hD', ha, hb, hc,
      ← htX, ← htY, ℓ, pair, sq, Complex.sq_norm, Complex.normSq_apply,
      Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [eDiv]
  have hV : mixedComparisonPotential q = -(h q ^ 2 * f / 2) -
      h q ^ 2 * f / 2 * (C / f) ^ 2 := by
    change mixedComparisonPotential q + h q ^ 2 * f / 2 * (C / f) ^ 2 =
      -(h q ^ 2 * f / 2) at hP
    linarith only [hP]
  rw [hV]
  simp only [mixedGradientForm, sq, pair]
  ring

private theorem rellich_decomposition {ω : L2} (d : MixedQuotientData ω) :
    ∀ᵐ q ∂μ, mixedRellichDensity d q =
      mixedCompletionDensity d.phi d.jet q +
        (mixedSecondOrderDensity d.phi (d.jet [0]) (d.jet [1]) q +
          (bulkJet d 0 q + bulkJet d 1 q)) := by
  filter_upwards [cell_ae, nonzero_ae, d.laplace_eq, mixed_rellich_weak_symm d]
    with q hq hR hl hs
  obtain ⟨hh, _⟩ := cell_cos hq
  have hw : liftL2 ω (diagInv q) =
      (h q / 2 : ℝ) • (mixedWeightedLaplacian d.jet q - d.phi q) := by
    rw [hl, add_sub_cancel_right, Complex.real_smul, Complex.ofReal_div]
    change liftL2 ω (diagInv q) = (↑(h q) / ↑(2 : ℝ) : ℂ) *
      (2 * (liftL2 ω (diagInv q) / (h q : ℂ)))
    have hn : (h q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
    push_cast
    field_simp
  have he := div_algebra hq hR (d.phi q) (d.jet [0] q) (d.jet [1] q)
    (d.jet [0, 0] q) (d.jet [0, 1] q) (d.jet [1, 1] q)
  have hJ : bulkJet d 0 q + bulkJet d 1 q =
      bulk 0 q (d.phi q) (d.jet [0] q) (d.jet [1] q) (d.jet [0, 0] q) (d.jet [0, 1] q) +
      bulk 1 q (d.phi q) (d.jet [0] q) (d.jet [1] q) (d.jet [0, 1] q) (d.jet [1, 1] q) := by
    simp only [bulkJet, ← hs]
  have hU : d.streamA q = h q • d.jet [0] q - u q • d.phi q := rfl
  have hV : d.streamB q = h q • d.jet [1] q := rfl
  unfold mixedRellichDensity
  rw [hw, hU, hV, hJ, ← add_assoc]
  exact he

/-- Static completion, with integrability of the square (not a totalized
identity between potentially divergent integrals). -/
theorem mixed_completion {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedCompletionDensity d.phi d.jet) mixedOpenCell ∧
    IntegrableOn (mixedSecondOrderDensity d.phi (d.jet [0]) (d.jet [1])) mixedOpenCell ∧
    (∀ σ : Bool, IntegrableOn (fun a ↦ Real.cos a * ‖mixedEdgeValue 1 σ d.phi a‖ ^ 2)
      (Ioo (-Real.pi / 2) (Real.pi / 2))) ∧
    mixedStaticForm d = (∫ q in mixedOpenCell, mixedCompletionDensity d.phi d.jet q) +
      mixedSecondOrderForm d.phi (d.jet [0]) (d.jet [1]) (fun σ ↦ mixedEdgeValue 1 σ d.phi) := by
  obtain ⟨_, hR, hT, hEq⟩ := mixed_rellich d
  have hL := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo) d.weakJet
  have hD := mixed_density_integrable d.h2.memLp (hL [0] (by decide)) (hL [1] (by decide))
  have hE (σ : Bool) := mixed_edge_integrable d.continuous σ
  have hB := (bulk_integrable d 0).add (bulk_integrable d 1)
  have hDB := hD.add hB
  have hSq : IntegrableOn (mixedCompletionDensity d.phi d.jet) mixedOpenCell := by
    apply (hR.sub hDB).congr
    filter_upwards [rellich_decomposition d] with q hq
    change mixedRellichDensity d q - (mixedSecondOrderDensity d.phi (d.jet [0]) (d.jet [1]) q +
      (bulkJet d 0 q + bulkJet d 1 q)) = _
    rw [hq, add_sub_cancel_right]
  refine ⟨hSq, hD, hE, ?_⟩
  have hi := integral_congr_ae (rellich_decomposition d)
  change (∫ q, mixedRellichDensity d q ∂μ) =
    ∫ q, (mixedCompletionDensity d.phi d.jet +
      (mixedSecondOrderDensity d.phi (d.jet [0]) (d.jet [1]) +
        (bulkJet d 0 + bulkJet d 1))) q ∂μ at hi
  have hsplit := (integral_add hSq hDB).trans (congrArg
    (fun x ↦ (∫ q in mixedOpenCell, mixedCompletionDensity d.phi d.jet q) + x)
    (integral_add hD hB))
  have hi := hi.trans hsplit
  have hb := current_integral d
  have ht (σ : Bool) :
      (∫ x in I, cos x * (sq (deriv (mixedEdgeValue 1 σ d.phi) x) +
          sq (mixedEdgeValue 1 σ d.phi x))) =
        (∫ x in I, cos x * ‖deriv (mixedEdgeValue 1 σ d.phi) x‖ ^ 2) +
        ∫ x in I, cos x * ‖mixedEdgeValue 1 σ d.phi x‖ ^ 2 := by
    have h := integral_add (hT σ) (hE σ)
    simpa only [sq, mul_add, neg_div, Pi.add_apply] using h
  simp_rw [ht, Finset.sum_add_distrib] at hb
  rw [neg_div] at hEq
  change (∫ q, (bulkJet d 0 + bulkJet d 1) q ∂μ) = _ at hb
  rw [hEq, hi, hb, mixedSecondOrderForm]
  simp only [neg_div]
  ring

end NoEmbeddedEigenvalues
