import NoEmbeddedEigenvalues.CosineTraceHardy
import NoEmbeddedEigenvalues.MixedStaticForm

/-!
# The corrected Rellich current for the mixed sector

Subtract the signed trace-mass current before integration. The combined flux
has a bounded cosine ratio in its coefficients, and only the Neumann sides
contribute to the boundary integral.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology ENNReal

local notation "Plane" => ℝ × ℝ

/-- Rellich density, in diagonal measure (including the Cartesian Jacobian). -/
def mixedRellichDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  2 * mixedFieldCoeff q * ‖liftL2 ω (diagInv q)‖ ^ 2 +
    ‖d.streamA q‖ ^ 2 + ‖d.streamB q‖ ^ 2 -
    4 * ((mixedFieldA q • d.streamA q + mixedFieldB q • d.streamB q) *
      conj (liftL2 ω (diagInv q))).re

/-- Quadratic current in terms of the quotient and the two stream derivatives. -/
def mixedRellichCurrentOfStream (A B : ℝ) (f U V : ℂ) : Plane :=
  let D := ‖U‖ ^ 2 - ‖V‖ ^ 2 - ‖f‖ ^ 2
  let C := 2 * (U * conj V).re
  (A * D + B * C, -B * D + A * C)

private theorem mixed_rellich_pair_hasDerivAt {F G : ℝ → ℂ} {f g : ℂ} {t : ℝ}
    (hF : HasDerivAt F f t) (hG : HasDerivAt G g t) :
    HasDerivAt (fun x ↦ (F x * conj (G x)).re)
      (f * conj (G t) + F t * conj g).re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hF.mul (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hG))

private theorem mixed_rellich_norm_sq_hasDerivAt {F : ℝ → ℂ} {f : ℂ} {t : ℝ}
    (hF : HasDerivAt F f t) :
    HasDerivAt (fun x ↦ ‖F x‖ ^ 2) (2 * (f * conj (F t)).re) t := by
  simpa only [real_inner_eq_re_inner, RCLike.inner_apply,
    show (RCLike.re : ℂ → ℝ) = Complex.re from rfl] using hF.norm_sq

/-- The two sectional product rules for the corrected current. Only the
symmetry of the stream Hessian and equality of the diagonal field partials
are needed. The functions in the two directions may be different ACL
representatives, provided their values at the point coincide. -/
theorem mixed_rellich_current_product_rule {t s : ℝ}
    {A B : ℝ} {F U V Fa Fb Ua Ub Vb : ℂ} {diag offA offB : ℝ}
    {A₁ B₁ A₂ B₂ : ℝ → ℝ} {F₁ U₁ V₁ F₂ U₂ V₂ : ℝ → ℂ}
    (hA₁ : A₁ t = A) (hB₁ : B₁ t = B) (hA₂ : A₂ s = A) (hB₂ : B₂ s = B)
    (hF₁ : F₁ t = F) (hU₁ : U₁ t = U) (hV₁ : V₁ t = V)
    (hF₂ : F₂ s = F) (hU₂ : U₂ s = U) (hV₂ : V₂ s = V)
    (dA₁ : HasDerivAt A₁ diag t) (dB₁ : HasDerivAt B₁ offA t)
    (dA₂ : HasDerivAt A₂ offB s) (dB₂ : HasDerivAt B₂ diag s)
    (dF₁ : HasDerivAt F₁ Fa t) (dU₁ : HasDerivAt U₁ Ua t) (dV₁ : HasDerivAt V₁ Ub t)
    (dF₂ : HasDerivAt F₂ Fb s) (dU₂ : HasDerivAt U₂ Ub s) (dV₂ : HasDerivAt V₂ Vb s) :
    deriv (fun x ↦ (mixedRellichCurrentOfStream (A₁ x) (B₁ x) (F₁ x) (U₁ x) (V₁ x)).1) t +
      deriv (fun x ↦ (mixedRellichCurrentOfStream (A₂ x) (B₂ x) (F₂ x) (U₂ x) (V₂ x)).2) s =
    2 * (offA + offB) * (U * conj V).re +
      2 * ((A • U + B • V) * conj (Ua + Vb)).re -
      2 * ((A • Fa - B • Fb) * conj F).re := by
  have hD₁ := ((mixed_rellich_norm_sq_hasDerivAt dU₁).sub
    (mixed_rellich_norm_sq_hasDerivAt dV₁)).sub (mixed_rellich_norm_sq_hasDerivAt dF₁)
  have hD₂ := ((mixed_rellich_norm_sq_hasDerivAt dU₂).sub
    (mixed_rellich_norm_sq_hasDerivAt dV₂)).sub (mixed_rellich_norm_sq_hasDerivAt dF₂)
  have hC₁ := (mixed_rellich_pair_hasDerivAt dU₁ dV₁).const_mul 2
  have hC₂ := (mixed_rellich_pair_hasDerivAt dU₂ dV₂).const_mul 2
  have h₁ := (dA₁.mul hD₁).add (dB₁.mul hC₁)
  have h₂ := (dB₂.neg.mul hD₂).add (dA₂.mul hC₂)
  have e₁ : deriv (fun x ↦
      (mixedRellichCurrentOfStream (A₁ x) (B₁ x) (F₁ x) (U₁ x) (V₁ x)).1) t = _ := h₁.deriv
  have e₂ : deriv (fun x ↦
      (mixedRellichCurrentOfStream (A₂ x) (B₂ x) (F₂ x) (U₂ x) (V₂ x)).2) s = _ := h₂.deriv
  rw [e₁, e₂]
  simp only [Pi.neg_apply, Pi.sub_apply, hA₁, hB₁, hA₂, hB₂, hF₁, hU₁, hV₁, hF₂, hU₂, hV₂,
    Complex.real_smul, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The Rellich current minus the signed trace-mass current. The subtraction
must precede integration; the two currents need not have integrable edge fluxes
separately. -/
def mixedRellichCurrent (φ da db : Plane → ℂ) (q : Plane) : Plane :=
  let U := (Real.cos q.1 : ℂ) * da q - (Real.sin q.1 : ℂ) * φ q
  let V := (Real.cos q.1 : ℂ) * db q
  mixedRellichCurrentOfStream (mixedFieldA q) (mixedFieldB q) (φ q) U V

/-- The potentially singular parts of the two currents cancel. The quotient
`h / (h + k)` is bounded on the cell, and the remaining polynomial is quadratic
in the quotient and its gradient. -/
theorem mixed_rellich_current_factor (φ da db : Plane → ℂ) (q : Plane) :
    let h := Real.cos q.1
    let k := Real.cos q.2
    let u := Real.sin q.1
    let v := Real.sin q.2
    let D := h * (‖da q‖ ^ 2 - ‖db q‖ ^ 2 - ‖φ q‖ ^ 2) - 2 * u * (da q * conj (φ q)).re
    let C := 2 * (h * (da q * conj (db q)).re - u * (φ q * conj (db q)).re)
    mixedRellichCurrent φ da db q =
      (h / (h + k) * (u * D + v * C), h / (h + k) * (-v * D + u * C)) := by
  have hu := Real.sin_sq_add_cos_sq q.1
  simp only [mixedRellichCurrent, mixedRellichCurrentOfStream, mixedFieldA, mixedFieldB,
    Prod.mk.injEq,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  constructor
  · linear_combination Real.sin q.1 / (Real.cos q.1 + Real.cos q.2) *
      ((φ q).re ^ 2 + (φ q).im ^ 2) * hu
  · linear_combination -(Real.sin q.2 / (Real.cos q.1 + Real.cos q.2)) *
      ((φ q).re ^ 2 + (φ q).im ^ 2) * hu

/-- The factored current vanishes in the Dirichlet normal component. -/
theorem mixed_rellich_current_dirichlet (φ da db : Plane → ℂ) (σ : Bool) (b : ℝ) :
    (mixedRellichCurrent φ da db (cellEdgeNormal σ, b)).1 = 0 := by
  rw [mixed_rellich_current_factor]
  cases σ <;> simp [cellEdgeNormal, neg_div]

/-- Evaluate the corrected current on the Neumann side using the tangential
derivative and zero normal gradient. -/
theorem mixed_rellich_current_neumann (φ da db : Plane → ℂ) (σ : Bool) {a : ℝ}
    (ha : a ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) (hb : db (a, cellEdgeNormal σ) = 0) :
    let s : ℝ := if σ then 1 else -1
    let q := (a, cellEdgeNormal σ)
    s * (mixedRellichCurrent φ da db q).2 =
      Real.cos a * ‖φ q‖ ^ 2 + 2 * Real.sin a * (da q * conj (φ q)).re -
        Real.cos a * ‖da q‖ ^ 2 := by
  have hc : Real.cos a ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using ha)).ne'
  dsimp only
  rw [mixed_rellich_current_factor]
  dsimp only [Prod.fst, Prod.snd]
  cases σ <;> simp only [cellEdgeNormal, Bool.false_eq_true, ↓reduceIte, neg_div] at hb ⊢ <;>
    simp [hb, hc] <;> ring

/-- The integrable normal flux on a Neumann side after subtracting trace mass. -/
def mixedRellichEdgeDensity (T : ℝ → ℂ) (a : ℝ) : ℝ :=
  Real.cos a * ‖T a‖ ^ 2 + 2 * Real.sin a * (deriv T a * conj (T a)).re -
    Real.cos a * ‖deriv T a‖ ^ 2

/-- The corrected Neumann flux is the difference of the two corner masses
with their outward signs, minus the weighted tangential energy. -/
theorem mixed_rellich_edge_integral {T : ℝ → ℂ}
    (hT : AbsolutelyContinuousOnInterval T (-Real.pi / 2) (Real.pi / 2))
    (hD : MemLp (deriv T) 2 (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2)))) :
    IntegrableOn (fun a ↦ Real.cos a * ‖deriv T a‖ ^ 2) (Ioo (-Real.pi / 2) (Real.pi / 2)) ∧
    IntegrableOn (mixedRellichEdgeDensity T) (Ioo (-Real.pi / 2) (Real.pi / 2)) ∧
    (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), mixedRellichEdgeDensity T a) =
      ‖T (-Real.pi / 2)‖ ^ 2 + ‖T (Real.pi / 2)‖ ^ 2 -
        ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖deriv T a‖ ^ 2 := by
  let l := -Real.pi / 2
  let r := Real.pi / 2
  let I := Ioo l r
  let J : ℝ → ℝ := fun a ↦ Real.sin a * ‖T a‖ ^ 2
  have hlr : l < r := by dsimp [l, r]; linarith [Real.pi_pos]
  have hE : IntegrableOn (fun a ↦ Real.cos a * ‖deriv T a‖ ^ 2) I := by
    exact (hD.integrable_norm_pow (by decide)).bdd_mul
      Real.continuous_cos.aestronglyMeasurable
      (.of_forall fun a ↦ by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one a)
  have hJ : AbsolutelyContinuousOnInterval J l r := by
    have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval hT
    have hs : ContDiffOn ℝ 1 Real.sin (uIcc l r) := Real.contDiff_sin.contDiffOn
    simpa only [J, pow_two, Function.comp_apply] using
      hs.absolutelyContinuousOnInterval.fun_mul (hn.fun_mul hn)
  have he : mixedRellichEdgeDensity T =ᵐ[volume.restrict I]
      fun a ↦ deriv J a - Real.cos a * ‖deriv T a‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hT.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a hd ha
    have hn : HasDerivAt (fun y ↦ ‖T y‖ ^ 2) (2 * (deriv T a * conj (T a)).re) a := by
      simpa only [real_inner_eq_re_inner, RCLike.inner_apply,
        show (RCLike.re : ℂ → ℝ) = Complex.re from rfl] using
        (hd (Icc_subset_uIcc (Ioo_subset_Icc_self ha))).hasDerivAt.norm_sq
    have h := ((Real.hasDerivAt_sin a).mul hn).deriv
    change deriv J a = _ at h
    rw [h]
    unfold mixedRellichEdgeDensity
    ring
  have hi : IntegrableOn (deriv J) I := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlr.le).mp
      hJ.intervalIntegrable_deriv).mono_set Ioo_subset_Ioc_self
  refine ⟨hE, (hi.sub hE).congr he.symm, ?_⟩
  have h : (∫ a in I, deriv J a) = J r - J l := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlr.le]
    exact hJ.integral_deriv_eq_sub
  change (∫ a in I, mixedRellichEdgeDensity T a) =
    ‖T l‖ ^ 2 + ‖T r‖ ^ 2 - ∫ a in I, Real.cos a * ‖deriv T a‖ ^ 2
  rw [integral_congr_ae he, integral_sub hi hE, h]
  simp [J, l, r, neg_div, sub_eq_add_neg, add_comm]

/-- Zero normal traces control both cosine divisors on the full open cell. -/
theorem MixedQuotientData.memLp_normal_div_cos {ω : L2} (d : MixedQuotientData ω) :
    MemLp (fun q ↦ d.jet [0] q / (Real.cos q.1 : ℂ)) 2 (volume.restrict mixedOpenCell) ∧
    MemLp (fun q ↦ d.jet [1] q / (Real.cos q.2 : ℂ)) 2 (volume.restrict mixedOpenCell) := by
  have hpre : Prod.swap ⁻¹' mixedOpenCell = mixedOpenCell := by
    ext q
    exact and_comm
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hL (j : Fin 2) := d.h2.memLp_weakJet hU d.weakJet [j, j] (by simp)
  have h0 := (d.weakJet.2 [0] (by decide) 0).comp_swap_fst hU
  rw [hpre] at h0
  have hL0 := memLp_comp_swap hU.measurableSet (hL 0)
  rw [hpre] at hL0
  have hs := HasTransverseH1Trace.memLp_div_cos_snd
    (l := -Real.pi / 2) (r := Real.pi / 2)
    (F := d.jet [0] ∘ Prod.swap) (D := d.jet [0, 0] ∘ Prod.swap)
    (show HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) (-(Real.pi / 2)) (Real.pi / 2)
        (-(Real.pi / 2)) id (d.jet [0] ∘ Prod.swap) (fun _ ↦ 0) from by
      rw [← neg_div]
      exact d.normal_zero 0 false)
    (show HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) (-(Real.pi / 2)) (Real.pi / 2)
        (Real.pi / 2) id (d.jet [0] ∘ Prod.swap) (fun _ ↦ 0) from by
      rw [← neg_div]
      exact d.normal_zero 0 true)
    (by simpa only [mixedOpenCell, neg_div] using h0)
    (by simpa only [mixedOpenCell, neg_div] using hL0)
  have hs' : MemLp (fun q ↦ (d.jet [0] ∘ Prod.swap) q / (Real.cos q.2 : ℂ)) 2
      (volume.restrict mixedOpenCell) := by simpa only [mixedOpenCell, neg_div] using hs
  have ha := memLp_comp_swap hU.measurableSet hs'
  rw [hpre] at ha
  refine ⟨?_, ?_⟩
  · convert ha using 1
    funext q
    simp only [Function.comp_apply, Prod.swap_swap, Prod.snd_swap]
  · have hb := HasTransverseH1Trace.memLp_div_cos_snd
      (l := -Real.pi / 2) (r := Real.pi / 2) (F := d.jet [1]) (D := d.jet [1, 1])
      (by simpa only [HasMixedEdgeTrace, cellEdgeNormal, Bool.false_eq_true, ↓reduceIte,
        show axisTraceChart 1 = id from rfl, neg_div] using d.normal_zero 1 false)
      (by simpa only [HasMixedEdgeTrace, cellEdgeNormal, ↓reduceIte,
        show axisTraceChart 1 = id from rfl, neg_div] using d.normal_zero 1 true)
      (by simpa only [mixedOpenCell, neg_div] using d.weakJet.2 [1] (by decide) 1)
      (by simpa only [mixedOpenCell, neg_div] using hL 1)
    simpa only [mixedOpenCell, neg_div] using hb

/-- Separate integrability of the volume terms in the Rellich identity. -/
theorem mixed_rellich_volume_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    IntegrableOn (mixedRellichDensity d) mixedOpenCell ∧
    IntegrableOn (mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1])) mixedOpenCell := by
  let μ := volume.restrict mixedOpenCell
  let h : Plane → ℝ := fun q ↦ Real.cos q.1
  let k : Plane → ℝ := fun q ↦ Real.cos q.2
  let u : Plane → ℝ := fun q ↦ Real.sin q.1
  let v : Plane → ℝ := fun q ↦ Real.sin q.2
  let p : Plane → ℝ := fun q ↦ h q + k q
  let H : Plane → ℝ := fun q ↦ h q / p q
  let K : Plane → ℝ := fun q ↦ k q / p q
  let a := d.jet [0]
  let b := d.jet [1]
  let O := fun q ↦ liftL2 ω (diagInv q)
  let N := fun q ↦ O q / (h q : ℂ)
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hμ := ae_restrict_mem (μ := volume) hU.measurableSet
  have hpos (q : Plane) (hq : q ∈ mixedOpenCell) : 0 < h q ∧ 0 < k q :=
    ⟨Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1),
      Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)⟩
  have hbounded {c : Plane → ℝ} (hm : Measurable c)
      (hc : ∀ q ∈ mixedOpenCell, |c q| ≤ 1) : MemLp c ∞ μ :=
    memLp_top_of_bound hm.aestronglyMeasurable 1 (hμ.mono fun q hq ↦ by
      rw [Real.norm_eq_abs]
      exact hc q hq)
  have hh := hbounded (c := h) (by dsimp [h]; fun_prop) (fun _ _ ↦ Real.abs_cos_le_one _)
  have hu := hbounded (c := u) (by dsimp [u]; fun_prop) (fun _ _ ↦ Real.abs_sin_le_one _)
  have hv := hbounded (c := v) (by dsimp [v]; fun_prop) (fun _ _ ↦ Real.abs_sin_le_one _)
  have hH := hbounded (c := H) (by dsimp [H, p, h, k]; fun_prop) (fun q hq ↦ by
    obtain ⟨hh, hk⟩ := hpos q hq
    rw [abs_of_nonneg (div_nonneg hh.le (add_pos hh hk).le)]
    exact (div_le_one (add_pos hh hk)).2 (le_add_of_nonneg_right hk.le))
  have hK := hbounded (c := K) (by dsimp [K, p, h, k]; fun_prop) (fun q hq ↦ by
    obtain ⟨hh, hk⟩ := hpos q hq
    rw [abs_of_nonneg (div_nonneg hk.le (add_pos hh hk).le)]
    exact (div_le_one (add_pos hh hk)).2 (le_add_of_nonneg_left hh.le))
  have ha := d.h2.memLp_weakJet hU d.weakJet [0] (by decide)
  have hb := d.h2.memLp_weakJet hU d.weakJet [1] (by decide)
  have hf := d.h2.memLp
  have hN : MemLp N 2 μ := d.vorticity_divided
  have hA : MemLp d.streamA 2 μ := (hh.smul ha).sub (hu.smul hf)
  have hB : MemLp d.streamB 2 μ := hh.smul hb
  have hpair {f g : Plane → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      Integrable (fun q ↦ (f q * conj (g q)).re) μ := by
    have hgc : MemLp (fun q ↦ conj (g q)) 2 μ :=
      hg.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
        (.of_forall fun q ↦ (Complex.norm_conj (g q)).symm)
    exact Complex.reCLM.integrable_comp (hf.integrable_mul hgc)
  obtain ⟨hda, hdb⟩ := d.memLp_normal_div_cos
  have hbp : MemLp (fun q ↦ b q / (p q : ℂ)) 2 μ := by
    apply (hK.smul hdb).ae_eq
    filter_upwards [hμ] with q hq
    obtain ⟨hh, hk⟩ := hpos q hq
    change K q • (b q / (k q : ℂ)) = b q / (p q : ℂ)
    simp only [Complex.real_smul, K, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr hk.ne']
  have hMass : IntegrableOn (mixedTraceMassDensity d.phi a b) mixedOpenCell := by
    apply ((hpair ((hu.smul (r := 2) (hH.smul (r := 2) hda)).sub
      (hv.smul (r := 2) (hK.smul (r := 2) hdb))) hf).const_mul 2).congr
    filter_upwards [hμ] with q hq
    obtain ⟨hh, hk⟩ := hpos q hq
    have he (c z : ℝ) (hz : z ≠ 0) (w : ℂ) :
        c • ((z / p q) • (w / (z : ℂ))) = (c / p q) • w := by
      simp only [Complex.real_smul, Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr hz]
    simp only [mixedTraceMassDensity, Pi.sub_apply, Pi.smul_apply']
    rw [show H q = h q / p q from rfl, show K q = k q / p q from rfl,
      he _ _ hh.ne', he _ _ hk.ne']
    rfl
  have hOmega : Integrable (fun q ↦ 2 * mixedFieldCoeff q * ‖O q‖ ^ 2) μ := by
    have hNu := hH.smul (r := 2) (hu.smul (r := 2) hN)
    have hNv := hH.smul (r := 2) (hv.smul (r := 2) hN)
    have hi := (hNu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add
      (hNv.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    apply (hi.const_mul 2).congr
    filter_upwards [hμ] with q hq
    have hh := (hpos q hq).1
    have hp := add_pos hh (hpos q hq).2
    simp only [Pi.add_apply, Pi.smul_apply', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      mixedFieldCoeff, N, norm_div, Complex.norm_real, div_pow]
    dsimp only [H, p, u, v, h, k] at *
    field_simp [hp.ne', hh.ne']
  have hCross : Integrable (fun q ↦
      2 * mixedFieldMatrixOffDiagonal q * (d.streamA q * conj (d.streamB q)).re) μ := by
    apply ((hpair hA (hH.smul (hu.smul (r := 2) (hv.smul (r := 2) hbp)))).const_mul 4).congr
    filter_upwards [hμ] with q hq
    have he : H q • u q • v q • (b q / (p q : ℂ)) =
        (u q * v q / p q ^ 2) • d.streamB q := by
      simp only [MixedQuotientData.streamB, H, Complex.real_smul, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_pow]
      change _ * (_ * (_ * _)) = _ * ((h q : ℂ) * b q)
      ring
    simp only [Pi.smul_apply']
    rw [he]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
    have he' : d.streamA q * ((↑(u q * v q / p q ^ 2) : ℂ) * conj (d.streamB q)) =
        (↑(u q * v q / p q ^ 2) : ℂ) * (d.streamA q * conj (d.streamB q)) := by ring
    rw [he', Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp only [mixedFieldMatrixOffDiagonal, p, h, k, u, v]
    ring
  have hW : Integrable (fun q ↦
      4 * ((mixedFieldA q • d.streamA q + mixedFieldB q • d.streamB q) * conj (O q)).re) μ := by
    apply ((hpair (hH.smul ((hu.smul (r := 2) hA).add (hv.smul (r := 2) hB)))
      hN).const_mul 4).congr
    filter_upwards [hμ] with q hq
    obtain ⟨hh, hk⟩ := hpos q hq
    have hp : p q ≠ 0 := (add_pos hh hk).ne'
    have he : H q • (u q • d.streamA q + v q • d.streamB q) * conj (N q) =
        (mixedFieldA q • d.streamA q + mixedFieldB q • d.streamB q) * conj (O q) := by
      simp only [N, Complex.real_smul, map_div₀, Complex.conj_ofReal, H, mixedFieldA,
        mixedFieldB, ← show p q = Real.cos q.1 + Real.cos q.2 from rfl,
        ← show u q = Real.sin q.1 from rfl, ← show v q = Real.sin q.2 from rfl, Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr hh.ne', Complex.ofReal_ne_zero.mpr hp]
    simpa only [Pi.smul_apply', Pi.add_apply] using congrArg (fun z : ℂ ↦ 4 * z.re) he
  have hAA := hA.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hBB := hB.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  refine ⟨?_, ?_, hMass⟩
  · exact (hOmega.add ((hAA.add hBB).add hCross)).congr
      (.of_forall fun q ↦ by simp [mixedVirialDensity, mixedGradientForm, O])
  · exact (((hOmega.add hAA).add hBB).sub hW).congr (.of_forall fun _ ↦ rfl)

private theorem mixed_rellich_field_partials {q : Plane} (hq : q ∈ mixedOpenCell) :
    let m := (mixedFieldCoeff q + 1) / 2
    let n := mixedFieldMatrixOffDiagonal q / 2
    HasDerivAt (fun x ↦ mixedFieldA (x, q.2)) m q.1 ∧
    HasDerivAt (fun x ↦ mixedFieldB (x, q.2)) n q.1 ∧
    HasDerivAt (fun y ↦ mixedFieldA (q.1, y)) n q.2 ∧
    HasDerivAt (fun y ↦ mixedFieldB (q.1, y)) m q.2 := by
  have h := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)
  have k := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)
  have hp := (add_pos h k).ne'
  have hx := ((Real.hasDerivAt_cos q.1).add_const (Real.cos q.2))
  have hy := ((Real.hasDerivAt_cos q.2).const_add (Real.cos q.1))
  have ha := (Real.hasDerivAt_sin q.1).div hx hp
  have hb := (hasDerivAt_const q.1 (Real.sin q.2)).div hx hp
  have hc := (hasDerivAt_const q.2 (Real.sin q.1)).div hy hp
  have hd := (Real.hasDerivAt_sin q.2).div hy hp
  refine ⟨ha.congr_deriv ?_, hb.congr_deriv ?_, hc.congr_deriv ?_, hd.congr_deriv ?_⟩ <;>
    simp only [mixedFieldCoeff, mixedFieldMatrixOffDiagonal, zero_mul]
  · field_simp [hp]
    nlinarith [Real.sin_sq_add_cos_sq q.1, Real.sin_sq_add_cos_sq q.2]
  · ring
  · ring
  · field_simp [hp]
    nlinarith [Real.sin_sq_add_cos_sq q.1, Real.sin_sq_add_cos_sq q.2]

/-- Commutation of the weak mixed derivatives, obtained by testing twice. -/
private theorem mixed_rellich_weak_symm {ω : L2} (d : MixedQuotientData ω) :
    d.jet [0, 1] =ᵐ[volume.restrict mixedOpenCell] d.jet [1, 0] := by
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have h0 := d.weakJet.2 [] (by decide) 0
  have h1 := d.weakJet.2 [] (by decide) 1
  have h01 := d.weakJet.2 [1] (by decide) 0
  have h10 := d.weakJet.2 [0] (by decide) 1
  apply (ae_restrict_iff' hU.measurableSet).mpr
  have he := ae_eq_zero_of_forall_test hU (h01.2.1.sub h10.2.1) fun φ hφ ↦ by
    have ht (j : Fin 2) : IsTestFunctionOn mixedOpenCell (coordPartial j φ) :=
      ⟨by
        have hd := hφ.contDiff.differentiable (by simp)
        have hf := hφ.contDiff.fderiv_right (m := (↑(⊤ : ℕ∞))) (by simp)
        unfold coordPartial
        split_ifs
        · rw [show partialX φ = _ from funext fun q ↦ partialX_eq_fderiv (hd q)]
          exact hf.clm_apply contDiff_const
        · rw [show partialY φ = _ from funext fun q ↦ partialY_eq_fderiv (hd q)]
          exact hf.clm_apply contDiff_const,
        hφ.hasCompactSupport_coordPartial j,
        (tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset⟩
    have hs : coordPartial 1 (coordPartial 0 φ) = coordPartial 0 (coordPartial 1 φ) := by
      have h2 : ContDiff ℝ 2 φ := hφ.contDiff.of_le (by simp)
      have hd := h2.differentiable (by decide)
      have hf := (h2.fderiv_right (m := 1) (by decide)).differentiable (by decide)
      have hx : partialX φ = fun q ↦ fderiv ℝ φ q (1, 0) :=
        funext fun q ↦ partialX_eq_fderiv (hd q)
      have hy : partialY φ = fun q ↦ fderiv ℝ φ q (0, 1) :=
        funext fun q ↦ partialY_eq_fderiv (hd q)
      funext q
      change partialY (partialX φ) q = partialX (partialY φ) q
      rw [hx, hy, partialY_eq_fderiv ((hf q).clm_apply (differentiableAt_const _)),
        partialX_eq_fderiv ((hf q).clm_apply (differentiableAt_const _)),
        fderiv_clm_apply (hf q) (differentiableAt_const _),
        fderiv_clm_apply (hf q) (differentiableAt_const _)]
      simpa using (h2.contDiffAt (x := q)).isSymmSndFDerivAt
        (by norm_num [minSmoothness]) (0, 1) (1, 0)
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub
      (integrable_mul_of_tsupport_subset h01.2.1 hφ.contDiff.continuous
        hφ.hasCompactSupport hφ.tsupport_subset)
      (integrable_mul_of_tsupport_subset h10.2.1 hφ.contDiff.continuous
        hφ.hasCompactSupport hφ.tsupport_subset),
      ← neg_neg (∫ p, d.jet [0, 1] p * φ p), ← h01.2.2 φ hφ,
      ← neg_neg (∫ p, d.jet [1, 0] p * φ p), ← h10.2.2 φ hφ,
      ← neg_neg (∫ p, d.jet [1] p * coordPartial 0 φ p), ← h1.2.2 _ (ht 0),
      ← neg_neg (∫ p, d.jet [0] p * coordPartial 1 φ p), ← h0.2.2 _ (ht 1), hs]
    simp
  filter_upwards [he] with q hq hmem
  exact sub_eq_zero.mp (hq hmem)

/-- The corrected divergence on two intersecting sections, with their
values and first derivatives supplied by the specified jet at the crossing. -/
theorem mixed_rellich_section_divergence {ω : L2} (d : MixedQuotientData ω)
    {q : Plane} (hq : q ∈ mixedOpenCell)
    (hsym : d.jet [0, 1] q = d.jet [1, 0] q)
    (hlap : mixedWeightedLaplacian d.jet q =
      2 * (liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)) + d.phi q)
    {F₁ A₁ B₁ F₂ A₂ B₂ : ℝ → ℂ}
    (hF₁ : F₁ q.1 = d.phi q) (hA₁ : A₁ q.1 = d.jet [0] q) (hB₁ : B₁ q.1 = d.jet [1] q)
    (hF₂ : F₂ q.2 = d.phi q) (hA₂ : A₂ q.2 = d.jet [0] q) (hB₂ : B₂ q.2 = d.jet [1] q)
    (dF₁ : HasDerivAt F₁ (d.jet [0] q) q.1)
    (dA₁ : HasDerivAt A₁ (d.jet [0, 0] q) q.1)
    (dB₁ : HasDerivAt B₁ (d.jet [0, 1] q) q.1)
    (dF₂ : HasDerivAt F₂ (d.jet [1] q) q.2)
    (dA₂ : HasDerivAt A₂ (d.jet [1, 0] q) q.2)
    (dB₂ : HasDerivAt B₂ (d.jet [1, 1] q) q.2) :
    deriv (fun x ↦ (mixedRellichCurrent (fun _ ↦ F₁ x) (fun _ ↦ A₁ x) (fun _ ↦ B₁ x)
      (x, q.2)).1) q.1 +
    deriv (fun y ↦ (mixedRellichCurrent (fun _ ↦ F₂ y) (fun _ ↦ A₂ y) (fun _ ↦ B₂ y)
      (q.1, y)).2) q.2 =
    mixedVirialDensity d q - mixedRellichDensity d q -
      mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q := by
  let h := Real.cos q.1
  let u := Real.sin q.1
  have hh : h ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)).ne'
  have hc (x : ℝ) : HasDerivAt (fun y ↦ (Real.cos y : ℂ)) (-(Real.sin x : ℂ)) x := by
    have e : HasDerivAt (fun y ↦ (Real.cos y : ℂ)) ((-Real.sin x : ℝ) : ℂ) x :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_cos x)
    rwa [Complex.ofReal_neg] at e
  have hu (x : ℝ) : HasDerivAt (fun y ↦ (Real.sin y : ℂ)) (Real.cos x : ℂ) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_sin x)
  let U₁ := fun x ↦ (Real.cos x : ℂ) * A₁ x - (Real.sin x : ℂ) * F₁ x
  let V₁ := fun x ↦ (Real.cos x : ℂ) * B₁ x
  let U₂ := fun y ↦ (h : ℂ) * A₂ y - (u : ℂ) * F₂ y
  let V₂ := fun y ↦ (h : ℂ) * B₂ y
  let aa := (h : ℂ) * d.jet [0, 0] q - 2 * (u : ℂ) * d.jet [0] q - (h : ℂ) * d.phi q
  let ab := (h : ℂ) * d.jet [0, 1] q - (u : ℂ) * d.jet [1] q
  let bb := (h : ℂ) * d.jet [1, 1] q
  have dU₁ : HasDerivAt U₁ aa q.1 := by
    apply (((hc q.1).mul dA₁).sub ((hu q.1).mul dF₁)).congr_deriv
    rw [hA₁, hF₁]
    dsimp only [aa, h, u]
    ring
  have dV₁ : HasDerivAt V₁ ab q.1 := by
    exact ((hc q.1).mul dB₁).congr_deriv (by rw [hB₁]; dsimp [ab, h, u]; ring)
  have dU₂ : HasDerivAt U₂ ab q.2 := by
    exact ((dA₂.const_mul (h : ℂ)).sub (dF₂.const_mul (u : ℂ))).congr_deriv
      (by rw [← hsym])
  have dV₂ : HasDerivAt V₂ bb q.2 := dB₂.const_mul _
  obtain ⟨hx, hy, hz, hw⟩ := mixed_rellich_field_partials hq
  have he := mixed_rellich_current_product_rule
    (A₁ := fun x ↦ mixedFieldA (x, q.2)) (B₁ := fun x ↦ mixedFieldB (x, q.2))
    (A₂ := fun y ↦ mixedFieldA (q.1, y)) (B₂ := fun y ↦ mixedFieldB (q.1, y))
    (t := q.1) (s := q.2) rfl rfl rfl rfl hF₁
    (show U₁ q.1 = d.streamA q by simp [U₁, MixedQuotientData.streamA, hA₁, hF₁])
    (show V₁ q.1 = d.streamB q by simp [V₁, MixedQuotientData.streamB, hB₁])
    hF₂ (show U₂ q.2 = d.streamA q by simp [U₂, MixedQuotientData.streamA, h, u, hA₂, hF₂])
    (show V₂ q.2 = d.streamB q by simp [V₂, MixedQuotientData.streamB, h, hB₂])
    hx hy hz hw dF₁ dU₁ dV₁ dF₂ dU₂ dV₂
  have hl : aa + bb = 2 * liftL2 ω (diagInv q) := by
    have e := congrArg (fun z : ℂ ↦ (h : ℂ) * z) hlap
    simp only [mixedWeightedLaplacian, Complex.real_smul, Real.tan_eq_sin_div_cos,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat] at e
    change (h : ℂ) * (d.jet [0, 0] q + d.jet [1, 1] q -
      2 * ((u : ℂ) / (h : ℂ)) * d.jet [0] q) =
      (h : ℂ) * (2 * (liftL2 ω (diagInv q) / (h : ℂ)) + d.phi q) at e
    have hc := Complex.ofReal_ne_zero.mpr hh
    field_simp [hc] at e
    dsimp only [aa, bb]
    linear_combination e
  rw [hl] at he
  change (deriv (fun x ↦
      (mixedRellichCurrentOfStream (mixedFieldA (x, q.2)) (mixedFieldB (x, q.2))
        (F₁ x) (U₁ x) (V₁ x)).1) q.1 + deriv (fun y ↦
      (mixedRellichCurrentOfStream (mixedFieldA (q.1, y)) (mixedFieldB (q.1, y))
        (F₂ y) (U₂ y) (V₂ y)).2) q.2) = _
  rw [he]
  simp only [mixedVirialDensity, mixedGradientForm, mixedRellichDensity, mixedTraceMassDensity,
    one_mul, map_mul, map_ofNat, Complex.mul_re, Complex.mul_im]
  norm_num
  ring

/-- On a fixed regular normal section the corrected current is absolutely
continuous up to both endpoints. The tangential cosine stays positive there,
so this step needs no bound uniform in the tangential coordinate. -/
theorem mixed_rellich_normal_section_ac (j : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) {F A B : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F (-Real.pi / 2) (Real.pi / 2))
    (hA : AbsolutelyContinuousOnInterval A (-Real.pi / 2) (Real.pi / 2))
    (hB : AbsolutelyContinuousOnInterval B (-Real.pi / 2) (Real.pi / 2)) :
    let J := fun t ↦ mixedRellichCurrent (fun _ ↦ F t) (fun _ ↦ A t) (fun _ ↦ B t)
      (axisTraceChart j (x, t))
    AbsolutelyContinuousOnInterval (if j = 0 then fun t ↦ (J t).1 else fun t ↦ (J t).2)
      (-Real.pi / 2) (Real.pi / 2) := by
  let l := -Real.pi / 2
  let r := Real.pi / 2
  let q := fun t ↦ axisTraceChart j (x, t)
  let h := fun t ↦ Real.cos (q t).1
  let k := fun t ↦ Real.cos (q t).2
  let u := fun t ↦ Real.sin (q t).1
  let v := fun t ↦ Real.sin (q t).2
  have hlr : l < r := by dsimp [l, r]; linarith [Real.pi_pos]
  have hc : ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      ContDiff ℝ 1 (fun t ↦ f (q t).1) ∧ ContDiff ℝ 1 (fun t ↦ f (q t).2) := by
    intro f hf
    fin_cases j
    · change ContDiff ℝ 1 f ∧ ContDiff ℝ 1 (fun _ : ℝ ↦ f x)
      exact ⟨hf, contDiff_const⟩
    · change ContDiff ℝ 1 (fun _ : ℝ ↦ f x) ∧ ContDiff ℝ 1 f
      exact ⟨contDiff_const, hf⟩
  obtain ⟨hh, hk⟩ := hc _ Real.contDiff_cos
  obtain ⟨hu, hv⟩ := hc _ Real.contDiff_sin
  have hp : ∀ t ∈ uIcc l r, h t + k t ≠ 0 := by
    intro t ht
    have ht' : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [uIcc_of_le hlr.le] at ht
      simpa only [l, r, neg_div] using ht
    have h₁ := Real.cos_nonneg_of_mem_Icc ht'
    have h₂ := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hx)
    fin_cases j
    · exact (add_pos_of_nonneg_of_pos h₁ h₂).ne'
    · exact (add_pos_of_pos_of_nonneg h₂ h₁).ne'
  have ha : AbsolutelyContinuousOnInterval (fun t ↦ mixedFieldA (q t)) l r :=
    (hu.contDiffOn.div (hh.add hk).contDiffOn hp).absolutelyContinuousOnInterval
  have hb : AbsolutelyContinuousOnInterval (fun t ↦ mixedFieldB (q t)) l r :=
    (hv.contDiffOn.div (hh.add hk).contDiffOn hp).absolutelyContinuousOnInterval
  have prof {Z : ℝ → ℂ} (hZ : AbsolutelyContinuousOnInterval Z l r) :
      AbsolutelyContinuousOnInterval (fun t ↦ (Z t).re) l r ∧
      AbsolutelyContinuousOnInterval (fun t ↦ (Z t).im) l r := by
    exact ⟨Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hZ,
      Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hZ⟩
  obtain ⟨hFr, hFi⟩ := prof hF
  obtain ⟨hAr, hAi⟩ := prof hA
  obtain ⟨hBr, hBi⟩ := prof hB
  have hhc := hh.contDiffOn (s := uIcc l r) |>.absolutelyContinuousOnInterval
  have huc := hu.contDiffOn (s := uIcc l r) |>.absolutelyContinuousOnInterval
  have hUr := (hhc.fun_mul hAr).sub (huc.fun_mul hFr)
  have hUi := (hhc.fun_mul hAi).sub (huc.fun_mul hFi)
  have hVr := hhc.fun_mul hBr
  have hVi := hhc.fun_mul hBi
  have hD := (((hUr.fun_mul hUr).add (hUi.fun_mul hUi)).sub
    ((hVr.fun_mul hVr).add (hVi.fun_mul hVi))).sub
    ((hFr.fun_mul hFr).add (hFi.fun_mul hFi))
  have hC := (LipschitzWith.const (2 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    |>.fun_mul ((hUr.fun_mul hVr).add (hUi.fun_mul hVi))
  dsimp only
  split_ifs
  · apply ((ha.fun_mul hD).add (hb.fun_mul hC)).congr
    intro t _
    simp only [mixedRellichCurrent, mixedRellichCurrentOfStream, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Pi.add_apply,
      Pi.sub_apply, zero_mul, sub_zero, q]
    ring
  · apply ((hb.neg.fun_mul hD).add (ha.fun_mul hC)).congr
    intro t _
    simp only [mixedRellichCurrent, mixedRellichCurrentOfStream, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, zero_mul, sub_zero, q]
    ring

/-- Sectionwise FTC for the corrected current, with endpoint values taken
from continuous section representatives. -/
theorem mixed_rellich_normal_section_integral (j : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) {F A B : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F (-Real.pi / 2) (Real.pi / 2))
    (hA : AbsolutelyContinuousOnInterval A (-Real.pi / 2) (Real.pi / 2))
    (hB : AbsolutelyContinuousOnInterval B (-Real.pi / 2) (Real.pi / 2))
    (hzero : j = 1 → ∀ σ : Bool, B (cellEdgeNormal σ) = 0)
    {P : ℝ → ℝ} (hP :
      let J := fun t ↦ mixedRellichCurrent (fun _ ↦ F t) (fun _ ↦ A t) (fun _ ↦ B t)
        (axisTraceChart j (x, t))
      P =ᵐ[volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2))]
        deriv (if j = 0 then fun t ↦ (J t).1 else fun t ↦ (J t).2)) :
    (∫ t in Ioo (-Real.pi / 2) (Real.pi / 2), P t) =
      if j = 0 then 0 else
        ∑ σ : Bool, (Real.cos x * ‖F (cellEdgeNormal σ)‖ ^ 2 +
          2 * Real.sin x * (A (cellEdgeNormal σ) * conj (F (cellEdgeNormal σ))).re -
          Real.cos x * ‖A (cellEdgeNormal σ)‖ ^ 2) := by
  let l := -Real.pi / 2
  let r := Real.pi / 2
  let J := fun t ↦ mixedRellichCurrent (fun _ ↦ F t) (fun _ ↦ A t) (fun _ ↦ B t)
    (axisTraceChart j (x, t))
  let N := if j = 0 then fun t ↦ (J t).1 else fun t ↦ (J t).2
  have hlr : l < r := by dsimp [l, r]; linarith [Real.pi_pos]
  have hac : AbsolutelyContinuousOnInterval N l r := mixed_rellich_normal_section_ac j hx hF hA hB
  have hi : (∫ t in Ioo l r, P t) = N r - N l := by
    rw [integral_congr_ae hP, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hlr.le]
    exact hac.integral_deriv_eq_sub
  rw [hi]
  fin_cases j
  · change (mixedRellichCurrent _ _ _ (r, x)).1 - (mixedRellichCurrent _ _ _ (l, x)).1 = 0
    change (mixedRellichCurrent _ _ _ (cellEdgeNormal true, x)).1 -
      (mixedRellichCurrent _ _ _ (cellEdgeNormal false, x)).1 = 0
    rw [mixed_rellich_current_dirichlet, mixed_rellich_current_dirichlet, sub_self]
  · have he (σ : Bool) := mixed_rellich_current_neumann
      (fun _ ↦ F (cellEdgeNormal σ)) (fun _ ↦ A (cellEdgeNormal σ))
      (fun _ ↦ B (cellEdgeNormal σ)) σ hx (hzero rfl σ)
    have ht := he true
    have hf := he false
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, cellEdgeNormal] at ht hf
    change (mixedRellichCurrent _ _ _ (x, r)).2 - (mixedRellichCurrent _ _ _ (x, l)).2 =
      ∑ σ : Bool, (Real.cos x * ‖F (cellEdgeNormal σ)‖ ^ 2 +
        2 * Real.sin x * (A (cellEdgeNormal σ) * conj (F (cellEdgeNormal σ))).re -
        Real.cos x * ‖A (cellEdgeNormal σ)‖ ^ 2)
    simp only [Fintype.sum_bool, cellEdgeNormal, l, r, Bool.false_eq_true, ↓reduceIte]
    linarith only [ht, hf]

/-- The corner denominator of the adapted field in diagonal coordinates. -/
def mixedRellichDenominator (q : Plane) : ℝ := Real.cos q.1 + Real.cos q.2

private theorem rellichP_pos {q : Plane} (hq : q ∈ mixedOpenCell) : 0 < mixedRellichDenominator q :=
  add_pos (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))

private theorem rellich_memLp_div_p {F : Plane → ℂ} (j : Fin 2)
    (hF : MemLp (fun q ↦ F q / (Real.cos (if j = 0 then q.1 else q.2) : ℂ))
      2 (volume.restrict mixedOpenCell)) :
    MemLp (fun q ↦ F q / (mixedRellichDenominator q : ℂ)) 2 (volume.restrict mixedOpenCell) := by
  let c := fun q : Plane ↦ Real.cos (if j = 0 then q.1 else q.2)
  let w := fun q ↦ c q / mixedRellichDenominator q
  have hμ := ae_restrict_mem (μ := volume) (s := mixedOpenCell)
    (measurableSet_Ioo.prod measurableSet_Ioo)
  have hc (q : Plane) (hq : q ∈ mixedOpenCell) :
      0 < c q ∧ c q ≤ mixedRellichDenominator q := by
    have ha := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)
    have hb := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)
    dsimp only [c, mixedRellichDenominator]
    split_ifs
    · exact ⟨ha, le_add_of_nonneg_right hb.le⟩
    · exact ⟨hb, le_add_of_nonneg_left ha.le⟩
  have hw : MemLp w ∞ (volume.restrict mixedOpenCell) := by
    have hm : Measurable w := by
      dsimp [w, c, mixedRellichDenominator]
      split_ifs <;> fun_prop
    apply memLp_top_of_bound hm.aestronglyMeasurable 1
    filter_upwards [hμ] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hc q hq).1.le (rellichP_pos hq).le)]
    exact (div_le_one (rellichP_pos hq)).2 (hc q hq).2
  apply (hw.smul (r := 2) hF).ae_eq
  filter_upwards [hμ] with q hq
  change w q • (F q / (c q : ℂ)) = F q / (mixedRellichDenominator q : ℂ)
  simp only [w, Complex.real_smul, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr (hc q hq).1.ne']

/-- Both first weak partials divided by the corner denominator are in L².
Only the two zero normal traces, not corner regularity, are needed. -/
theorem MixedQuotientData.memLp_partials_div_corner {ω : L2} (d : MixedQuotientData ω) :
    MemLp (fun q ↦ d.jet [0] q / (mixedRellichDenominator q : ℂ)) 2
      (volume.restrict mixedOpenCell) ∧
    MemLp (fun q ↦ d.jet [1] q / (mixedRellichDenominator q : ℂ)) 2
      (volume.restrict mixedOpenCell) := by
  obtain ⟨ha, hb⟩ := d.memLp_normal_div_cos
  exact ⟨rellich_memLp_div_p 0 ha, rellich_memLp_div_p 1 hb⟩

/-- Integrable representatives of the separate normal derivatives of the
corrected current, together with the ACL sections on which they are computed.
Only the Neumann endpoint values need to be identified explicitly. -/
def MixedRellichNormalDerivative {ω : L2} (d : MixedQuotientData ω)
    (j : Fin 2) (P : Plane → ℝ) : Prop :=
  let l := -Real.pi / 2
  let r := Real.pi / 2
  let I := Ioo l r
  IntegrableOn P mixedOpenCell ∧
    ∀ᵐ x ∂volume.restrict I, ∃ F A B : ℝ → ℂ,
      let J := fun t ↦ mixedRellichCurrent (fun _ ↦ F t) (fun _ ↦ A t) (fun _ ↦ B t)
        (axisTraceChart j (x, t))
      AbsolutelyContinuousOnInterval F l r ∧
      AbsolutelyContinuousOnInterval A l r ∧
      AbsolutelyContinuousOnInterval B l r ∧
      (j = 1 → ∀ σ : Bool,
        F (cellEdgeNormal σ) = mixedEdgeValue 1 σ d.phi x ∧
        A (cellEdgeNormal σ) = deriv (mixedEdgeValue 1 σ d.phi) x ∧
        B (cellEdgeNormal σ) = 0) ∧
      (fun t ↦ P (axisTraceChart j (x, t))) =ᵐ[volume.restrict I]
        deriv (if j = 0 then fun t ↦ (J t).1 else fun t ↦ (J t).2)

/-- Lift the two sectional derivatives to integrable bulk representatives.
The only weights needed for the lift are the bounded ratio `h/(h+k)`
and the divided first partials. -/
theorem mixed_rellich_integrable_sections {ω : L2} (d : MixedQuotientData ω) :
    ∃ P Q, MixedRellichNormalDerivative d 0 P ∧ MixedRellichNormalDerivative d 1 Q ∧
      ∀ᵐ q ∂volume.restrict mixedOpenCell,
        P q + Q q = mixedVirialDensity d q - mixedRellichDensity d q -
          mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q := by
  sorry

/-- Sobolev flux identity for the corrected Rellich current. Integrate the
combined divergence, so no separate corner flux for either singular summand
has to be assigned. The zero Dirichlet flux is omitted from the right side. -/
theorem mixed_rellich_current_integral {ω : L2} (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, mixedVirialDensity d q - mixedRellichDensity d q -
        mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) =
      ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
        mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a := by
  let I := Ioo (-Real.pi / 2) (Real.pi / 2)
  let μ := volume.restrict I
  obtain ⟨P, Q, ⟨hP, hPs⟩, ⟨hQ, hQs⟩, he⟩ := mixed_rellich_integrable_sections d
  have hprod : μ.prod μ = volume.restrict mixedOpenCell := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hP' : Integrable P (μ.prod μ) := hprod.symm ▸ hP
  have hQ' : Integrable Q (μ.prod μ) := hprod.symm ▸ hQ
  rw [integral_congr_ae (he.mono fun _ h ↦ h.symm), integral_add hP hQ,
    ← hprod, integral_prod_symm P hP', integral_prod Q hQ']
  have hI := ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo
  have h0 : (fun x ↦ ∫ t in I, P (t, x)) =ᵐ[μ] 0 := by
    filter_upwards [hPs, hI] with x hx hm
    obtain ⟨F, A, B, hF, hA, hB, _, hd⟩ := hx
    exact mixed_rellich_normal_section_integral 0 hm hF hA hB
      (fun h ↦ absurd h (by decide)) hd
  have h1 : (fun x ↦ ∫ t in I, Q (x, t)) =ᵐ[μ]
      fun x ↦ ∑ σ : Bool, mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) x := by
    filter_upwards [hQs, hI] with x hx hm
    obtain ⟨F, A, B, hF, hA, hB, hT, hd⟩ := hx
    have h := mixed_rellich_normal_section_integral 1 hm hF hA hB
      (fun _ σ ↦ (hT rfl σ).2.2) hd
    change (∫ t in I, Q (x, t)) = _ at h
    rw [h]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
    apply Finset.sum_congr rfl
    intro σ _
    rw [(hT rfl σ).1, (hT rfl σ).2.1]
    rfl
  change (∫ x in I, ∫ t in I, P (t, x)) + (∫ x in I, ∫ t in I, Q (x, t)) = _
  rw [integral_congr_ae h0, integral_congr_ae h1, Pi.zero_def, integral_zero, zero_add]
  rw [integral_finsetSum]
  intro σ _
  obtain ⟨hT, hD⟩ := mixed_quotient_edge_h1 d σ
  exact (mixed_rellich_edge_integral (T := mixedEdgeValue 1 σ d.phi) hT hD).2.1

/-- The Rellich identity removes the corner masses from the static form. -/
theorem mixed_rellich {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    IntegrableOn (mixedRellichDensity d) mixedOpenCell ∧
    (∀ σ : Bool, IntegrableOn
      (fun a ↦ Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2)
      (Ioo (-Real.pi / 2) (Real.pi / 2))) ∧
    mixedStaticForm d = (∫ q in mixedOpenCell, mixedRellichDensity d q) -
      ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
        Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2 := by
  obtain ⟨hV, hR, hM⟩ := mixed_rellich_volume_integrable d
  have hEdge (σ : Bool) := mixed_quotient_edge_h1 d σ
  have hFTC (σ : Bool) :=
    mixed_rellich_edge_integral (T := mixedEdgeValue 1 σ d.phi) (hEdge σ).1 (hEdge σ).2
  refine ⟨hV, hR, fun σ ↦ (hFTC σ).1, ?_⟩
  have h := mixed_rellich_current_integral d
  rw [show (fun q ↦ mixedVirialDensity d q - mixedRellichDensity d q -
        mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) =
      (fun q ↦ (mixedVirialDensity d - mixedRellichDensity d) q -
        mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) from rfl,
    integral_sub (hV.sub hR) hM] at h
  simp only [Pi.sub_apply, integral_sub hV hR] at h
  have hcorners :
      (∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
          mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a) =
        (∑ a : Bool, ∑ b : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal b)‖ ^ 2) -
          ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
            Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2 := by
    simp only [Fintype.sum_bool, (hFTC false).2.2, (hFTC true).2.2, mixedEdgeValue,
      show axisTraceChart 1 = id from rfl, id_eq, cellEdgeNormal, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [hcorners] at h
  unfold mixedStaticForm
  linarith only [h]

end NoEmbeddedEigenvalues
