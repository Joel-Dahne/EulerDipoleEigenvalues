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

/-- Sobolev flux identity for the corrected Rellich current. Integrate the
combined divergence, so no separate corner flux for either singular summand
has to be assigned. The zero Dirichlet flux is omitted from the right side. -/
theorem mixed_rellich_current_integral {ω : L2} (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, mixedVirialDensity d q - mixedRellichDensity d q -
        mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) =
      ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
        mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a := by
  sorry

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
