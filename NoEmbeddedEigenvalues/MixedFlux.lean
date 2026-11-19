import NoEmbeddedEigenvalues.MixedStaticForm
import NoEmbeddedEigenvalues.MixedBoundarySquare
import NoEmbeddedEigenvalues.CanonicalBoundaryForm
import NoEmbeddedEigenvalues.Melnikov
import NoEmbeddedEigenvalues.NormalField
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.BoundedVariation

/-! # Paired mixed-sector flux and its Neumann trace -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- An absolute-level collar in the Cartesian lift. -/
def mixedSeparatrixCollar (ε : ℝ) : Set Plane := {p | |dipoleLift p| < ε}

/-- Regularity across the separatrix and the one-factor cell quotient. -/
theorem mixed_quotient_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) :
    Nonempty (MixedQuotientData ω) ∧
      ∃ ε : ℝ, 0 < ε ∧
        MemSobolevLocOn 1 (mixedSeparatrixCollar ε) (liftL2 ω) ∧
        MemSobolevLocOn 3 (mixedSeparatrixCollar ε) (liftL2 (invLap ω)) ∧
        ∀ σ : Bool, HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 0 σ
          (liftL2 ω) (fun _ ↦ 0) := by
  sorry

/-- The two Neumann arcs, with their inherited orientations. -/
def mixedNeumannArc (positive : Bool) (t : ℝ) : Plane :=
  cellArc (if positive then 0 else 2) t

/-- Inverse flow time on a Neumann side, in tangential coordinate `a`.
On the positive side `sin a = -tanh t`; on the negative side the sign reverses. -/
def mixedNeumannTime (positive : Bool) (a : ℝ) : ℝ :=
  Real.artanh ((if positive then -1 else 1) * Real.sin a)

/-- The physical stream trace, using the continuous quotient on the Neumann arc. -/
def mixedNeumannStream (φ : Plane → ℂ) (positive : Bool) (t : ℝ) : ℂ :=
  let q := diagCoord (mixedNeumannArc positive t)
  (Real.cos q.1 : ℂ) * φ q

/-- The transformed stream trace `G = ψ/sech t` in `x = tanh t`. -/
def mixedNeumannG (φ : Plane → ℂ) (positive : Bool) (x : ℝ) : ℂ :=
  φ (diagCoord (mixedNeumannArc positive (Real.artanh x)))

/-- The transformed canonical unknown `F = z/sech t`. -/
def mixedNeumannF (lam : ℝ) (φ : Plane → ℂ) (positive : Bool) (x : ℝ) : ℂ :=
  canonicalUnknown lam (mixedNeumannStream φ positive) (Real.artanh x) /
    (Real.sqrt (boundaryWeight x) : ℂ)

/-- Boundary square and physical trace for the actual mixed Neumann profile. -/
theorem mixed_boundary_square_traces {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    let F := mixedNeumannF lam d.phi σ
    let G := mixedNeumannG d.phi σ
    Integrable (deriv g) ∧ MixedBoundaryLocAC F ∧ MixedBoundaryLocAC G ∧
    MixedBoundaryLocAC (deriv F) ∧
    G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F ∧
    (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      ‖F x‖ ≤ C ∧ ‖G x‖ ≤ C ∧ ‖(boundaryWeight x : ℂ) * deriv F x‖ ≤ C) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) (Ioo (-1) 1) ∧
    ((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
        ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) ∧
    ∃ ε : ℝ, 0 < ε ∧ HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 1 σ (liftL2 ω)
      (fun a ↦ canonicalProfile lam g (mixedNeumannTime σ a)) := by
  sorry

/-- Neumann contribution to the cutoff flux, before renormalizing the gradient term. -/
def mixedNeumannFluxCutoff (lam : ℝ) (φ : Plane → ℂ) (σ : Bool) (T : ℝ) : ℝ :=
  let g := mixedNeumannStream φ σ
  ∫ t in Ioo (-T) T, ‖deriv g t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 +
    (canonicalProfile lam g t * conj (g t)).re

/-- The paired edge expression before taking the limit. On a Dirichlet side,
the squared physical normal derivative is `|φ|²/2`. On a Neumann side the
physical tangential derivative is the time derivative divided by the flow speed. -/
def mixedPairedFluxCutoff (lam : ℝ) (φ : Plane → ℂ) (T : ℝ) : ℝ :=
  let dir := fun k : ℕ ↦ ∫ t in Ioo (-T) T, ‖φ (diagCoord (cellArc k t))‖ ^ 2 / 2
  dir 1 + dir 3 - ∑ σ : Bool, mixedNeumannFluxCutoff lam φ σ T

/-- Normal-field virial density in diagonal measure. The normal and tangent
are still physical unit directions in Cartesian coordinates. -/
def mixedNormalVirialDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  let p := diagInv q
  let dx := fun r ↦ (d.streamA (diagCoord r) + d.streamB (diagCoord r)) / 2
  let dy := fun r ↦ (d.streamA (diagCoord r) - d.streamB (diagCoord r)) / 2
  2 * (normalCoeff p * ‖liftL2 ω p‖ ^ 2 +
    (2 - normalC p) * ‖normalDeriv dx dy p‖ ^ 2 +
    normalC p * ‖tangentDeriv dx dy p‖ ^ 2)

/-- The normal-field paired flux. This uses the canonical profile and takes
no physical vorticity trace. The mixed-character limit remains to be proved. -/
theorem mixed_paired_flux {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedNormalVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedNormalVirialDensity d q)) := by
  sorry

/-- The mixed-field virial. The boundary profile in the paired expression is
the physical vorticity trace by `mixed_boundary_square_traces`. -/
theorem mixed_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedVirialDensity d q)) := by
  sorry

private theorem mixed_tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun t ↦ by
    rw [(hasDerivAt_tanh t).deriv, one_sub_tanh_sq]
    positivity

private theorem mixed_tanh_mem (t : ℝ) : Real.tanh t ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩

private theorem mixed_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  apply tendsto_order.2
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ Eventually.of_forall fun t ↦ (Real.tanh_lt_one t).trans hx⟩
  obtain ⟨y, hxy, hy⟩ := exists_between (max_lt (show (-1 : ℝ) < 1 by norm_num) hx)
  filter_upwards [eventually_ge_atTop (Real.artanh y)] with t ht
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨(le_max_left _ _).trans_lt hxy, hy⟩
  calc
    x < y := (le_max_right _ _).trans_lt hxy
    _ = Real.tanh (Real.artanh y) := (Real.tanh_artanh hy').symm
    _ ≤ Real.tanh t := mixed_tanh_strictMono.monotone ht

private theorem mixedLocAC_ae_diff {F : ℝ → ℂ} (h : MixedBoundaryLocAC F) :
    ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → DifferentiableAt ℝ F x := by
  have hq (a b : ℚ) : ∀ᵐ x : ℝ, -1 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      x ∈ Icc (a : ℝ) (b : ℝ) → DifferentiableAt ℝ F x := by
    by_cases hab : -1 < (a : ℝ) ∧ (a : ℝ) < b ∧ (b : ℝ) < 1
    · have hv := (h a b hab.1 hab.2.1 hab.2.2).boundedVariationOn
      filter_upwards [BoundedVariationOn.ae_differentiableAt_of_mem_uIcc hv]
        with x hx _ _ _ hm
      exact hx (Icc_subset_uIcc hm)
    · exact Eventually.of_forall fun _ ha hab' hb _ ↦ (hab ⟨ha, hab', hb⟩).elim
  filter_upwards [ae_all_iff.2 fun a ↦ ae_all_iff.2 (hq a)] with x hx hm
  obtain ⟨a, ha, hax⟩ := exists_rat_btwn hm.1
  obtain ⟨b, hxb, hb⟩ := exists_rat_btwn hm.2
  exact hx a b ha (hax.trans hxb) hb ⟨hax.le, hxb.le⟩

private theorem mixedNeumannArc_cos (σ : Bool) (t : ℝ) :
    Real.cos (diagCoord (mixedNeumannArc σ t)).1 = (Real.cosh t)⁻¹ := by
  cases σ <;>
    simp [mixedNeumannArc, cellArc, Function.iterate_succ_apply', rotLift,
      separatrixArc, diagCoord, show ∀ a : ℝ, (a + (a - Real.pi)) / 2 = a - Real.pi / 2
        from fun a ↦ by ring,
      show ∀ a : ℝ, (-a + (Real.pi - a)) / 2 = -(a - Real.pi / 2)
        from fun a ↦ by ring, Real.cos_sub, sin_arcAngle, one_div]

private theorem mixedNeumannArc_mem (σ : Bool) (t : ℝ) :
    diagCoord (mixedNeumannArc σ t) ∈ closure mixedOpenCell := by
  rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos])]
  have ha : 0 < arcAngle t ∧ arcAngle t < Real.pi := by
    unfold arcAngle
    constructor
    · exact mul_pos (by norm_num) (Real.arctan_pos.mpr (Real.exp_pos _))
    · linarith [Real.arctan_lt_pi_div_two (Real.exp (-t))]
  cases σ <;>
    simp only [mixedNeumannArc, Bool.false_eq_true, ↓reduceIte, cellArc,
      Function.iterate_succ_apply', Function.iterate_zero_apply, rotLift, separatrixArc,
      diagCoord, mem_prod, mem_Icc] <;> constructor <;> constructor <;>
      linarith [ha.1, ha.2, Real.pi_pos]

private theorem mixed_sech_deriv (t : ℝ) :
    HasDerivAt (fun s ↦ (Real.cosh s)⁻¹) (-(Real.cosh t)⁻¹ * Real.tanh t) t := by
  convert (Real.hasDerivAt_cosh t).inv (Real.cosh_pos t).ne' using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

private theorem mixed_hasDerivAt_weightedFlow {U : ℝ → ℂ} {t : ℝ}
    (h : DifferentiableAt ℝ U (Real.tanh t)) :
    HasDerivAt (fun s ↦ ((Real.cosh s)⁻¹ : ℝ) * U (Real.tanh s))
      (((Real.cosh t)⁻¹ : ℝ) *
        ((boundaryWeight (Real.tanh t) : ℂ) * deriv U (Real.tanh t) -
          (Real.tanh t : ℂ) * U (Real.tanh t))) t := by
  convert ((mixed_sech_deriv t).ofReal_comp).mul
    (hasDerivAt_flowValue h.hasDerivAt) using 1 <;>
    simp [flowValue, flowFirst, Pi.mul_def]
  ring

private theorem mixed_tanh_integral {f : ℝ → ℝ} {a b : ℝ} :
    (∫ t in Ioo a b, boundaryWeight (Real.tanh t) * f (Real.tanh t)) =
      ∫ x in Ioo (Real.tanh a) (Real.tanh b), f x := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t (_ : t ∈ Ioo a b) ↦ (hasDerivAt_tanh t).hasDerivWithinAt)
    Real.tanh_injective.injOn f
  have hc : Continuous Real.tanh := continuous_iff_continuousAt.2
    fun t ↦ (hasDerivAt_tanh t).continuousAt
  rw [hc.image_Ioo_of_strictMono mixed_tanh_strictMono] at h
  rw [h]
  congr 1
  funext t
  rw [abs_of_pos (by rw [one_sub_tanh_sq]; positivity), boundaryWeight, smul_eq_mul]

private theorem mixed_tanh_integrable {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : IntegrableOn f (Real.tanh '' s)) :
    IntegrableOn (fun t ↦ boundaryWeight (Real.tanh t) * f (Real.tanh t)) s := by
  apply ((integrableOn_image_iff_integrableOn_abs_deriv_smul hs
    (fun t _ ↦ (hasDerivAt_tanh t).hasDerivWithinAt) Real.tanh_injective.injOn f).mp h).congr
  exact Eventually.of_forall fun t ↦ by
    dsimp only
    rw [abs_of_pos (by rw [one_sub_tanh_sq]; positivity), boundaryWeight, smul_eq_mul]

private theorem mixed_norm_boundary_ac {G : ℝ → ℂ} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ x * ‖G x‖ ^ 2) a b := by
  have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval h
  have hi : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x) a b :=
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  simpa only [Function.comp_apply, pow_two] using hi.fun_mul (hn.fun_mul hn)

private theorem mixed_norm_boundary_deriv {G : ℝ → ℂ} {x : ℝ}
    (h : DifferentiableAt ℝ G x) :
    deriv (fun y ↦ y * ‖G y‖ ^ 2) x =
      ‖G x‖ ^ 2 + 2 * x * (deriv G x * conj (G x)).re := by
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h.hasDerivAt
  have hI := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h.hasDerivAt
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_def] at hR hI
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hd := ((hasDerivAt_id x).mul ((hR.mul hR).add (hI.mul hI))).deriv
  simp only [id_eq, Pi.add_apply, Pi.mul_def, Pi.add_def] at hd
  rw [hd]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem mixed_flux_gradient_pointwise (t : ℝ) (U V : ℂ) :
    2 * ‖((Real.cosh t)⁻¹ : ℝ) *
        ((boundaryWeight (Real.tanh t) : ℂ) * V - (Real.tanh t : ℂ) * U) /
        (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 - ‖U‖ ^ 2 =
      boundaryWeight (Real.tanh t) *
        (boundaryWeight (Real.tanh t) * ‖V‖ ^ 2 -
          (‖U‖ ^ 2 + 2 * Real.tanh t * (V * conj U).re)) := by
  have he (z : ℂ) :
      ((Real.cosh t)⁻¹ : ℝ) * z / (Real.sqrt 2 / Real.cosh t : ℝ) =
        z / (Real.sqrt 2 : ℝ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
    rw [← Complex.ofReal_cosh, mul_div_cancel_left₀ _
      (Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne')]
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (by norm_num)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, boundaryWeight]
  ring

/-- On a single Neumann edge, subtract the trace mass before taking the cutoff
limit. In `x = tanh t` the leftover gradient term is the weighted energy
minus the derivative of `x |G|²`; the latter gives the two corner values. -/
theorem mixed_neumann_flux_renormalized {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    (σ : Bool) :
    let F := mixedNeumannF lam d.phi σ
    let G := mixedNeumannG d.phi σ
    Tendsto (fun T ↦ 2 * mixedNeumannFluxCutoff lam d.phi σ T -
      ∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2) atTop
      (𝓝 (((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
        2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re)) -
        ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2)) := by
  let g := mixedNeumannStream d.phi σ
  let F := mixedNeumannF lam d.phi σ
  let G := mixedNeumannG d.phi σ
  let H := fun x : ℝ ↦ x * ‖G x‖ ^ 2
  let e := fun x : ℝ ↦ boundaryWeight x * ‖deriv G x‖ ^ 2
  let c := fun x : ℝ ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re
  let w := fun t : ℝ ↦ boundaryWeight (Real.tanh t)
  let m := fun t : ℝ ↦ ‖G (Real.tanh t)‖ ^ 2
  let j := fun t : ℝ ↦ ‖deriv g t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 +
    (canonicalProfile lam g t * conj (g t)).re
  obtain ⟨hg, hF, hG, _, _, _, he, hc, _⟩ := mixed_boundary_square_traces hlam hω hs d σ
  have hmass (t : ℝ) : G (Real.tanh t) = d.phi (diagCoord (mixedNeumannArc σ t)) := by
    simp [G, mixedNeumannG, Real.artanh_tanh]
  have hg_eq : g = fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * G (Real.tanh t) := by
    funext t
    simp only [g, mixedNeumannStream, mixedNeumannArc_cos, hmass]
  have hz_eq : canonicalUnknown lam g = fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * F (Real.tanh t) := by
    funext t
    simp only [F, mixedNeumannF, Real.artanh_tanh, boundaryWeight_tanh, one_div, Real.sqrt_inv,
      Real.sqrt_sq (Real.cosh_pos t).le, Complex.ofReal_inv]
    change _ = (↑(Real.cosh t) : ℂ)⁻¹ * (canonicalUnknown lam g t / (↑(Real.cosh t) : ℂ)⁻¹)
    have hcosh : (↑(Real.cosh t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
    rw [mul_comm, div_mul_cancel₀ _ (inv_ne_zero hcosh)]
  have hgd := ae_comp_tanh (mixedLocAC_ae_diff hG)
  have hfd := ae_comp_tanh (mixedLocAC_ae_diff hF)
  have hgd' : ∀ᵐ t, DifferentiableAt ℝ g t := by
    filter_upwards [hgd] with t ht
    rw [hg_eq]
    exact (mixed_hasDerivAt_weightedFlow (ht (mixed_tanh_mem t))).differentiableAt
  have hprofile := ae_hasDerivAt_canonicalUnknown hlam hg hgd'
  have hpoint : ∀ᵐ t, 2 * j t - m t =
      w t * ((e (Real.tanh t) - 2 * c (Real.tanh t)) - deriv H (Real.tanh t)) := by
    filter_upwards [hgd, hfd, hprofile] with t hgt hft hz
    have hgt := hgt (mixed_tanh_mem t)
    have hft := hft (mixed_tanh_mem t)
    have hderiv := (mixed_hasDerivAt_weightedFlow hgt).deriv
    have hdz := hz.unique (hz_eq.symm ▸ mixed_hasDerivAt_weightedFlow hft)
    have hΩ : canonicalProfile lam g t =
        -(((Real.cosh t)⁻¹ : ℝ) : ℂ) * mixedBoundaryTransport 0 F (Real.tanh t) := by
      unfold mixedBoundaryTransport
      simp only [Complex.ofReal_zero, zero_mul, sub_zero]
      linear_combination Complex.I * hdz + (Complex.I_sq) * canonicalProfile lam g t
    have hp : (canonicalProfile lam g t * conj (g t)).re = -(w t * c (Real.tanh t)) := by
      rw [hΩ, congrFun hg_eq t]
      simp only [c, w, boundaryWeight_tanh, map_mul, Complex.conj_ofReal,
        neg_mul, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, one_div]
      ring
    dsimp only [j, m, H, e]
    rw [congrArg (fun f : ℝ → ℂ ↦ deriv f t) hg_eq, hderiv, hp, mixed_norm_boundary_deriv hgt]
    linarith only [mixed_flux_gradient_pointwise t (G (Real.tanh t)) (deriv G (Real.tanh t))]
  have hE : IntegrableOn (fun x ↦ e x - 2 * c x) (Ioo (-1 : ℝ) 1) :=
    he.sub (hc.const_mul 2)
  have htime : Integrable (fun t ↦ w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) := by
    rw [← integrableOn_univ]
    apply mixed_tanh_integrable (f := fun x ↦ e x - 2 * c x) MeasurableSet.univ
    rwa [Real.tanh_bijOn.image_eq]
  have hcut (T : ℝ) (hT : 0 < T) :
      2 * mixedNeumannFluxCutoff lam d.phi σ T -
        (∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2) =
      (∫ t in Ioo (-T) T, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) -
        (H (Real.tanh T) - H (Real.tanh (-T))) := by
    have ht : -T < T := by linarith
    have hab := mixed_tanh_strictMono ht
    have hH := mixed_norm_boundary_ac (hG _ _ (mixed_tanh_mem (-T)).1 hab (mixed_tanh_mem T).2)
    have hHi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hH.intervalIntegrable_deriv
    have hDi : IntegrableOn (fun t ↦ w t * deriv H (Real.tanh t)) (Ioo (-T) T) := by
      apply mixed_tanh_integrable measurableSet_Ioo
      have htc : Continuous Real.tanh := continuous_iff_continuousAt.2
        fun t ↦ (hasDerivAt_tanh t).continuousAt
      rwa [htc.image_Ioo_of_strictMono mixed_tanh_strictMono]
    have hm : Continuous m := by
      have ha : Continuous (fun t ↦ diagCoord (mixedNeumannArc σ t)) := by
        cases σ <;> simp only [mixedNeumannArc, Bool.false_eq_true, ↓reduceIte, cellArc,
          Function.iterate_succ_apply', Function.iterate_zero_apply, rotLift,
          separatrixArc, diagCoord]
        all_goals
          have hac : Continuous arcAngle := continuous_iff_continuousAt.2
            fun t ↦ (hasDerivAt_arcAngle t).continuousAt
          fun_prop
      rw [show m = fun t ↦ ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2 by
        funext t; simp only [m, hmass]]
      exact (d.continuous.comp_continuous ha (mixedNeumannArc_mem σ)).norm.pow _
    have hmi : IntegrableOn m (Ioo (-T) T) :=
      (hm.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hp' : IntegrableOn (fun t ↦ 2 * j t - m t) (Ioo (-T) T) := by
      apply ((htime.integrableOn (s := Ioo (-T) T)).sub hDi).congr
      filter_upwards [ae_restrict_of_ae hpoint] with t h
      simpa only [Pi.sub_apply, mul_sub] using h.symm
    have hji : IntegrableOn j (Ioo (-T) T) := by
      apply ((hp'.add hmi).const_mul (1 / 2 : ℝ)).congr
      exact Eventually.of_forall fun t ↦ by dsimp; ring
    simp only [mixedNeumannFluxCutoff, ← hmass]
    change 2 * (∫ t in Ioo (-T) T, j t) - (∫ t in Ioo (-T) T, m t) = _
    rw [← integral_const_mul, ← integral_sub (hji.const_mul 2) hmi]
    calc
      _ = ∫ t in Ioo (-T) T, w t * (e (Real.tanh t) - 2 * c (Real.tanh t)) -
          w t * deriv H (Real.tanh t) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hpoint] with t h
          rw [h, mul_sub]
      _ = _ := by
        have hd : (∫ x in Ioo (Real.tanh (-T)) (Real.tanh T), deriv H x) =
            H (Real.tanh T) - H (Real.tanh (-T)) := by
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
          exact hH.integral_deriv_eq_sub
        rw [integral_sub htime.integrableOn hDi, mixed_tanh_integral, hd]
  have htimeLim := intervalIntegral_tendsto_integral htime tendsto_neg_atTop_atBot tendsto_id
  rw [show (∫ t, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) =
      (∫ x in Ioo (-1) 1, e x) - 2 * (∫ x in Ioo (-1) 1, c x) by
    rw [show (∫ t, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) =
      ∫ x in Ioo (-1) 1, e x - 2 * c x by
      simpa only [w, boundaryWeight_tanh, smul_eq_mul] using
        integral_tanh_subst (fun x ↦ e x - 2 * c x)]
    rw [integral_sub he (hc.const_mul 2), integral_const_mul]] at htimeLim
  -- The endpoints are the two corners of this edge (in opposite orders for the two edges).
  have hEnds : Tendsto (fun T ↦ H (Real.tanh T) - H (Real.tanh (-T))) atTop
      (𝓝 (∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2)) := by
    have hminus : Tendsto (fun T : ℝ ↦ Real.tanh (-T)) atTop (𝓝 (-1)) := by
      simpa only [Real.tanh_neg] using mixed_tanh_atTop.neg
    let R (p : Plane) : Plane := if σ then p else (-p.1, -p.2)
    have hR : Continuous R := by
      cases σ <;> dsimp [R] <;> fun_prop
    have hArc (t : ℝ) : mixedNeumannArc σ t = R (separatrixArc t) := by
      cases σ <;> simp [R, mixedNeumannArc, cellArc, Function.iterate_succ_apply', rotLift]
    have hp : Tendsto (fun t ↦ diagCoord (mixedNeumannArc σ t)) atTop
        (𝓝 (diagCoord (R (0, -Real.pi)))) := by
      simpa only [hArc, Function.comp_def] using ((continuous_diagCoord.comp hR).tendsto _).comp
        tendsto_separatrixArc_atTop
    have hn : Tendsto (fun t ↦ diagCoord (mixedNeumannArc σ (-t))) atTop
        (𝓝 (diagCoord (R (Real.pi, 0)))) := by
      simpa only [hArc, Function.comp_def] using ((continuous_diagCoord.comp hR).tendsto _).comp
        (tendsto_separatrixArc_atBot.comp tendsto_neg_atTop_atBot)
    have hClosed : IsClosed (closure mixedOpenCell) := isClosed_closure
    have hpMem := hClosed.mem_of_tendsto hp (Eventually.of_forall (mixedNeumannArc_mem σ))
    have hnMem := hClosed.mem_of_tendsto hn
      (Eventually.of_forall fun t ↦ mixedNeumannArc_mem σ (-t))
    have hpG := (d.continuous _ hpMem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hp, Eventually.of_forall (mixedNeumannArc_mem σ)⟩)
    have hnG := (d.continuous _ hnMem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hn, Eventually.of_forall fun t ↦ mixedNeumannArc_mem σ (-t)⟩)
    have h := (mixed_tanh_atTop.mul (hpG.norm.pow 2)).sub (hminus.mul (hnG.norm.pow 2))
    have hP : diagCoord (R (0, -Real.pi)) = (cellEdgeNormal (!σ), cellEdgeNormal σ) := by
      cases σ <;> simp [R, diagCoord, cellEdgeNormal]
    have hN : diagCoord (R (Real.pi, 0)) = (cellEdgeNormal σ, cellEdgeNormal σ) := by
      cases σ <;> simp [R, diagCoord, cellEdgeNormal]
    rw [hP, hN] at h
    simp only [H, hmass]
    cases σ <;> simpa [Fintype.sum_bool, add_comm] using h
  apply (htimeLim.sub hEnds).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [id_eq]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Ioc_eq_integral_Ioo]
  exact (hcut T hT).symm

/-- Static identity and its sign for the original mixed eigenproblem. -/
theorem mixed_static_identity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    0 = mixedStaticForm d + (∑ σ : Bool, ∫ x in Ioo (-1) 1,
      boundaryWeight x * ‖mixedBoundarySquare lam (mixedNeumannF lam d.phi σ) x‖ ^ 2) ∧
    mixedStaticForm d ≤ 0 := by
  let square (σ : Bool) : ℝ := ∫ x in Ioo (-1) 1,
    boundaryWeight x * ‖mixedBoundarySquare lam (mixedNeumannF lam d.phi σ) x‖ ^ 2
  let corner (σ : Bool) : ℝ := ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2
  let edge (σ : Bool) (T : ℝ) : ℝ := 2 * mixedNeumannFluxCutoff lam d.phi σ T -
    ∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2
  have hEdge (σ : Bool) : Tendsto (edge σ) atTop (𝓝 (square σ - corner σ)) := by
    have h := mixed_neumann_flux_renormalized hlam hω hs d σ
    dsimp only at h
    rw [(mixed_boundary_square_traces hlam hω hs d σ).2.2.2.2.2.2.2.2.2.1] at h
    exact h
  have hSum : Tendsto (fun T ↦ ∑ σ : Bool, edge σ T) atTop
      (𝓝 (∑ σ : Bool, (square σ - corner σ))) := by
    simp only [Fintype.sum_bool]
    exact (hEdge true).add (hEdge false)
  have hlim := (mixed_trace_mass d).2.2.2.sub hSum
  have hCutoff (T : ℝ) :
      mixedTraceMassCutoff d.phi T - (∑ σ : Bool, edge σ T) =
        2 * mixedPairedFluxCutoff lam d.phi T := by
    simp only [mixedTraceMassCutoff, mixedPairedFluxCutoff, edge, mixedNeumannArc,
      Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, div_eq_mul_inv, integral_mul_const]
    ring
  have hEq := tendsto_nhds_unique (mixed_virial hlam hω hs d).2
    (hlim.congr (fun T ↦ hCutoff T))
  have hCorners : (∑ σ : Bool, corner σ) =
      ∑ a : Bool, ∑ b : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal b)‖ ^ 2 :=
    Finset.sum_comm
  rw [Finset.sum_sub_distrib, hCorners] at hEq
  have hId : 0 = mixedStaticForm d + ∑ σ : Bool, square σ := by
    unfold mixedStaticForm
    linarith only [hEq]
  refine ⟨hId, ?_⟩
  have hNonneg : 0 ≤ ∑ σ : Bool, square σ := by
    apply Finset.sum_nonneg
    intro σ _
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))]
      with x hx
    have hw : 0 ≤ boundaryWeight x := by
      unfold boundaryWeight
      have hl : 0 ≤ x + 1 := by linarith [hx.1]
      have hr : 0 ≤ 1 - x := by linarith [hx.2]
      nlinarith only [mul_nonneg hl hr]
    exact mul_nonneg hw (sq_nonneg _)
  linarith only [hId, hNonneg]

end NoEmbeddedEigenvalues
