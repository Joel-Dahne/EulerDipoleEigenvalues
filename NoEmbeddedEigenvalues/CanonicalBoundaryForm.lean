import NoEmbeddedEigenvalues.FlowBoundaryForm
import NoEmbeddedEigenvalues.CanonicalProfile

/-!
# The canonical arc form and explicit boundary derivatives

Blueprint: `def:canonical-arc-form`, `lem:canonical-arc-form`,
`lem:weighted-flow-derivatives`, and continuity in `lem:canonical-profile-ode`.

The weighted boundary domain gives a.e. derivatives after composition with `tanh`.
Together with the canonical profile equation this implies a.e. differentiability of the
trace itself, without an additional absolute-continuity hypothesis on that trace.
Continuity then identifies the first flow derivative with `-iΩ` everywhere. Its a.e.
derivative gives the second flow derivative and hence the equality of the two forms.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory Set Filter Topology

/-- Pullback by `tanh` preserves almost-everywhere statements. Its inverse is differentiable
    on `(-1,1)`, so preimages of null sets are images of null sets under `artanh`. -/
theorem ae_comp_tanh {P : ℝ → Prop} (hP : ∀ᵐ x, P x) : ∀ᵐ s, P (Real.tanh s) := by
  have hd : DifferentiableOn ℝ Real.artanh (Ioo (-1) 1) := by
    intro x hx
    have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
    have hq : DifferentiableAt ℝ (fun x : ℝ ↦ (1 + x) / (1 - x)) x :=
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).differentiableAt.div
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).differentiableAt
        (by linarith [hx.2])
    exact ((hq.sqrt hp.ne').log (Real.sqrt_pos.2 hp).ne').differentiableWithinAt
  rw [ae_iff] at hP ⊢
  have hn : volume ({x | ¬P x} ∩ Ioo (-1 : ℝ) 1) = 0 :=
    measure_mono_null inter_subset_left hP
  have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hd.mono inter_subset_right) hn
  have heq : {s | ¬P (Real.tanh s)} =
      Real.artanh '' ({x | ¬P x} ∩ Ioo (-1 : ℝ) 1) := by
    ext s
    constructor
    · intro hs
      exact ⟨Real.tanh s, ⟨hs, ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩⟩,
        Real.artanh_tanh s⟩
    · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
      change ¬P (Real.tanh (Real.artanh x))
      rw [Real.tanh_artanh hxi]
      exact hx
  rw [heq]
  exact him

/-- The first weighted derivative is the derivative of the flow-time value a.e. -/
theorem HasWeightedBoundaryH2.ae_hasDerivAt_flowValue {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) :
    ∀ᵐ s, HasDerivAt (flowValue F) (flowFirst D s) s := by
  filter_upwards [ae_comp_tanh h.h1.hasDerivAt_ae] with s hs
  exact hasDerivAt_flowValue (hs ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)

/-- The second weighted derivative is the derivative of the first flow derivative a.e. -/
theorem HasWeightedBoundaryH2.ae_hasDerivAt_flowFirst {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) :
    ∀ᵐ s, HasDerivAt (flowFirst D) (flowSecond D E s) s := by
  filter_upwards [ae_comp_tanh h.hasDerivAt_first_ae] with s hs
  exact hasDerivAt_flowFirst (hs ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)

/-- The first flow derivative is continuous; only interior continuity of `D` is needed. -/
theorem HasWeightedBoundaryH2.continuous_flowFirst {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) : Continuous (flowFirst D) := by
  have hD : ContinuousOn D (Ioo (-1) 1) := by
    intro x hx
    have hac := h.locally_absolutelyContinuous_first ((x - 1) / 2) ((x + 1) / 2)
      (by linarith [hx.1]) (by linarith) (by linarith [hx.2])
    have hc := hac.continuousOn
    rw [uIcc_of_le (by linarith : (x - 1) / 2 ≤ (x + 1) / 2)] at hc
    exact (hc.continuousAt (Icc_mem_nhds (by linarith [hx.1])
      (by linarith [hx.2]))).continuousWithinAt
  have ht : Continuous Real.tanh := continuous_iff_continuousAt.mpr
    (fun s ↦ (hasDerivAt_tanh s).continuousAt)
  have hcomp : Continuous (fun s ↦ D (Real.tanh s)) :=
    hD.comp_continuous ht (fun s ↦ ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)
  exact (continuous_ofReal.comp (continuous_const.sub (ht.pow 2))).mul hcomp

/-- The canonical profile is continuous whenever its defining derivative is integrable. -/
theorem continuous_canonicalProfile {lam : ℝ} {g : ℝ → ℂ} (hg : Integrable (deriv g)) :
    Continuous (canonicalProfile lam g) := by
  have hc := (integrable_profileIntegrand (lam := lam) hg).continuous_primitive (0 : ℝ)
  have htail : Continuous (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) := by
    have heq : (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) =
        fun s ↦ (∫ t in Ioi 0, profileIntegrand lam g t) -
          ∫ t in (0 : ℝ)..s, profileIntegrand lam g t :=
      funext fun s ↦ integral_Ioi_profileIntegrand hg s
    rw [heq]
    exact continuous_const.sub hc
  exact (by fun_prop : Continuous fun s : ℝ ↦ Complex.exp (Complex.I * lam * s)).mul htail

/-- The canonical arc form, written directly in terms of the arc trace and profile. -/
def canonicalArcForm (lam : ℝ) (g : ℝ → ℂ) : ℝ :=
  (∫ s, Real.cosh s ^ 2 / 2 * ‖deriv g s‖ ^ 2) +
    ∫ s, (canonicalProfile lam g s * (starRingEnd ℂ) (g s)).re

/-- The canonical profile form agrees with the flow-time form with explicit derivatives.
    The weighted-domain hypothesis itself supplies the a.e. differentiability needed to
    apply the profile equation; no separate regularity assumption on `g` is required. -/
theorem canonicalArcForm_eq_flowBoundaryForm {lam : ℝ} (hlam : lam ≠ 0) {g : ℝ → ℂ}
    (hg : Integrable (deriv g))
    (_he : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2) {D E : ℝ → ℂ}
    (hF : HasWeightedBoundaryH2 (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) D E) :
    canonicalArcForm lam g = flowBoundaryForm lam
      (flowValue (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)))
      (flowFirst D) (flowSecond D E) := by
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam
  have hz : flowValue (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) =
      canonicalUnknown lam g := by
    funext s
    simp only [flowValue, Real.artanh_tanh]
  have hdZ : ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (flowFirst D s) s := by
    simpa only [hz] using hF.ae_hasDerivAt_flowValue
  have hdΩ := ae_hasDerivAt_canonicalProfile (lam := lam) hg
  have hg_eq : g = fun s ↦ -(lam : ℂ) * canonicalUnknown lam g s - canonicalProfile lam g s := by
    funext s
    simp only [canonicalUnknown]
    field_simp
    ring
  have hgd : ∀ᵐ s, DifferentiableAt ℝ g s := by
    filter_upwards [hdZ, hdΩ] with s hzs hΩs
    rw [hg_eq]
    exact ((hzs.const_mul (-(lam : ℂ))).sub hΩs).differentiableAt
  have hfirst_ae : flowFirst D =ᵐ[volume] (fun s ↦ Complex.I * -canonicalProfile lam g s) := by
    filter_upwards [hdZ, ae_hasDerivAt_canonicalUnknown hlam hg hgd] with s hzs hcs
    exact hzs.unique hcs
  have hfirst : flowFirst D = (fun s ↦ Complex.I * -canonicalProfile lam g s) :=
    Measure.eq_of_ae_eq hfirst_ae hF.continuous_flowFirst
      (continuous_const.mul (continuous_canonicalProfile hg).neg)
  have hsecond : ∀ᵐ s,
      -Complex.I * flowSecond D E s - lam * flowFirst D s = deriv g s := by
    filter_upwards [hF.ae_hasDerivAt_flowFirst, hdΩ] with s hs hΩs
    have hh := hΩs.neg.const_mul Complex.I
    change HasDerivAt (fun t ↦ Complex.I * -canonicalProfile lam g t)
      (Complex.I * -(Complex.I * lam * canonicalProfile lam g s - deriv g s)) s at hh
    rw [← hfirst] at hh
    have hd := hs.unique hh
    rw [hd, hfirst]
    ring_nf
    simp [Complex.I_sq]
  have hP (s : ℝ) : -Complex.I * flowFirst D s = -canonicalProfile lam g s := by
    rw [hfirst]
    ring_nf
    simp [Complex.I_sq]
  have hG (s : ℝ) : -Complex.I * flowFirst D s - lam *
      flowValue (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) s = g s := by
    rw [hP, hz, canonicalUnknown]
    field_simp
    ring
  have henergy : (∫ s, Real.cosh s ^ 2 *
      Complex.normSq (-Complex.I * flowSecond D E s - lam * flowFirst D s)) =
      ∫ s, Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hsecond] with s hs
    rw [hs, Complex.normSq_eq_norm_sq]
  have hpair : (∫ s, (-Complex.I * flowFirst D s * (starRingEnd ℂ)
      (-Complex.I * flowFirst D s - lam *
        flowValue (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) s)).re) =
      -(∫ s, (canonicalProfile lam g s * (starRingEnd ℂ) (g s)).re) := by
    simp_rw [hG, hP, neg_mul, Complex.neg_re]
    exact integral_neg _
  rw [flowBoundaryForm, henergy, hpair, canonicalArcForm]
  rw [show (fun s ↦ Real.cosh s ^ 2 / 2 * ‖deriv g s‖ ^ 2) =
      fun s ↦ (1 / 2 : ℝ) * (Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2) by funext s; ring,
    integral_const_mul]
  ring

end NoEmbeddedEigenvalues
