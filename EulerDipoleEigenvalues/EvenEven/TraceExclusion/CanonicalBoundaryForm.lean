module

public import EulerDipoleEigenvalues.Transport.CanonicalProfile.ProfileContinuity

/-! # The canonical arc form -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real Complex MeasureTheory Set Filter Topology

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

end EulerDipoleEigenvalues
