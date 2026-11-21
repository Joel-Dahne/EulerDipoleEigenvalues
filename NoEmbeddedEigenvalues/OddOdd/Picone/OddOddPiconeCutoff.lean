module

public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddGroundResidual
public import NoEmbeddedEigenvalues.Analysis.Inequalities.Picone

/-!
# Weak Picone testing and annular extraction

Blueprint: `lem:dd-picone-cutoff`, `lem:dd-picone-annular`.

Periodic quadratic integration by parts follows directly from Fourier partials.
The normalized ground flux identifies the Picone defect with a weak divergence.
Annular cutoffs remove the critical levels before testing; coarea and the weak
one-dimensional fundamental theorem give a common exceptional set of endpoints.
No smooth approximation or pointwise Sobolev gradient trace is used.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- Weak quadratic integration by parts for a smooth periodic real field.
    Fourier derivative witnesses suffice; no smooth approximation is used. -/
theorem squareIntegral_weak_value_divergence {W₁ W₂ : ℝ × ℝ → ℝ}
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    {φ dx dy : L2} (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy) :
    squareIntegral (fun p ↦ divergence W₁ W₂ p * ‖liftL2 φ p‖ ^ 2 +
      2 * (W₁ p * (liftL2 dx p * (starRingEnd ℂ) (liftL2 φ p)).re +
        W₂ p * (liftL2 dy p * (starRingEnd ℂ) (liftL2 φ p)).re)) = 0 := by
  let D (p : ℝ × ℝ) : ℂ := W₁ p • liftL2 dx p + W₂ p • liftL2 dy p +
    ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 φ p
  have hd (j : Fin 2) : HasFourierPartial j φ (![dx, dy] j) := by
    fin_cases j <;> assumption
  have h := squarePairing_halfDensityGen_h1 hW₁ hW₂ hpW₁ hpW₂ hd hd
  change squarePairing D (liftL2 φ) = -squarePairing (liftL2 φ) D at h
  rw [squarePairing_comm D (liftL2 φ)] at h
  have hz : (squarePairing D (liftL2 φ)).re = 0 := by
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hr
    linarith
  have hdiv : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real (hW₁.of_le (by norm_num))).add
      (continuous_partialY_real (hW₂.of_le (by norm_num)))
  have hpdiv : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hi : IntegrableOn (fun p ↦ D p * (starRingEnd ℂ) (liftL2 φ p)) periodSquare := by
    convert ((integrableOn_smul_liftL2_mul_conj hW₁.continuous hpW₁ dx φ).add
      (integrableOn_smul_liftL2_mul_conj hW₂.continuous hpW₂ dy φ)).add
        (integrableOn_smul_liftL2_mul_conj (continuous_const.mul hdiv)
          (hpdiv.const_mul (1 / 2)) φ φ) using 1
    ext p
    simp only [D, add_mul, Pi.add_apply, Pi.mul_apply]
  have heq (p : ℝ × ℝ) :
      divergence W₁ W₂ p * ‖liftL2 φ p‖ ^ 2 +
        2 * (W₁ p * (liftL2 dx p * (starRingEnd ℂ) (liftL2 φ p)).re +
          W₂ p * (liftL2 dy p * (starRingEnd ℂ) (liftL2 φ p)).re) =
      2 * (D p * (starRingEnd ℂ) (liftL2 φ p)).re := by
    simp only [D, add_mul, Complex.add_re, Complex.real_smul, mul_assoc,
      Complex.re_ofReal_mul, re_mul_conj_self]
    ring
  simp_rw [heq]
  unfold squareIntegral
  rw [integral_const_mul]
  have hr := integral_re hi
  simp only [RCLike.re_to_complex] at hr
  rw [hr]
  change 2 * (squarePairing D (liftL2 φ)).re = 0
  rw [hz, mul_zero]

/-- The two components of `M ∇w / w`, before multiplication by the value mass. -/
def ddGroundLogFlux₁ (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₁ ddMxx ddMxy ddGround p / ddGround p

def ddGroundLogFlux₂ (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₂ ddMxy ddMyy ddGround p / ddGround p

/-- The normalized ground flux is smooth on the regular positive levels. -/
theorem contDiffAt_ddGroundLogFlux {p : ℝ × ℝ}
    (hs : 0 < dipoleLift p) (hs2 : dipoleLift p < 2) :
    ContDiffAt ℝ ∞ ddGroundLogFlux₁ p ∧ ContDiffAt ℝ ∞ ddGroundLogFlux₂ p := by
  have hr := gradSq_dipoleLift_pos hs hs2
  have hsc : ContDiffAt ℝ ∞ dipoleLift p := by unfold dipoleLift; fun_prop
  have hrc : ContDiffAt ℝ ∞ (gradSq dipoleLift) p := by rw [gradSq_dipoleLift]; fun_prop
  have hc : ContDiffAt ℝ ∞ ddC p := by unfold ddC; fun_prop (disch := positivity)
  have ha : ContDiffAt ℝ ∞ ddA p := by unfold ddA; fun_prop (disch := positivity)
  have hxx : ContDiffAt ℝ ∞ ddMxx p := by unfold ddMxx; fun_prop (disch := positivity)
  have hxy : ContDiffAt ℝ ∞ ddMxy p := by unfold ddMxy; fun_prop (disch := positivity)
  have hyy : ContDiffAt ℝ ∞ ddMyy p := by unfold ddMyy; fun_prop (disch := positivity)
  have hg := contDiffAt_ddGround hr.ne'
  obtain ⟨hx, hy⟩ := contDiffAt_ddGround_partials hr.ne'
  have hn : ddGround p ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_ddGround p)).ne'
  constructor
  · exact ((hxx.mul hx).add (hxy.mul hy)).div hg hn
  · exact ((hxy.mul hx).add (hyy.mul hy)).div hg hn

/-- Periodicity is pointwise, including totalized critical values. -/
theorem isPeriodicLift_ddGroundLogFlux :
    IsPeriodicLift ddGroundLogFlux₁ ∧ IsPeriodicLift ddGroundLogFlux₂ := by
  have hg : IsPeriodicLift ddGround := fun p ↦ by
    simp only [ddGround, gradSq_dipoleLift, dipoleLift,
      Real.sin_add_two_pi, Real.cos_add_two_pi, and_self]
  have hx := hg.partialX
  have hy := hg.partialY
  constructor <;> intro p <;>
    simp only [ddGroundLogFlux₁, ddGroundLogFlux₂, piconeGroundFlux₁, piconeGroundFlux₂,
      ddMxx, ddMxy, ddMyy, ddA, ddC, gradSq_dipoleLift, dipoleLift,
      Real.sin_add_two_pi, Real.cos_add_two_pi, (hg p).1, (hg p).2,
      (hx p).1, (hx p).2, (hy p).1, (hy p).2, and_self]

/-- The orbit-time coefficient is minus the stream derivative of the normalized
    ground flux, in accordance with the outward normal convention. -/
theorem ddGroundCurrentCoeff_eq_flux {p : ℝ × ℝ}
    (hs : 0 < dipoleLift p) (hs2 : dipoleLift p < 2) :
    ddGroundCurrentCoeff p = -(partialX dipoleLift p * ddGroundLogFlux₁ p +
      partialY dipoleLift p * ddGroundLogFlux₂ p) := by
  have hr := (gradSq_dipoleLift_pos hs hs2).ne'
  have hw : ddGround p ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_ddGround p)).ne'
  simp only [ddGroundCurrentCoeff, ddGroundLogFlux₁, ddGroundLogFlux₂,
    piconeGroundFlux₁, piconeGroundFlux₂, ddMxx, ddMxy, ddMyy,
    partialX_dipoleLift, partialY_dipoleLift]
  rw [gradSq_dipoleLift] at hr ⊢
  field_simp
  ring

private theorem piconeMatrixForm_jet (a b c : ℝ) {g : ℝ} (hg : 0 < g)
    (gx gy : ℝ) (z zx zy : ℂ) :
    piconeMatrixForm a b c zx zy =
      g ^ 2 * piconeMatrixForm a b c
        (zx / (g : ℂ) - z * (gx : ℂ) / (g : ℂ) ^ 2)
        (zy / (g : ℂ) - z * (gy : ℂ) / (g : ℂ) ^ 2) +
      (a * gx + b * gy) * (2 * (zx * (starRingEnd ℂ) z).re / g - ‖z‖ ^ 2 * gx / g ^ 2) +
      (b * gx + c * gy) * (2 * (zy * (starRingEnd ℂ) z).re / g - ‖z‖ ^ 2 * gy / g ^ 2) := by
  have h := picone_algebra (ι := Fin 2) ![![a, b], ![b, c]]
    (by intro i j; fin_cases i <;> fin_cases j <;> rfl) hg ![gx, gy] z ![zx, zy]
  simp only [piconeQuadratic, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im] at h
  simp only [piconeMatrixForm, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linear_combination h

/-- Picone's defect in divergence form for arbitrary specified first-jet values.
    No classical differentiability of the supplied L² representatives is asserted. -/
theorem ddPicone_defect {φ dx dy : L2} {p : ℝ × ℝ}
    (hs : 0 < dipoleLift p) (hs2 : dipoleLift p < 2) :
    ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p =
      divergence ddGroundLogFlux₁ ddGroundLogFlux₂ p * ‖liftL2 φ p‖ ^ 2 +
        2 * (ddGroundLogFlux₁ p * (liftL2 dx p * (starRingEnd ℂ) (liftL2 φ p)).re +
          ddGroundLogFlux₂ p * (liftL2 dy p * (starRingEnd ℂ) (liftL2 φ p)).re) := by
  have hr := (gradSq_dipoleLift_pos hs hs2).ne'
  have hw : 0 < ddGround p := lt_of_lt_of_le zero_lt_one (one_le_ddGround p)
  have hg := (contDiffAt_ddGround hr).differentiableAt (by simp)
  have hb := contDiffAt_ddGroundLogFlux hs hs2
  have hb₁ := hb.1.differentiableAt (by simp)
  have hb₂ := hb.2.differentiableAt (by simp)
  have hB₁ : piconeGroundFlux₁ ddMxx ddMxy ddGround =
      fun q ↦ ddGroundLogFlux₁ q * ddGround q := by
    funext q
    have hn : ddGround q ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_ddGround q)).ne'
    simp [ddGroundLogFlux₁, hn]
  have hB₂ : piconeGroundFlux₂ ddMxy ddMyy ddGround =
      fun q ↦ ddGroundLogFlux₂ q * ddGround q := by
    funext q
    have hn : ddGround q ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_ddGround q)).ne'
    simp [ddGroundLogFlux₂, hn]
  have hx : partialX (piconeGroundFlux₁ ddMxx ddMxy ddGround) p =
      partialX ddGroundLogFlux₁ p * ddGround p + ddGroundLogFlux₁ p * partialX ddGround p := by
    rw [hB₁]
    exact ((hasDerivAt_partialX hb₁).mul (hasDerivAt_partialX hg)).deriv
  have hy : partialY (piconeGroundFlux₂ ddMxy ddMyy ddGround) p =
      partialY ddGroundLogFlux₂ p * ddGround p + ddGroundLogFlux₂ p * partialY ddGround p := by
    rw [hB₂]
    exact ((hasDerivAt_partialY hb₂).mul (hasDerivAt_partialY hg)).deriv
  simp only [ddRawEnergy, ddPiconeGradient, ddPiconePotential, ddDividedPartial,
    coordPartial, show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false]
  rw [ddMatrixForm_eq_cartesian _ _ hr, ddMatrixForm_eq_cartesian _ _ hr]
  change piconeMatrixForm (ddMxx p) (ddMxy p) (ddMyy p) (liftL2 dx p) (liftL2 dy p) -
      ddF p * ‖liftL2 φ p‖ ^ 2 -
      ddGround p ^ 2 * piconeMatrixForm (ddMxx p) (ddMxy p) (ddMyy p) _ _ -
      ddGroundResidual p / ddGround p * ‖liftL2 φ p‖ ^ 2 = _
  rw [piconeMatrixForm_jet _ _ _ hw (partialX ddGround p) (partialY ddGround p)
    (liftL2 φ p) (liftL2 dx p) (liftL2 dy p)]
  change (_ + piconeGroundFlux₁ ddMxx ddMxy ddGround p * _ +
      piconeGroundFlux₂ ddMxy ddMyy ddGround p * _) - _ - _ - _ = _
  have hres : ddGroundResidual p =
      -(partialX (piconeGroundFlux₁ ddMxx ddMxy ddGround) p +
        partialY (piconeGroundFlux₂ ddMxy ddMyy ddGround) p) - ddF p * ddGround p := rfl
  rw [hres, hx, hy, hB₁, hB₂]
  unfold divergence
  field_simp [hw.ne']
  ring

private theorem contDiff_groundFlux_cutoff {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * ddGroundLogFlux₁ p) ∧
      ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * ddGroundLogFlux₂ p) := by
  have hcut {F : ℝ × ℝ → ℝ}
      (hF : ∀ p, 0 < dipoleLift p → dipoleLift p < 2 → ContDiffAt ℝ ∞ F p) :
      ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * F p) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : dipoleLift p ∈ tsupport χ
    · exact (hχ.comp (by unfold dipoleLift; fun_prop)).contDiffAt.mul
        (hF p (hχs hp).1 (hχs hp).2)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
        (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt
      filter_upwards [hz] with q hq
      change χ (dipoleLift q) = 0 at hq
      simp [hq]
  exact ⟨hcut fun p hs ht ↦ (contDiffAt_ddGroundLogFlux hs ht).1,
    hcut fun p hs ht ↦ (contDiffAt_ddGroundLogFlux hs ht).2⟩

private theorem periodic_groundFlux_cutoff (χ : ℝ → ℝ) :
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * ddGroundLogFlux₁ p) ∧
      IsPeriodicLift (fun p ↦ χ (dipoleLift p) * ddGroundLogFlux₂ p) := by
  have hs : IsPeriodicLift dipoleLift := fun p ↦ by
    simp only [dipoleLift, Real.cos_add_two_pi, and_self]
  obtain ⟨h₁, h₂⟩ := isPeriodicLift_ddGroundLogFlux
  constructor <;> intro p <;>
    simp only [(hs p).1, (hs p).2, (h₁ p).1, (h₁ p).2, (h₂ p).1, (h₂ p).2, and_self]

/-- The cutoff divergence algebra holds even at totalized critical values,
    since an annular cutoff vanishes near those stream levels. -/
theorem ddPicone_cutoff_algebra {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) (φ dx dy : L2) (p : ℝ × ℝ) :
    divergence (fun q ↦ χ (dipoleLift q) * ddGroundLogFlux₁ q)
        (fun q ↦ χ (dipoleLift q) * ddGroundLogFlux₂ q) p * ‖liftL2 φ p‖ ^ 2 +
      2 * ((χ (dipoleLift p) * ddGroundLogFlux₁ p) *
          (liftL2 dx p * (starRingEnd ℂ) (liftL2 φ p)).re +
        (χ (dipoleLift p) * ddGroundLogFlux₂ p) *
          (liftL2 dy p * (starRingEnd ℂ) (liftL2 φ p)).re) =
    χ (dipoleLift p) *
        (ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p) -
      deriv χ (dipoleLift p) * ddGroundCurrentCoeff p * ‖liftL2 φ p‖ ^ 2 := by
  by_cases hp : dipoleLift p ∈ tsupport χ
  · have hs := hχs hp
    have hb := contDiffAt_ddGroundLogFlux hs.1 hs.2
    have hsc : DifferentiableAt ℝ dipoleLift p := by unfold dipoleLift; fun_prop
    have hx : partialX (fun q ↦ χ (dipoleLift q) * ddGroundLogFlux₁ q) p =
        deriv χ (dipoleLift p) * partialX dipoleLift p * ddGroundLogFlux₁ p +
          χ (dipoleLift p) * partialX ddGroundLogFlux₁ p := by
      exact (((hχ.differentiable (by simp) _).hasDerivAt.comp p.1
        (hasDerivAt_partialX hsc)).mul
          (hasDerivAt_partialX (hb.1.differentiableAt (by simp)))).deriv
    have hy : partialY (fun q ↦ χ (dipoleLift q) * ddGroundLogFlux₂ q) p =
        deriv χ (dipoleLift p) * partialY dipoleLift p * ddGroundLogFlux₂ p +
          χ (dipoleLift p) * partialY ddGroundLogFlux₂ p := by
      exact (((hχ.differentiable (by simp) _).hasDerivAt.comp p.2
        (hasDerivAt_partialY hsc)).mul
          (hasDerivAt_partialY (hb.2.differentiableAt (by simp)))).deriv
    rw [ddPicone_defect hs.1 hs.2, ddGroundCurrentCoeff_eq_flux hs.1 hs.2]
    unfold divergence
    rw [hx, hy]
    ring
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hp
    have hc : χ (dipoleLift p) = 0 := hz.self_of_nhds
    have hd : deriv χ (dipoleLift p) = 0 := by
      rw [hz.deriv_eq]
      exact deriv_const _ _
    have hv := hz.comp_tendsto
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt
    have hx : ∀ᶠ q in 𝓝 p, χ (dipoleLift q) * ddGroundLogFlux₁ q = 0 := by
      filter_upwards [hv] with q hq
      change χ (dipoleLift q) = 0 at hq
      simp [hq]
    have hy : ∀ᶠ q in 𝓝 p, χ (dipoleLift q) * ddGroundLogFlux₂ q = 0 := by
      filter_upwards [hv] with q hq
      change χ (dipoleLift q) = 0 at hq
      simp [hq]
    simp [divergence, partialX_eq_zero_of_eventually hx,
      partialY_eq_zero_of_eventually hy, hc, hd]

/-- Weak Picone tested against an annular stream cutoff. This formula is proved
    directly in the Fourier H¹ domain, without smooth density or boundary traces. -/
theorem ddPicone_cutoff_zero {φ dx dy : L2}
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    (∫ p in cellSquare,
      χ (dipoleLift p) *
          (ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p) -
        deriv χ (dipoleLift p) * ddGroundCurrentCoeff p * ‖liftL2 φ p‖ ^ 2) = 0 := by
  let W₁ (p : ℝ × ℝ) := χ (dipoleLift p) * ddGroundLogFlux₁ p
  let W₂ (p : ℝ × ℝ) := χ (dipoleLift p) * ddGroundLogFlux₂ p
  let H (p : ℝ × ℝ) := divergence W₁ W₂ p * ‖liftL2 φ p‖ ^ 2 +
    2 * (W₁ p * (liftL2 dx p * (starRingEnd ℂ) (liftL2 φ p)).re +
      W₂ p * (liftL2 dy p * (starRingEnd ℂ) (liftL2 φ p)).re)
  obtain ⟨hW₁, hW₂⟩ := contDiff_groundFlux_cutoff hχ hχs
  obtain ⟨hpW₁, hpW₂⟩ := periodic_groundFlux_cutoff χ
  change IsPeriodicLift W₁ at hpW₁
  change IsPeriodicLift W₂ at hpW₂
  have hzero : squareIntegral H = 0 := squareIntegral_weak_value_divergence
    (hW₁.of_le (by simp)) (hW₂.of_le (by simp)) hpW₁ hpW₂ hdx hdy
  have hdiv : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real (hW₁.of_le (by simp))).add
      (continuous_partialY_real (hW₂.of_le (by simp)))
  have hpdiv : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hm (f : L2) : Measurable (liftL2 f) :=
    (Lp.stronglyMeasurable f).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have hmH : Measurable H := by
    dsimp only [H]
    have hw₁ : Continuous W₁ := hW₁.continuous
    have hw₂ : Continuous W₂ := hW₂.continuous
    fun_prop
  have hpH : IsPeriodicLift H := by
    intro p
    have hu := isPeriodicLift_liftL2 φ p
    have hx := isPeriodicLift_liftL2 dx p
    have hy := isPeriodicLift_liftL2 dy p
    constructor <;>
      simp only [H, (hpdiv p).1, (hpdiv p).2, (hpW₁ p).1, (hpW₁ p).2,
        (hpW₂ p).1, (hpW₂ p).2, hu.1, hu.2, hx.1, hx.2, hy.1, hy.2]
  have hH0 : ∀ p, dipoleLift p ≤ 0 → H p = 0 := by
    intro p hp
    have hn : dipoleLift p ∉ tsupport χ := fun h ↦ not_lt_of_ge hp (hχs h).1
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    have hc : χ (dipoleLift p) = 0 := hz.self_of_nhds
    have hd : deriv χ (dipoleLift p) = 0 := by
      rw [hz.deriv_eq]
      exact deriv_const _ _
    have heq := ddPicone_cutoff_algebra hχ hχs φ dx dy p
    change H p = _ at heq
    rw [heq, hc, hd]
    ring
  rw [squareIntegral_eq_setIntegral_cellSquare hpH hmH hH0] at hzero
  calc
    _ = ∫ p in cellSquare, H p :=
      setIntegral_congr_fun isOpen_cellSquare.measurableSet fun p _ ↦
        (ddPicone_cutoff_algebra hχ hχs φ dx dy p).symm
    _ = 0 := hzero

private theorem picone_current_band_integrable (φ : L2) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    IntegrableOn (fun p ↦ ddGroundCurrentCoeff p *
      ‖continuousRep φ (torusProj p)‖ ^ 2)
      {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} := by
  let K : Set (ℝ × ℝ) := closure cellSquare ∩
    {p | 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b}
  have hs : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hbc : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  have hK : IsCompact K := hbc.isCompact_closure.inter_right
    ((isClosed_le continuous_const hs).inter (isClosed_le hs continuous_const))
  have hc : ContinuousOn (fun p ↦ ddGroundCurrentCoeff p *
      ‖continuousRep φ (torusProj p)‖ ^ 2) K := by
    intro p hp
    have h0 : 0 < dipoleLift p := by linarith [hp.2.1]
    have h2 : dipoleLift p < 2 := by linarith [hp.2.2]
    exact ((continuousAt_ddGroundCurrentCoeff h0.ne'
      (gradSq_dipoleLift_pos h0 h2).ne').mul
        (((continuousRep φ).continuous.comp
          isOpenQuotientMap_torusProj.continuous).continuousAt.norm.pow 2)).continuousWithinAt
  exact (hc.integrableOn_compact hK).mono_set fun p hp ↦ ⟨subset_closure hp.1, hp.2⟩

private theorem integrable_stream_cutoff {F : ℝ × ℝ → ℝ} {a b : ℝ}
    (hF : IntegrableOn F {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b})
    {χ : ℝ → ℝ} (hχ : Measurable χ) {C : ℝ} (hC : ∀ s, |χ s| ≤ C)
    (hsupp : ∀ s, χ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    IntegrableOn (fun p ↦ χ (dipoleLift p / 2) * F p) cellSquare := by
  have hm : Measurable (fun p ↦ χ (dipoleLift p / 2)) :=
    hχ.comp (by unfold dipoleLift; fun_prop)
  have hi : IntegrableOn (fun p ↦ χ (dipoleLift p / 2) * F p)
      {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} :=
    hF.bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using hC (dipoleLift p / 2))
  apply hi.of_forall_sdiff_eq_zero isOpen_cellSquare.measurableSet
  intro p hp
  have hz : χ (dipoleLift p / 2) = 0 := by
    by_contra hn
    obtain ⟨hl, hu⟩ := hsupp _ hn
    exact hp.2 ⟨hp.1, by linarith, by linarith⟩
  simp [hz]

/-- The weak cutoff formula gives Picone on annuli outside one common null set
    of stream levels. Boundary values use the continuous representative. -/
theorem ddPicone_annular {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy) :
    ∃ N : Set ℝ, volume N = 0 ∧
      ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
        (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'},
          ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p) =
          ddGroundCurrent φ (2 * h) - ddGroundCurrent φ (2 * h') := by
  let J := fun p ↦ ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p
  let B := fun p ↦ ddGroundCurrentCoeff p * ‖continuousRep φ (torusProj p)‖ ^ 2
  have hJ (a b : ℝ) (ha : 0 < a) (_hb : b < 1) :
      IntegrableOn J {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} := by
    have hi : IntegrableOn J (ddTruncatedCell a) :=
      ((ddRawEnergy_integrable φ dx dy ha).sub
        (ddPiconeGradient_integrable φ dx dy ha)).sub
          ((dd_piconePotential_integrable hφ).mono_set fun p hp ↦ hp.1)
    exact hi.mono_set fun p hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩
  have hB (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
      IntegrableOn B {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} :=
    picone_current_band_integrable φ ha hb
  have hcut : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, f s ≠ 0 → a ≤ s ∧ s ≤ b) →
        (∫ p in cellSquare, f (dipoleLift p / 2) * J p) =
          ∫ p in cellSquare, deriv f (dipoleLift p / 2) / 2 * B p := by
    intro f hf a b ha hb hsupp
    let χ := fun s ↦ f (s / 2)
    have hχ : ContDiff ℝ ∞ χ := hf.comp (contDiff_id.div_const 2)
    have hχb : tsupport χ ⊆ Icc (2 * a) (2 * b) := by
      apply closure_minimal _ isClosed_Icc
      intro s hs
      obtain ⟨hl, hu⟩ := hsupp (s / 2) hs
      exact ⟨by linarith, by linarith⟩
    have hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2 := fun s hs ↦
      ⟨by linarith [(hχb hs).1], by linarith [(hχb hs).2]⟩
    have hdχ (s : ℝ) : deriv χ s = deriv f (s / 2) / 2 := by
      have h := ((hf.differentiable (by simp) (s / 2)).hasDerivAt.comp s
        ((hasDerivAt_id s).div_const 2)).deriv
      convert h using 1
      · rfl
      · ring
    have hdsupp : ∀ s, deriv f s ≠ 0 → a ≤ s ∧ s ≤ b := by
      intro s hs
      by_contra hn
      have hz : f =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds
          (show s ∉ Icc a b from hn)] with t ht
        by_contra hne
        exact ht (hsupp t hne)
      exact hs (by rw [hz.deriv_eq, deriv_const])
    have hcpt {v : ℝ → ℝ} (hv : ∀ s, v s ≠ 0 → a ≤ s ∧ s ≤ b) :
        HasCompactSupport v := HasCompactSupport.intro isCompact_Icc fun s hs ↦ by
          by_contra hn
          exact hs (hv s hn)
    have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
    obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support (hcpt hsupp)
    obtain ⟨C', hC'⟩ := hdc.bounded_above_of_compact_support (hcpt hdsupp)
    have iJ := integrable_stream_cutoff (hJ a b ha hb) hf.continuous.measurable hC hsupp
    have iB := integrable_stream_cutoff (hB a b ha hb) (hdc.measurable.div_const 2)
      (C := C' / 2) (fun s ↦ by rw [abs_div, abs_two]; gcongr; exact hC' s)
      (fun s hs ↦ hdsupp s (fun hz ↦ hs (by simp [hz])))
    have hz : (∫ p in cellSquare, f (dipoleLift p / 2) * J p -
        deriv f (dipoleLift p / 2) / 2 * B p) = 0 := by
      calc
        _ = ∫ p in cellSquare, χ (dipoleLift p) * J p -
            deriv χ (dipoleLift p) * ddGroundCurrentCoeff p * ‖liftL2 φ p‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae (ae_torusProj (coeFn_eq_continuousRep hφ))]
            with p hp
          change liftL2 φ p = continuousRep φ (torusProj p) at hp
          rw [hdχ, hp]
          dsimp only [χ, B]
          ring
        _ = 0 := ddPicone_cutoff_zero hdx hdy hχ hχs
    rw [integral_sub iJ iB] at hz
    linarith
  obtain ⟨N, hN, hid⟩ := annular_virial_of_cutoff_identity hJ hB hcut
  refine ⟨N, hN, ?_⟩
  intro h h' h0 hh' h'1 hn hn'
  simpa only [ddGroundCurrent, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    hid h h' h0 hh' h'1 hn hn'

end NoEmbeddedEigenvalues
