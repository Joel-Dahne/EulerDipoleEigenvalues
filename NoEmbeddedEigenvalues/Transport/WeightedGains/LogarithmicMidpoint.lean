import NoEmbeddedEigenvalues.Transport.WeightedGains.LogarithmicDivision
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Ordinary and logarithmic control of the midpoint coefficient

The phase derivative costs Q/h, not a derivative of the logarithmic weight.
All derivative representatives are specified explicitly. Local H¹ is retained:
an a.e. classical derivative alone would not justify weak reconstruction.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Phase relating the quarter endpoint quotient to the midpoint. -/
def quarterMidpointPhase (lam h : ℝ) : ℂ :=
  Complex.exp (2 * Complex.I * (lam : ℂ) * (eighthPeriod h : ℂ))

/-- Midpoint coefficient obtained from the endpoint quotient and the half numerator. -/
def quarterMidpoint (lam : ℝ) (Q : ℝ → ℂ) (g : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  Complex.I * quarterMidpointPhase lam h * Q h + Complex.I * quarterHalfNumerator lam g h

/-- Specified derivative of the midpoint coefficient. -/
def quarterMidpointDerivative (lam : ℝ) (Q Q₁ B₁ : ℝ → ℂ) (h : ℝ) : ℂ :=
  Complex.I * quarterMidpointPhase lam h *
    (Q₁ h + (2 * Complex.I * (lam : ℂ) * ((deriv eighthPeriod h : ℝ) : ℂ)) * Q h) +
      Complex.I * B₁ h

private theorem interval_memLp_top {a b : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f ⊤ (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound
    ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x (Ioo_subset_Icc_self hx)

/-- C¹ multiplication on a compact interval, with a supplied continuous derivative. -/
private theorem interval_mul_c1 {a b : ℝ} {F D M M₁ : ℝ → ℂ}
    (hF : HasIntervalH1 a b F D) (hM : ContDiffOn ℝ 1 M (Icc a b))
    (hM₁ : ContinuousOn M₁ (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt M (M₁ x) x) :
    HasIntervalH1 a b (fun x ↦ M x * F x) (fun x ↦ M₁ x * F x + M x * D x) := by
  refine ⟨(interval_memLp_top hM.continuousOn).mul hF.memLp_value, ?_, ?_, ?_⟩
  · exact MemLp.add (f := fun x ↦ M₁ x * F x) (g := fun x ↦ M x * D x)
      ((interval_memLp_top hM₁).mul hF.memLp_value)
      ((interval_memLp_top hM.continuousOn).mul hF.memLp_derivative)
  · intro c d hac hcd hdb
    have hsub : uIcc c d ⊆ Icc a b := by
      rw [uIcc_of_le hcd]
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨K, hK⟩ := (hM.mono hsub).exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc
    exact hK.absolutelyContinuousOnInterval.smul
      (hF.locally_absolutelyContinuous c d hac hcd hdb)
  · filter_upwards [hF.hasDerivAt_ae] with x hx hxI
    exact (hd x hxI).mul (hx hxI)

private theorem interval_restrict {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hac : a ≤ c) (hdb : d ≤ b) :
    HasIntervalH1 c d F D := by
  have hs : Ioo c d ⊆ Ioo a b := fun _ hx ↦ ⟨hac.trans_lt hx.1, hx.2.trans_le hdb⟩
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono hs le_rfl),
    h.memLp_derivative.mono_measure (Measure.restrict_mono hs le_rfl),
    fun u v hcu huv hvd ↦ h.locally_absolutelyContinuous u v
      (hac.trans_lt hcu) huv (hvd.trans_le hdb),
    h.hasDerivAt_ae.mono fun x hx hxcd ↦ hx (hs hxcd)⟩

private theorem phase_contDiff (lam : ℝ) :
    ContDiffOn ℝ 1 (quarterMidpointPhase lam) (Ioo 0 1) := by
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_eighthPeriod.of_le (by simp)))).cexp)

private theorem period_deriv_continuous : ContinuousOn (deriv eighthPeriod) (Ioo 0 1) := by
  exact contDiffOn_eighthPeriod.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)

private theorem phase_deriv (lam : ℝ) {h : ℝ} (hh : h ∈ Ioo 0 1) :
    HasDerivAt (quarterMidpointPhase lam)
      (quarterMidpointPhase lam h *
        (2 * Complex.I * (lam : ℂ) * ((deriv eighthPeriod h : ℝ) : ℂ))) h := by
  have hd := ((contDiffOn_eighthPeriod.contDiffAt (isOpen_Ioo.mem_nhds hh)).differentiableAt
    (by simp)).hasDerivAt
  exact (hd.ofReal_comp.const_mul (2 * Complex.I * (lam : ℂ))).cexp

/-- Local interval H¹ of the exact midpoint, retaining both supplied derivatives. -/
theorem quarterMidpoint_h1Loc {lam b : ℝ} (hb : b < 1)
    {Q Q₁ B₁ : ℝ → ℂ} {g : ℝ × ℝ → ℂ}
    (hQ : HasIntervalH1 0 b Q Q₁)
    (hB : HasIntervalH1Loc 0 b (quarterHalfNumerator lam g) B₁) :
    HasIntervalH1Loc 0 b (quarterMidpoint lam Q g)
      (quarterMidpointDerivative lam Q Q₁ B₁) := by
  let M : ℝ → ℂ := fun h ↦ Complex.I * quarterMidpointPhase lam h
  intro c d hc hcd hd
  have hcdsub : Icc c d ⊆ Ioo 0 1 := fun _ hx ↦ ⟨hc.trans_le hx.1, hx.2.trans_lt (hd.trans hb)⟩
  have hm : ContDiffOn ℝ 1 M (Icc c d) :=
    contDiffOn_const.mul ((phase_contDiff lam).mono hcdsub)
  have hm₁ : ContinuousOn (fun h ↦ M h *
      (2 * Complex.I * (lam : ℂ) * ((deriv eighthPeriod h : ℝ) : ℂ))) (Icc c d) := by
    exact hm.continuousOn.mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (period_deriv_continuous.mono hcdsub)))
  have hmder (h : ℝ) (hh : h ∈ Ioo c d) : HasDerivAt M
      (M h * (2 * Complex.I * (lam : ℂ) * ((deriv eighthPeriod h : ℝ) : ℂ))) h := by
    simpa only [M, mul_assoc] using
      (phase_deriv lam (hcdsub (Ioo_subset_Icc_self hh))).const_mul Complex.I
  have hh := interval_mul_c1 (interval_restrict hQ hc.le hd.le) hm hm₁ hmder
  convert hh.add ((hB c d hc hcd hd).smul Complex.I) using 1
  · rfl
  · funext h
    dsimp [quarterMidpointDerivative, M]
    ring

/-- Ordinary midpoint gain: the phase derivative costs Q/h, without a logarithmic
weight or a change of the supplied scalar derivative representatives. -/
theorem midpoint_gain {lam b K : ℝ} (hb : b < 1)
    {Q Q₁ B₁ : ℝ → ℂ} {g : ℝ × ℝ → ℂ}
    (hQ : HasIntervalH1 0 b Q Q₁)
    (hB : HasIntervalH1Loc 0 b (quarterHalfNumerator lam g) B₁)
    (hK : ∀ h ∈ Ioo 0 b, |h * deriv eighthPeriod h| ≤ K)
    (hQh : MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 b)))
    (hB₁ : MemLp B₁ 2 (volume.restrict (Ioo 0 b))) :
    HasIntervalH1Loc 0 b (quarterMidpoint lam Q g) (quarterMidpointDerivative lam Q Q₁ B₁) ∧
      MemLp (quarterMidpointDerivative lam Q Q₁ B₁) 2 (volume.restrict (Ioo 0 b)) := by
  refine ⟨quarterMidpoint_h1Loc hb hQ hB, ?_⟩
  have hsub : Ioo 0 b ⊆ Ioo 0 1 := fun _ hh ↦ ⟨hh.1, hh.2.trans hb⟩
  let M : ℝ → ℂ := fun h ↦ Complex.I * quarterMidpointPhase lam h
  let R : ℝ → ℂ := fun h ↦ (2 * Complex.I * (lam : ℂ)) * ((h * deriv eighthPeriod h : ℝ) : ℂ)
  have hMc : ContinuousOn M (Ioo 0 b) :=
    continuousOn_const.mul ((phase_contDiff lam).continuousOn.mono hsub)
  have hRc : ContinuousOn R (Ioo 0 b) := continuousOn_const.mul
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.mul (period_deriv_continuous.mono hsub)))
  have hMtop : MemLp M ⊤ (volume.restrict (Ioo 0 b)) := by
    apply memLp_top_of_bound (hMc.aestronglyMeasurable measurableSet_Ioo) 1
    exact Eventually.of_forall fun h ↦ by
      simp [M, quarterMidpointPhase, Complex.norm_exp]
  have hRtop : MemLp R ⊤ (volume.restrict (Ioo 0 b)) := by
    apply memLp_top_of_bound (hRc.aestronglyMeasurable measurableSet_Ioo)
      (‖2 * Complex.I * (lam : ℂ)‖ * K)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    simp only [R, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using hK h hh) (by positivity)
  have hs := hQ.memLp_derivative.add (hRtop.mul hQh)
  have hf := (hMtop.mul hs).add (hB₁.const_mul Complex.I)
  apply hf.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  dsimp [M, R, quarterMidpointDerivative]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hh.1.ne']

/-- The logarithmic midpoint gain (`lem:log-midpoint-gain`). -/
theorem log_midpoint_gain {lam b K : ℝ} (hb : b < 1)
    {Q Q₁ B₁ : ℝ → ℂ} {g : ℝ × ℝ → ℂ}
    (hQ : HasIntervalH1 0 b Q Q₁)
    (hB : HasIntervalH1Loc 0 b (quarterHalfNumerator lam g) B₁)
    (hK : ∀ h ∈ Ioo 0 b, |h * deriv eighthPeriod h| ≤ K)
    (hQw : MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ)) 2
      (volume.restrict (Ioo 0 b)))
    (hQ₁w : MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h) 2
      (volume.restrict (Ioo 0 b)))
    (hBw : MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * B₁ h) 2
      (volume.restrict (Ioo 0 b))) :
    HasIntervalH1Loc 0 b (quarterMidpoint lam Q g) (quarterMidpointDerivative lam Q Q₁ B₁) ∧
      MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) *
        quarterMidpointDerivative lam Q Q₁ B₁ h) 2 (volume.restrict (Ioo 0 b)) := by
  have hsub : Ioo 0 b ⊆ Ioo 0 1 := fun _ hh ↦ ⟨hh.1, hh.2.trans hb⟩
  let M : ℝ → ℂ := fun h ↦ Complex.I * quarterMidpointPhase lam h
  let R : ℝ → ℂ := fun h ↦ (2 * Complex.I * (lam : ℂ)) * ((h * deriv eighthPeriod h : ℝ) : ℂ)
  have hMc : ContinuousOn M (Ioo 0 b) :=
    continuousOn_const.mul ((phase_contDiff lam).continuousOn.mono hsub)
  have hRc : ContinuousOn R (Ioo 0 b) := continuousOn_const.mul
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.mul (period_deriv_continuous.mono hsub)))
  constructor
  · exact quarterMidpoint_h1Loc hb hQ hB
  · have hphase (h : ℝ) : ‖quarterMidpointPhase lam h‖ = 1 := by
      rw [quarterMidpointPhase, Complex.norm_exp]
      simp
    have hMtop : MemLp M ⊤ (volume.restrict (Ioo 0 b)) := by
      apply memLp_top_of_bound (hMc.aestronglyMeasurable measurableSet_Ioo) 1
      exact Eventually.of_forall fun h ↦ by simp [M, hphase]
    have hRtop : MemLp R ⊤ (volume.restrict (Ioo 0 b)) := by
      apply memLp_top_of_bound (hRc.aestronglyMeasurable measurableSet_Ioo)
        (‖2 * Complex.I * (lam : ℂ)‖ * K)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      simp only [R, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using hK h hh) (by positivity)
    have hs := MemLp.add (f := fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h)
      (g := fun h ↦ R h * ((Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ)))
      hQ₁w (hRtop.mul hQw)
    have hf := MemLp.add (f := fun h ↦ M h *
        ((Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h +
          R h * ((Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ))))
      (g := fun h ↦ Complex.I * ((Real.sqrt (logLevelWeight h) : ℂ) * B₁ h))
      (hMtop.mul hs) (hBw.const_mul Complex.I)
    apply hf.ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    dsimp [M, R, quarterMidpointDerivative]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hh.1.ne']

/-- The scalar midpoint is the value of an orbitwise ACL representative
(`lem:quarter-midpoint-reconstruction`), not a raw spatial trace. -/
theorem quarter_midpoint_reconstruction_with_rep {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hA : orbitAnnulus 0 b ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) f) {Q : ℝ → ℂ}
    (hdiv : ∀ h ∈ Ioo 0 b, quarterDivisor lam κ h * Q h = quarterNumerator lam g h)
    (hne : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), quarterDivisor lam κ h ≠ 0) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
      (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
      (∀ᵐ t, HasDerivAt Z (Complex.I * ((lam : ℂ) * Z t + g (dipoleOrbit h t))) t) ∧
      Z 0 = quarterMidpoint lam Q g h ∧
      ∀ t, Z t = Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ)) * quarterMidpoint lam Q g h +
        Complex.I * ∫ u in 0..t,
          Complex.exp (Complex.I * ((lam * (t - u) : ℝ) : ℂ)) * g (dipoleOrbit h u) := by
  obtain ⟨Em, Ep, _, hprof⟩ := quarter_endpoint_formula hκ hp hb hb1 hA hg hfg hvκ hfκ
  filter_upwards [hprof, hne, ae_restrict_mem measurableSet_Ioo] with h hZ hn hh
  obtain ⟨Z, hzeq, _, hac, hode, hzm, _, _, hEm, _⟩ := hZ
  have hEmQ : Em h =
      Complex.I * Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) * Q h := by
    apply mul_left_cancel₀ hn
    rw [hEm, ← hdiv h hh]
    ring
  have hcont : Continuous (fun t ↦ g (dipoleOrbit h t)) := by
    apply hg.comp_continuous
      (continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt)
    intro t
    have hm : dipoleOrbit h t ∈ puncturedCell := by
      simpa only [actionAngleInv,
        div_mul_cancel₀ t (orbitPeriod_pos hh.1 (hh.2.trans hb1)).ne'] using
        actionAngleInv_mem_puncturedCell hh.1 (hh.2.trans hb1) (t / orbitPeriod h)
    exact hA ⟨hm, (levelCoord_dipoleOrbit hh.1 (hh.2.trans hb1) t).symm ▸ hh⟩
  have hint := transport_integratingFactor (hac (-eighthPeriod h) 0)
    (hcont.intervalIntegrable _ _) (hode.mono fun _ ht _ ↦ ht)
  have hexp : Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) = quarterMidpointPhase lam h := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hhalf : (∫ t in (-eighthPeriod h)..0,
      Complex.exp (-(Complex.I * (lam : ℂ) * (t : ℂ))) * g (dipoleOrbit h t)) =
        quarterHalfNumerator lam g h := by
    apply intervalIntegral.integral_congr
    intro t _
    push_cast
    rw [show -(Complex.I * (lam : ℂ) * (t : ℂ)) =
      -Complex.I * ((lam : ℂ) * (t : ℂ)) by ring, mul_comm]
  rw [hzm, hEmQ, hhalf] at hint
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_neg, mul_neg, neg_neg, Complex.ofReal_mul] at hint
  have hmid : Z 0 = quarterMidpoint lam Q g h := by
    dsimp [quarterMidpoint]
    rw [← hexp]
    push_cast
    simp only [mul_assoc] at hint ⊢
    linear_combination hint
  refine ⟨Z, hzeq, hac, hode, hmid, ?_⟩
  intro t
  have ht := transport_integratingFactor (hac 0 t)
    (hcont.intervalIntegrable _ _) (hode.mono fun _ ht _ ↦ ht)
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, hmid] at ht
  let e := Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ))
  have he : e * Complex.exp (-(Complex.I * (lam : ℂ) * (t : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    push_cast
    congr 1
    ring
  have hconv : e * (∫ u in 0..t,
      Complex.exp (-(Complex.I * (lam : ℂ) * (u : ℂ))) * g (dipoleOrbit h u)) =
      ∫ u in 0..t, Complex.exp (Complex.I * ((lam * (t - u) : ℝ) : ℂ)) * g (dipoleOrbit h u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [e]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← hconv]
  change Z t = e * quarterMidpoint lam Q g h + _
  linear_combination e * ht - he * Z t

/-- The scalar midpoint is the value of an orbitwise ACL representative
(`lem:quarter-midpoint-reconstruction`), not a raw spatial trace. -/
theorem quarter_midpoint_reconstruction {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v g)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hA : orbitAnnulus 0 b ⊆ U)
    (hg : Continuous g) (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) v)
    (hgκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) g) {Q : ℝ → ℂ}
    (hdiv : ∀ h ∈ Ioo 0 b, quarterDivisor lam κ h * Q h = quarterNumerator lam g h)
    (hne : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), quarterDivisor lam κ h ≠ 0) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v g (dipoleOrbit h t)) ∧
      (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
      (∀ᵐ t, HasDerivAt Z (Complex.I * ((lam : ℂ) * Z t + g (dipoleOrbit h t))) t) ∧
      Z 0 = quarterMidpoint lam Q g h ∧
      ∀ t, Z t = Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ)) * quarterMidpoint lam Q g h +
        Complex.I * ∫ u in 0..t,
          Complex.exp (Complex.I * ((lam * (t - u) : ℝ) : ℂ)) * g (dipoleOrbit h u) := by
  exact quarter_midpoint_reconstruction_with_rep hκ hp hb hb1 hA hg.continuousOn
    (Eventually.of_forall fun _ ↦ rfl) hvκ hgκ hdiv hne

end NoEmbeddedEigenvalues
