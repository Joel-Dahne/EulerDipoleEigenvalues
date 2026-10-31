import NoEmbeddedEigenvalues.OddOddVirial
import NoEmbeddedEigenvalues.Picone

/-!
# Picone on positive stream truncations

Blueprint: `lem:dd-truncated-picone`.

Bulk densities use supplied Fourier derivatives; the boundary current uses the
continuous representative. On a positive truncation the raw coefficients are
bounded even near the center, although their totalized center values need not
be their limits. The current on each regular level is continuous.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- The comparison function is bounded below without a residual sign certificate. -/
theorem one_le_ddGround (p : ℝ × ℝ) : 1 ≤ ddGround p := by
  have hr : 0 ≤ gradSq dipoleLift p := by
    rw [gradSq_dipoleLift]
    positivity
  have hr2 : gradSq dipoleLift p ≤ 2 := by
    rw [gradSq_dipoleLift]
    nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
  have hlog : Real.log (gradSq dipoleLift p / 2) ≤ 0 := by
    rcases eq_or_lt_of_le hr with hz | hp
    · simp [← hz]
    · exact Real.log_nonpos (by positivity) (by linarith)
  unfold ddGround
  nlinarith [sq_nonneg (dipoleLift p), sq_nonneg (gradSq dipoleLift p),
    mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ gradSq dipoleLift p ^ 2 / 256) hlog]

/-- Smoothness is only asserted off the critical points of the dipole. -/
theorem contDiffAt_ddGround {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    ContDiffAt ℝ ∞ ddGround p := by
  have hlog : gradSq dipoleLift p / 2 ≠ 0 := div_ne_zero hr (by norm_num)
  unfold ddGround
  simp only [gradSq_dipoleLift, dipoleLift] at *
  fun_prop

/-- Partial derivatives of the comparison function are continuous at regular points. -/
private theorem continuousAt_ddGround_partials {p : ℝ × ℝ}
    (hr : gradSq dipoleLift p ≠ 0) :
    ContinuousAt (partialX ddGround) p ∧ ContinuousAt (partialY ddGround) p := by
  have hg : ContDiffAt ℝ 2 ddGround p := (contDiffAt_ddGround hr).of_le (by simp)
  have hn : ∀ᶠ q in 𝓝 p, gradSq dipoleLift q ≠ 0 :=
    (show Continuous (gradSq dipoleLift) by
      rw [gradSq_dipoleLift]; fun_prop).continuousAt.eventually_ne hr
  have hd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ ddGround q :=
    hn.mono fun q hq ↦ (contDiffAt_ddGround hq).differentiableAt (by simp)
  constructor
  · apply (((hg.fderiv_right (m := 1) (by norm_num)).continuousAt).clm_apply
      continuousAt_const).congr
    exact hd.mono fun q hq ↦ (partialX_eq_fderiv hq).symm
  · apply (((hg.fderiv_right (m := 1) (by norm_num)).continuousAt).clm_apply
      continuousAt_const).congr
    exact hd.mono fun q hq ↦ (partialY_eq_fderiv hq).symm

/-- The outward current coefficient has no singularity on a positive regular level. -/
theorem continuousAt_ddGroundCurrentCoeff {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ContinuousAt ddGroundCurrentCoeff p := by
  have hsc : ContinuousAt dipoleLift p := by unfold dipoleLift; fun_prop
  have hrc : ContinuousAt (gradSq dipoleLift) p := by rw [gradSq_dipoleLift]; fun_prop
  have hC : ContinuousAt ddC p := by
    unfold ddC
    exact (hsc.mul (continuousAt_const.sub (hsc.pow 3))).div
      (continuousAt_const.mul hrc) (mul_ne_zero (by norm_num) hr)
  have hA : ContinuousAt ddA p := by
    unfold ddA
    exact (((continuousAt_const.mul (hsc.pow 2)).div_const 3).add
      (continuousAt_const.div (continuousAt_const.mul hsc)
        (mul_ne_zero (by norm_num) hs))).sub hC
  have hg := (contDiffAt_ddGround hr).continuousAt
  have hgp := continuousAt_ddGround_partials hr
  have hgn : ddGround p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_ddGround p))
  unfold ddGroundCurrentCoeff
  rw [partialX_dipoleLift, partialY_dipoleLift]
  exact (hA.neg.mul (((by fun_prop : ContinuousAt (fun q : ℝ × ℝ ↦ -Real.sin q.1) p).mul
    hgp.1).add ((by fun_prop : ContinuousAt (fun q : ℝ × ℝ ↦ -Real.sin q.2) p).mul
    hgp.2))).div hg hgn

/-- Absolute integrability of the raw energy needs only L² values, not parity,
    Fourier derivative relations, or the eigenfunction equation. -/
theorem ddRawEnergy_integrable (φ dx dy : L2) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) := by
  have hb : Bornology.IsBounded (ddTruncatedCell ε) :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  have h := ddVirialDensity_integrable hε (memLp_liftL2 φ hb)
    (MemLp.zero : MemLp (fun _ : ℝ × ℝ ↦ (0 : ℂ)) 2 (volume.restrict (ddTruncatedCell ε)))
    (memLp_liftL2 dx hb) (memLp_liftL2 dy hb)
  convert h using 1
  ext p
  simp [ddRawEnergy, ddVirialDensity]
  ring

/-- Every regular-level current is integrable over a full orbit period. Only
    continuity of the chosen value representative is used. -/
theorem ddGroundCurrent_intervalIntegrable (φ : L2) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
      ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
      volume 0 (orbitPeriod (ε / 2)) := by
  have h0 : 0 < ε / 2 := by linarith [hε.1]
  have h1 : ε / 2 < 1 := by linarith [hε.2]
  have ho : Continuous (fun t : ℝ ↦ dipoleOrbit (ε / 2) t) :=
    continuous_dipoleOrbit.comp (f := fun t : ℝ ↦ (ε / 2, t))
      (continuous_const.prodMk continuous_id)
  have hc : Continuous (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs := dipoleLift_dipoleOrbit h0 h1 t
    have hp : 0 < dipoleLift (dipoleOrbit (ε / 2) t) := by rw [hs]; positivity
    have hp2 : dipoleLift (dipoleOrbit (ε / 2) t) < 2 := by rw [hs]; linarith
    exact (continuousAt_ddGroundCurrentCoeff hp.ne'
      (gradSq_dipoleLift_pos hp hp2).ne').comp ho.continuousAt
  exact (hc.mul (((continuousRep φ).continuous.comp
    (isOpenQuotientMap_torusProj.continuous.comp ho)).norm.pow 2)).intervalIntegrable _ _

/-- The logarithmic coefficient occurring in the first derivatives of the ground state. -/
private def groundLogCoeff (r : ℝ) : ℝ :=
  r * (2 * Real.log (r / 2) + 1) / 128

private theorem groundLogCoeff_bound {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) :
    |groundLogCoeff r| ≤ 1 / 8 := by
  rcases eq_or_lt_of_le hr with hz | hp
  · simp [← hz, groundLogCoeff]
  have hl := (Real.abs_log_mul_self_lt (r / 2) (by positivity) (by linarith)).le
  have hb : |r * Real.log (r / 2)| ≤ 2 := by
    have he : r * Real.log (r / 2) = 2 * (Real.log (r / 2) * (r / 2)) := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have ht : |r * (2 * Real.log (r / 2) + 1)| ≤ 6 := by
    calc
      _ = |2 * (r * Real.log (r / 2)) + r| := by congr 1; ring
      _ ≤ |2 * (r * Real.log (r / 2))| + |r| := abs_add_le _ _
      _ ≤ 6 := by
        rw [abs_mul, abs_of_nonneg hr]
        norm_num only
        linarith
  unfold groundLogCoeff
  rw [abs_div]
  norm_num only
  linarith

/-- Explicit first derivative on the regular set; the logarithmic coefficient
    has a bounded continuous extension to the center. -/
theorem partialX_ddGround {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddGround p =
      -Real.sin p.1 * Real.cos p.2 / 8 -
        groundLogCoeff (gradSq dipoleLift p) * Real.sin p.1 * Real.cos p.1 := by
  have hdr := hasDerivAt_partialX
    (show DifferentiableAt ℝ (gradSq dipoleLift) p by rw [gradSq_dipoleLift]; fun_prop)
  have hds := hasDerivAt_partialX
    (show DifferentiableAt ℝ dipoleLift p by unfold dipoleLift; fun_prop)
  have h := (((hdr.add (hds.pow 2)).div_const 16).const_add 1).sub
    (((hdr.pow 2).div_const 256).mul ((hdr.div_const 2).log (div_ne_zero hr (by norm_num))))
  change deriv (fun t ↦ ddGround (t, p.2)) p.1 = _
  convert h.deriv using 1
  · rfl
  · simp only [partialX_gradSq_dipoleLift, partialX_dipoleLift, dipoleLift, groundLogCoeff,
      Pi.pow_apply, Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, Prod.mk.eta]
    field_simp [hr]
    ring

theorem partialY_ddGround {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddGround p =
      -Real.sin p.2 * Real.cos p.1 / 8 -
        groundLogCoeff (gradSq dipoleLift p) * Real.sin p.2 * Real.cos p.2 := by
  have hdr := hasDerivAt_partialY
    (show DifferentiableAt ℝ (gradSq dipoleLift) p by rw [gradSq_dipoleLift]; fun_prop)
  have hds := hasDerivAt_partialY
    (show DifferentiableAt ℝ dipoleLift p by unfold dipoleLift; fun_prop)
  have h := (((hdr.add (hds.pow 2)).div_const 16).const_add 1).sub
    (((hdr.pow 2).div_const 256).mul ((hdr.div_const 2).log (div_ne_zero hr (by norm_num))))
  change deriv (fun t ↦ ddGround (p.1, t)) p.2 = _
  convert h.deriv using 1
  · rfl
  · simp only [partialY_gradSq_dipoleLift, partialY_dipoleLift, dipoleLift, groundLogCoeff,
      Pi.pow_apply, Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, Prod.mk.eta]
    field_simp [hr]
    ring

private def groundSlope (x y r : ℝ) : ℝ :=
  -Real.sin x * Real.cos y / 8 - groundLogCoeff r * Real.sin x * Real.cos x

private theorem groundSlope_bound (x y : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) :
    |groundSlope x y r| ≤ 1 := by
  unfold groundSlope
  calc
    _ ≤ |-Real.sin x * Real.cos y / 8| +
        |groundLogCoeff r * Real.sin x * Real.cos x| := abs_sub _ _
    _ = |Real.sin x| * |Real.cos y| / 8 +
        |groundLogCoeff r| * |Real.sin x| * |Real.cos x| := by
      simp only [abs_div, abs_mul, abs_neg]
      norm_num
    _ ≤ 1 * 1 / 8 + (1 / 8) * 1 * 1 := by
      gcongr
      · exact Real.abs_sin_le_one x
      · exact Real.abs_cos_le_one y
      · exact groundLogCoeff_bound hr hr2
      · exact Real.abs_sin_le_one x
      · exact Real.abs_cos_le_one x
    _ ≤ 1 := by norm_num

private def groundPartial (j : Fin 2) (p : ℝ × ℝ) : ℝ :=
  if j = 0 then groundSlope p.1 p.2 (gradSq dipoleLift p)
  else groundSlope p.2 p.1 (gradSq dipoleLift p)

private theorem groundPartial_bound (j : Fin 2) (p : ℝ × ℝ) :
    |groundPartial j p| ≤ 1 := by
  have hr : 0 ≤ gradSq dipoleLift p := by rw [gradSq_dipoleLift]; positivity
  have hr2 : gradSq dipoleLift p ≤ 2 := by
    rw [gradSq_dipoleLift]
    nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
  unfold groundPartial
  split_ifs <;> exact groundSlope_bound _ _ hr hr2

private theorem groundPartial_eq (j : Fin 2) {p : ℝ × ℝ}
    (hr : gradSq dipoleLift p ≠ 0) :
    groundPartial j p = coordPartial j ddGround p := by
  fin_cases j <;> simp [groundPartial, groundSlope, coordPartial,
    partialX_ddGround hr, partialY_ddGround hr]

private theorem ae_regular_ddTruncatedCell {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂volume.restrict (ddTruncatedCell ε), gradSq dipoleLift p ≠ 0 := by
  filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell ε).measurableSet,
    ae_restrict_of_ae ae_cos_fst_ne_cos_snd] with p hp hn
  have hs : 0 < dipoleLift p := hε.trans hp.2
  intro hz
  have h := dipoleLift_mul_le_gradSq p
  rw [hz] at h
  have hs2 : 2 ≤ dipoleLift p := by nlinarith
  unfold dipoleLift at hs2
  exact hn (by linarith [Real.cos_le_one p.1, Real.cos_le_one p.2])

/-- Homogeneity of the quadratic form, including the totalized critical values. -/
theorem ddMatrixForm_real_mul (p : ℝ × ℝ) (c : ℝ) (vx vy : ℂ) :
    ddMatrixForm p ((c : ℂ) * vx) ((c : ℂ) * vy) =
      c ^ 2 * ddMatrixForm p vx vy := by
  have hn : normalDeriv (fun _ ↦ (c : ℂ) * vx) (fun _ ↦ (c : ℂ) * vy) p =
      (c : ℂ) * normalDeriv (fun _ ↦ vx) (fun _ ↦ vy) p := by
    unfold normalDeriv
    ring
  have ht : tangentDeriv (fun _ ↦ (c : ℂ) * vx) (fun _ ↦ (c : ℂ) * vy) p =
      (c : ℂ) * tangentDeriv (fun _ ↦ vx) (fun _ ↦ vy) p := by
    unfold tangentDeriv
    ring
  simp only [ddMatrixForm, hn, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

/-- Positive-truncation divided-gradient integrability uses only L² data.
    Parity and the eigenfunction equation are unnecessary away from the separatrix. -/
theorem ddPiconeGradient_integrable (φ dx dy : L2) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) := by
  have hb : Bornology.IsBounded (ddTruncatedCell ε) :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  let g (j : Fin 2) (d : L2) (p : ℝ × ℝ) : ℂ :=
    liftL2 d p - liftL2 φ p * (groundPartial j p : ℂ) / (ddGround p : ℂ)
  have hg (j : Fin 2) (d : L2) :
      MemLp (g j d) 2 (volume.restrict (ddTruncatedCell ε)) := by
    have hm (f : L2) : Measurable (liftL2 f) :=
      (Lp.stronglyMeasurable f).measurable.comp
        isOpenQuotientMap_torusProj.continuous.measurable
    have mg : Measurable (g j d) := by
      dsimp only [g]
      unfold groundPartial groundSlope groundLogCoeff ddGround
      simp only [gradSq_dipoleLift, dipoleLift]
      split_ifs <;> fun_prop
    apply ((memLp_liftL2 d hb).norm.add (memLp_liftL2 φ hb).norm).mono'
      mg.aestronglyMeasurable
    filter_upwards [] with p
    have hw : 0 < ddGround p := lt_of_lt_of_le zero_lt_one (one_le_ddGround p)
    calc
      ‖g j d p‖ ≤ ‖liftL2 d p‖ + ‖liftL2 φ p * (groundPartial j p : ℂ) /
          (ddGround p : ℂ)‖ := norm_sub_le _ _
      _ = ‖liftL2 d p‖ + ‖liftL2 φ p‖ * |groundPartial j p| / ddGround p := by
        rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hw]
      _ ≤ ‖liftL2 d p‖ + ‖liftL2 φ p‖ := by
        have hp := groundPartial_bound j p
        have hdiv : ‖liftL2 φ p‖ * |groundPartial j p| / ddGround p ≤ ‖liftL2 φ p‖ := by
          apply (div_le_iff₀ hw).mpr
          calc
            _ ≤ ‖liftL2 φ p‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
            _ ≤ _ := by gcongr; exact one_le_ddGround p
        exact add_le_add le_rfl hdiv
  have heq : ∀ᵐ p ∂volume.restrict (ddTruncatedCell ε),
      ∀ j d, g j d p = (ddGround p : ℂ) * ddDividedPartial φ d j p := by
    filter_upwards [ae_regular_ddTruncatedCell hε] with p hp j d
    have hw : (ddGround p : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_ddGround p)))
    dsimp only [g, ddDividedPartial]
    rw [groundPartial_eq j hp]
    field_simp
  have hi := ddVirialDensity_integrable hε MemLp.zero MemLp.zero (hg 0 dx) (hg 1 dy)
  apply hi.congr
  filter_upwards [heq] with p hp
  simp only [ddVirialDensity, sub_self, mul_zero, zero_add]
  rw [hp 0 dx, hp 1 dy, ddMatrixForm_real_mul]
  rfl

/-- All four integrability assertions on a positive Picone truncation. No
    Fourier derivative relations are needed for these assertions. -/
theorem dd_truncated_picone_integrability {φ : L2} (hφ : MemSobolev 2 φ) (dx dy : L2)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconePotential φ) (ddTruncatedCell ε) ∧
      IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
        ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
        volume 0 (orbitPeriod (ε / 2)) := by
  exact ⟨ddRawEnergy_integrable φ dx dy hε.1,
    ddPiconeGradient_integrable φ dx dy hε.1,
    (dd_piconePotential_integrable hφ).mono_set (fun _ hp ↦ hp.1),
    ddGroundCurrent_intervalIntegrable φ hε⟩

/-- Sobolev Picone on every positive truncation, with bulk and current integrability.
    The center is included; its removal and limiting argument belong to this input. -/
theorem dd_truncated_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconePotential φ) (ddTruncatedCell ε) ∧
      IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
        ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
        volume 0 (orbitPeriod (ε / 2)) ∧
      (∫ p in ddTruncatedCell ε, ddRawEnergy φ dx dy p) =
        (∫ p in ddTruncatedCell ε, ddPiconeGradient φ dx dy p) +
          (∫ p in ddTruncatedCell ε, ddPiconePotential φ p) + ddGroundCurrent φ ε := by
  obtain ⟨hr, hg, hp, hc⟩ := dd_truncated_picone_integrability hφ dx dy hε
  refine ⟨hr, hg, hp, hc, ?_⟩
  sorry

end NoEmbeddedEigenvalues
