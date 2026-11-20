import NoEmbeddedEigenvalues.MixedVirialBulk
import NoEmbeddedEigenvalues.MixedRellich

/-! # Tangential virial current on mixed level shells -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology ENNReal

local notation "Plane" => ℝ × ℝ
private abbrev trh (q : Plane) : ℝ := Real.cos q.1
private abbrev trk (q : Plane) : ℝ := Real.cos q.2
private abbrev tru (q : Plane) : ℝ := Real.sin q.1
private abbrev trv (q : Plane) : ℝ := Real.sin q.2

private def shellLevel (q : Plane) : ℝ := trh q * trk q
private def tanG (q : Plane) : ℝ := (trk q * tru q) ^ 2 + (trh q * trv q) ^ 2
private def tanP (q : Plane) : ℝ := trh q + trk q

private def shellFactor (q : Plane) : ℝ :=
  2 * (trh q - trk q) * tru q * trv q / (tanP q * tanG q)

private def realPair (z w : ℂ) : ℝ := (z * conj w).re

/-- The outward tangential virial current in the level variable
`cos a * cos b`, with both diagonal Jacobian factors included. -/
def mixedTangentialCurrent {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  let A := d.streamA q
  let B := d.streamB q
  shellFactor q * (shellLevel q * tru q * trv q * (‖A‖ ^ 2 - ‖B‖ ^ 2) +
    ((trh q * trv q) ^ 2 - (trk q * tru q) ^ 2) * realPair A B)

private def shellSqCoeff (q : Plane) : ℝ := shellFactor q * tru q * trv q * trh q * tanP q
private def shellCrossCoeff (q : Plane) : ℝ :=
  shellFactor q * ((trh q * trv q) ^ 2 - (trk q * tru q) ^ 2)

private theorem cosines_pos {q : Plane} (hq : q ∈ mixedOpenCell) : 0 < trh q ∧ 0 < trk q :=
  ⟨Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1),
    Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2)⟩

private theorem shellCoeffs_bounded {q : Plane} (hq : q ∈ mixedOpenCell) :
    ‖shellSqCoeff q‖ ≤ 4 ∧ ‖shellCrossCoeff q‖ ≤ 2 := by
  obtain ⟨hh, hk⟩ := cosines_pos hq
  have hp : 0 < tanP q := add_pos hh hk
  have hd : |trh q - trk q| ≤ tanP q := by
    change |trh q - trk q| ≤ trh q + trk q
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hg : 0 ≤ tanG q := by unfold tanG; positivity
  rcases hg.eq_or_lt with hz | hg'
  · simp [shellSqCoeff, shellCrossCoeff, shellFactor, ← hz]
  have hu := Real.abs_sin_le_one q.1
  have hv := Real.abs_sin_le_one q.2
  have huv : |tru q| * |trv q| ≤ 1 := by
    simpa using mul_le_mul hu hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hs : tru q ^ 2 * trv q ^ 2 * (trh q ^ 2 + trk q ^ 2) ≤ tanG q := by
    unfold tanG
    nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one q.1)) (sq_nonneg (trh q * trv q)),
      mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one q.2)) (sq_nonneg (trk q * tru q))]
  have hhp : trh q * tanP q ≤ 2 * (trh q ^ 2 + trk q ^ 2) := by
    unfold tanP
    nlinarith [sq_nonneg (trh q - trk q), sq_nonneg (trk q)]
  have hsq : tru q ^ 2 * trv q ^ 2 * (trh q * tanP q) ≤ 2 * tanG q :=
    calc
      _ ≤ tru q ^ 2 * trv q ^ 2 * (2 * (trh q ^ 2 + trk q ^ 2)) :=
        mul_le_mul_of_nonneg_left hhp (by positivity)
      _ = 2 * (tru q ^ 2 * trv q ^ 2 * (trh q ^ 2 + trk q ^ 2)) := by ring
      _ ≤ _ := by linarith only [hs]
  have hcross : abs ((trh q * trv q) ^ 2 - (trk q * tru q) ^ 2) ≤ tanG q := by
    unfold tanG
    exact abs_le.2 ⟨by linarith [sq_nonneg (trh q * trv q)],
      by linarith [sq_nonneg (trk q * tru q)]⟩
  constructor
  · rw [Real.norm_eq_abs, shellSqCoeff, shellFactor]
    have he : 2 * (trh q - trk q) * tru q * trv q / (tanP q * tanG q) * tru q * trv q * trh q *
        tanP q = (2 * (trh q - trk q) * (tru q ^ 2 * trv q ^ 2 * (trh q * tanP q))) /
          (tanP q * tanG q) := by ring
    rw [he, abs_div, abs_of_pos (mul_pos hp hg'), abs_mul, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ tru q ^ 2 * trv q ^ 2 * (trh q * tanP q)),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (mul_pos hp hg')]
    calc
      _ ≤ 2 * tanP q * (2 * tanG q) := by gcongr
      _ = _ := by ring
  · rw [Real.norm_eq_abs, shellCrossCoeff, shellFactor, div_mul_eq_mul_div,
      abs_div, abs_of_pos (mul_pos hp hg'), div_le_iff₀ (mul_pos hp hg')]
    rw [show 2 * (trh q - trk q) * tru q * trv q =
      2 * (trh q - trk q) * (tru q * trv q) by ring, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul]
    calc
      _ ≤ 2 * tanP q * 1 * tanG q := by gcongr
      _ = _ := by ring

/-- Contracting the tangential field with the diagonal stream gradient and
the outward level conormal gives the shell current. The factor two includes
the Cartesian area Jacobian and the metric conversion for the conormal. -/
theorem mixed_tangential_current_eq {ω : L2} (d : MixedQuotientData ω)
    {q : Plane} (hq : q ∈ mixedOpenCell) (hr : gradSq dipoleLift (diagInv q) ≠ 0) :
    let p := diagInv q
    let a := mixedFieldA q - (normalField₁ p + normalField₂ p) / 2
    let b := mixedFieldB q - (normalField₁ p - normalField₂ p) / 2
    mixedTangentialCurrent d q =
      2 * realPair (a • d.streamA q + b • d.streamB q)
        ((trk q * tru q) • d.streamA q + (trh q * trv q) • d.streamB q) := by
  obtain ⟨ha, hb⟩ := mixed_field_tangential_factor hq hr
  dsimp only
  rw [ha, hb]
  have eG : tru q ^ 2 * trk q ^ 2 + trv q ^ 2 * trh q ^ 2 = tanG q := by
    unfold tanG
    ring
  rw [eG]
  dsimp only [mixedTangentialCurrent, shellFactor, shellLevel, tanP]
  simp only [Complex.sq_norm, Complex.normSq_apply, realPair, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im]
  ring

private def streamModel {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℂ :=
  (-(tru q) : ℝ) • d.phi q

/-- After factoring out the level, the non-model part of the current pairs
the undivided stream derivatives with Hardy-controlled quotient derivatives. -/
def mixedTangentialRemainder {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  let a := d.jet [0] q / (tanP q : ℂ)
  let b := d.jet [1] q / (tanP q : ℂ)
  let b₀ := d.jet [1] q / (trk q : ℂ)
  shellSqCoeff q * (realPair a (d.streamA q + streamModel d q) - realPair b (d.streamB q) -
    trh q / tanP q * ‖d.phi q‖ ^ 2) +
    shellCrossCoeff q * realPair (d.streamA q) b₀

private theorem norm_sq_diff_eq_pair (z w : ℂ) :
    ‖z‖ ^ 2 - ‖w‖ ^ 2 = realPair (z - w) (z + w) := by
  simp only [realPair, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem pair_real_mul (c : ℝ) (z w : ℂ) :
    realPair ((c : ℂ) * z) w = c * realPair z w ∧
    realPair z ((c : ℂ) * w) = c * realPair z w := by
  constructor <;> simp only [realPair, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- Exact decomposition into the continuous quotient times the scalar model
kernel, and a remainder carrying a full factor of the level. -/
theorem mixed_tangential_current_split {ω : L2} (d : MixedQuotientData ω) {q : Plane}
    (hq : q ∈ mixedOpenCell) :
    mixedTangentialCurrent d q = mixedTangentialCornerKernel q * ‖d.phi q‖ ^ 2 +
      (trh q * trk q) * mixedTangentialRemainder d q := by
  obtain ⟨hh, hk⟩ := cosines_pos hq
  have hp : 0 < tanP q := add_pos hh hk
  have eP : ((tanP q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have eK : ((trk q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have eA : d.streamA q - streamModel d q =
      ((trh q * tanP q : ℝ) : ℂ) * (d.jet [0] q / (tanP q : ℂ)) := by
    simp only [MixedQuotientData.streamA, streamModel, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_neg]
    field_simp
    ring
  have eB : d.streamB q = ((trh q * tanP q : ℝ) : ℂ) * (d.jet [1] q / (tanP q : ℂ)) := by
    simp only [MixedQuotientData.streamB, Complex.ofReal_mul]
    field_simp
  have eB' : d.streamB q = ((trh q * trk q : ℝ) : ℂ) * (d.jet [1] q / (trk q : ℂ)) := by
    simp only [MixedQuotientData.streamB, Complex.ofReal_mul]
    field_simp
  have eM : ‖streamModel d q‖ ^ 2 = tru q ^ 2 * ‖d.phi q‖ ^ 2 := by
    simp only [streamModel, norm_smul, mul_pow, norm_neg, Real.norm_eq_abs, sq_abs]
  have mA := norm_sq_diff_eq_pair (d.streamA q) (streamModel d q)
  rw [eA, (pair_real_mul _ _ _).1, eM] at mA
  have mB : ‖d.streamB q‖ ^ 2 = trh q * tanP q *
      realPair (d.jet [1] q / (tanP q : ℂ)) (d.streamB q) := by
    rw [← re_mul_conj_self]
    change realPair (d.streamB q) (d.streamB q) = _
    exact (congrArg (fun z ↦ realPair z (d.streamB q)) eB).trans (pair_real_mul _ _ _).1
  have mC : realPair (d.streamA q) (d.streamB q) =
      (trh q * trk q) * realPair (d.streamA q) (d.jet [1] q / (trk q : ℂ)) := by
    conv_lhs => rw [eB', (pair_real_mul _ _ _).2]
  have eK : mixedTangentialCornerKernel q = shellFactor q * shellLevel q * tru q * trv q := by
    unfold mixedTangentialCornerKernel shellFactor shellLevel tanG tanP
    ring_nf
  have hs := Real.sin_sq_add_cos_sq q.1
  have he : tanP q * (trh q / tanP q) = trh q := by
    rw [mul_div_left_comm, div_self hp.ne', mul_one]
  dsimp only [mixedTangentialCurrent, mixedTangentialRemainder, shellSqCoeff, shellCrossCoeff]
  rw [mB, mC, eK]
  unfold shellLevel
  linear_combination shellFactor q * (trh q * trk q) * tru q * trv q * (mA + ‖d.phi q‖ ^ 2 * hs) +
    shellFactor q * (trh q * trk q) * tru q * trv q * trh q * ‖d.phi q‖ ^ 2 * he

/-- The remainder divided by the level is integrable on the whole cell.
No restriction to good levels or unweighted corner trace of a derivative
is used. -/
theorem mixed_tangential_remainder_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedTangentialRemainder d) mixedOpenCell := by
  let μ := volume.restrict mixedOpenCell
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hmem := ae_restrict_mem (μ := volume) hU.measurableSet
  have hc : MemLp trh ∞ μ := memLp_top_of_bound (by fun_prop) 1
    (.of_forall fun q ↦ Real.abs_cos_le_one q.1)
  have hs : MemLp (fun q ↦ -(tru q)) ∞ μ := memLp_top_of_bound (by fun_prop) 1
    (.of_forall fun q ↦ by simpa only [norm_neg, Real.norm_eq_abs] using Real.abs_sin_le_one q.1)
  have hF : MemLp d.phi 2 μ := d.h2.memLp
  have hM : MemLp (streamModel d) 2 μ := hs.smul hF
  have hA : MemLp d.streamA 2 μ := by
    have ha := hc.smul (r := 2) (d.h2.memLp_weakJet hU d.weakJet [0] (by decide))
    have he : (fun q ↦ trh q • d.jet [0] q) + streamModel d = d.streamA := by
      funext q
      simp only [Pi.add_apply, streamModel, MixedQuotientData.streamA, Complex.real_smul,
        Complex.ofReal_neg]
      ring
    rw [← he]
    exact ha.add hM
  have hB : MemLp d.streamB 2 μ := by
    exact hc.smul (d.h2.memLp_weakJet hU d.weakJet [1] (by decide))
  obtain ⟨ha, hb⟩ := d.memLp_partials_div_corner
  have hb₀ := d.memLp_normal_div_cos.2
  have hp {F G : Plane → ℂ} (hf : MemLp F 2 μ) (hg : MemLp G 2 μ) :
      Integrable (fun q ↦ realPair (F q) (G q)) μ := by
    have hgc : MemLp (fun q ↦ conj (G q)) 2 μ :=
      hg.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
        (.of_forall fun q ↦ (Complex.norm_conj (G q)).symm)
    exact Complex.reCLM.integrable_comp (hf.integrable_mul hgc)
  have hrm : Measurable (fun q ↦ trh q / tanP q) := by unfold tanP; fun_prop
  have hratio : ∀ᵐ q ∂μ, ‖trh q / tanP q‖ ≤ 1 := by
    filter_upwards [hmem] with q hq
    obtain ⟨hh, hk⟩ := cosines_pos hq
    unfold tanP
    rw [Real.norm_of_nonneg (div_nonneg hh.le (add_pos hh hk).le),
      div_le_one (add_pos hh hk)]
    exact le_add_of_nonneg_right hk.le
  have hS := ((hp ha (hA.add hM)).sub (hp hb hB)).sub
    (hF.norm.integrable_sq.bdd_mul hrm.aestronglyMeasurable hratio)
  have hC := hp hA hb₀
  have hsm : Measurable shellSqCoeff := by
    unfold shellSqCoeff shellFactor tanP tanG
    fun_prop
  have hcm : Measurable shellCrossCoeff := by
    unfold shellCrossCoeff shellFactor tanP tanG
    fun_prop
  exact (hS.bdd_mul hsm.aestronglyMeasurable
    (hmem.mono fun _ hq ↦ (shellCoeffs_bounded hq).1)).add
    (hC.bdd_mul hcm.aestronglyMeasurable (hmem.mono fun _ hq ↦ (shellCoeffs_bounded hq).2))

/-- Vanishing of the analytic remainder against level cutoffs. The bounded
weight is the level times the cutoff derivative, not the derivative itself. -/
theorem mixed_tangential_remainder_limit {ω : L2} (d : MixedQuotientData ω)
    {w : ℕ → Plane → ℝ} {C : ℝ} (hm : ∀ n, Measurable (w n))
    (hb : ∀ n, ∀ᵐ q ∂volume.restrict mixedOpenCell, ‖w n q‖ ≤ C)
    (hl : ∀ᵐ q ∂volume.restrict mixedOpenCell, Tendsto (fun n ↦ w n q) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ q in mixedOpenCell, w n q * mixedTangentialRemainder d q)
      atTop (𝓝 0) := by
  have hi := mixed_tangential_remainder_integrable d
  have he : (∫ _q in mixedOpenCell, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← he]
  apply tendsto_integral_of_dominated_convergence (fun q ↦ C * ‖mixedTangentialRemainder d q‖)
  · exact fun n ↦ (hm n).aestronglyMeasurable.mul hi.aestronglyMeasurable
  · exact hi.norm.const_mul C
  · intro n
    filter_upwards [hb n] with q hq
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  · filter_upwards [hl] with q hq
    simpa only [zero_mul] using hq.mul_const (mixedTangentialRemainder d q)

/-- The absolute model kernel divided by the level is bounded by the
inverse-square corner weight. Away from the corners this controls it
uniformly, even next to a regular edge. -/
theorem mixed_tangential_corner_kernel_bound {q : Plane} (hq : q ∈ mixedOpenCell) :
    ‖mixedTangentialCornerKernel q‖ ≤
      4 * (Real.cos q.1 * Real.cos q.2) / (Real.cos q.1 + Real.cos q.2) ^ 2 := by
  obtain ⟨hh, hk⟩ := cosines_pos hq
  have hp : 0 < tanP q := add_pos hh hk
  have hd : |trh q - trk q| ≤ tanP q := by
    change |trh q - trk q| ≤ trh q + trk q
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hg : 0 ≤ tanG q := by unfold tanG; positivity
  have eG : tru q ^ 2 * trk q ^ 2 + trv q ^ 2 * trh q ^ 2 = tanG q := by
    unfold tanG
    ring
  change ‖2 * trh q * trk q * tru q ^ 2 * trv q ^ 2 * (trh q - trk q) /
    (tanP q * (tru q ^ 2 * trk q ^ 2 + trv q ^ 2 * trh q ^ 2))‖ ≤
    4 * (trh q * trk q) / tanP q ^ 2
  rw [eG]
  rcases hg.eq_or_lt with hz | hg'
  · rw [← hz, mul_zero, div_zero, norm_zero]
    positivity
  have hs : tru q ^ 2 * trv q ^ 2 * tanP q ^ 2 ≤ 2 * tanG q := by
    have he : (trh q + trk q) ^ 2 ≤ 2 * (trh q ^ 2 + trk q ^ 2) := by
      nlinarith [sq_nonneg (trh q - trk q)]
    have hs : tru q ^ 2 * trv q ^ 2 * (trh q ^ 2 + trk q ^ 2) ≤ tanG q := by
      unfold tanG
      nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one q.1))
          (sq_nonneg (trh q * trv q)),
        mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one q.2)) (sq_nonneg (trk q * tru q))]
    calc
      _ ≤ tru q ^ 2 * trv q ^ 2 * (2 * (trh q ^ 2 + trk q ^ 2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * (tru q ^ 2 * trv q ^ 2 * (trh q ^ 2 + trk q ^ 2)) := by ring
      _ ≤ _ := by linarith only [hs]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hp hg'), abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * trh q * trk q * tru q ^ 2 * trv q ^ 2)]
  apply (div_le_div_iff₀ (mul_pos hp hg') (sq_pos_of_pos hp)).2
  calc
    _ = (2 * trh q * trk q) * |trh q - trk q| * (tru q ^ 2 * trv q ^ 2 * tanP q ^ 2) := by
      ring
    _ ≤ (2 * trh q * trk q) * tanP q * (2 * tanG q) := by gcongr
    _ = _ := by ring

private theorem swap_mem_closed_cell {q : Plane} (hq : q ∈ closure mixedOpenCell) :
    q.swap ∈ closure mixedOpenCell := by
  rw [mixedOpenCell, closure_prod_eq] at hq ⊢
  exact ⟨hq.2, hq.1⟩

/-- Antisymmetrizing the squared quotient leaves a continuous defect on
the closed cell. At each corner the swap either fixes the point or is
central inversion, so the defect vanishes. -/
theorem mixed_tangential_model_defect {ω : L2} (d : MixedQuotientData ω) :
    ContinuousOn (fun q : Plane ↦ ‖d.phi q‖ ^ 2 - ‖d.phi q.swap‖ ^ 2) (closure mixedOpenCell) ∧
    ∀ q : Plane, q ∈ closure mixedOpenCell → Real.cos q.1 = 0 → Real.cos q.2 = 0 →
      ‖d.phi q‖ ^ 2 - ‖d.phi q.swap‖ ^ 2 = 0 := by
  have hswap : Continuous (Prod.swap : Plane → Plane) := continuous_snd.prodMk continuous_fst
  refine ⟨(d.continuous.norm.pow 2).sub
    ((d.continuous.comp hswap.continuousOn (fun _ ↦ swap_mem_closed_cell)).norm.pow 2), ?_⟩
  intro q hq h1 h2
  have hmem (x : ℝ) (hx : x ∈ closure (Ioo (-Real.pi / 2) (Real.pi / 2)))
      (hz : Real.cos x = 0) : x = -(Real.pi / 2) ∨ x = Real.pi / 2 := by
    rw [closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)] at hx
    change -Real.pi / 2 ≤ x ∧ x ≤ Real.pi / 2 at hx
    by_contra! h
    have hpos := Real.cos_pos_of_mem_Ioo
      (show x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [lt_of_le_of_ne hx.1 (by simpa [neg_div] using h.1.symm)],
          lt_of_le_of_ne hx.2 h.2⟩)
    exact hpos.ne' hz
  have hq' := hq
  rw [mixedOpenCell, closure_prod_eq] at hq'
  obtain ha | ha := hmem q.1 hq'.1 h1 <;> obtain hb | hb := hmem q.2 hq'.2 h2
  · have he : q.swap = q := Prod.ext (hb.trans ha.symm) (ha.trans hb.symm)
    rw [he, sub_self]
  · have he : q.swap = -q := Prod.ext (by change q.2 = -q.1; rw [ha, hb, neg_neg])
      (by change q.1 = -q.2; rw [ha, hb])
    rw [he, d.central_odd q hq, norm_neg, sub_self]
  · have he : q.swap = -q := Prod.ext (by change q.2 = -q.1; rw [ha, hb])
      (by change q.1 = -q.2; rw [ha, hb, neg_neg])
    rw [he, d.central_odd q hq, norm_neg, sub_self]
  · have he : q.swap = q := Prod.ext (hb.trans ha.symm) (ha.trans hb.symm)
    rw [he, sub_self]

/-- The model current on a symmetric shell can be computed against half
the antisymmetric defect, rather than against the full squared quotient. -/
theorem mixed_tangential_model_antisymmetrize {ω : L2} (d : MixedQuotientData ω)
    {w : Plane → ℝ} (hs : ∀ q, w q.swap = w q) (hi : IntegrableOn w mixedOpenCell) :
    IntegrableOn (fun q ↦ w q * mixedTangentialCornerKernel q * ‖d.phi q‖ ^ 2)
      mixedOpenCell ∧
    (∫ q in mixedOpenCell, w q * mixedTangentialCornerKernel q * ‖d.phi q‖ ^ 2) =
      (1 / 2) * ∫ q in mixedOpenCell,
        w q * mixedTangentialCornerKernel q * (‖d.phi q‖ ^ 2 - ‖d.phi q.swap‖ ^ 2) := by
  let F : Plane → ℝ := fun q ↦ ‖d.phi q‖ ^ 2
  let G : Plane → ℝ := F ∘ Prod.swap
  have hS : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  have hFc : ContinuousOn F (closure mixedOpenCell) := d.continuous.norm.pow 2
  have hswap : Continuous (Prod.swap : Plane → Plane) := continuous_snd.prodMk continuous_fst
  have hGc : ContinuousOn G (closure mixedOpenCell) :=
    hFc.comp hswap.continuousOn (fun _ ↦ swap_mem_closed_cell)
  have hcomp : IsCompact (closure mixedOpenCell) := by
    rw [mixedOpenCell, closure_prod_eq,
      closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)]
    exact isCompact_Icc.prod isCompact_Icc
  have bound {f : Plane → ℝ} (hc : ContinuousOn f (closure mixedOpenCell)) :
      ∃ C : ℝ, ∀ᵐ q ∂volume.restrict mixedOpenCell, ‖f q‖ ≤ C := by
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hc
    exact ⟨C, (ae_restrict_mem (μ := volume) hS).mono fun q hq ↦ hC q (subset_closure hq)⟩
  obtain ⟨C, hC⟩ := bound hFc
  obtain ⟨D, hD⟩ := bound hGc
  have mF := (hFc.mono subset_closure).aestronglyMeasurable (μ := volume) hS
  have mG := (hGc.mono subset_closure).aestronglyMeasurable (μ := volume) hS
  let K := mixedTangentialCornerKernel
  have hK := (mixed_tangential_corner_cancel hs hi).1
  have hF : IntegrableOn (fun q ↦ w q * K q * F q) mixedOpenCell :=
    (hK.bdd_mul mF hC).congr (.of_forall fun q ↦ mul_comm (F q) (w q * K q))
  have hG : IntegrableOn (fun q ↦ w q * K q * G q) mixedOpenCell :=
    (hK.bdd_mul mG hD).congr (.of_forall fun q ↦ mul_comm (G q) (w q * K q))
  have hW : IntegrableOn (fun q ↦ w q * (F q + G q)) mixedOpenCell := by
    have he := (hi.bdd_mul mF hC).add (hi.bdd_mul mG hD)
    refine he.congr (.of_forall fun q ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hsym : ∀ q : Plane, w q.swap * (F q.swap + G q.swap) = w q * (F q + G q) := by
    intro q
    rw [hs]
    simp only [G, Function.comp_apply, Prod.swap_swap, add_comm]
  have h0 := (mixed_tangential_corner_cancel hsym hW).2
  have hadd : (fun q ↦ w q * (F q + G q) * K q) =
      (fun q ↦ w q * K q * F q) + (fun q ↦ w q * K q * G q) := by
    funext q
    simp only [Pi.add_apply]
    ring
  have hsub : (fun q ↦ w q * K q * (F q - G q)) =
      (fun q ↦ w q * K q * F q) - (fun q ↦ w q * K q * G q) := by
    funext q
    simp only [Pi.sub_apply]
    ring
  change (∫ q in mixedOpenCell, w q * (F q + G q) * K q) = 0 at h0
  rw [hadd] at h0
  change (∫ q in mixedOpenCell, w q * K q * F q + w q * K q * G q) = 0 at h0
  rw [integral_add hF hG] at h0
  refine ⟨hF, ?_⟩
  change (∫ q in mixedOpenCell, w q * K q * F q) =
    (1 / 2) * ∫ q in mixedOpenCell, w q * K q * (F q - G q)
  rw [hsub]
  change _ = (1 / 2 : ℝ) *
    ∫ q in mixedOpenCell, w q * K q * F q - w q * K q * G q
  rw [integral_sub hF hG]
  linarith only [h0]

/-- Passing from the model limit to the full current limit costs no further
trace estimates. Here `w` is the cutoff derivative and `w * cos a * cos b`
is its uniformly bounded rescaling. -/
theorem mixed_tangential_current_limit_of_model {ω : L2} (d : MixedQuotientData ω)
    {w : ℕ → Plane → ℝ} {C : ℝ} (hm : ∀ n, Measurable (w n))
    (hs : ∀ n q, w n q.swap = w n q)
    (hi : ∀ n, IntegrableOn (w n) mixedOpenCell)
    (hb : ∀ n, ∀ᵐ q ∂volume.restrict mixedOpenCell, ‖w n q * (trh q * trk q)‖ ≤ C)
    (hl : ∀ᵐ q ∂volume.restrict mixedOpenCell,
      Tendsto (fun n ↦ w n q * (trh q * trk q)) atTop (𝓝 0))
    (hmodel : Tendsto (fun n ↦ ∫ q in mixedOpenCell, w n q * mixedTangentialCornerKernel q *
      (‖d.phi q‖ ^ 2 - ‖d.phi q.swap‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ q in mixedOpenCell, w n q * mixedTangentialCurrent d q) atTop (𝓝 0) := by
  have he := fun n ↦ mixed_tangential_model_antisymmetrize d (hs n) (hi n)
  have hμ : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  have hR := mixed_tangential_remainder_integrable d
  let W (n : ℕ) := fun q ↦ w n q * (trh q * trk q)
  have hW (n : ℕ) : Measurable (W n) := (hm n).mul (by fun_prop)
  have hWi (n : ℕ) :
      IntegrableOn (fun q ↦ W n q * mixedTangentialRemainder d q) mixedOpenCell :=
    hR.bdd_mul (hW n).aestronglyMeasurable (hb n)
  have hRlim := mixed_tangential_remainder_limit d hW hb hl
  have hMlim := (hmodel.const_mul (1 / 2 : ℝ)).congr fun n ↦ (he n).2.symm
  have hlim := hMlim.add hRlim
  rw [mul_zero, zero_add] at hlim
  apply hlim.congr
  intro n
  rw [← integral_add (he n).1 (hWi n)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hμ] with q hq
  rw [mixed_tangential_current_split d hq]
  dsimp only [W]
  ring

end NoEmbeddedEigenvalues
