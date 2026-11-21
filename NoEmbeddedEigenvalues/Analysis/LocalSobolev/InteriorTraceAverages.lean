import NoEmbeddedEigenvalues.Analysis.LocalSobolev.BoundaryTraceContinuity
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTrace
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Rectangular averages recover the canonical ACL trace -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Metric Filter
open scoped Topology ContDiff

private theorem closedBall_prod (x t r : ℝ) :
    closedBall (x, t) r = closedBall x r ×ˢ closedBall t r := by
  ext q
  simp [Metric.mem_closedBall, Prod.dist_eq]

private theorem ae_average_closedBall_norm_sub {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → E} (hF : Integrable F) :
    ∀ᵐ x : ℝ, Tendsto (fun r ↦ (∫ y in closedBall x r, ‖F y - F x‖) / (2 * r))
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℝ)).ae_tendsto_average_norm_sub
    hF.locallyIntegrable] with x hx
  apply (hx.comp (Besicovitch.tendsto_filterAt volume x)).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Function.comp_apply, setAverage_eq, Real.volume_real_closedBall hr.le, smul_eq_mul,
    div_eq_inv_mul]

/-- At almost every point of an interior trace, the bulk mean absolute
oscillation about the trace value tends to zero in centered squares. -/
theorem HasTransverseH1Trace.tendsto_square_oscillation {l r a b : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b 0 chart F T) (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ x ∂(volume.restrict (Ioo l r)),
      Tendsto (fun ε ↦ (∫ q in closedBall (x, (0 : ℝ)) ε, ‖F (chart q) - T x‖) /
          (2 * ε) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨_, hab, _, G, D, hGm, hGF, hG, hD, hACL, hT⟩ := h
  let I := Ioo l r
  let J := Ioo a b
  let E : ℝ → ℝ := fun x ↦ ∫ t in J, ‖D (x, t)‖ ^ 2
  let P : ℝ → ℝ := fun x ↦ Real.sqrt (E x)
  have ht : IntegrableOn T I := ((hACL.l2_trace hab hGm hG hD 0 ⟨ha.le, hb.le⟩).1.ae_eq hT.symm).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hDp : MemLp D 2 ((volume.restrict I).prod (volume.restrict J)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hD
  have hE : IntegrableOn E I := hDp.norm.integrable_sq.integral_prod_left
  have hP : IntegrableOn P I := by
    have hi : Integrable E (volume.restrict I) := hE
    have h1 : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc l r) :=
      integrableOn_const isCompact_Icc.measure_lt_top.ne
    apply (hi.add (h1.mono_set Ioo_subset_Icc_self)).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hE.aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (E x) ≤ E x + 1
    nlinarith [Real.sq_sqrt (show 0 ≤ E x from integral_nonneg fun _ ↦ sq_nonneg _),
      sq_nonneg (Real.sqrt (E x) - 1)]
  have hinc : ∀ᵐ x ∂(volume.restrict I), ∀ t ∈ J,
      ‖G (x, t) - T x‖ ≤ Real.sqrt |t| * P x := by
    filter_upwards [hACL.ae_trace_eq hab hG hD, hACL.ae_hasIntervalH1 hG hD, hT]
      with x hx hHx hTx t ht'
    rw [hTx, ← hx t ht']
    have hh := hHx.extension_sub_sq_le_distance hab ⟨ha.le, hb.le⟩ (Ioo_subset_Icc_self ht')
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
    simpa only [sub_zero, aclTrace] using hh
  have hTdiff := ae_average_closedBall_norm_sub (ht.integrable_indicator measurableSet_Ioo)
  have hPdiff := ae_average_closedBall_norm_sub (hP.integrable_indicator measurableSet_Ioo)
  filter_upwards [ae_restrict_of_ae hTdiff, ae_restrict_of_ae hPdiff,
    ae_restrict_mem measurableSet_Ioo] with x hxT hxP hx
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧
      closedBall x ε ⊆ I ∧ closedBall 0 ε ⊆ J := by
    filter_upwards [Ioo_mem_nhdsGT (show 0 < min (min (x-l) (r-x)) (min (-a) b) from
      lt_min (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)) (lt_min (neg_pos.mpr ha) hb))]
      with ε hε
    have he : ε < min (x - l) (r - x) := hε.2.trans_le (min_le_left _ _)
    have he' : ε < min (-a) b := hε.2.trans_le (min_le_right _ _)
    simp only [Real.closedBall_eq_Icc]
    exact ⟨hε.1, Icc_subset_Ioo (by linarith [he.trans_le (min_le_left _ _)])
      (by linarith [he.trans_le (min_le_right _ _)]),
      Icc_subset_Ioo (by linarith [he'.trans_le (min_le_left _ _)])
        (by linarith [he'.trans_le (min_le_right _ _)])⟩
  have htlim : Tendsto (fun ε ↦ (∫ y in closedBall x ε, ‖T y - T x‖) / (2 * ε))
      (𝓝[>] 0) (𝓝 0) := by
    apply hxT.congr'
    filter_upwards [hsmall] with ε he
    rw [indicator_of_mem hx]
    congr 1
    exact setIntegral_congr_fun isClosed_closedBall.measurableSet fun y hy ↦ by
      rw [indicator_of_mem (he.2.1 hy)]
  have hplim : Tendsto (fun ε ↦ (∫ y in closedBall x ε, ‖P y - P x‖) / (2 * ε))
      (𝓝[>] 0) (𝓝 0) := by
    apply hxP.congr'
    filter_upwards [hsmall] with ε he
    rw [indicator_of_mem hx]
    congr 1
    exact setIntegral_congr_fun isClosed_closedBall.measurableSet fun y hy ↦ by
      rw [indicator_of_mem (he.2.1 hy)]
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := htlim.add (hsqrt.mul (hplim.add (tendsto_const_nhds (x := P x))))
  rw [zero_add, zero_mul] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (sq_nonneg _)) ?_ hlim
  filter_upwards [hsmall] with ε he
  obtain ⟨he, hXI, hYJ⟩ := he
  let X := closedBall x ε
  let Y := closedBall (0 : ℝ) ε
  let R := X ×ˢ Y
  have hR : R ⊆ I ×ˢ J := prod_mono hXI hYJ
  have hRc : IsCompact R := (isCompact_closedBall x ε).prod (isCompact_closedBall 0 ε)
  let : IsFiniteMeasure (volume.restrict R) := ⟨by simpa using hRc.measure_lt_top (μ := volume)⟩
  have hGt : IntegrableOn (fun q ↦ ‖G q - T x‖) R :=
    (((hG.mono_measure (Measure.restrict_mono_set _ hR)).integrable (by norm_num)).sub
      (integrable_const (T x))).norm
  have hGtp : Integrable (fun q ↦ ‖G q - T x‖) ((volume.restrict X).prod (volume.restrict Y)) := by
    simpa only [IntegrableOn, R, Measure.prod_restrict, Measure.volume_eq_prod] using hGt
  have heq : (∫ q in closedBall (x, (0 : ℝ)) ε, ‖F (chart q) - T x‖) =
      ∫ y in X, ∫ t in Y, ‖G (y, t) - T x‖ := by
    rw [closedBall_prod, ← integral_prod _ hGtp, Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integral_congr_ae ((hGF.filter_mono (ae_mono (Measure.restrict_mono_set _ hR))).mono
      fun _ hq ↦ congrArg (fun z : ℂ ↦ ‖z - T x‖) hq.symm)
  have hBound : ∀ᵐ y ∂(volume.restrict X), (∫ t in Y, ‖G (y, t) - T x‖) ≤
      (2 * ε) * (‖T y - T x‖ + Real.sqrt ε * (‖P y - P x‖ + P x)) := by
    filter_upwards [hGtp.prod_right_ae, hinc.filter_mono (ae_mono (Measure.restrict_mono_set _ hXI))]
      with y hGy hy
    have hid : (∫ _ in Y, ‖T y - T x‖ + Real.sqrt ε * (‖P y - P x‖ + P x)) =
        (2 * ε) * (‖T y - T x‖ + Real.sqrt ε * (‖P y - P x‖ + P x)) := by
      rw [setIntegral_const, Real.volume_real_closedBall he.le, smul_eq_mul]
    rw [← hid]
    apply integral_mono_ae hGy (integrableOn_const (isCompact_closedBall (0 : ℝ) ε).measure_lt_top.ne)
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with t ht'
    have ht'' : |t| ≤ ε := by simpa [Y, Real.dist_eq, Metric.mem_closedBall] using ht'
    have h₁ : ‖G (y, t) - T x‖ ≤ ‖G (y, t) - T y‖ + ‖T y - T x‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (G (y, t) - T y) (T y - T x)
    have h₂ := hy t (hYJ ht')
    have h₃ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht'') (Real.sqrt_nonneg (E y))
    have h₄ := mul_le_mul_of_nonneg_left (le_abs_self (P y - P x)) (Real.sqrt_nonneg ε)
    rw [Real.norm_eq_abs]
    change _ ≤ _ at h₁
    linarith [show Real.sqrt (E y) = P y from rfl]
  have hfin := (isCompact_closedBall x ε).measure_lt_top (μ := volume)
  have hXT : IntegrableOn (fun _ ↦ T x) X := integrableOn_const hfin.ne
  have hXP : IntegrableOn (fun _ ↦ P x) X := integrableOn_const hfin.ne
  have ihT : IntegrableOn (fun y ↦ ‖T y - T x‖) X := ((ht.mono_set hXI).sub hXT).norm
  have ihP : IntegrableOn (fun y ↦ ‖P y - P x‖) X := ((hP.mono_set hXI).sub hXP).norm
  have ihB := (ihP.add hXP).const_mul (Real.sqrt ε)
  have hAll := integral_mono_ae hGtp.integral_prod_left
    ((ihT.add ihB).const_mul (2 * ε)) hBound
  simp only [Pi.add_apply] at hAll
  have hhB : IntegrableOn (fun y ↦ Real.sqrt ε * (‖P y - P x‖ + P x)) X := ihB
  rw [integral_const_mul, integral_add ihT hhB,
    integral_const_mul, integral_add ihP hXP, setIntegral_const] at hAll
  change _ ≤ (2 * ε) * (_ + Real.sqrt ε * (_ +
    volume.real (closedBall x ε) • P x)) at hAll
  rw [Real.volume_real_closedBall he.le, smul_eq_mul] at hAll
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 2 * ε))).mpr
  convert hAll using 1
  field_simp [he.ne']
  <;> ring

private theorem continuous_det_plane : Continuous (fun A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) ↦ A.det) := by
  have he (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
      A.det = (A (1, 0)).1 * (A (0, 1)).2 - (A (0, 1)).1 * (A (1, 0)).2 := by
    change LinearMap.det A.toLinearMap = _
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd]
  simp_rw [he]
  fun_prop

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- A smooth nonsingular chart transfers vanishing mean oscillation from
coordinate squares to physical squares. Only local integrability in physical
space is used, and the inverse chart is needed only at the center. -/
theorem tendsto_physical_square_oscillation {U R : Set (ℝ × ℝ)} (hU : IsOpen U) (hR : IsOpen R)
    {F : ℝ × ℝ → ℂ} (hF : LocallyIntegrableOn F U) {C : ℝ × ℝ → ℝ × ℝ}
    (hC : ContDiffOn ℝ ∞ C R) (hCU : MapsTo C R U)
    (hFC : LocallyIntegrableOn (F ∘ C) R) {q : ℝ × ℝ} (hq : q ∈ R)
    {A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} (hA : HasFDerivAt C (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q) {z : ℂ}
    (hz : Tendsto (fun ε ↦ (∫ p in closedBall q ε, ‖F (C p) - z‖) / (2 * ε) ^ 2)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε ↦ (∫ p in closedBall (C q) ε, ‖F p - z‖) / (2 * ε) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hc := hC.contDiffAt (hR.mem_nhds hq)
  let e := hc.toOpenPartialHomeomorph C hA (by simp)
  have he : (e : (ℝ × ℝ) → ℝ × ℝ) = C := rfl
  have hqe : q ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hA (by simp)
  have hqet : C q ∈ e.target := hc.image_mem_toOpenPartialHomeomorph_target hA (by simp)
  have heinv : e.symm (C q) = q := e.left_inv hqe
  have hi : DifferentiableAt ℝ e.symm (C q) := (hc.to_localInverse hA (by simp)).differentiableAt (by simp)
  obtain ⟨L, hL, hLb⟩ := hi.isBigO_sub.exists_pos
  have hLd : ∀ᶠ p in 𝓝 (C q), dist (e.symm p) q ≤ L * dist p (C q) := by
    simpa only [dist_eq_norm, heinv] using hLb.bound
  have hD : ContinuousAt (fun p ↦ |(fderiv ℝ C p).det|) q :=
    (continuous_det_plane.continuousAt.comp (hc.continuousAt_fderiv (by simp))).abs
  let M := |(fderiv ℝ C q).det| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hDb : ∀ᶠ p in 𝓝 q, |(fderiv ℝ C p).det| < M := hD.eventually
    (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.1
    ((hDb.and (hR.mem_nhds hq)).and (e.open_source.mem_nhds hqe))
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.1
    ((hLd.and (hU.mem_nhds (hCU hq))).and (e.open_target.mem_nhds hqet))
  have hscale : Tendsto (fun ε : ℝ ↦ L * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc' : Continuous (fun ε : ℝ ↦ L * ε) := by fun_prop
      simpa only [mul_zero] using (hc'.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hL hε
  have hlim := (hz.comp hscale).const_mul (M * L ^ 2)
  simp only [Function.comp_apply, mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ ↦
    div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (sq_nonneg _)) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη (div_pos hδ hL))] with ε hε
  have hεL : L * ε < δ := by
    rw [mul_comm]
    exact (lt_div_iff₀ hL).1 (hε.2.trans_le (min_le_right _ _))
  let B := closedBall (C q) ε
  let S := closedBall q (L * ε)
  have hB (p : ℝ × ℝ) (hp : p ∈ B) :
      (dist (e.symm p) q ≤ L * dist p (C q) ∧ p ∈ U) ∧ p ∈ e.target :=
    hηs ((mem_closedBall.1 hp).trans_lt (hε.2.trans_le (min_le_left _ _)))
  have hS (p : ℝ × ℝ) (hp : p ∈ S) :
      (|(fderiv ℝ C p).det| < M ∧ p ∈ R) ∧ p ∈ e.source :=
    hδs ((mem_closedBall.1 hp).trans_lt hεL)
  have him : B ⊆ C '' S := by
    intro p hp
    refine ⟨e.symm p, mem_closedBall.2 ((hB p hp).1.1.trans
      (mul_le_mul_of_nonneg_left (mem_closedBall.1 hp) hL.le)), ?_⟩
    rw [← he, e.right_inv (hB p hp).2]
  have hSin : InjOn C S := he ▸ (e.injOn.mono fun p hp ↦ (hS p hp).2)
  have hCS : ContDiffOn ℝ ∞ C S := hC.mono fun p hp ↦ (hS p hp).1.2
  have hK : IsCompact (C '' S) := (isCompact_closedBall _ _).image_of_continuousOn hCS.continuousOn
  have hKU : C '' S ⊆ U := image_subset_iff.mpr fun p hp ↦ hCU (hS p hp).1.2
  have hKi : IntegrableOn (fun p ↦ ‖F p - z‖) (C '' S) :=
    ((hF.integrableOn_compact_subset hKU hK).sub (integrableOn_const hK.measure_lt_top.ne)).norm
  have hder p (hp : p ∈ S) : HasFDerivWithinAt C (fderiv ℝ C p) S p :=
    ((hC.contDiffAt (hR.mem_nhds (hS p hp).1.2)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hSc : IsCompact S := isCompact_closedBall _ _
  have hiC : IntegrableOn (fun p ↦ ‖F (C p) - z‖) S :=
    ((hFC.integrableOn_compact_subset (fun p hp ↦ (hS p hp).1.2) hSc).sub
      (integrableOn_const hSc.measure_lt_top.ne)).norm
  have hI := (setIntegral_mono_set hKi (Eventually.of_forall fun p ↦ norm_nonneg (F p - z))
    (Eventually.of_forall fun _ hp ↦ him hp))
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume isClosed_closedBall.measurableSet hder hSin] at hI
  have hJ := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isClosed_closedBall.measurableSet hder hSin _).mp hKi
  have hIm := integral_mono_ae hJ (hiC.const_mul M) (by
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet : MeasurableSet S)] with p hp
    exact mul_le_mul_of_nonneg_right (hS p hp).1.1.le (norm_nonneg _))
  rw [integral_const_mul] at hIm
  have hle := div_le_div_of_nonneg_right (hI.trans hIm) (sq_nonneg (2 * ε))
  refine hle.trans_eq ?_
  field_simp [hε.1.ne', hL.ne']

/-- The canonical trace of a smooth local chart is an intrinsic physical
mean value at almost every base point. -/
theorem HasTransverseH1Trace.tendsto_physical_square_oscillation
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {l r a b : ℝ}
    {C : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b 0 C F T) (ha : a < 0) (hb : 0 < b)
    (hF : LocallyIntegrableOn F U)
    (hc : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ Ioo a b))
    (hCU : MapsTo C (Ioo l r ×ˢ Ioo a b) U)
    (hA : ∀ x ∈ Ioo l r, ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt C (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (x, 0)) :
    ∀ᵐ x ∂(volume.restrict (Ioo l r)),
      Tendsto (fun ε ↦ (∫ p in closedBall (C (x, 0)) ε, ‖F p - T x‖) /
        (2 * ε) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hFC : LocallyIntegrableOn (F ∘ C) (Ioo l r ×ˢ Ioo a b) := by
    obtain ⟨_, _, _, _, _, _, he, hG, _⟩ := h
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hG.ae_eq he).locallyIntegrable (by norm_num))
  filter_upwards [h.tendsto_square_oscillation ha hb, ae_restrict_mem measurableSet_Ioo]
    with x hx hxr
  obtain ⟨A, hA⟩ := hA x hxr
  exact NoEmbeddedEigenvalues.tendsto_physical_square_oscillation hU
    (isOpen_Ioo.prod isOpen_Ioo) hF hc hCU hFC ⟨hxr, ha, hb⟩ hA hx

/-- The physical mean oscillation determines at most one trace value. -/
theorem eq_of_tendsto_physical_square_oscillation {F : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : LocallyIntegrableOn F U) {p : ℝ × ℝ} (hp : p ∈ U) {z w : ℂ}
    (hz : Tendsto (fun ε ↦ (∫ q in closedBall p ε, ‖F q - z‖) / (2 * ε) ^ 2)
      (𝓝[>] 0) (𝓝 0))
    (hw : Tendsto (fun ε ↦ (∫ q in closedBall p ε, ‖F q - w‖) / (2 * ε) ^ 2)
      (𝓝[>] 0) (𝓝 0)) : z = w := by
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hp)
  have hlim := hz.add hw
  rw [zero_add] at hlim
  have hle : ‖z - w‖ ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hK := isCompact_closedBall p ε
    have hKi := hF.integrableOn_compact_subset
      (fun q hq ↦ hδb ((mem_closedBall.1 hq).trans_lt hε.2)) hK
    have hi (x : ℂ) : IntegrableOn (fun q ↦ ‖F q - x‖) (closedBall p ε) :=
      (hKi.sub (integrableOn_const hK.measure_lt_top.ne)).norm
    have hvol : volume.real (closedBall p ε) = (2 * ε) ^ 2 := by
      obtain ⟨x, t⟩ := p
      rw [closedBall_prod, Measure.volume_eq_prod, measureReal_prod_prod,
        Real.volume_real_closedBall hε.1.le, Real.volume_real_closedBall hε.1.le, pow_two]
    have hmono := integral_mono_ae (integrableOn_const (C := ‖z - w‖) hK.measure_lt_top.ne)
      ((hi z).add (hi w)) (Eventually.of_forall fun q ↦ show ‖z - w‖ ≤ ‖F q - z‖ + ‖F q - w‖ from by
        simpa only [norm_sub_rev (F q) z, sub_add_sub_cancel] using norm_add_le (z - F q) (F q - w))
    simp only [Pi.add_apply] at hmono
    rw [setIntegral_const, hvol, smul_eq_mul, integral_add (hi z) (hi w)] at hmono
    rw [← add_div]
    exact (le_div_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hε.1))).2
      (by simpa only [mul_comm] using hmono)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

end NoEmbeddedEigenvalues
