import NoEmbeddedEigenvalues.Analysis.AxisReflectionJets
import NoEmbeddedEigenvalues.SpecifiedJetLp
import NoEmbeddedEigenvalues.IntervalH1Estimates
import NoEmbeddedEigenvalues.TraceL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Sobolev averaging along normal segments

Use the reparametrization `t = s²` of the normal segment. The factor `2s`
then cancels the inverse normal Jacobian in the joint squared integral.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

/-- Dilation of the second coordinate. -/
def normalScale (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, t * p.2)

private theorem contDiff_normalScale (t : ℝ) : ContDiff ℝ ∞ (normalScale t) := by
  unfold normalScale
  fun_prop

private def scaleHomeo (t : ℝ) (ht : t ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.smulOfNeZero t ht)

private theorem scaleHomeo_apply (t : ℝ) (ht : t ≠ 0) (p : ℝ × ℝ) :
    scaleHomeo t ht p = normalScale t p := rfl

private theorem scaleHomeo_symm_apply (t : ℝ) (ht : t ≠ 0) (p : ℝ × ℝ) :
    (scaleHomeo t ht).symm p = normalScale t⁻¹ p := rfl

private theorem map_normalScale {t : ℝ} (ht : 0 < t) :
    Measure.map (normalScale t) volume = ENNReal.ofReal t⁻¹ • volume := by
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map id (fun y : ℝ ↦ t * y)) (volume.prod volume) = _
  have hm : Measurable (fun y : ℝ ↦ t * y) := by fun_prop
  rw [← Measure.map_prod_map _ _ measurable_id hm,
    Measure.map_id, Real.map_volume_mul_left ht.ne', abs_of_pos (inv_pos.mpr ht),
    Measure.prod_smul_right]

private theorem map_normalScale_restrict_le {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {t : ℝ} (ht : 0 < t) (hT : MapsTo (normalScale t) U U) :
    Measure.map (normalScale t) (volume.restrict U) ≤ ENNReal.ofReal t⁻¹ • volume.restrict U := by
  have hm := (contDiff_normalScale t).continuous.measurable
  calc
    _ ≤ Measure.map (normalScale t) (volume.restrict (normalScale t ⁻¹' U)) :=
      Measure.map_mono (Measure.restrict_mono hT le_rfl) hm
    _ = _ := by rw [← Measure.restrict_map hm hU, map_normalScale ht, Measure.restrict_smul]

private theorem memLp_normalScale {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {t : ℝ} (ht : 0 < t) (hT : MapsTo (normalScale t) U U) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun p ↦ f (normalScale t p)) 2 (volume.restrict U) := by
  have h := (hf.smul_measure (ENNReal.ofReal_ne_top (r := t⁻¹))).mono_measure
    (map_normalScale_restrict_le hU ht hT)
  exact (scaleHomeo t ht.ne').measurableEmbedding.memLp_map_measure_iff.mp h

private theorem coordPartial_normalScale {φ : ℝ × ℝ → ℂ} (hφ : Differentiable ℝ φ)
    (t : ℝ) (j : Fin 2) (p : ℝ × ℝ) :
    coordPartial j (φ ∘ normalScale t) p =
      (if j = 0 then 1 else (t : ℂ)) * coordPartial j φ (normalScale t p) := by
  fin_cases j
  · change partialX (φ ∘ normalScale t) p = 1 * partialX φ (normalScale t p)
    rw [one_mul]
    rfl
  · change deriv (fun y : ℝ ↦ φ (p.1, t * y)) p.2 =
      (t : ℂ) * deriv (fun y : ℝ ↦ φ (p.1, y)) (t * p.2)
    have hd : DifferentiableAt ℝ (fun y : ℝ ↦ φ (p.1, y)) (t * p.2) :=
      (hφ (p.1, t * p.2)).comp (t * p.2)
        ((differentiableAt_const p.1).prodMk differentiableAt_id)
    have ht : HasDerivAt (fun y : ℝ ↦ t * y) t p.2 := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id p.2).const_mul t
    have hh := (hd.hasDerivAt.scomp p.2 ht).deriv
    change deriv (fun y : ℝ ↦ φ (p.1, t * y)) p.2 = _ at hh
    simpa only [Complex.real_smul] using hh

/-- Weak chain rule for a normal dilation taking the patch into itself. -/
theorem HasWeakPartialOn.comp_normalScale {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {t : ℝ} (ht : 0 < t) (hT : MapsTo (normalScale t) U U)
    {f d : ℝ × ℝ → ℂ} {j : Fin 2} (hd : HasWeakPartialOn U j f d)
    (hf : MemLp f 2 (volume.restrict U)) (hL : MemLp d 2 (volume.restrict U)) :
    HasWeakPartialOn U j (fun p ↦ f (normalScale t p))
      (fun p ↦ (if j = 0 then 1 else (t : ℂ)) * d (normalScale t p)) := by
  let T := scaleHomeo t ht.ne'
  let a : ℂ := if j = 0 then 1 else (t : ℂ)
  have hfi := memLp_normalScale hU.measurableSet ht hT hf
  have hdi := (memLp_normalScale hU.measurableSet ht hT hL).const_mul a
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hfi.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdi.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  let ψ := φ ∘ T.symm
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨hφ.contDiff.comp (contDiff_normalScale t⁻¹),
      hφ.hasCompactSupport.comp_homeomorph T.symm, ?_⟩
    intro p hp
    have hh : T.symm p ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ T.symm) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    have hmem : T (T.symm p) ∈ U := hT (hφ.tsupport_subset hh)
    rwa [T.apply_symm_apply] at hmem
  have hchain (p : ℝ × ℝ) : a * coordPartial j ψ (T p) = coordPartial j φ p := by
    have he := coordPartial_normalScale (hψ.contDiff.differentiable (by simp)) t j p
    have hcomp : ψ ∘ NoEmbeddedEigenvalues.normalScale t = φ :=
      funext fun p ↦ congrArg φ (T.symm_apply_apply p)
    rw [hcomp] at he
    exact he.symm
  have hw := congrArg (a * ·) (hd.2.2 ψ hψ)
  rw [← integral_const_mul, mul_neg, ← integral_const_mul] at hw
  have hmap : Measure.map T volume = ENNReal.ofReal t⁻¹ • volume := map_normalScale ht
  have hchange (g : ℝ × ℝ → ℂ) : (∫ p, g (T p)) = (t⁻¹ : ℝ) • ∫ p, g p := by
    rw [← T.measurableEmbedding.integral_map (g := g), hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)]
  have h1 := hchange (fun p ↦ a * (f p * coordPartial j ψ p))
  have h2 := hchange (fun p ↦ a * (d p * ψ p))
  simp only [mul_left_comm a (f (T _)), hchain] at h1
  simp only [ψ, Function.comp_apply, T.symm_apply_apply, ← mul_assoc] at h2
  change (∫ p, f (T p) * coordPartial j φ p) = -(∫ p, (a * d (T p)) * φ p)
  rw [h1, h2, hw, smul_neg]
  simp only [ψ, Function.comp_apply, mul_assoc]

/-- The reparametrized integrand for the order-`k` segment average. -/
def normalKernel (k : ℕ) (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (s : ℝ) : ℂ :=
  (2 * s ^ (2 * k + 1) : ℝ) • f (normalScale (s ^ 2) p)

/-- Average with normal-derivative weight `t^k`, reparametrized by `t = s²`. -/
def normalAverage (k : ℕ) (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∫ s in Ioo (0 : ℝ) 1, normalKernel k f p s

private theorem measurable_normalKernel (k : ℕ) {f : ℝ × ℝ → ℂ} (hf : Measurable f) :
    Measurable (fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k f q.1 q.2) := by
  unfold normalKernel normalScale
  fun_prop

/-- Normal averaging of a measurable representative is measurable. -/
theorem measurable_normalAverage (k : ℕ) {f : ℝ × ℝ → ℂ} (hf : Measurable f) :
    Measurable (normalAverage k f) :=
  (measurable_normalKernel k hf).stronglyMeasurable.integral_prod_right'.measurable

private abbrev unitVol : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

private theorem normalKernel_memLp {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    [IsFiniteMeasure (volume.restrict U)]
    (hT : ∀ t ∈ Ioo (0 : ℝ) 1, MapsTo (normalScale t) U U)
    {f : ℝ × ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2 (volume.restrict U)) (k : ℕ) :
    let B := fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k f q.1 q.2
    MemLp B 2 ((volume.restrict U).prod unitVol) ∧
      (∫ q, ‖B q‖ ^ 2 ∂((volume.restrict U).prod unitVol)) ≤ 4 * ∫ p in U, ‖f p‖ ^ 2 := by
  let B := fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k f q.1 q.2
  have hBm := measurable_normalKernel k hfm
  let M := ∫ p in U, ‖f p‖ ^ 2
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hslice (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      IntegrableOn (fun p ↦ ‖B (p, s)‖ ^ 2) U ∧ (∫ p in U, ‖B (p, s)‖ ^ 2) ≤ 4 * M := by
    have hss : s ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨pow_pos hs.1 _, pow_lt_one₀ hs.1.le hs.2 (by decide)⟩
    have hL := memLp_normalScale hU hss.1 (hT _ hss) hf
    have hB : MemLp (fun p ↦ B (p, s)) 2 (volume.restrict U) :=
      hL.const_smul (2 * s ^ (2 * k + 1) : ℝ)
    refine ⟨hB.integrable_norm_pow (by decide), ?_⟩
    have hscale : (∫ p in U, ‖f (normalScale (s ^ 2) p)‖ ^ 2) ≤ (s ^ 2)⁻¹ * M := by
      let T := scaleHomeo (s ^ 2) hss.1.ne'
      change (∫ p in U, ‖f (T p)‖ ^ 2) ≤ _
      rw [← T.measurableEmbedding.integral_map (g := fun p ↦ ‖f p‖ ^ 2)]
      have hi := (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).smul_measure
        (ENNReal.ofReal_ne_top (r := (s ^ 2)⁻¹))
      have he := integral_mono_measure (map_normalScale_restrict_le hU hss.1 (hT _ hss))
        (Eventually.of_forall fun p ↦ sq_nonneg ‖f p‖) hi
      rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at he
      exact he
    have hpoint (p : ℝ × ℝ) : ‖B (p, s)‖ ^ 2 =
        (2 * s ^ (2 * k + 1)) ^ 2 * ‖f (normalScale (s ^ 2) p)‖ ^ 2 := by
      simp only [B, normalKernel, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [hpoint]
    rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_left hscale (sq_nonneg _)).trans
    rw [← mul_assoc, show (2 * s ^ (2 * k + 1)) ^ 2 * (s ^ 2)⁻¹ =
        4 * (s ^ (2 * k)) ^ 2 by rw [pow_succ]; field_simp [hs.1.ne']; ring]
    have hpow : (s ^ (2 * k)) ^ 2 ≤ 1 := by
      rw [← pow_mul]
      exact pow_le_one₀ hs.1.le hs.2.le
    exact mul_le_mul_of_nonneg_right (by linarith only [hpow]) hM
  have houter : Integrable (fun s ↦ ∫ p in U, ‖B (p, s)‖ ^ 2) unitVol := by
    apply (integrable_const (4 * M)).mono'
      ((hBm.norm.pow_const 2).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
    exact (hslice s hs).2
  have hprod : Integrable (fun q ↦ ‖B q‖ ^ 2) ((volume.restrict U).prod unitVol) := by
    apply (integrable_prod_iff' (hBm.norm.pow_const 2).aestronglyMeasurable).2
    refine ⟨(ae_restrict_mem measurableSet_Ioo).mono fun s hs ↦ (hslice s hs).1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using houter
  refine ⟨(memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable).2 hprod, ?_⟩
  rw [integral_prod_symm _ hprod]
  have hi := integral_mono_ae houter (integrable_const (4 * M))
    ((ae_restrict_mem measurableSet_Ioo).mono fun s hs ↦ (hslice s hs).2)
  simpa [unitVol, Measure.real, Real.volume_Ioo] using hi

/-- The squared normal-average bound, uniform in the derivative weight. -/
theorem normalAverage_memLp {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    [IsFiniteMeasure (volume.restrict U)]
    (hT : ∀ t ∈ Ioo (0 : ℝ) 1, MapsTo (normalScale t) U U)
    {f : ℝ × ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2 (volume.restrict U)) (k : ℕ) :
    MemLp (normalAverage k f) 2 (volume.restrict U) ∧
      (∫ p in U, ‖normalAverage k f p‖ ^ 2) ≤ 4 * ∫ p in U, ‖f p‖ ^ 2 := by
  let B := fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k f q.1 q.2
  have hBm := measurable_normalKernel k hfm
  obtain ⟨hBL, hBE⟩ := normalKernel_memLp hU hT hfm hf k
  have hBs : Integrable (fun q ↦ ‖B q‖ ^ 2) ((volume.restrict U).prod unitVol) :=
    hBL.integrable_norm_pow (by decide)
  have hAm : AEStronglyMeasurable (normalAverage k f) (volume.restrict U) :=
    hBm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hpoint : ∀ᵐ p ∂volume.restrict U,
      ‖normalAverage k f p‖ ^ 2 ≤ ∫ s, ‖B (p, s)‖ ^ 2 ∂unitVol := by
    filter_upwards [hBs.prod_right_ae] with p hp
    have hL : MemLp (fun s ↦ B (p, s)) 2 unitVol :=
      (memLp_two_iff_integrable_sq_norm
        ((hBm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).2 hp
    have hL' : MemLp (fun s ↦ B (p, s)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
      rwa [← restrict_Ioo_eq_restrict_Icc]
    have h := norm_intervalIntegral_sq_le zero_le_one hL'
    simpa only [normalAverage, B, unitVol, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, sub_zero, one_mul] using h
  have hAs : IntegrableOn (fun p ↦ ‖normalAverage k f p‖ ^ 2) U := by
    apply hBs.integral_prod_left.mono' (hAm.norm.pow 2)
    filter_upwards [hpoint] with p hp
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hp
  refine ⟨(memLp_two_iff_integrable_sq_norm hAm).2 hAs, ?_⟩
  exact (integral_mono_ae hAs hBs.integral_prod_left hpoint).trans
    ((integral_prod _ hBs).symm.le.trans hBE)

/-- A normal average differentiates under the integral. Only normal derivatives
increase the power of the segment parameter. -/
theorem HasWeakPartialOn.average_normal {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    (hT : ∀ t ∈ Ioo (0 : ℝ) 1, MapsTo (normalScale t) U U)
    {f d : ℝ × ℝ → ℂ} {j : Fin 2} (hd : HasWeakPartialOn U j f d)
    (hfm : Measurable f) (hdm : Measurable d)
    (hf : MemLp f 2 (volume.restrict U)) (hL : MemLp d 2 (volume.restrict U)) (k : ℕ) :
    HasWeakPartialOn U j (normalAverage k f) (normalAverage (k + if j = 0 then 0 else 1) d) := by
  let k' := k + if j = 0 then 0 else 1
  let μ := volume.restrict U
  let F := fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k f q.1 q.2
  let D := fun q : (ℝ × ℝ) × ℝ ↦ normalKernel k' d q.1 q.2
  have hAF := (normalAverage_memLp hU.measurableSet hT hfm hf k).1
  have hAD := (normalAverage_memLp hU.measurableSet hT hdm hL k').1
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hAF.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hAD.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  have hb {ψ : ℝ × ℝ → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
      ∃ C : ℝ, ∀ p, ‖ψ p‖ ≤ C := by
    obtain ⟨C, hC⟩ := hs.isCompact.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, fun p ↦ ?_⟩
    by_cases hp : p ∈ tsupport ψ
    · exact (hC p hp).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport hp]
  have hInt {B : (ℝ × ℝ) × ℝ → ℂ} (hB : MemLp B 2 (μ.prod unitVol))
      {ψ : ℝ × ℝ → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
      Integrable (fun q ↦ B q * ψ q.1) (μ.prod unitVol) := by
    obtain ⟨C, hC⟩ := hb hc hs
    exact (hB.integrable (by norm_num)).mul_bdd
      (hc.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun q ↦ hC q.1)
  have hiF := hInt (normalKernel_memLp hU.measurableSet hT hfm hf k).1
    (hφ.continuous_coordPartial j) (hφ.hasCompactSupport_coordPartial j)
  have hiD := hInt (normalKernel_memLp hU.measurableSet hT hdm hL k').1
    hφ.contDiff.continuous hφ.hasCompactSupport
  have hrestrict {g ψ : ℝ × ℝ → ℂ} (hs : tsupport ψ ⊆ U) :
      (∫ p, g p * ψ p) = ∫ p, g p * ψ p ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hs h)), mul_zero]
  rw [hrestrict ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset),
    hrestrict hφ.tsupport_subset]
  have hFub {B : (ℝ × ℝ) × ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
      (hI : Integrable (fun q ↦ B q * ψ q.1) (μ.prod unitVol)) :
      (∫ p, (∫ s, B (p, s) ∂unitVol) * ψ p ∂μ) =
        ∫ s, (∫ p, B (p, s) * ψ p ∂μ) ∂unitVol := by
    rw [← integral_prod_symm _ hI, integral_prod _ hI]
    simp only [integral_mul_const]
  change (∫ p, (∫ s, F (p, s) ∂unitVol) * coordPartial j φ p ∂μ) =
    -(∫ p, (∫ s, D (p, s) ∂unitVol) * φ p ∂μ)
  rw [hFub hiF, hFub hiD, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have ht : s ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨pow_pos hs.1 _, pow_lt_one₀ hs.1.le hs.2 (by decide)⟩
  have h := ((hd.comp_normalScale hU ht.1 (hT _ ht) hf hL).const_mul
    ((2 * s ^ (2 * k + 1) : ℝ) : ℂ)).2.2 φ hφ
  rw [hrestrict ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset),
    hrestrict hφ.tsupport_subset] at h
  have he (p : ℝ × ℝ) : ((2 * s ^ (2 * k + 1) : ℝ) : ℂ) *
      ((if j = 0 then 1 else (↑(s ^ 2) : ℂ)) * d (normalScale (s ^ 2) p)) = D (p, s) := by
    dsimp only [D, normalKernel, k']
    rw [Complex.real_smul]
    split_ifs with hj
    · simp
    · push_cast
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
      ring
  change (∫ p, F (p, s) * coordPartial j φ p ∂μ) = -(∫ p, D (p, s) * φ p ∂μ)
  simp only [he] at h
  simpa only [F, normalKernel, Complex.real_smul] using h

/-- Dilation of a primitive, including its orientation when the height is negative. -/
theorem mul_normalAverage_zero (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    (p.2 : ℂ) * normalAverage 0 f p = ∫ y in (0 : ℝ)..p.2, f (p.1, y) := by
  rw [normalAverage, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [normalKernel, zero_add, mul_zero, pow_one, normalScale]
  let g : ℝ → ℝ := fun s ↦ s ^ 2 * p.2
  let g' : ℝ → ℝ := fun s ↦ 2 * s * p.2
  have hg : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    simpa [g, g'] using ((hasDerivAt_pow 2 s).mul_const p.2)
  have hgc : ContinuousOn g (uIcc 0 1) := (by fun_prop : Continuous g).continuousOn
  have hh : ∀ s ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt g (g' s) s := fun s _ ↦ hg s
  have hsub : (∫ s in (0 : ℝ)..1, g' s • (f (p.1, g s))) = ∫ y in g 0..g 1, f (p.1, y) := by
    rcases le_total 0 p.2 with hp | hp
    · apply intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
        (g := fun y ↦ f (p.1, y)) hgc hh
      intro s hs
      have hs₀ : 0 ≤ s := by simpa only [min_eq_left zero_le_one] using hs.1.le
      exact mul_nonneg (mul_nonneg (by norm_num) hs₀) hp
    · apply intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
        (g := fun y ↦ f (p.1, y)) hgc hh
      intro s hs
      have hs₀ : 0 ≤ s := by simpa only [min_eq_left zero_le_one] using hs.1.le
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hs₀) hp
  simp only [g, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, one_pow,
    one_mul] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  simp only [g', Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The primitive of the normal weak partial recovers the odd function a.e. -/
theorem HasWeakPartialOn.eq_mul_normalAverage_of_odd {b l r : ℝ} (hb : 0 < b) (hlr : l < r)
    {R d : ℝ × ℝ → ℂ}
    (hw : HasWeakPartialOn (Ioo l r ×ˢ Ioo (-b) b) 1 R d)
    (hR : MemLp R 2 (volume.restrict (Ioo l r ×ˢ Ioo (-b) b)))
    (hd : MemLp d 2 (volume.restrict (Ioo l r ×ˢ Ioo (-b) b))) (hdm : Measurable d)
    (ho : ∀ᵐ p ∂volume.restrict (Ioo l r ×ˢ Ioo (-b) b), R (p.1, -p.2) = -R p) :
    ∀ᵐ p ∂volume.restrict (Ioo l r ×ˢ Ioo (-b) b), R p = (p.2 : ℂ) * normalAverage 0 d p := by
  let I := Ioo l r
  let J := Ioo (-b) b
  let U := I ×ˢ J
  have hz : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hb, hb⟩
  have hneg : MapsTo (fun t : ℝ ↦ -t) J J := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmaps : MapsTo (axisReflect 1) U U := fun p hp ↦ ⟨hp.1, hneg hp.2⟩
  obtain ⟨G, hGm, hGe, hGa⟩ := hw.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr hlr) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr (hz.1.trans hz.2))
  have hGr := ((measurePreserving_axisReflect 1).quasiMeasurePreserving.restrict hmaps).ae hGe
  have hGo : (fun p : ℝ × ℝ ↦ G (p.1, -p.2)) =ᵐ[volume.restrict U] fun p ↦ -G p := by
    filter_upwards [hGr, hGe, ho] with p hp he ho
    change G (p.1, -p.2) = R (p.1, -p.2) at hp
    rw [hp, ho, he]
  have hc := hGa.ae_continuousOn isOpen_Ioo
  have hco : ∀ᵐ x ∂(volume.restrict I), ContinuousOn (fun t ↦ G (x, -t)) J := by
    filter_upwards [hc] with x hx
    exact hx.comp continuous_neg.continuousOn hneg
  have hrows := ae_eqOn_sections_of_ae_eq isOpen_Ioo hGo hco (hc.mono fun x hx ↦ hx.neg)
  have hGzero : ∀ᵐ x ∂(volume.restrict I), G (x, 0) = 0 := by
    filter_upwards [hrows] with x hx
    apply CharZero.eq_neg_self_iff.mp
    simpa only [neg_zero] using hx 0 hz
  have hm : Measurable (fun p : ℝ × ℝ ↦ (p.2 : ℂ) * normalAverage 0 d p) := by
    have h := measurable_normalAverage 0 hdm
    fun_prop
  have hprod : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict J)),
      G p = (p.2 : ℂ) * normalAverage 0 d p := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hGm hm)]
    filter_upwards [hGa.ae_hasIntervalH1 (hR.ae_eq hGe.symm) hd, hGzero] with x hx hx0
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [mul_normalAverage_zero d (x, y), hx.integral_eq_sub hz hy, hx0, sub_zero]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  exact hGe.symm.trans hprod

end NoEmbeddedEigenvalues
