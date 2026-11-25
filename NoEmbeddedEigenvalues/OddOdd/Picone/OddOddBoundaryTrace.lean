module

public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddForms

/-!
# The B-weighted level trace

The vanishing coefficient compensates for the orbit-time Jacobian. In diagonal
coordinates its absolute value is bounded by a constant times `cos a`, uniformly
on small quarter orbits. This gives a bounded dominating density on a fixed
finite interval, without Sobolev derivative traces or exceptional levels.
Only boundedness and continuity of the chosen value representative are used.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Set Filter Topology

private theorem boundaryGround_ge_one {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) :
    1 ≤ ddBoundaryGround r := by
  have hl : Real.log (r / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  unfold ddBoundaryGround
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hl]

-- A square-root bound is enough: on a quarter graph sqrt(r) ≤ 2 cos(a).
private theorem abs_boundaryB_le_sqrt {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    |ddBoundaryB r| ≤ 6 * √r := by
  let L := Real.log (r / 2)
  have hL : L ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hden := boundaryGround_ge_one hr.le hr2
  have hc : |32 - 25 * r| ≤ 32 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hk : |16 - 12 * r| ≤ 16 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hi : |(32 - 25 * r) * L + 16 - 12 * r| ≤ 32 * (-L) + 16 := by
    calc
      _ = |(32 - 25 * r) * L + (16 - 12 * r)| := by congr 1; ring
      _ ≤ |(32 - 25 * r) * L| + |16 - 12 * r| := abs_add_le _ _
      _ ≤ 32 * (-L) + 16 := by
        rw [abs_mul, abs_of_nonpos hL]
        exact add_le_add (mul_le_mul_of_nonneg_right hc (neg_nonneg.mpr hL)) hk
  have hB : |ddBoundaryB r| ≤ r + r * (-L) := by
    rw [ddBoundaryB, abs_div, abs_of_pos (by linarith : 0 < ddBoundaryGround r)]
    calc
      _ ≤ |5 * r / 16 + r / 256 * ((32 - 25 * r) * L + 16 - 12 * r)| :=
        div_le_self (abs_nonneg _) hden
      _ ≤ 5 * r / 16 + r / 256 * (32 * (-L) + 16) := by
        apply (abs_add_le _ _).trans
        rw [abs_of_nonneg (by positivity : 0 ≤ 5 * r / 16), abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ r / 256)]
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hr.le (neg_nonneg.mpr hL)]
  let z := √(r / 2)
  have hz : 0 < z := Real.sqrt_pos.mpr (by positivity)
  have hzs : z ^ 2 = r / 2 := Real.sq_sqrt (by positivity)
  have hz1 : z ≤ 1 := by nlinarith
  have hlz : L = 2 * Real.log z := by
    dsimp [L]
    rw [← hzs, Real.log_pow]
    norm_num
  have hzl : z * (-Real.log z) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hz) hz.le
    rw [mul_sub, mul_inv_cancel₀ hz.ne'] at hh
    linarith
  have hrl : r * (-L) ≤ 4 * z := by
    calc
      _ = 4 * (z * (z * (-Real.log z))) := by
        rw [show r = 2 * z ^ 2 by linarith, hlz]
        ring
      _ ≤ 4 * z := by nlinarith [mul_le_mul_of_nonneg_left hzl hz.le]
  have hzr : z ≤ √r := Real.sqrt_le_sqrt (by linarith)
  have hrz : r ≤ 2 * z := by nlinarith
  linarith

private theorem gradSq_diag (a b : ℝ) :
    gradSq dipoleLift (diagInv (a, b)) =
      2 * (sin a ^ 2 * cos b ^ 2 + cos a ^ 2 * sin b ^ 2) := by
  simp [gradSq_dipoleLift, diagInv_apply, Real.sin_add, Real.sin_sub]
  ring

private theorem gradSq_range (p : ℝ × ℝ) :
    0 ≤ gradSq dipoleLift p ∧ gradSq dipoleLift p ≤ 2 := by
  rw [gradSq_dipoleLift]
  constructor
  · positivity
  · nlinarith [sin_sq_add_cos_sq p.1, sin_sq_add_cos_sq p.2,
      sq_nonneg (cos p.1), sq_nonneg (cos p.2)]

private theorem quarter_gradSq_bound {h a : ℝ} (hh : h ∈ Ioo (0 : ℝ) (1 / 4))
    (ha : a ∈ Ioo (-arccos √h) (arccos √h)) :
    0 < gradSq dipoleLift (diagInv (a, quarterHeight h a)) ∧
      gradSq dipoleLift (diagInv (a, quarterHeight h a)) ≤ 4 * cos a ^ 2 := by
  have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, by linarith [hh.2]⟩
  have hc : √h < cos a := sqrt_lt_cos_of_abs_lt_arccos hh1
    (abs_lt.mpr ⟨by linarith [ha.1], ha.2⟩)
  have hc0 : 0 < cos a := (Real.sqrt_pos.mpr hh.1).trans hc
  have hc2 : h < cos a ^ 2 := by
    have hs := mul_pos (sub_pos.mpr hc) (show 0 < cos a + √h by positivity)
    nlinarith [Real.sq_sqrt hh.1.le]
  have hc1 : cos a ≤ 1 := Real.cos_le_one a
  have hq0 : 0 < h / cos a := div_pos hh.1 hc0
  have hq1 : h / cos a < 1 := (div_lt_one hc0).mpr (by nlinarith)
  have hb : cos (quarterHeight h a) = h / cos a :=
    Real.cos_arccos (by linarith) hq1.le
  have hbc : cos (quarterHeight h a) ≤ cos a := by
    rw [hb]
    exact (div_le_iff₀ hc0).mpr (by nlinarith)
  have hb0 : 0 ≤ cos (quarterHeight h a) := by rw [hb]; positivity
  have hbs : 0 < sin (quarterHeight h a) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (quarterHeight h a)]
  rw [gradSq_diag]
  constructor
  · nlinarith [mul_pos (sq_pos_of_pos hc0) hbs,
      mul_nonneg (sq_nonneg (sin a)) (sq_nonneg (cos (quarterHeight h a)))]
  · have hs1 : sin a ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq a, sq_nonneg (cos a)]
    have hs2 : sin (quarterHeight h a) ^ 2 ≤ 1 := by
      nlinarith [sin_sq_add_cos_sq (quarterHeight h a), sq_nonneg (cos (quarterHeight h a))]
    have hb2 := pow_le_pow_left₀ hb0 hbc 2
    have hm1 := mul_le_mul_of_nonneg_right hs1 (sq_nonneg (cos (quarterHeight h a)))
    have hm2 := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (cos a))
    nlinarith

private theorem measurable_boundaryB : Measurable ddBoundaryB := by
  unfold ddBoundaryB ddBoundaryGround
  fun_prop

private theorem continuousAt_boundaryB {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ContinuousAt ddBoundaryB r := by
  have hd : ddBoundaryGround r ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (boundaryGround_ge_one hr.le hr2))
  unfold ddBoundaryB
  apply ContinuousAt.div _ _ hd
  · fun_prop (disch := positivity)
  · unfold ddBoundaryGround
    fun_prop (disch := positivity)

private theorem continuous_gradSq : Continuous (gradSq dipoleLift) := by
  rw [gradSq_dipoleLift]
  fun_prop

private theorem abs_boundaryB_le_cos {r c : ℝ} (hr : 0 < r) (hr2 : r ≤ 2)
    (hc : 0 < c) (hbound : r ≤ 4 * c ^ 2) : |ddBoundaryB r| ≤ 12 * c := by
  have hs : √r ≤ 2 * c := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  linarith [abs_boundaryB_le_sqrt hr hr2]

private theorem quarter_density_bound {f : ℝ × ℝ → ℝ} {M h a : ℝ}
    (hM : 0 ≤ M) (hf : ∀ p, |f p| ≤ M) (hh : h ∈ Ioo (0 : ℝ) (1 / 4))
    (ha : a ∈ Ioo (-arccos √h) (arccos √h)) :
    ‖ddBoundaryB (gradSq dipoleLift (diagInv (a, quarterHeight h a))) *
      f (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2)‖ ≤ 24 * M := by
  have hc : √h < cos a := sqrt_lt_cos_of_abs_lt_arccos
    ⟨hh.1, by linarith [hh.2]⟩ (abs_lt.mpr ⟨by linarith [ha.1], ha.2⟩)
  have hc0 : 0 < cos a := (Real.sqrt_pos.mpr hh.1).trans hc
  have hc2 : h ≤ cos a ^ 2 := by
    have hs := mul_pos (sub_pos.mpr hc) (show 0 < cos a + √h by positivity)
    nlinarith [Real.sq_sqrt hh.1.le]
  obtain ⟨hr, hrle⟩ := quarter_gradSq_bound hh ha
  have hb := abs_boundaryB_le_cos hr (gradSq_range _).2 hc0 hrle
  have hw := one_div_sqrt_cos_sq_sub_le_two_div hh.1.le hc0 hc2 (Or.inr hh.2.le)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
  calc
    _ ≤ (12 * cos a) * M * (2 / cos a) := by
      apply mul_le_mul (mul_le_mul hb (hf _) (abs_nonneg _) (by positivity))
        (by simpa only [one_div] using hw) (by positivity) (by positivity)
    _ = _ := by field_simp; ring

private theorem arc_density_bound {f : ℝ × ℝ → ℝ} {M a : ℝ}
    (hM : 0 ≤ M) (hf : ∀ p, |f p| ≤ M) (ha : a ∈ Ioo (-(π / 2)) (π / 2)) :
    ‖ddBoundaryB (gradSq dipoleLift (diagInv (a, π / 2))) *
      f (diagInv (a, π / 2)) / cos a‖ ≤ 24 * M := by
  have hc := cos_pos_of_mem_Ioo ha
  have hr : gradSq dipoleLift (diagInv (a, π / 2)) = 2 * cos a ^ 2 := by
    rw [gradSq_diag]
    simp
  have hb := abs_boundaryB_le_cos (by rw [hr]; positivity :
      0 < gradSq dipoleLift (diagInv (a, π / 2))) (gradSq_range _).2 hc
    (by rw [hr]; nlinarith [sq_nonneg (cos a)])
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hc]
  have hh := mul_le_mul hb (hf (diagInv (a, π / 2))) (abs_nonneg _) (by positivity)
  apply (div_le_iff₀ hc).mpr
  nlinarith

private theorem boundaryB_quarter_limit {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ p, |f p| ≤ M) :
    Integrable (fun t ↦ ddBoundaryB (gradSq dipoleLift (separatrixArc t)) * f (separatrixArc t)) ∧
    (∀ h ∈ Ioo (0 : ℝ) (1 / 4), IntegrableOn
      (fun t ↦ ddBoundaryB (gradSq dipoleLift (dipoleOrbit h t)) * f (dipoleOrbit h t))
      (Ioo (-eighthPeriod h) (eighthPeriod h))) ∧
    Tendsto (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        ddBoundaryB (gradSq dipoleLift (dipoleOrbit h t)) * f (dipoleOrbit h t))
      (𝓝[>] 0) (𝓝 (∫ t,
        ddBoundaryB (gradSq dipoleLift (separatrixArc t)) * f (separatrixArc t))) := by
  let g : ℝ × ℝ → ℝ := fun p ↦ ddBoundaryB (gradSq dipoleLift p) * f p
  let A := Ioo (-(π / 2)) (π / 2)
  let S : ℝ → Set ℝ := fun h ↦ Ioo (-arccos √h) (arccos √h)
  let H : ℝ → ℝ → ℝ := fun h ↦ (S h).indicator
    (fun a ↦ g (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2))
  have hgm : Measurable g :=
    (measurable_boundaryB.comp continuous_gradSq.measurable).mul hf.measurable
  have hHm (h : ℝ) : Measurable (H h) := by
    apply Measurable.indicator _ measurableSet_Ioo
    apply Measurable.div
    · apply hgm.comp
      unfold quarterHeight
      fun_prop
    · fun_prop
  have hSA (h : ℝ) (h0 : 0 < h) : S h ⊆ A :=
    Ioo_subset_Ioo (by linarith [Real.arccos_lt_pi_div_two.mpr (Real.sqrt_pos.mpr h0)])
      (Real.arccos_lt_pi_div_two.mpr (Real.sqrt_pos.mpr h0)).le
  have hHbound (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4)) (a : ℝ) : ‖H h a‖ ≤ 24 * M := by
    by_cases ha : a ∈ S h
    · rw [show H h a = g (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2) from
        indicator_of_mem ha _]
      exact quarter_density_bound hM hbound hh ha
    · rw [show H h a = 0 from indicator_of_notMem ha _]
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) hM
  have hArc : IntegrableOn (fun a ↦ g (diagInv (a, π / 2)) / cos a) A := by
    apply Integrable.mono' (integrable_const (24 * M))
      ((hgm.comp (by fun_prop)).div (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact arc_density_bound hM hbound ha
  have hga : Integrable (fun t ↦ g (separatrixArc t)) := by
    refine ⟨(hgm.comp (by unfold separatrixArc arcAngle; fun_prop)).aestronglyMeasurable, ?_⟩
    apply hasFiniteIntegral_iff_eNorm.mpr
    rw [lintegral_separatrixArc_eq (fun p ↦ ‖g p‖ₑ)]
    have he : (∫⁻ a in A, ENNReal.ofReal (1 / cos a) * ‖g (diagInv (a, π / 2))‖ₑ) =
        ∫⁻ a in A, ‖g (diagInv (a, π / 2)) / cos a‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      have hc := cos_pos_of_mem_Ioo ha
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / cos a)]
      congr 1
      simp only [norm_div, Real.norm_eq_abs, abs_of_pos hc]
      ring
    rw [he]
    exact hasFiniteIntegral_iff_eNorm.mp hArc.hasFiniteIntegral
  have hquarter (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4)) :
      (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), g (dipoleOrbit h t)) = ∫ a in A, H h a := by
    rw [integral_quarter_eq hh.1 (by linarith [hh.2]),
      show (∫ a in A, H h a) = ∫ a in S h,
        g (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2) by
          rw [show (H h) = (S h).indicator
            (fun a ↦ g (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2)) from rfl,
            integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            inter_eq_left.mpr (hSA h hh.1)]]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro a _
    simp only [smul_eq_mul, one_div]
    ring
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) (1 / 4) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict A)
    (F := H) (f := fun a ↦ g (diagInv (a, π / 2)) / cos a) (fun _ ↦ 24 * M)
    (Eventually.of_forall fun h ↦ (hHm h).aestronglyMeasurable)
    (hev.mono fun h hh ↦ Eventually.of_forall (hHbound h hh)) (integrable_const _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      have hc := cos_pos_of_mem_Ioo ha
      have hr : gradSq dipoleLift (diagInv (a, π / 2)) = 2 * cos a ^ 2 := by
        rw [gradSq_diag]
        simp
      have hgc : ContinuousAt g (diagInv (a, π / 2)) := by
        apply ContinuousAt.mul _ hf.continuousAt
        exact (continuousAt_boundaryB (by rw [hr]; positivity) (gradSq_range _).2).comp
          continuous_gradSq.continuousAt
      have hβ : ContinuousAt (fun h : ℝ ↦ quarterHeight h a) 0 := by
        unfold quarterHeight
        fun_prop
      have hβ0 : quarterHeight 0 a = π / 2 := by simp [quarterHeight]
      have hpt : Tendsto (fun h : ℝ ↦ diagInv (a, quarterHeight h a)) (𝓝 0)
          (𝓝 (diagInv (a, π / 2))) := by
        simpa only [hβ0, Function.comp_def] using
          ((diagInv.continuous.tendsto (a, quarterHeight 0 a)).comp
            (tendsto_const_nhds.prodMk_nhds hβ.tendsto))
      have hw : Tendsto (fun h : ℝ ↦ √(cos a ^ 2 - h ^ 2)) (𝓝 0) (𝓝 (cos a)) := by
        simpa [Real.sqrt_sq hc.le] using
          (show Continuous (fun h : ℝ ↦ √(cos a ^ 2 - h ^ 2)) by fun_prop).tendsto 0
      have hmem : ∀ᶠ h in 𝓝 (0 : ℝ), a ∈ S h := by
        have ht := ((Real.continuous_arccos.comp Real.continuous_sqrt).tendsto (0 : ℝ)).eventually
          (lt_mem_nhds (show |a| < arccos √(0 : ℝ) by
            simpa using abs_lt.mpr ha))
        filter_upwards [ht] with h hh
        exact abs_lt.mp hh
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact ((hgc.tendsto.comp hpt).div hw hc.ne').congr'
        (hmem.mono fun h hh ↦ (indicator_of_mem hh _).symm))
  refine ⟨hga, ?_, ?_⟩
  · intro h hh
    rw [integrableOn_quarter_iff hh.1 (by linarith [hh.2]) g]
    have hi : IntegrableOn (H h) A := Integrable.mono' (integrable_const (24 * M))
      (hHm h).aestronglyMeasurable (Eventually.of_forall (hHbound h hh))
    apply (hi.mono_set (hSA h hh.1)).congr_fun _ measurableSet_Ioo
    intro a ha
    dsimp only [H]
    rw [indicator_of_mem ha]
    simp only [smul_eq_mul]
    ring
  · have heq : (∫ t, g (separatrixArc t)) = ∫ a in A, g (diagInv (a, π / 2)) / cos a := by
      rw [integral_separatrixArc_eq]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro a _
      simp only [smul_eq_mul]
      ring
    rw [heq]
    exact hlim.congr' (hev.mono fun h hh ↦ (hquarter h hh).symm)

private theorem gradSq_rot (k : ℕ) (p : ℝ × ℝ) :
    gradSq dipoleLift (rotLift^[k] p) = gradSq dipoleLift p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hr (q : ℝ × ℝ) : gradSq dipoleLift (rotLift q) = gradSq dipoleLift q := by
      simp [gradSq_dipoleLift, rotLift, add_comm]
    rw [hr, ih]

private theorem gradSq_arc (t : ℝ) :
    gradSq dipoleLift (separatrixArc t) = 2 / Real.cosh t ^ 2 := by
  simp only [gradSq_dipoleLift, separatrixArc, Real.sin_sub_pi, neg_sq, sin_arcAngle]
  ring

/-- The logarithmic `B` weight is integrable on every arc and has a full level limit. -/
theorem dd_boundaryB_trace_limit {φ : L2} (_hφ : MemSobolev 2 φ) :
    (∀ k : Fin 4, Integrable (ddArcCorrection φ k)) ∧
      Tendsto (ddLevelBMass φ) (𝓝[>] 0)
        (𝓝 (∑ k : Fin 4, ∫ t, ddArcCorrection φ k t)) := by
  let f : Fin 4 → ℝ × ℝ → ℝ := fun k p ↦
    ‖continuousRep φ (torusProj (rotLift^[k.val] p))‖ ^ 2
  let g : ℝ × ℝ → ℝ := fun p ↦ ddBoundaryB (gradSq dipoleLift p) *
    ‖continuousRep φ (torusProj p)‖ ^ 2
  have hf (k : Fin 4) : Continuous (f k) :=
    (((continuousRep φ).continuous.comp isOpenQuotientMap_torusProj.continuous).comp
      ((show Continuous rotLift by unfold rotLift; fun_prop).iterate k.val)).norm.pow 2
  have hb (k : Fin 4) (p : ℝ × ℝ) : |f k p| ≤ ‖continuousRep φ‖ ^ 2 := by
    dsimp [f]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((continuousRep φ).norm_coe_le_norm _) 2
  have hq (k : Fin 4) := boundaryB_quarter_limit (hf k) (sq_nonneg ‖continuousRep φ‖) (hb k)
  have hrot (k : Fin 4) (p : ℝ × ℝ) :
      g (rotLift^[k.val] p) = ddBoundaryB (gradSq dipoleLift p) * f k p := by
    dsimp [g, f]
    rw [gradSq_rot]
  have harc (k : Fin 4) (t : ℝ) :
      ddBoundaryB (gradSq dipoleLift (separatrixArc t)) * f k (separatrixArc t) =
        ddArcCorrection φ k t := by
    rw [gradSq_arc]
    rfl
  have hqi (k : Fin 4) (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4)) :
      IntervalIntegrable (fun t ↦ g (rotLift^[k.val] (dipoleOrbit h t))) volume
        (-eighthPeriod h) (eighthPeriod h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by linarith [eighthPeriod_pos hh.1 (by linarith [hh.2])])]
    simpa only [hrot] using (hq k).2.1 h hh
  have hsum : Tendsto
      (fun h ↦ ∑ k : Fin 4, ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        ddBoundaryB (gradSq dipoleLift (dipoleOrbit h t)) * f k (dipoleOrbit h t))
      (𝓝[>] 0) (𝓝 (∑ k : Fin 4, ∫ t, ddArcCorrection φ k t)) := by
    apply tendsto_finsetSum
    intro k _
    simpa only [harc] using (hq k).2.2
  have hlevel : Tendsto (fun h ↦ levelIntegral h g) (𝓝[>] 0)
      (𝓝 (∑ k : Fin 4, ∫ t, ddArcCorrection φ k t)) := by
    apply hsum.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
    rw [levelIntegral_eq_sum_quarter' hh.1 (by linarith [hh.2])
      (fun k hk ↦ hqi ⟨k, hk⟩ h hh)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_of_le
      (by linarith [eighthPeriod_pos hh.1 (by linarith [hh.2])]), integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    exact (hrot k (dipoleOrbit h t)).symm
  refine ⟨fun k ↦ by simpa only [harc] using (hq k).1, ?_⟩
  have hscale : Tendsto (fun ε : ℝ ↦ ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_id : Tendsto (fun ε : ℝ ↦ ε) (𝓝 0) (𝓝 0))).div_const 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change (0 : ℝ) < ε / 2
      exact div_pos hε (by norm_num)
  exact hlevel.comp hscale

end NoEmbeddedEigenvalues
