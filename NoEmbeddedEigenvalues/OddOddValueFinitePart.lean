import NoEmbeddedEigenvalues.OddOddForms

/-!
# Finite part of the level value mass

Squared continuous H² values are one-half Hölder. Their endpoint-subtracted
arc values have exponential tails, while the orbit–arc comparison error is
bounded by a quarter power of the level. Integration on the growing quarter
window and the leading period asymptotic give the full positive-level limit.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology Real

private def valueMass (u : L2) (k : Fin 4) (p : ℝ × ℝ) : ℝ :=
  ‖continuousRep u (torusProj (rotLift^[k.val] p))‖ ^ 2

private theorem rotation_isometry (k : ℕ) : Isometry (rotLift^[k]) := by
  have hr : Isometry rotLift := Isometry.of_dist_eq fun p q ↦ by
    simp [rotLift, Prod.dist_eq, max_comm]
  induction k with
  | zero => exact isometry_id
  | succ k ih => exact ih.comp hr

private theorem valueMass_continuous (u : L2) (k : Fin 4) : Continuous (valueMass u k) :=
  (((continuousRep u).continuous.comp isOpenQuotientMap_torusProj.continuous).comp
    ((show Continuous rotLift by unfold rotLift; fun_prop).iterate k.val)).norm.pow 2

private theorem continuous_arc : Continuous separatrixArc := by
  unfold separatrixArc arcAngle
  fun_prop

private theorem valueMass_holder {u : L2} (hu : MemSobolev 2 u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : Fin 4, ∀ p q : ℝ × ℝ,
      |valueMass u k p - valueMass u k q| ≤ K * √(dist p q) := by
  obtain ⟨K, hK, hbound⟩ := exists_continuousRep_norm_sq_holder hu
  refine ⟨K, hK, fun k p q ↦
    (hbound (torusProj (rotLift^[k.val] p)) (torusProj (rotLift^[k.val] q))).trans ?_⟩
  gcongr
  exact (dist_torusProj_le _ _).trans_eq ((rotation_isometry k.val).dist_eq p q)

private theorem sqrt_two_exp (r : ℝ) : √(2 * exp r) = √2 * exp (r / 2) := by
  simp only [sqrt_eq_rpow]
  rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (exp_pos r).le, ← exp_mul]
  congr 2
  ring

private theorem arc_remainder_bound {u : L2} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ k : Fin 4, ∀ p q : ℝ × ℝ,
      |valueMass u k p - valueMass u k q| ≤ K * √(dist p q))
    (k : Fin 4) (t : ℝ) :
    |ddArcValueRemainder u k t| ≤ K * √2 * exp (-(1 / 2) * |t|) := by
  change |valueMass u k (separatrixArc t) -
    if t < 0 then valueMass u k (π, 0) else valueMass u k (0, -π)| ≤ _
  by_cases ht : t < 0
  · rw [ite_eq_left ht, abs_of_neg ht]
    calc _ ≤ K * √(dist (separatrixArc t) (π, 0)) := hbound k _ _
         _ ≤ K * √(2 * exp t) := by gcongr; exact dist_arc_neg_le t
         _ = _ := by
           rw [sqrt_two_exp, show t / 2 = -(1 / 2 : ℝ) * -t by ring]
           ring
  · rw [ite_eq_right ht, abs_of_nonneg (not_lt.mp ht)]
    calc _ ≤ K * √(dist (separatrixArc t) (0, -π)) := hbound k _ _
         _ ≤ K * √(2 * exp (-t)) := by gcongr; exact dist_arc_pos_le t
         _ = _ := by
           rw [sqrt_two_exp, show -t / 2 = -(1 / 2 : ℝ) * t by ring]
           ring

/-- The endpoint-subtracted squared value on each arc is absolutely integrable. -/
theorem ddArcValueRemainder_integrable {u : L2} (hu : MemSobolev 2 u) (k : Fin 4) :
    Integrable (ddArcValueRemainder u k) := by
  obtain ⟨K, hK, hbound⟩ := valueMass_holder hu
  have hm : Measurable (fun t ↦ valueMass u k (separatrixArc t)) :=
    ((valueMass_continuous u k).comp continuous_arc).measurable
  apply (integrable_exp_neg_half_abs.const_mul (K * √2)).mono'
  · change AEStronglyMeasurable (fun t ↦ valueMass u k (separatrixArc t) -
      if t < 0 then valueMass u k (π, 0) else valueMass u k (0, -π)) volume
    exact (hm.sub (measurable_const.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ by
      simpa only [Real.norm_eq_abs] using arc_remainder_bound hK hbound k t

private theorem quarter_integrable (u : L2) (k : Fin 4) (h : ℝ) :
    IntervalIntegrable (fun t ↦ valueMass u k (dipoleOrbit h t)) volume
      (-eighthPeriod h) (eighthPeriod h) := by
  have hc : Continuous (fun t ↦ dipoleOrbit h t) :=
    continuous_dipoleOrbit.comp (f := fun t : ℝ ↦ (h, t))
      (continuous_const.prodMk continuous_id)
  exact ((valueMass_continuous u k).comp hc).intervalIntegrable _ _

private theorem arc_integral_subtract {u : L2} (hu : MemSobolev 2 u) (k : Fin 4)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in (-L)..L, valueMass u k (separatrixArc t)) -
      L * (‖ddArcEnd u k false‖ ^ 2 + ‖ddArcEnd u k true‖ ^ 2) =
        ∫ t in (-L)..L, ddArcValueRemainder u k t := by
  let M := fun t ↦ valueMass u k (separatrixArc t)
  let cm := valueMass u k (π, 0)
  let cp := valueMass u k (0, -π)
  have hMc : Continuous M := (valueMass_continuous u k).comp continuous_arc
  have hR := ddArcValueRemainder_integrable hu k
  have hn : (∫ t in (-L)..0, ddArcValueRemainder u k t) =
      (∫ t in (-L)..0, M t) - L * cm := by
    calc _ = ∫ t in (-L)..0, M t - cm := by
           apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
           intro t ht
           change valueMass u k (separatrixArc t) -
             (if t < 0 then cm else cp) = M t - cm
           rw [ite_eq_left ht.2]
         _ = _ := by
           rw [intervalIntegral.integral_sub (hMc.intervalIntegrable _ _) intervalIntegrable_const,
             intervalIntegral.integral_const]
           simp only [smul_eq_mul]
           ring
  have hp : (∫ t in (0 : ℝ)..L, ddArcValueRemainder u k t) =
      (∫ t in (0 : ℝ)..L, M t) - L * cp := by
    calc _ = ∫ t in (0 : ℝ)..L, M t - cp := by
           apply intervalIntegral.integral_congr_Ioo_of_le hL
           intro t ht
           change valueMass u k (separatrixArc t) -
             (if t < 0 then cm else cp) = M t - cp
           rw [ite_eq_right (not_lt.mpr ht.1.le)]
         _ = _ := by
           rw [intervalIntegral.integral_sub (hMc.intervalIntegrable _ _) intervalIntegrable_const,
             intervalIntegral.integral_const]
           simp only [smul_eq_mul]
           ring
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hR.intervalIntegrable (a := -L) (b := 0)) (hR.intervalIntegrable (a := 0) (b := L))
  have hsM := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hMc.intervalIntegrable (-L) 0) (hMc.intervalIntegrable 0 L)
  rw [hn, hp] at hs
  change (∫ t in (-L)..L, M t) - L * (cm + cp) = _
  nlinarith [hsM]

private theorem value_comparison {u : L2} (hu : MemSobolev 2 u) :
    ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h ∈ Ioo 0 h₀, ∀ k : Fin 4, ∀ t, |t| ≤ eighthPeriod h →
        |valueMass u k (dipoleOrbit h t) - valueMass u k (separatrixArc t)| ≤
          C * h ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := valueMass_holder hu
  obtain ⟨Co, ho, hho, hclose⟩ := orbit_close_arc
  let D := max Co 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨K * √D, min ho 1, by positivity, lt_min hho zero_lt_one,
    min_le_right _ _, fun h hh k t ht ↦ ?_⟩
  have hd : dist (dipoleOrbit h t) (separatrixArc t) ≤ D * √h := by
    rw [dist_eq_norm]
    exact (hclose h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩ t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sqrt_nonneg _))
  calc _ ≤ K * √(dist (dipoleOrbit h t) (separatrixArc t)) := hbound k _ _
       _ ≤ K * √(D * √h) := by gcongr
       _ = K * √D * h ^ (1 / 4 : ℝ) := by
         rw [sqrt_eq_rpow, mul_rpow hD (sqrt_nonneg _), sqrt_eq_rpow,
           ← rpow_mul hh.1.le, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num,
           ← sqrt_eq_rpow]
         ring

private theorem quarter_error_bound {u : L2} {C h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (k : Fin 4) (hcomp : ∀ t, |t| ≤ eighthPeriod h →
      |valueMass u k (dipoleOrbit h t) - valueMass u k (separatrixArc t)| ≤
        C * h ^ (1 / 4 : ℝ)) :
    |(∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (dipoleOrbit h t)) -
      (∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (separatrixArc t))| ≤
        2 * C * (eighthPeriod h * h ^ (1 / 4 : ℝ)) := by
  have hL := (eighthPeriod_pos hh.1 hh.2).le
  have hiArc : IntervalIntegrable (fun t ↦ valueMass u k (separatrixArc t)) volume
      (-eighthPeriod h) (eighthPeriod h) :=
    ((valueMass_continuous u k).comp continuous_arc).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub (quarter_integrable u k h) hiArc]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -eighthPeriod h) (b := eighthPeriod h)
    (f := fun t ↦ valueMass u k (dipoleOrbit h t) - valueMass u k (separatrixArc t))
    (fun t ht ↦ by
      rw [Real.norm_eq_abs]
      apply hcomp
      rw [uIoc_of_le (by linarith)] at ht
      exact abs_le.mpr ⟨ht.1.le, ht.2⟩)
  rw [Real.norm_eq_abs] at hb
  refine hb.trans_eq ?_
  rw [show eighthPeriod h - -eighthPeriod h = 2 * eighthPeriod h by ring,
    abs_of_nonneg (by positivity)]
  ring

private theorem eighthPeriod_mul_quarterPower :
    Tendsto (fun h : ℝ ↦ eighthPeriod h * h ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun h : ℝ ↦ h ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuousAt_rpow_const 0 (1 / 4 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 4) (by norm_num)
  have hupper : Tendsto (fun h : ℝ ↦ (2 - (1 / 2) * log h) * h ^ (1 / 4 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have hh := (hp.const_mul 2).sub (hl.const_mul (1 / 2))
    simp only [mul_zero, sub_zero] at hh
    exact hh.congr fun h ↦ by ring
  apply squeeze_zero' _ _ hupper
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
    exact mul_nonneg (eighthPeriod_pos hh.1 (by linarith [hh.2])).le
      (rpow_nonneg hh.1.le _)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
    obtain ⟨-, hb⟩ := eighthPeriod_sub_log_bounds hh.1 hh.2
    rw [one_div, log_inv] at hb
    apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hh.1.le _)
    linarith

private theorem quarter_value_limit {u : L2} (hu : MemSobolev 2 u) (k : Fin 4) :
    Tendsto (fun h ↦
      (∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (dipoleOrbit h t)) -
        eighthPeriod h * (‖ddArcEnd u k false‖ ^ 2 + ‖ddArcEnd u k true‖ ^ 2))
      (𝓝[>] 0) (𝓝 (∫ t, ddArcValueRemainder u k t)) := by
  obtain ⟨C, h₀, hC, hh₀, hh₀1, hcomp⟩ := value_comparison hu
  have hE : Tendsto (fun h : ℝ ↦ 2 * C * (eighthPeriod h * h ^ (1 / 4 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using eighthPeriod_mul_quarterPower.const_mul (2 * C)
  have herr : Tendsto (fun h ↦
      (∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (dipoleOrbit h t)) -
        (∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (separatrixArc t)))
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hE
    filter_upwards [Ioo_mem_nhdsGT hh₀] with h hh
    simpa only [Real.norm_eq_abs] using quarter_error_bound ⟨hh.1, hh.2.trans_le hh₀1⟩
      k (hcomp h hh k)
  have hRlim := intervalIntegral_tendsto_integral (ddArcValueRemainder_integrable hu k)
    (tendsto_neg_atTop_atBot.comp tendsto_eighthPeriod_atTop) tendsto_eighthPeriod_atTop
  have hsum := herr.add hRlim
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
  simp only [Function.comp_apply]
  rw [← arc_integral_subtract hu k (eighthPeriod_pos hh.1 hh.2).le]
  ring

private theorem level_value_remainder_limit {u : L2} (hu : MemSobolev 2 u) :
    Tendsto (fun h ↦ levelIntegral h (fun p ↦ ‖continuousRep u (torusProj p)‖ ^ 2) -
      2 * eighthPeriod h * ddCornerMass u) (𝓝[>] 0)
      (𝓝 (∑ k : Fin 4, ∫ t, ddArcValueRemainder u k t)) := by
  have hsum : Tendsto (fun h ↦ ∑ k : Fin 4,
      ((∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (dipoleOrbit h t)) -
        eighthPeriod h * (‖ddArcEnd u k false‖ ^ 2 + ‖ddArcEnd u k true‖ ^ 2)))
      (𝓝[>] 0) (𝓝 (∑ k : Fin 4, ∫ t, ddArcValueRemainder u k t)) := by
    apply tendsto_finsetSum
    exact fun k _ ↦ quarter_value_limit hu k
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with h hh
  rw [levelIntegral_eq_sum_quarter' hh.1 hh.2
    (fun k hk ↦ quarter_integrable u ⟨k, hk⟩ h), ← Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin 4,
    ((∫ t in (-eighthPeriod h)..eighthPeriod h, valueMass u k (dipoleOrbit h t)) -
      eighthPeriod h * (‖ddArcEnd u k false‖ ^ 2 + ‖ddArcEnd u k true‖ ^ 2))) =
    (∑ k : Fin 4, ∫ t in (-eighthPeriod h)..eighthPeriod h,
      valueMass u k (dipoleOrbit h t)) - 2 * eighthPeriod h * ddCornerMass u
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold ddCornerMass
  ring

private theorem quarter_length_finite_part :
    Tendsto (fun ε : ℝ ↦ 2 * eighthPeriod (ε / 2) - log (1 / ε))
      (𝓝[>] 0) (𝓝 (log 8)) := by
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hscale : Tendsto (fun ε : ℝ ↦ ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hid.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change (0 : ℝ) < ε / 2
      exact div_pos hε (by norm_num)
  have hlim := ((orbitPeriod_leading_asymptotic.comp hscale).div_const 4).add_const (log 8)
  simp only [zero_div, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def, orbitPeriod]
  rw [show (4 : ℝ) / (ε / 2) = 8 / ε by ring,
    log_div (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hε), one_div, log_inv]
  ring

/-- The scalar value finite part and absolute integrability of its renormalized arc terms. -/
theorem dd_value_finite_part {φ : L2} (hφ : MemSobolev 2 φ) :
    (∀ k : Fin 4, Integrable (ddArcValueRemainder φ k)) ∧
      Tendsto (fun ε ↦ ddLevelMass φ ε - ddCornerMass φ * Real.log (1 / ε))
        (𝓝[>] 0) (𝓝 (ddValueFinitePart φ)) := by
  refine ⟨ddArcValueRemainder_integrable hφ, ?_⟩
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hscale : Tendsto (fun ε : ℝ ↦ ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hid.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change (0 : ℝ) < ε / 2
      exact div_pos hε (by norm_num)
  have hlim := ((level_value_remainder_limit hφ).comp hscale).add
    (quarter_length_finite_part.mul_const (ddCornerMass φ))
  change Tendsto _ _ (𝓝 (ddValueFinitePart φ)) at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun ε ↦ by
    dsimp only [Function.comp_def, ddLevelMass]
    ring

end NoEmbeddedEigenvalues
