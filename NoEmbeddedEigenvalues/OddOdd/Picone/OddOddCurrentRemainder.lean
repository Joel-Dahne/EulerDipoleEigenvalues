module

public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddPiconeIntegrability

/-!
# The integrated current remainder

The outward Picone current differs from `-(8/3)(1-B)` by a uniformly
linear stream-level error. The logarithmic period bound then gives the
full-level limit, using only bounded continuous values.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

private def boundarySlope (r : ℝ) : ℝ :=
  1 / 16 - r * (2 * Real.log (r / 2) + 1) / 256

private theorem ground_normal_formula {p : ℝ × ℝ}
    (hr : gradSq dipoleLift p ≠ 0) :
    partialX dipoleLift p * partialX ddGround p +
      partialY dipoleLift p * partialY ddGround p =
    dipoleLift p * (gradSq dipoleLift p / 8 +
      (4 - dipoleLift p ^ 2 - 3 * gradSq dipoleLift p) *
        boundarySlope (gradSq dipoleLift p)) := by
  let r := gradSq dipoleLift p
  let c := r * (2 * Real.log (r / 2) + 1) / 128
  have hx : partialX ddGround p =
      -Real.sin p.1 * Real.cos p.2 / 8 - c * Real.sin p.1 * Real.cos p.1 :=
    partialX_ddGround hr
  have hy : partialY ddGround p =
      -Real.sin p.2 * Real.cos p.1 / 8 - c * Real.sin p.2 * Real.cos p.2 :=
    partialY_ddGround hr
  have hx' : partialX ddGround p = dipoleLift p / 8 * partialX dipoleLift p +
      boundarySlope r * partialX (gradSq dipoleLift) p := by
    rw [hx, partialX_dipoleLift, partialX_gradSq_dipoleLift]
    dsimp [c, boundarySlope, dipoleLift]
    ring
  have hy' : partialY ddGround p = dipoleLift p / 8 * partialY dipoleLift p +
      boundarySlope r * partialY (gradSq dipoleLift) p := by
    rw [hy, partialY_dipoleLift, partialY_gradSq_dipoleLift]
    dsimp [c, boundarySlope, dipoleLift]
    ring
  rw [hx', hy']
  calc
    _ = dipoleLift p / 8 * gradSq dipoleLift p +
        boundarySlope r * gradDot dipoleLift (gradSq dipoleLift) p := by
      simp only [gradSq, gradDot]
      ring
    _ = _ := by rw [gradDot_dipoleLift_gradSq]; ring

private theorem boundary_ground_ge_one {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    1 ≤ ddBoundaryGround r := by
  have hl : Real.log (r / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  unfold ddBoundaryGround
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hl]

private theorem abs_boundarySlope_le {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    |boundarySlope r| ≤ 1 := by
  have hl := (Real.abs_log_mul_self_lt (r / 2) (by positivity) (by linarith)).le
  have hb : |r * Real.log (r / 2)| ≤ 2 := by
    have he : r * Real.log (r / 2) = 2 * (Real.log (r / 2) * (r / 2)) := by ring
    rw [he, abs_mul]
    norm_num only at *
    linarith
  have ht : |r * (2 * Real.log (r / 2) + 1)| ≤ 6 := by
    calc
      _ = |2 * (r * Real.log (r / 2)) + r| := by congr 1; ring
      _ ≤ |2 * (r * Real.log (r / 2))| + |r| := abs_add_le _ _
      _ ≤ 6 := by rw [abs_mul, abs_of_pos hr]; norm_num only; linarith
  calc
    _ ≤ |(1 / 16 : ℝ)| + |r * (2 * Real.log (r / 2) + 1) / 256| := abs_sub _ _
    _ ≤ 1 := by simp only [abs_div]; norm_num only; linarith

private theorem boundaryB_slope {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (8 / 3 : ℝ) * (1 - ddBoundaryB r) =
      (32 / 3 : ℝ) * (r / 8 + (4 - 3 * r) * boundarySlope r) / ddBoundaryGround r := by
  have hw := boundary_ground_ge_one hr hr2
  unfold ddBoundaryB boundarySlope
  field_simp [show ddBoundaryGround r ≠ 0 by linarith]
  unfold ddBoundaryGround
  ring

private theorem scalar_current_error {s r d v : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hsr : s ≤ r)
    (hd : |d| ≤ 1) (hv : 1 ≤ v) (hq : |r / 8 + (4 - 3 * r) * d| ≤ 5) :
    |-(2 * s ^ 3 / 3 + 32 / 3 - s ^ 2 * (8 - s ^ 3) / (3 * r)) *
        (r / 8 + (4 - 3 * r) * d - s ^ 2 * d) / (v + s ^ 2 / 16) +
      (32 / 3 : ℝ) * (r / 8 + (4 - 3 * r) * d) / v| ≤ 64 * s := by
  let a := 2 * s ^ 3 / 3 + 32 / 3 - s ^ 2 * (8 - s ^ 3) / (3 * r)
  let q := r / 8 + (4 - 3 * r) * d
  let w := v + s ^ 2 / 16
  have hr : 0 < r := hs.trans_le hsr
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hs3 : s ^ 3 ≤ s := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs2)]
  have hs3' : s ^ 3 ≤ 1 := hs3.trans hs1
  have h8 : 0 ≤ 8 - s ^ 3 := by linarith
  have hq' : |q| ≤ 5 := hq
  have hfrac : 0 ≤ s ^ 2 * (8 - s ^ 3) / (3 * r) := by positivity
  have hfrac' : s ^ 2 * (8 - s ^ 3) / (3 * r) ≤ 8 * s / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * r)).mpr
    calc
      _ ≤ s ^ 2 * 8 :=
        mul_le_mul_of_nonneg_left (by linarith [pow_nonneg hs.le 3]) (sq_nonneg s)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsr hs.le]
  have hδ : |a - 32 / 3| ≤ 4 * s := by
    apply abs_le.mpr
    dsimp [a]
    constructor <;> nlinarith [pow_nonneg hs.le 3]
  have ha : |a| ≤ 16 := by
    have ht : |a| ≤ |a - 32 / 3| + |(32 / 3 : ℝ)| := by
      calc
        _ = |(a - 32 / 3) + 32 / 3| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    norm_num at ht
    linarith
  have hw : 1 ≤ w := by dsimp [w]; nlinarith [sq_nonneg s]
  have hwp : 0 < w := by linarith
  have hvp : 0 < v := by linarith
  have hprod : 1 ≤ w * v := by nlinarith
  have he : -a * (q - s ^ 2 * d) / w + (32 / 3 : ℝ) * q / v =
      -(a - 32 / 3) * q / w + a * s ^ 2 * d / w +
        (32 / 3 : ℝ) * q * (s ^ 2 / 16) / (w * v) := by
    dsimp [w]
    field_simp
    ring
  change |-a * (q - s ^ 2 * d) / w + (32 / 3 : ℝ) * q / v| ≤ _
  rw [he]
  calc
    _ ≤ |-(a - 32 / 3) * q / w + a * s ^ 2 * d / w| +
        |(32 / 3 : ℝ) * q * (s ^ 2 / 16) / (w * v)| := abs_add_le _ _
    _ ≤ (|-(a - 32 / 3) * q / w| + |a * s ^ 2 * d / w|) +
        |(32 / 3 : ℝ) * q * (s ^ 2 / 16) / (w * v)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (4 * s * 5 + 16 * s ^ 2 * 1) + (32 / 3 : ℝ) * 5 * (s ^ 2 / 16) := by
      apply add_le_add
      · apply add_le_add
        · rw [abs_div, abs_mul, abs_neg, abs_of_pos hwp]
          exact (div_le_self (by positivity) hw).trans
            (mul_le_mul hδ hq (abs_nonneg _) (by positivity))
        · rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos hs, abs_of_pos hwp]
          apply (div_le_self (by positivity) hw).trans
          gcongr
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (mul_pos hwp hvp),
          abs_of_nonneg (by positivity : 0 ≤ s ^ 2 / 16)]
        norm_num only
        apply (div_le_self (by positivity) hprod).trans
        gcongr
        linarith [hq']
    _ ≤ _ := by nlinarith

private theorem current_coefficient_error {p : ℝ × ℝ}
    (hs : 0 < dipoleLift p) (hs1 : dipoleLift p ≤ 1) :
    |ddGroundCurrentCoeff p + (8 / 3 : ℝ) * (1 - ddBoundaryB (gradSq dipoleLift p))| ≤
      64 * dipoleLift p := by
  let s := dipoleLift p
  let r := gradSq dipoleLift p
  let d := boundarySlope r
  have hr : 0 < r := gradSq_dipoleLift_pos hs (by linarith)
  have hr2 : r ≤ 2 := by
    dsimp [r]
    rw [gradSq_dipoleLift]
    nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
  have hsr : s ≤ r := by
    have h := dipoleLift_mul_le_gradSq p
    change s * (2 - s) ≤ r at h
    nlinarith
  have hd : |d| ≤ 1 := abs_boundarySlope_le hr hr2
  have hv := boundary_ground_ge_one hr hr2
  have hq : |r / 8 + (4 - 3 * r) * d| ≤ 5 := by
    have hk : |4 - 3 * r| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      _ ≤ |r / 8| + |(4 - 3 * r) * d| := abs_add_le _ _
      _ ≤ r / 8 + 4 * 1 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ r / 8), abs_mul]
        exact add_le_add le_rfl (mul_le_mul hk hd (abs_nonneg _) (by norm_num))
      _ ≤ _ := by linarith
  have ha : s * ddA p = 2 * s ^ 3 / 3 + 32 / 3 - s ^ 2 * (8 - s ^ 3) / (3 * r) := by
    unfold ddA ddC
    change s * (2 * s ^ 2 / 3 + 32 / (3 * s) - s * (8 - s ^ 3) / (3 * r)) = _
    have hs' : s ≠ 0 := hs.ne'
    field_simp [hs', hr.ne']
  have hw : ddGround p = ddBoundaryGround r + s ^ 2 / 16 := by
    dsimp [ddGround, ddBoundaryGround, r, s]
    ring
  have hb : ddGroundCurrentCoeff p =
      -(2 * s ^ 3 / 3 + 32 / 3 - s ^ 2 * (8 - s ^ 3) / (3 * r)) *
        (r / 8 + (4 - 3 * r) * d - s ^ 2 * d) / (ddBoundaryGround r + s ^ 2 / 16) := by
    rw [ddGroundCurrentCoeff, ground_normal_formula hr.ne', hw]
    change -ddA p * (s * (r / 8 + (4 - s ^ 2 - 3 * r) * d)) / _ = _
    calc
      _ = -(s * ddA p) * (r / 8 + (4 - 3 * r) * d - s ^ 2 * d) /
          (ddBoundaryGround r + s ^ 2 / 16) := by ring
      _ = _ := by rw [ha]
  rw [hb, boundaryB_slope hr hr2]
  exact scalar_current_error hs hs1 hsr hd hv hq

private theorem continuousAt_boundaryB {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ContinuousAt ddBoundaryB r := by
  have hd : ddBoundaryGround r ≠ 0 := by linarith [boundary_ground_ge_one hr hr2]
  unfold ddBoundaryB
  apply ContinuousAt.div _ _ hd
  · fun_prop (disch := positivity)
  · unfold ddBoundaryGround
    fun_prop (disch := positivity)

private theorem integrated_current_error (φ : L2) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    |ddGroundCurrent φ ε + (8 / 3 : ℝ) * ddLevelMass φ ε -
      (8 / 3 : ℝ) * ddLevelBMass φ ε| ≤
      64 * ε * ‖continuousRep φ‖ ^ 2 * orbitPeriod (ε / 2) := by
  let V : ℝ → ℝ := fun t ↦ ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2
  let C : ℝ → ℝ := fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t)
  let B : ℝ → ℝ := fun t ↦ ddBoundaryB (gradSq dipoleLift (dipoleOrbit (ε / 2) t))
  have h0 : 0 < ε / 2 := by linarith [hε.1]
  have h1 : ε / 2 < 1 := by linarith [hε.2]
  have hs (t : ℝ) : dipoleLift (dipoleOrbit (ε / 2) t) = ε := by
    rw [dipoleLift_dipoleOrbit h0 h1 t]
    ring
  have ho : Continuous (fun t : ℝ ↦ dipoleOrbit (ε / 2) t) :=
    continuous_dipoleOrbit.comp (f := fun t : ℝ ↦ (ε / 2, t))
      (continuous_const.prodMk continuous_id)
  have hvc : Continuous V := (((continuousRep φ).continuous.comp
    (isOpenQuotientMap_torusProj.continuous.comp ho)).norm.pow 2)
  have hvi : IntervalIntegrable V volume 0 (orbitPeriod (ε / 2)) := hvc.intervalIntegrable _ _
  have hci : IntervalIntegrable (fun t ↦ C t * V t) volume 0 (orbitPeriod (ε / 2)) :=
    ddGroundCurrent_intervalIntegrable φ ⟨hε.1, by linarith [hε.2]⟩
  have hbc : Continuous B := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hr : 0 < gradSq dipoleLift (dipoleOrbit (ε / 2) t) :=
      gradSq_dipoleLift_pos (by rw [hs]; exact hε.1) (by rw [hs]; linarith [hε.2])
    have hr2 : gradSq dipoleLift (dipoleOrbit (ε / 2) t) ≤ 2 := by
      rw [gradSq_dipoleLift]
      nlinarith [Real.sin_sq_le_one (dipoleOrbit (ε / 2) t).1,
        Real.sin_sq_le_one (dipoleOrbit (ε / 2) t).2]
    exact (continuousAt_boundaryB hr hr2).comp
      (f := fun u : ℝ ↦ gradSq dipoleLift (dipoleOrbit (ε / 2) u))
      (((show Continuous (gradSq dipoleLift) by
        rw [gradSq_dipoleLift]; fun_prop).comp ho).continuousAt)
  have hbi : IntervalIntegrable (fun t ↦ B t * V t) volume 0 (orbitPeriod (ε / 2)) :=
    (hbc.mul hvc).intervalIntegrable _ _
  have heq : ddGroundCurrent φ ε + (8 / 3 : ℝ) * ddLevelMass φ ε -
      (8 / 3 : ℝ) * ddLevelBMass φ ε =
      ∫ t in (0 : ℝ)..orbitPeriod (ε / 2), (C t + (8 / 3 : ℝ) * (1 - B t)) * V t := by
    have hp : (fun t ↦ (C t + (8 / 3 : ℝ) * (1 - B t)) * V t) =
        (fun t ↦ C t * V t + (8 / 3 : ℝ) * V t - (8 / 3 : ℝ) * (B t * V t)) := by
      funext t
      ring
    rw [hp, intervalIntegral.integral_sub (hci.add (hvi.const_mul _)) (hbi.const_mul _),
      intervalIntegral.integral_add hci (hvi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := orbitPeriod (ε / 2)) (C := 64 * ε * ‖continuousRep φ‖ ^ 2)
    (f := fun t ↦ (C t + (8 / 3 : ℝ) * (1 - B t)) * V t) (fun t _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      have hc := current_coefficient_error
        (p := dipoleOrbit (ε / 2) t) (by rw [hs]; exact hε.1) (by rw [hs]; exact hε.2.le)
      rw [hs] at hc
      have hv : |V t| ≤ ‖continuousRep φ‖ ^ 2 := by
        dsimp [V]
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((continuousRep φ).norm_coe_le_norm _) 2
      exact mul_le_mul hc hv (abs_nonneg _)
        (mul_nonneg (by norm_num) hε.1.le))
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos (orbitPeriod_pos h0 h1)] using hb

/-- The error in replacing the actual current coefficient by `-(8/3)(1-B)` integrates
    to zero: the uniform `O(ε)` coefficient error times the logarithmic period vanishes. -/
theorem dd_current_remainder_limit {φ : L2} (_hφ : MemSobolev 2 φ) :
    Tendsto (fun ε ↦ ddGroundCurrent φ ε + (8 / 3 : ℝ) * ddLevelMass φ ε -
      (8 / 3 : ℝ) * ddLevelBMass φ ε) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun ε : ℝ ↦ ε * Real.log (1 / ε)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num)).neg
    simpa only [one_div, Real.log_inv, Real.rpow_one, neg_mul, mul_neg, mul_comm,
      neg_zero] using h
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have ht : Tendsto (fun ε : ℝ ↦ 64 * ‖continuousRep φ‖ ^ 2 *
      (4 * (ε * Real.log (1 / ε)) + (4 * Real.log 2 + 16) * ε)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hlog.const_mul 4).add (hid.const_mul (4 * Real.log 2 + 16))).const_mul
      (64 * ‖continuousRep φ‖ ^ 2)
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
  have hL := (eighthPeriod_sub_log_bounds (by linarith [hε.1] : 0 < ε / 2)
    (by linarith [hε.2] : ε / 2 < 1 / 2)).2
  have heq : Real.log (1 / (ε / 2)) = Real.log 2 + Real.log (1 / ε) := by
    rw [show 1 / (ε / 2) = 2 / ε by ring,
      Real.log_div (by norm_num) hε.1.ne', one_div, Real.log_inv]
    ring
  rw [heq] at hL
  have hT : orbitPeriod (ε / 2) ≤ 4 * Real.log (1 / ε) + 4 * Real.log 2 + 16 := by
    unfold orbitPeriod
    linarith
  rw [Real.norm_eq_abs]
  calc
    _ ≤ 64 * ε * ‖continuousRep φ‖ ^ 2 * orbitPeriod (ε / 2) := integrated_current_error φ hε
    _ ≤ 64 * ε * ‖continuousRep φ‖ ^ 2 *
        (4 * Real.log (1 / ε) + 4 * Real.log 2 + 16) :=
      mul_le_mul_of_nonneg_left hT
        (mul_nonneg (mul_nonneg (by norm_num) hε.1.le) (sq_nonneg _))
    _ = _ := by ring

end NoEmbeddedEigenvalues
