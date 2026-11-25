module

public import EulerDipoleEigenvalues.Mixed.PositiveComparisons.MixedRobinRectangle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cutoff current estimates for the mixed Robin comparison

On the right face the diagonal and shear both carry the factor
`h/(h+k)`. The shear cancels the cotangent singularity of the
odd-in-b ground function. A separated estimate uses the integrable
weight `1/√(cos b)`, including up to the top corner.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Set MeasureTheory Filter
open scoped Topology ContDiff

local notation "L" => (Real.pi / 2)

private theorem robin_quarter_cos {x : ℝ} (hx : x ∈ Ico 0 L) :
    0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩

private theorem robin_quarter_cos_nonneg {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ Real.cos x :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩

private theorem robin_abs_sin (x : ℝ) : |Real.sin x| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

private theorem robin_quarter_sin_nonneg {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ Real.sin x :=
  Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (hx.2.trans (half_le_self Real.pi_pos.le))

private theorem robin_ratio_data {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |partialX ρ p / ρ p| + |partialY ρ p / ρ p| ≤ C * (1 + |Real.log p.1|) := by
  obtain ⟨m, M, hm, hb⟩ := hρ.bounded
  obtain ⟨C, hC, hD⟩ := hρ.derivative_bound
  refine ⟨C / m, by positivity, fun p hp ↦ ?_⟩
  have hmp := (hb p ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩).1
  have hpos := hm.trans_le hmp
  rw [abs_div, abs_div, abs_of_pos hpos, ← add_div, div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) hm hmp).trans
    (div_le_div_of_nonneg_right (hD p hp) hm.le)

private theorem mixed_robin_degenerate_coefficients {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 L ×ˢ Icc 0 L) :
    let h := Real.cos q.1
    let k := Real.cos q.2
    let R := h / (h + k)
    0 ≤ R ∧ R ≤ 1 ∧
      |mixedComparisonDiagonal q| ≤ 4 * R ∧
      |mixedComparisonOffDiagonal q| ≤ 2 * R * Real.sin q.2 := by
  dsimp only
  let h := Real.cos q.1
  let k := Real.cos q.2
  let R := h / (h + k)
  have hh : 0 < h := robin_quarter_cos hq.1
  have hk : 0 ≤ k := robin_quarter_cos_nonneg hq.2
  have hh₁ : h ≤ 1 := Real.cos_le_one _
  have hk₁ : k ≤ 1 := Real.cos_le_one _
  have hs := add_pos_of_pos_of_nonneg hh hk
  have hR : 0 ≤ R := (div_pos hh hs).le
  have hR₁ : R ≤ 1 := (div_le_one hs).mpr (le_add_of_nonneg_right hk)
  have hh₂ : h ^ 2 ≤ 1 := pow_le_one₀ hh.le hh₁
  have hv : 0 ≤ Real.sin q.2 := robin_quarter_sin_nonneg hq.2
  refine ⟨hR, hR₁, ?_, ?_⟩
  · change |h ^ 2 + 2 * h * (1 - h ^ 2) / (h + k)| ≤ 4 * R
    have he : h ^ 2 + 2 * h * (1 - h ^ 2) / (h + k) =
        R * (h * (h + k) + 2 * (1 - h ^ 2)) := by dsimp [R]; field_simp
    rw [he, abs_of_nonneg (by positivity)]
    rw [mul_comm 4 R]
    apply mul_le_mul_of_nonneg_left _ hR
    nlinarith only [sq_nonneg h, mul_le_mul hh₁ (show h + k ≤ 2 by linarith) hs.le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  · change |2 * h ^ 2 / (h + k) ^ 2 * Real.sin q.1 * Real.sin q.2| ≤ 2 * R * Real.sin q.2
    have he : 2 * h ^ 2 / (h + k) ^ 2 = 2 * R ^ 2 := by dsimp [R]; rw [div_pow, mul_div_assoc]
    rw [he, abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg (show 0 ≤ 2 * R ^ 2 by positivity)]
    apply mul_le_mul_of_nonneg_right _ hv
    exact (mul_le_of_le_one_right (by positivity) (robin_abs_sin _)).trans
      (mul_le_mul_of_nonneg_left (by simpa [pow_two] using
        (mul_le_of_le_one_right hR hR₁)) (by norm_num))

private theorem robin_right_envelope (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, a ∈ Ico (L / 2) L → b ∈ Ioo 0 L →
      ∀ z : ℝ × ℝ → ℂ,
      |mixedRobinCurrentA (mixedRobinComparison oddA ρ) z (a, b)| ≤
        C * (Real.cos a / (Real.cos a + Real.cos b)) *
          (1 + |Real.log (Real.cos a)|) * ‖z (a, b)‖ ^ 2 := by
  obtain ⟨C, hC, hD⟩ := robin_ratio_data hρ
  refine ⟨8 + 6 * C, by positivity, ?_⟩
  intro a b ha hb z
  let q : ℝ × ℝ := (a, b)
  let g := mixedRobinComparison oddA ρ
  let h := Real.cos a
  let k := Real.cos b
  let u := Real.sin a
  let v := Real.sin b
  let R := h / (h + k)
  let W := C * (1 + |Real.log h|)
  let X := partialX ρ (h, k) / ρ (h, k)
  let Y := partialY ρ (h, k) / ρ (h, k)
  have ha₀ : 0 < a := (half_pos (half_pos Real.pi_pos)).trans_le ha.1
  have hq : q ∈ Ico 0 L ×ˢ Icc 0 L :=
    ⟨⟨ha₀.le, ha.2⟩, Ioo_subset_Icc_self hb⟩
  have hh : 0 < h := robin_quarter_cos hq.1
  have hk : 0 ≤ k := robin_quarter_cos_nonneg hq.2
  have hk₁ : k ≤ 1 := Real.cos_le_one _
  have hv : 0 < v := Real.sin_pos_of_pos_of_lt_pi hb.1 (hb.2.trans (half_lt_self Real.pi_pos))
  have hu : 0 < u := Real.sin_pos_of_pos_of_lt_pi ha₀ (ha.2.trans (half_lt_self Real.pi_pos))
  have hv₁ : v ≤ 1 := Real.sin_le_one _
  have hu₁ : u ≤ 1 := Real.sin_le_one _
  have hU : (1 / 2 : ℝ) ≤ u := by
    have hs := Real.mul_le_sin ha₀.le ha.2.le
    have hp : 1 / 2 ≤ 2 / Real.pi * a := by
      have he : 1 / 2 = 2 / Real.pi * (L / 2) := by field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left ha.1 (by positivity)
    exact hp.trans hs
  have hX' : |X| + |Y| ≤ W := hD _ ⟨⟨hh, Real.cos_le_one _⟩, ⟨hk, hk₁⟩⟩
  have hX : |X| ≤ W := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hX'
  have hY : |Y| ≤ W := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hX'
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨hR, _, hd, hj⟩ := mixed_robin_degenerate_coefficients hq
  have hp : 0 < if oddA then q.1 else q.2 := by
    cases oddA
    · exact hb.1
    · exact ha₀
  obtain ⟨hx, hy⟩ := mixed_robin_ground_logPartials oddA hρ hq hp
  change |mixedRobinCurrentA g z q| ≤ _
  unfold mixedRobinCurrentA piconeCurrent₁ piconeGroundFlux₁
  rw [add_div, mul_div_assoc, mul_div_assoc, hx, hy, abs_mul,
    abs_of_nonneg (sq_nonneg ‖z q‖)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖z q‖)
  have hux : |u * X| ≤ W := by
    rw [abs_mul, abs_of_pos hu]
    exact (mul_le_of_le_one_left (abs_nonneg X) hu₁).trans hX
  have hvy : |v * Y| ≤ W := by
    rw [abs_mul, abs_of_pos hv]
    exact (mul_le_of_le_one_left (abs_nonneg Y) hv₁).trans hY
  have hkdiv : 0 ≤ k / v := div_nonneg hk hv.le
  have hhdiv : 0 ≤ h / u := div_nonneg hh.le hu.le
  have hcot : h / u ≤ 2 := (div_le_iff₀ hu).mpr (by linarith [Real.cos_le_one a])
  have hd' : |mixedComparisonDiagonal q| ≤ 4 * R := hd
  have hj' : |mixedComparisonOffDiagonal q| ≤ 2 * R * v := hj
  have hJ : 0 ≤ 2 * R * v := by positivity
  have hD' : 0 ≤ 4 * R := by positivity
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  change |mixedComparisonDiagonal q| * |(if oddA then h / u else 0) - u * X| +
    |mixedComparisonOffDiagonal q| * |(if oddA then 0 else k / v) - v * Y| ≤
    (8 + 6 * C) * R * (1 + |Real.log h|)
  have hrlog : R ≤ R * (1 + |Real.log h|) :=
    le_mul_of_one_le_right hR (le_add_of_nonneg_right (abs_nonneg _))
  cases oddA
  · simp only [Bool.false_eq_true, ite_false, zero_sub, abs_neg]
    have hV : |k / v - v * Y| ≤ k / v + W := by
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hkdiv]; exact add_le_add_right hvy _)
    have h₁ := mul_le_mul hd' hux (abs_nonneg _) hD'
    have h₂ := mul_le_mul hj' hV (abs_nonneg _) hJ
    have h₃ : 2 * R * v * (k / v + W) ≤ 2 * R * (1 + W) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [mul_add, ← mul_div_assoc, mul_comm v k, mul_div_cancel_right₀ _ hv.ne']
      linarith [mul_le_of_le_one_left hW hv₁]
    dsimp only [W] at *
    nlinarith only [h₁, h₂, h₃, hrlog, hR]
  · simp only [ite_true, zero_sub, abs_neg]
    have hU' : |h / u - u * X| ≤ 2 + W :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg hhdiv]; exact add_le_add hcot hux)
    have h₁ := mul_le_mul hd' hU' (abs_nonneg _) hD'
    have h₂ := mul_le_mul hj' hvy (abs_nonneg _) hJ
    have h₃ : 2 * R * v * W ≤ 2 * R * W := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hW hv₁) (by positivity)
    dsimp only [W] at *
    nlinarith only [h₁, h₂, h₃, hrlog]

private theorem mixed_robin_invSqrtCos_integrable :
    IntegrableOn (fun b : ℝ ↦ (Real.sqrt (Real.cos b))⁻¹) (Ioo 0 L) := by
  have hpow : IntervalIntegrable (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) volume 0 L :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrev : IntervalIntegrable (fun b : ℝ ↦ (L - b) ^ (-(1 / 2 : ℝ))) volume 0 L := by
    simpa only [sub_self, sub_zero] using (hpow.comp_sub_left L).symm
  have hc : 0 < 2 / Real.pi := by positivity
  apply ((hrev.1.mono_set Ioo_subset_Ioc_self).const_mul ((2 / Real.pi) ^ (-(1 / 2 : ℝ)))).mono'
    (by
      have hm : Measurable (fun b : ℝ ↦ (Real.sqrt (Real.cos b))⁻¹) := by
        exact (Real.continuous_sqrt.comp Real.continuous_cos).measurable.inv
      exact hm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
  have hcos : 0 < Real.cos b := robin_quarter_cos ⟨hb.1.le, hb.2⟩
  have hd : 0 < L - b := sub_pos.mpr hb.2
  have hs := Real.mul_le_sin hd.le (by linarith [hb.1])
  rw [Real.sin_pi_div_two_sub] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_neg hcos.le,
    ← Real.mul_rpow hc.le hd.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hd) hs (by norm_num)

private theorem robin_ratio_le_sqrt {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    h / (h + k) ≤ Real.sqrt h * (Real.sqrt k)⁻¹ := by
  have hu := Real.sqrt_pos.mpr hh
  have hv := Real.sqrt_pos.mpr hk
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (add_pos hh hk) hv).mpr
  have hmul : Real.sqrt h * Real.sqrt k ≤ h + k := by
    nlinarith only [sq_nonneg (Real.sqrt h - Real.sqrt k), Real.sq_sqrt hh.le,
      Real.sq_sqrt hk.le, mul_nonneg hu.le hv.le]
  simpa only [← mul_assoc, ← pow_two, Real.sq_sqrt hh.le] using
    mul_le_mul_of_nonneg_left hmul hu.le

/-- Right-face current tends to zero uniformly over the lower integration
endpoint. The estimate includes the corner $b=π/2$. -/
theorem mixed_robin_right_current_bound (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 1 z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Ico (L / 2) L, ∀ b₀ ∈ Ico 0 L,
      |∫ b in Ioo b₀ L, mixedRobinCurrentA (mixedRobinComparison oddA ρ) z (a, b)| ≤
        K * (Real.sqrt (Real.cos a) * (1 + |Real.log (Real.cos a)|)) := by
  obtain ⟨C, hC, hJ⟩ := robin_right_envelope oddA hρ
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L)).exists_bound_of_continuousOn
      hz.continuous.continuousOn
  let w : ℝ → ℝ := fun b ↦ (Real.sqrt (Real.cos b))⁻¹
  have hw : ∀ b, 0 ≤ w b := fun b ↦ inv_nonneg.mpr (Real.sqrt_nonneg _)
  let K := C * (max M 0) ^ 2 * (∫ b in Ioo (0 : ℝ) L, w b)
  refine ⟨K, mul_nonneg (by positivity) (integral_nonneg hw), fun a ha b₀ hb₀ ↦ ?_⟩
  let J : ℝ → ℝ := fun b ↦ mixedRobinCurrentA (mixedRobinComparison oddA ρ) z (a, b)
  let h := Real.cos a
  let r := Real.sqrt h * (1 + |Real.log h|)
  let S := Ioo b₀ L
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ha₀ : 0 < a := (half_pos (half_pos Real.pi_pos)).trans_le ha.1
  have hh : 0 < h := robin_quarter_cos ⟨ha₀.le, ha.2⟩
  have hsub : S ⊆ Ioo 0 L := fun _ hb ↦ ⟨hb₀.1.trans_lt hb.1, hb.2⟩
  let B := C * (max M 0) ^ 2 * r
  have hbnd : ∀ b ∈ S, |J b| ≤ B * w b := by
    intro b hb
    have hb' := hsub hb
    have hk : 0 < Real.cos b := robin_quarter_cos ⟨hb'.1.le, hb'.2⟩
    have hm' := hM (a, b) ⟨⟨ha₀.le, ha.2.le⟩, Ioo_subset_Icc_self hb'⟩
    have hm := pow_le_pow_left₀ (norm_nonneg _) (hm'.trans (le_max_left M 0)) 2
    calc
      _ ≤ C * (h / (h + Real.cos b)) * (1 + |Real.log h|) * ‖z (a, b)‖ ^ 2 :=
        hJ ha hb' z
      _ ≤ C * (Real.sqrt h * w b) * (1 + |Real.log h|) * (max M 0) ^ 2 := by
        gcongr
        exact robin_ratio_le_sqrt hh hk
      _ = _ := by dsimp [B, r]; ring
  have hcont : ContinuousOn J S := fun b hb ↦ by
    have hb' := hsub hb
    have hp : 0 < if oddA then (a, b).1 else (a, b).2 := by
      cases oddA
      · exact hb'.1
      · exact ha₀
    exact (((mixed_robin_current_contDiffAt oddA hρ hz
      ⟨⟨ha₀.le, ha.2⟩, Ioo_subset_Icc_self hb'⟩ hp).1.continuousAt).comp
        (show ContinuousAt (fun t : ℝ ↦ (a, t)) b by fun_prop)).continuousWithinAt
  have hW : IntegrableOn w (Ioo 0 L) := mixed_robin_invSqrtCos_integrable
  have hi := hW.mono_set hsub
  calc
    _ ≤ ∫ b in S, |J b| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm J
    _ ≤ ∫ b in S, B * w b := by
      have hiB := hi.const_mul B
      have hm := hcont.abs.aestronglyMeasurable (μ := volume) measurableSet_Ioo
      have hiJ := hiB.mono' hm ((ae_restrict_mem measurableSet_Ioo).mono
        (fun b hb ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hbnd b hb))
      exact setIntegral_mono_on hiJ hiB measurableSet_Ioo hbnd
    _ = B * ∫ b in S, w b := integral_const_mul B w
    _ ≤ K * r := by
      have hwle := setIntegral_mono_set hW (Eventually.of_forall hw)
        (Eventually.of_forall hsub)
      have hBB : 0 ≤ B := by dsimp [B]; positivity
      calc
        _ ≤ B * ∫ b in Ioo (0 : ℝ) L, w b := mul_le_mul_of_nonneg_left hwle hBB
        _ = _ := by dsimp [B, K]; ring

private theorem mixed_robin_odd_density_bound (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {A : ℝ} (hA : A ∈ Ioo 0 L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Icc 0 A ×ˢ Icc 0 L,
      ∀ z : ℝ × ℝ → ℂ, ∀ t : ℝ, t = (if oddA then q.1 else q.2) → 0 < t →
        (if oddA then |mixedRobinCurrentA (mixedRobinComparison oddA ρ) z q|
         else |mixedRobinCurrentB (mixedRobinComparison oddA ρ) z q|) ≤
          4 * (L / t + K) * ‖z q‖ ^ 2 := by
  obtain ⟨C, hC, hD⟩ := robin_ratio_data hρ
  let K := C * (1 + |Real.log (Real.cos A)|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun q hq z t ht ht₀ ↦ ?_⟩
  let g := mixedRobinComparison oddA ρ
  let p := (Real.cos q.1, Real.cos q.2)
  have hq' : q ∈ Ico 0 L ×ˢ Icc 0 L := ⟨⟨hq.1.1, hq.1.2.trans_lt hA.2⟩, hq.2⟩
  have hh : 0 < p.1 := robin_quarter_cos hq'.1
  have hcA : 0 < Real.cos A := robin_quarter_cos ⟨hA.1.le, hA.2⟩
  have hcs : Real.cos A ≤ p.1 :=
    Real.cos_le_cos_of_nonneg_of_le_pi hq.1.1 (hA.2.trans (half_lt_self Real.pi_pos)).le hq.1.2
  have hlog : |Real.log p.1| ≤ |Real.log (Real.cos A)| := by
    rw [abs_of_nonpos (Real.log_nonpos hh.le (Real.cos_le_one _)),
      abs_of_nonpos (Real.log_nonpos hcA.le (Real.cos_le_one _))]
    exact neg_le_neg (Real.log_le_log hcA hcs)
  have hs : |partialX ρ p / ρ p| + |partialY ρ p / ρ p| ≤ K :=
    (hD p ⟨⟨hh, Real.cos_le_one _⟩, ⟨robin_quarter_cos_nonneg hq.2, Real.cos_le_one _⟩⟩).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) hC)
  have hp : 0 < if oddA then q.1 else q.2 := ht ▸ ht₀
  have htL : t ≤ L := by
    rw [ht]
    cases oddA
    · exact hq.2.2
    · exact hq.1.2.trans hA.2.le
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht₀
    (htL.trans_lt (half_lt_self Real.pi_pos))
  have hcot : |Real.cos t / Real.sin t| ≤ L / t := by
    rw [abs_of_nonneg (div_nonneg (robin_quarter_cos_nonneg ⟨ht₀.le, htL⟩) hsin.le)]
    apply (div_le_div_iff₀ hsin ht₀).mpr
    have hj := mul_le_mul_of_nonneg_left (Real.mul_le_sin ht₀.le htL) (half_pos Real.pi_pos).le
    have he : L * (2 / Real.pi * t) = t := by field_simp
    rw [he] at hj
    exact (mul_le_of_le_one_left ht₀.le (Real.cos_le_one _)).trans hj
  have hnorm (a x : ℝ) : |Real.sin a * x| ≤ |x| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (robin_abs_sin _)
  obtain ⟨hx, hy⟩ := mixed_robin_ground_logPartials oddA hρ hq' hp
  have hab : |partialX g q / g q| + |partialY g q / g q| ≤ L / t + K := by
    rw [hx, hy]
    cases oddA
    · simp only [Bool.false_eq_true, ite_false, zero_sub, abs_neg]
      change |Real.sin q.1 * (partialX ρ p / ρ p)| +
        |Real.cos q.2 / Real.sin q.2 - Real.sin q.2 * (partialY ρ p / ρ p)| ≤ _
      rw [show q.2 = t from ht.symm]
      linarith only [hs, hcot, hnorm q.1 (partialX ρ p / ρ p),
        hnorm t (partialY ρ p / ρ p), abs_sub (Real.cos t / Real.sin t)
          (Real.sin t * (partialY ρ p / ρ p))]
    · simp only [ite_true, zero_sub, abs_neg]
      change |Real.cos q.1 / Real.sin q.1 - Real.sin q.1 * (partialX ρ p / ρ p)| +
        |Real.sin q.2 * (partialY ρ p / ρ p)| ≤ _
      rw [show q.1 = t from ht.symm]
      linarith only [hs, hcot, hnorm t (partialX ρ p / ρ p),
        hnorm q.2 (partialY ρ p / ρ p), abs_sub (Real.cos t / Real.sin t)
          (Real.sin t * (partialX ρ p / ρ p))]
  obtain ⟨hR, hR₁, hd, hj⟩ := mixed_robin_degenerate_coefficients hq'
  have hd' : |mixedComparisonDiagonal q| ≤ 4 :=
    hd.trans (by linarith)
  have hj' : |mixedComparisonOffDiagonal q| ≤ 4 :=
    hj.trans ((mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)).trans (by linarith))
  have hcombine {d j} (hd : |d| ≤ (4 : ℝ)) (hj : |j| ≤ (4 : ℝ)) :
      |d * (partialX g q / g q) + j * (partialY g q / g q)| ≤ 4 * (L / t + K) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    refine (add_le_add (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hj (abs_nonneg _))).trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hab (by norm_num)
  cases oddA
  · simp only [Bool.false_eq_true, ite_false]
    unfold mixedRobinCurrentB piconeCurrent₂ piconeGroundFlux₂
    rw [add_div, mul_div_assoc, mul_div_assoc, abs_mul, abs_of_nonneg (sq_nonneg ‖z q‖)]
    exact mul_le_mul_of_nonneg_right (hcombine hj' hd') (sq_nonneg _)
  · simp only [ite_true]
    unfold mixedRobinCurrentA piconeCurrent₁ piconeGroundFlux₁
    rw [add_div, mul_div_assoc, mul_div_assoc, abs_mul, abs_of_nonneg (sq_nonneg ‖z q‖)]
    exact mul_le_mul_of_nonneg_right (hcombine hd' hj') (sq_nonneg _)

/-- At fixed right endpoint, the odd-face current is of order at most the
distance to the axis. The test function vanishes linearly there. -/
theorem mixed_robin_odd_current_bound (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 1 z)
    (hzero : ∀ t ∈ Icc 0 L, (if oddA then z (0, t) else z (t, 0)) = 0)
    {A : ℝ} (hA : A ∈ Ioo 0 L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ ∈ Ioo 0 A,
      (if oddA then
        |∫ b in Ioo 0 L, mixedRobinCurrentA (mixedRobinComparison true ρ) z (δ, b)|
       else |∫ a in Ioo 0 A, mixedRobinCurrentB (mixedRobinComparison false ρ) z (a, δ)|) ≤
        M * δ := by
  obtain ⟨K, hK, hb⟩ := mixed_robin_odd_density_bound oddA hρ hA
  let S := Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨N, hN⟩ := hS.exists_bound_of_continuousOn
    (hz.continuous_fderiv one_ne_zero).continuousOn
  let B := max N 0
  have hB : 0 ≤ B := le_max_right _ _
  have hL := half_pos Real.pi_pos
  have hLip (p q : ℝ × ℝ) (hp : p ∈ S) (hq : q ∈ S) :
      ‖z q - z p‖ ≤ B * ‖q - p‖ :=
    ((convex_Icc 0 L).prod (convex_Icc 0 L)).norm_image_sub_le_of_norm_fderiv_le
      (fun _ _ ↦ hz.differentiable one_ne_zero _) (fun x hx ↦ (hN x hx).trans (le_max_left N 0))
      hp hq
  let M := 4 * B ^ 2 * (L + K * L)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * L, mul_nonneg hM hL.le, fun δ hδ ↦ ?_⟩
  have hdL := hδ.2.trans hA.2
  have hd₀ := hδ.1.le
  have hZ (q : ℝ × ℝ) (hq : q ∈ Icc 0 A ×ˢ Icc 0 L)
      (he : δ = (if oddA then q.1 else q.2)) : ‖z q‖ ≤ B * δ := by
    have hqS : q ∈ S := ⟨⟨hq.1.1, hq.1.2.trans hA.2.le⟩, hq.2⟩
    cases oddA
    · have hp : (q.1, 0) ∈ S := ⟨hqS.1, ⟨le_rfl, hL.le⟩⟩
      have hz' : z (q.1, 0) = 0 := hzero _ hqS.1
      have hn : ‖q - (q.1, 0)‖ = δ := by
        simp [Prod.norm_def, Real.norm_eq_abs, ← show δ = q.2 from he, abs_of_pos hδ.1, hd₀]
      simpa only [hz', sub_zero, hn] using hLip _ _ hp hqS
    · have hp : (0, q.2) ∈ S := ⟨⟨le_rfl, hL.le⟩, hqS.2⟩
      have hz' : z (0, q.2) = 0 := hzero _ hqS.2
      have hn : ‖q - (0, q.2)‖ = δ := by
        simp [Prod.norm_def, Real.norm_eq_abs, ← show δ = q.1 from he, abs_of_pos hδ.1, hd₀]
      simpa only [hz', sub_zero, hn] using hLip _ _ hp hqS
  have hpoint (q : ℝ × ℝ) (hq : q ∈ Icc 0 A ×ˢ Icc 0 L)
      (he : δ = (if oddA then q.1 else q.2)) :
      (if oddA then |mixedRobinCurrentA (mixedRobinComparison oddA ρ) z q|
       else |mixedRobinCurrentB (mixedRobinComparison oddA ρ) z q|) ≤ M * δ := by
    refine (hb q hq z δ he hδ.1).trans ?_
    calc
      _ ≤ 4 * (L / δ + K) * (B * δ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hZ q hq he) 2) (by positivity)
      _ = 4 * B ^ 2 * (L + K * δ) * δ := by field_simp [hδ.1.ne']
      _ ≤ M * δ := by dsimp [M]; gcongr
  have hint {J : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ L)
      (hJ : ∀ t ∈ Ioo 0 d, |J t| ≤ M * δ) :
      |∫ t in Ioo 0 d, J t| ≤ M * L * δ := by
    have hfin : volume (Ioo (0 : ℝ) d) < ⊤ := measure_Ioo_lt_top
    have h := norm_setIntegral_le_of_norm_le_const hfin
      (fun t ht ↦ (show ‖J t‖ ≤ M * δ from hJ t ht))
    rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hd] at h
    exact h.trans (by nlinarith [mul_nonneg (mul_nonneg hM hδ.1.le) (sub_nonneg.mpr hd')])
  cases oddA
  · exact hint hA.1.le hA.2.le (fun t ht ↦ hpoint (t, δ)
      ⟨Ioo_subset_Icc_self ht, ⟨hδ.1.le, hdL.le⟩⟩ rfl)
  · exact hint hL.le le_rfl (fun t ht ↦ hpoint (δ, t)
      ⟨Ioo_subset_Icc_self hδ, Ioo_subset_Icc_self ht⟩ rfl)

private theorem robin_integral_exhaustion {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s : Set X} (hs : MeasurableSet s) {f : X → ℝ} (hf : IntegrableOn f s μ)
    {l : Filter ℝ} [l.IsCountablyGenerated] {R : ℝ → Set X}
    (hm : ∀ t, MeasurableSet (R t)) (hsub : ∀ᶠ t in l, R t ⊆ s)
    (hex : ∀ x ∈ s, ∀ᶠ t in l, x ∈ R t) :
    Tendsto (fun t ↦ ∫ x in R t, f x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ.restrict s)
    (F := fun t ↦ (R t).indicator f) (f := f) (fun x ↦ ‖f x‖)
    (Eventually.of_forall fun t ↦ hf.aestronglyMeasurable.indicator (hm t))
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ R t
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _)
    hf.norm (by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact tendsto_const_nhds.congr' ((hex x hx).mono fun t ht ↦ (indicator_of_mem ht _).symm))
  apply h.congr'
  filter_upwards [hsub] with t ht
  rw [setIntegral_indicator (hm t), inter_eq_right.mpr ht]

private theorem robin_quarter_smooth_integrable {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 2 z) :
    IntegrableOn (mixedRobinBulk z (partialX z) (partialY z)) mixedQuarterCell := by
  let K : Set (ℝ × ℝ) := Icc 0 L ×ˢ Icc 0 L
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hxc := (contDiff_partialX (n := 1) hz).continuous
  have hyc := (contDiff_partialY (n := 1) hz).continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hz.continuous.norm.add hxc.norm).add hyc.norm).continuousOn
  have hs : MeasurableSet mixedQuarterCell := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : mixedQuarterCell ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hfin : IsFiniteMeasure (volume.restrict mixedQuarterCell) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top
  have hR (q : ℝ × ℝ) (hq : q ∈ mixedQuarterCell) :
      q ∈ Ico 0 L ×ˢ Icc 0 L := ⟨⟨hq.1.1.le, hq.1.2⟩, (hsub hq).2⟩
  have hcont : ContinuousOn (mixedRobinBulk z (partialX z) (partialY z)) mixedQuarterCell := by
    intro q hq
    obtain ⟨hd, hj⟩ := mixed_robin_coefficients_contDiffAt (n := 1) (hR q hq)
    have hdc := hd.continuousAt
    have hjc := hj.continuousAt
    have hV := mixed_robin_potential_continuousAt (hR q hq) (Or.inl hq.1.1)
    have hx := hxc.continuousAt (x := q)
    have hy := hyc.continuousAt (x := q)
    have hzq := hz.continuous.continuousAt (x := q)
    apply ContinuousAt.continuousWithinAt
    unfold mixedRobinBulk
    fun_prop
  apply (integrable_const (μ := volume.restrict mixedQuarterCell) (16 * M ^ 2)).mono'
    (hcont.aestronglyMeasurable hs)
  filter_upwards [ae_restrict_mem hs] with q hq
  have hm := hM q (hsub hq)
  change ‖(‖z q‖ + ‖partialX z q‖) + ‖partialY z q‖‖ ≤ M at hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hm
  have hzM : ‖z q‖ ≤ M := by linarith [norm_nonneg (partialX z q), norm_nonneg (partialY z q)]
  have hxM : ‖partialX z q‖ ≤ M := by linarith [norm_nonneg (z q), norm_nonneg (partialY z q)]
  have hyM : ‖partialY z q‖ ≤ M := by linarith [norm_nonneg (z q), norm_nonneg (partialX z q)]
  have hq' : q ∈ mixedOpenCell := ⟨⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩,
    ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩⟩
  obtain ⟨hV, hV', _, hj⟩ := mixed_comparison_coefficient_bounds hq'
  obtain ⟨hR₀, hR₁, hd, _⟩ := mixed_robin_degenerate_coefficients (hR q hq)
  have hD : |mixedComparisonDiagonal q| ≤ 4 := hd.trans (by linarith)
  have hV₀ : |mixedComparisonPotential q| ≤ 4 := by rwa [abs_of_nonpos (by linarith)]
  have hxy := Complex.abs_re_le_norm (partialX z q * (starRingEnd ℂ) (partialY z q))
  rw [norm_mul, Complex.norm_conj] at hxy
  have hxy' := hxy.trans (mul_le_mul hxM hyM (norm_nonneg _) ((norm_nonneg _).trans hxM))
  rw [Real.norm_eq_abs, mixedRobinBulk]
  have ht : 16 * M ^ 2 = 12 * M ^ 2 + 4 * M ^ 2 := by ring
  rw [ht]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
  · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ ‖partialX z q‖ ^ 2 + ‖partialY z q‖ ^ 2),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh₁ := mul_le_mul hD
      (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hxM 2)
        (pow_le_pow_left₀ (norm_nonneg _) hyM 2)) (by positivity) (by norm_num)
    have hh₂ := mul_le_mul (mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2))
      hxy' (abs_nonneg _) (by norm_num)
    linarith only [hh₁, hh₂]
  · rw [abs_mul, abs_of_nonneg (sq_nonneg ‖z q‖)]
    exact mul_le_mul hV₀ (pow_le_pow_left₀ (norm_nonneg _) hzM 2) (by positivity) (by norm_num)

private theorem robin_sqrt_log_tendsto :
    Tendsto (fun a : ℝ ↦ Real.sqrt (Real.cos a) * (1 + |Real.log (Real.cos a)|))
      (𝓝[<] L) (𝓝 0) := by
  have hc : Tendsto Real.cos (𝓝[<] L) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Real.cos_pi_div_two] using Real.continuous_cos.continuousWithinAt.tendsto
        (s := Iio L) (x := L)
    · filter_upwards [Ioo_mem_nhdsLT (half_pos Real.pi_pos)] with a ha
      exact robin_quarter_cos ⟨ha.1.le, ha.2⟩
  have hs : Tendsto (fun h : ℝ ↦ Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousWithinAt.tendsto (s := Ioi (0 : ℝ)) (x := 0)
  have hl := ((tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)).abs)
  have hl' : Tendsto (fun h : ℝ ↦ Real.sqrt h * |Real.log h|) (𝓝[>] 0) (𝓝 0) := by
    apply (by simpa only [abs_zero] using hl :
      Tendsto (fun h : ℝ ↦ |Real.log h * h ^ (1 / 2 : ℝ)|) (𝓝[>] 0) (𝓝 0)).congr'
    exact Eventually.of_forall fun h ↦ by
      change |Real.log h * h ^ (1 / 2 : ℝ)| = _
      rw [abs_mul, ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
  simpa only [Function.comp_def, mul_add, mul_one, zero_add] using (hs.add hl').comp hc

/-- Remove the two artificial faces in order, first the odd face with fixed
right endpoint, then the degenerate right face. -/
theorem mixed_robin_comparison_smooth (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    (hrobin : ∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ mixedRobinNumerator oddA ρ h)
    {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 2 z)
    (hzero : ∀ t ∈ Icc 0 L, (if oddA then z (0, t) else z (t, 0)) = 0) :
    c * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      (∫ q in mixedQuarterCell, mixedRobinBulk z (partialX z) (partialY z) q) +
        ∫ x in Ioo (0 : ℝ) L, Real.cos x * ‖z (x, L)‖ ^ 2 := by
  let S := Ioo (0 : ℝ) L
  let R (A : ℝ) := Ioo (0 : ℝ) A ×ˢ S
  let g := mixedRobinComparison oddA ρ
  let m : ℝ × ℝ → ℝ := fun q ↦ Real.cos q.1 ^ 2 * ‖z q‖ ^ 2
  let F := mixedRobinBulk z (partialX z) (partialY z)
  let T : ℝ → ℝ := fun a ↦ Real.cos a * ‖z (a, L)‖ ^ 2
  let w : ℝ → ℝ := fun a ↦ Real.sqrt (Real.cos a) * (1 + |Real.log (Real.cos a)|)
  have hz₁ : ContDiff ℝ 1 z := hz.of_le (by norm_num)
  have hzc := hz.continuous
  have hm : IntegrableOn m mixedQuarterCell := by
    have hc : Continuous m := by unfold m; fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hF := robin_quarter_smooth_integrable hz
  have hT : IntegrableOn T S := by
    have hc : Continuous T := by unfold T; fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨K, hK, hright⟩ := mixed_robin_right_current_bound oddA hρ hz₁
  have hL := half_pos Real.pi_pos
  have hfixed (A : ℝ) (hA : A ∈ Ico (L / 2) L) :
      c * (∫ q in R A, m q) ≤ (∫ q in R A, F q) + (∫ x in Ioo 0 A, T x) + K * w A := by
    have ha : A ∈ Ioo 0 L := ⟨(half_pos hL).trans_le hA.1, hA.2⟩
    obtain ⟨M, hM, hodd⟩ := mixed_robin_odd_current_bound oddA hρ hz₁ hzero ha
    let s (δ : ℝ) := Ioo (if oddA then δ else 0) A
    let r (δ : ℝ) := s δ ×ˢ Ioo (if oddA then 0 else δ) L
    have hS : Ioo (0 : ℝ) A ⊆ S := fun _ hx ↦ ⟨hx.1, hx.2.trans ha.2⟩
    have hR : R A ⊆ mixedQuarterCell := prod_mono hS (fun _ h ↦ h)
    have hδ : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioo 0 A := Ioo_mem_nhdsGT ha.1
    have hsSub : ∀ᶠ δ in 𝓝[>] (0 : ℝ), s δ ⊆ Ioo 0 A := hδ.mono fun δ hδ ↦ by
      cases oddA
      · exact fun _ h ↦ h
      · exact Ioo_subset_Ioo_left hδ.1.le
    have hrSub : ∀ᶠ δ in 𝓝[>] (0 : ℝ), r δ ⊆ R A := hδ.mono fun δ hδ ↦ by
      cases oddA
      · exact prod_mono (fun _ h ↦ h) (Ioo_subset_Ioo_left hδ.1.le)
      · exact prod_mono (Ioo_subset_Ioo_left hδ.1.le) (fun _ h ↦ h)
    have hsEx (x : ℝ) (hx : x ∈ Ioo 0 A) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x ∈ s δ := by
      filter_upwards [Ioo_mem_nhdsGT hx.1] with δ h
      cases oddA
      · exact hx
      · exact ⟨h.2, hx.2⟩
    have hrEx (q : ℝ × ℝ) (hq : q ∈ R A) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), q ∈ r δ := by
      filter_upwards [hsEx q.1 hq.1, Ioo_mem_nhdsGT hq.2.1] with δ h₁ h₂
      refine ⟨h₁, ?_⟩
      cases oddA
      · exact ⟨h₂.2, hq.2.2⟩
      · exact hq.2
    have hlim (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f mixedQuarterCell) :=
      robin_integral_exhaustion (measurableSet_Ioo.prod measurableSet_Ioo) (hf.mono_set hR)
        (fun _ ↦ measurableSet_Ioo.prod measurableSet_Ioo) hrSub hrEx
    have htlim := robin_integral_exhaustion measurableSet_Ioo (hT.mono_set hS)
      (fun _ ↦ measurableSet_Ioo) hsSub hsEx
    have hml := (hlim m hm).const_mul c
    have hfl := ((hlim F hF).add htlim).add
      (tendsto_const_nhds (x := K * w A))
    have herror : Tendsto (fun δ : ℝ ↦ M * δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ ↦ M * δ) := by fun_prop
      simpa only [mul_zero] using hc.continuousWithinAt.tendsto (s := Ioi (0 : ℝ)) (x := 0)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        c * (∫ q in r δ, m q) ≤ (∫ q in r δ, F q) + (∫ x in s δ, T x) + K * w A + M * δ := by
      filter_upwards [hδ] with δ hd
      have hdL := hd.2.trans ha.2
      have hzBound := hodd δ hd
      cases oddA
      · have hi := mixed_robin_rectangle false hρ hinterior hrobin hz
          (a := 0) (A := A) (b := δ) le_rfl ha.1 ha.2 hd.1.le hdL hd.1
        dsimp only at hi
        have he (y : ℝ) (hy : y ∈ Ioo δ L) :=
          (mixed_robin_even_axis_current hρ ⟨hd.1.trans hy.1, hy.2⟩ z).1
        have he' : (∫ y in Ioo δ L,
            mixedRobinCurrentA g z (A, y) - mixedRobinCurrentA g z (0, y)) =
            ∫ y in Ioo δ L, mixedRobinCurrentA g z (A, y) :=
          setIntegral_congr_fun measurableSet_Ioo fun y hy ↦ by
            rw [show mixedRobinCurrentA g z (0, y) = 0 from he y hy, sub_zero]
        change _ + (∫ y in Ioo δ L, mixedRobinCurrentA g z (A, y) -
          mixedRobinCurrentA g z (0, y)) - _ ≤ _ at hi
        rw [he'] at hi
        have hr := neg_le_of_abs_le (hright A hA δ ⟨hd.1.le, hdL⟩)
        have hl := le_of_abs_le hzBound
        change c * (∫ q in r δ, m q) ≤ _ + _ + K * w A + M * δ
        change c * (∫ q in r δ, m q) + (∫ y in Ioo δ L, mixedRobinCurrentA g z (A, y)) -
          (∫ x in Ioo 0 A, mixedRobinCurrentB g z (x, δ)) ≤
            (∫ q in r δ, F q) + (∫ x in s δ, T x) at hi
        change -(K * w A) ≤ ∫ y in Ioo δ L, mixedRobinCurrentA g z (A, y) at hr
        change (∫ x in Ioo 0 A, mixedRobinCurrentB g z (x, δ)) ≤ M * δ at hl
        linarith only [hi, hr, hl]
      · have hi := mixed_robin_rectangle true hρ hinterior hrobin hz
          (a := δ) (A := A) (b := 0) hd.1.le hd.2 ha.2 le_rfl hL hd.1
        dsimp only at hi
        have he' : (∫ x in Ioo δ A, mixedRobinCurrentB g z (x, 0)) = 0 := by
          calc
            _ = ∫ _x in Ioo δ A, (0 : ℝ) :=
              setIntegral_congr_fun measurableSet_Ioo fun x hx ↦
                (mixed_robin_even_axis_current hρ ⟨hd.1.trans hx.1, hx.2.trans ha.2⟩ z).2
            _ = 0 := integral_zero _ _
        have hc (t : ℝ) (ht : t ∈ Ioo 0 L) :
            IntegrableOn (fun y ↦ mixedRobinCurrentA g z (t, y)) S := by
          have hcont : ContinuousOn (fun y ↦ mixedRobinCurrentA g z (t, y)) (Icc 0 L) :=
            fun y hy ↦ (((mixed_robin_current_contDiffAt true hρ hz₁ (q := (t, y))
              ⟨⟨ht.1.le, ht.2⟩, hy⟩ ht.1).1.continuousAt).comp
              (show ContinuousAt (fun y : ℝ ↦ (t, y)) y by fun_prop)).continuousWithinAt
          exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
        change c * (∫ q in r δ, m q) + (∫ y in S, mixedRobinCurrentA g z (A, y) -
          mixedRobinCurrentA g z (δ, y)) - (∫ x in Ioo δ A, mixedRobinCurrentB g z (x, 0)) ≤
            (∫ q in r δ, F q) + (∫ x in s δ, T x) at hi
        rw [he', integral_sub (hc A ha) (hc δ ⟨hd.1, hdL⟩), sub_zero] at hi
        have hr := neg_le_of_abs_le (hright A hA 0 ⟨le_rfl, hL⟩)
        have hl := le_of_abs_le hzBound
        change c * (∫ q in r δ, m q) ≤ _ + _ + K * w A + M * δ
        change -(K * w A) ≤ ∫ y in S, mixedRobinCurrentA g z (A, y) at hr
        change (∫ y in S, mixedRobinCurrentA g z (δ, y)) ≤ M * δ at hl
        linarith only [hi, hr, hl]
    have hfin := le_of_tendsto_of_tendsto hml (hfl.add herror) hev
    simpa only [R, S, add_zero] using hfin
  have hAev : ∀ᶠ A : ℝ in 𝓝[<] L, A ∈ Ico (L / 2) L :=
    (show ∀ᶠ A in 𝓝[<] L, A ∈ Ioo (L / 2) L from
      Ioo_mem_nhdsLT (half_lt_self hL)).mono Ioo_subset_Ico_self
  have hsub : ∀ᶠ A : ℝ in 𝓝[<] L, Ioo 0 A ⊆ S :=
    hAev.mono fun A hA ↦ Ioo_subset_Ioo_right hA.2.le
  have hex (x : ℝ) (hx : x ∈ S) : ∀ᶠ A : ℝ in 𝓝[<] L, x ∈ Ioo 0 A :=
    (show ∀ᶠ A in 𝓝[<] L, A ∈ Ioo x L from Ioo_mem_nhdsLT hx.2).mono
      fun _ hA ↦ ⟨hx.1, hA.1⟩
  have hlim (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f mixedQuarterCell) :=
    robin_integral_exhaustion (measurableSet_Ioo.prod measurableSet_Ioo) hf
      (fun _ ↦ measurableSet_Ioo.prod measurableSet_Ioo)
      (hsub.mono fun _ hA ↦ prod_mono hA (fun _ h ↦ h))
      (fun q hq ↦ (hex q.1 hq.1).mono fun _ hA ↦ ⟨hA, hq.2⟩)
  have hTop := robin_integral_exhaustion measurableSet_Ioo hT (fun _ ↦ measurableSet_Ioo) hsub hex
  have hRight := robin_sqrt_log_tendsto.const_mul K
  have hfin := le_of_tendsto_of_tendsto ((hlim m hm).const_mul c)
    (((hlim F hF).add hTop).add hRight) (hAev.mono hfixed)
  simpa only [mixedQuarterCell, m, F, T, S, mul_zero, add_zero] using hfin

end EulerDipoleEigenvalues
