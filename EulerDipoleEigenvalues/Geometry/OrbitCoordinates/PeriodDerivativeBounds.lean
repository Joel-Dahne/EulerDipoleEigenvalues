module

public import EulerDipoleEigenvalues.Geometry.OrbitCoordinates.Period

/-!
# Coarse bounds for the first two period derivatives

Blueprint: `lem:period-derivative-bounds`.

Differentiate the regular quadrature twice on its open positive-denominator set.
With B = 1 + h - t² and 0 < h < 1/2, both sqrt(Q) and Q_h are comparable to B.
The resulting derivatives are bounded by fixed multiples of (h + 1 - t)⁻²
and (h + 1 - t)⁻³. Their elementary primitives give uniform weighted bounds.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open Real Set Filter intervalIntegral
open scoped Topology ContDiff

private def periodSlope (q : ℝ × ℝ) : ℝ :=
  q.2 ^ 2 * (1 + q.1 - q.2 ^ 2) + (1 - (1 - q.1) * q.2 ^ 2)

private def periodIntegrand₁ (q : ℝ × ℝ) : ℝ :=
  -periodSlope q / (2 * (sqrt (periodDenom q)) ^ 3)

private def periodIntegrand₂ (q : ℝ × ℝ) : ℝ :=
  (3 * periodSlope q ^ 2 - 4 * q.2 ^ 2 * (sqrt (periodDenom q)) ^ 2) /
    (4 * (sqrt (periodDenom q)) ^ 5)

private theorem isOpen_periodDomain : IsOpen {q : ℝ × ℝ | 0 < periodDenom q} :=
  isOpen_lt continuous_const (by unfold periodDenom; fun_prop)

private theorem contDiffOn_periodIntegrand₁ :
    ContDiffOn ℝ ∞ periodIntegrand₁ {q | 0 < periodDenom q} := by
  have hS : ContDiff ℝ ∞ periodSlope := by unfold periodSlope; fun_prop
  have hQ : ContDiff ℝ ∞ periodDenom := by unfold periodDenom; fun_prop
  exact hS.contDiffOn.neg.div
    (contDiffOn_const.mul ((hQ.contDiffOn.sqrt (fun q (hq : 0 < periodDenom q) ↦ hq.ne')).pow 3))
    (fun q hq ↦ mul_ne_zero (by norm_num) (pow_ne_zero _ (sqrt_pos.2 hq).ne'))

private theorem contDiffOn_periodIntegrand₂ :
    ContDiffOn ℝ ∞ periodIntegrand₂ {q | 0 < periodDenom q} := by
  have hS : ContDiff ℝ ∞ periodSlope := by unfold periodSlope; fun_prop
  have hQ : ContDiff ℝ ∞ periodDenom := by unfold periodDenom; fun_prop
  have hR : ContDiffOn ℝ ∞ (fun q ↦ sqrt (periodDenom q)) {q | 0 < periodDenom q} :=
    hQ.contDiffOn.sqrt (fun _ hq ↦ hq.ne')
  exact ((contDiffOn_const.mul (hS.contDiffOn.pow 2)).sub
    ((contDiffOn_const.mul (contDiffOn_snd.pow 2)).mul (hR.pow 2))).div
      (contDiffOn_const.mul (hR.pow 5))
      (fun q hq ↦ mul_ne_zero (by norm_num) (pow_ne_zero _ (sqrt_pos.2 hq).ne'))

private theorem periodIntegrand_derivatives {h t : ℝ} (hQ : 0 < periodDenom (h, t)) :
    HasDerivAt (fun x ↦ 1 / sqrt (periodDenom (x, t))) (periodIntegrand₁ (h, t)) h ∧
      HasDerivAt (fun x ↦ periodIntegrand₁ (x, t)) (periodIntegrand₂ (h, t)) h := by
  have hdA : HasDerivAt (fun x : ℝ ↦ 1 - (1 - x) * t ^ 2) (t ^ 2) h := by
    convert! (hasDerivAt_const h (1 : ℝ)).sub
      (((hasDerivAt_const h (1 : ℝ)).sub (hasDerivAt_id h)).mul_const (t ^ 2)) using 1
    ring
  have hdB : HasDerivAt (fun x : ℝ ↦ 1 + x - t ^ 2) 1 h := by
    simpa using! ((hasDerivAt_const h (1 : ℝ)).add (hasDerivAt_id h)).sub_const (t ^ 2)
  have hdQ : HasDerivAt (fun x ↦ periodDenom (x, t)) (periodSlope (h, t)) h := by
    simpa only [periodDenom, periodSlope, mul_one] using! hdA.mul hdB
  have hdS : HasDerivAt (fun x ↦ periodSlope (x, t)) (2 * t ^ 2) h := by
    convert! (hdB.const_mul (t ^ 2)).add hdA using 1
    ring
  have hdR := hdQ.sqrt hQ.ne'
  have hR : sqrt (periodDenom (h, t)) ≠ 0 := (sqrt_pos.2 hQ).ne'
  constructor
  · convert! hdR.inv hR using 1
    · funext x; simp only [one_div, Pi.inv_apply]
    · simp only [periodIntegrand₁]
      field_simp
  · convert! hdS.neg.div ((hdR.pow 3).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hR))
      using 1
    simp only [periodIntegrand₂, Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

private theorem hasDerivAt_integral_explicit {F D : ℝ × ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {h : ℝ}
    (hh : {h} ×ˢ Icc (0 : ℝ) 1 ⊆ U)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun x ↦ F (x, t)) (D (h, t)) h) :
    HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, D (h, t)) h := by
  have hi := hasDerivAt_integral_smooth hU hF hh
  convert hi using 1
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hft : HasDerivAt (fun x ↦ F (x, t)) (fderiv ℝ F (h, t) (1, 0)) h :=
    ((hF.contDiffAt (hU.mem_nhds (hh ⟨by simp, ht⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt h
        ((hasDerivAt_id h).prodMk (hasDerivAt_const h t))
  exact (hd t ht).unique hft

private theorem eighthPeriod_hasDerivAt_regular {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt eighthPeriod (∫ t in (0 : ℝ)..1, periodIntegrand₁ (h, t)) h := by
  have hi := hasDerivAt_integral_explicit isOpen_periodDomain contDiffOn_periodIntegrand
    (h := h) (D := periodIntegrand₁) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩; rcases mem_singleton_iff.1 hx with rfl
      exact periodDenom_pos hh ht)
    (fun t ht ↦ (periodIntegrand_derivatives (periodDenom_pos hh ht)).1)
  apply hi.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hh.1 hh.2] with x hx
  exact eighthPeriod_eq_regular hx

private theorem eighthPeriod_deriv_hasDerivAt_regular {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv eighthPeriod) (∫ t in (0 : ℝ)..1, periodIntegrand₂ (h, t)) h := by
  have hi := hasDerivAt_integral_explicit isOpen_periodDomain contDiffOn_periodIntegrand₁
    (h := h) (D := periodIntegrand₂) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩; rcases mem_singleton_iff.1 hx with rfl
      exact periodDenom_pos hh ht)
    (fun t ht ↦ (periodIntegrand_derivatives (periodDenom_pos hh ht)).2)
  apply hi.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hh.1 hh.2] with x hx
  exact (eighthPeriod_hasDerivAt_regular hx).deriv

private theorem period_root_slope_bounds {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) (1 / 2))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    let H := h + 1 - t
    H / 2 ≤ sqrt (periodDenom (h, t)) ∧ sqrt (periodDenom (h, t)) ≤ 2 * H ∧
      H / 2 ≤ periodSlope (h, t) ∧ periodSlope (h, t) ≤ 4 * H := by
  let A := 1 - (1 - h) * t ^ 2
  let B := 1 + h - t ^ 2
  let H := h + 1 - t
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hB : 0 < B := by dsimp [B]; linarith [hh.1]
  have hHB : H ≤ B := by dsimp [H, B]; nlinarith [ht.1, ht.2]
  have hBH : B ≤ 2 * H := by dsimp [B, H]; nlinarith [sq_nonneg (1 - t), hh.1]
  have hAB : A ≤ B := by
    have := mul_le_mul_of_nonneg_left ht2 hh.1.le
    dsimp [A, B]; nlinarith
  have hBA : B / 2 ≤ A := by
    have := mul_nonneg (show 0 ≤ 1 / 2 - h by linarith [hh.2]) (sub_nonneg.2 ht2)
    dsimp [A, B]; nlinarith [hh.1]
  have hQ := periodDenom_pos ⟨hh.1, by linarith [hh.2]⟩ ht
  have he : periodDenom (h, t) = A * B := rfl
  have hRlo : B / 2 ≤ sqrt (periodDenom (h, t)) := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ B / 2) (sqrt_nonneg _)).1
    rw [sq_sqrt hQ.le, he]
    nlinarith [mul_le_mul_of_nonneg_right hBA hB.le]
  have hRhi : sqrt (periodDenom (h, t)) ≤ B := by
    apply (sq_le_sq₀ (sqrt_nonneg _) hB.le).1
    rw [sq_sqrt hQ.le, he]
    nlinarith [mul_le_mul_of_nonneg_right hAB hB.le]
  have hSB : periodSlope (h, t) ≤ 2 * B := by
    have := mul_le_mul_of_nonneg_right ht2 hB.le
    change t ^ 2 * B + A ≤ 2 * B
    linarith
  have hBS : B / 2 ≤ periodSlope (h, t) := by
    change B / 2 ≤ t ^ 2 * B + A
    nlinarith [mul_nonneg (sq_nonneg t) hB.le]
  change H / 2 ≤ _ ∧ _ ≤ 2 * H ∧ H / 2 ≤ _ ∧ _ ≤ 4 * H
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem period_integrand_bounds_algebra {H R S t : ℝ} (hH : 0 < H)
    (hRlo : H / 2 ≤ R) (hRhi : R ≤ 2 * H) (hSlo : H / 2 ≤ S)
    (hShi : S ≤ 4 * H) (ht : t ^ 2 ≤ 1) :
    1 / (32 * H ^ 2) ≤ S / (2 * R ^ 3) ∧ S / (2 * R ^ 3) ≤ 16 / H ^ 2 ∧
      |(3 * S ^ 2 - 4 * t ^ 2 * R ^ 2) / (4 * R ^ 5)| ≤ 512 / H ^ 3 := by
  have hR : 0 < R := (half_pos hH).trans_le hRlo
  have hS : 0 < S := (half_pos hH).trans_le hSlo
  constructor
  · calc
      1 / (32 * H ^ 2) = (H / 2) / (2 * (2 * H) ^ 3) := by field_simp; ring
      _ ≤ S / (2 * R ^ 3) := by gcongr
  constructor
  · calc
      S / (2 * R ^ 3) ≤ (4 * H) / (2 * (H / 2) ^ 3) := by gcongr
      _ = 16 / H ^ 2 := by field_simp; ring
  · have hS2 : S ^ 2 ≤ (4 * H) ^ 2 := pow_le_pow_left₀ hS.le hShi 2
    have hR2 : R ^ 2 ≤ (2 * H) ^ 2 := pow_le_pow_left₀ hR.le hRhi 2
    have htR : t ^ 2 * R ^ 2 ≤ R ^ 2 := mul_le_of_le_one_left (sq_nonneg R) ht
    have hnum : |3 * S ^ 2 - 4 * t ^ 2 * R ^ 2| ≤ 64 * H ^ 2 := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (by positivity : 0 ≤ 3 * S ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ 4 * t ^ 2 * R ^ 2)]
      nlinarith
    calc
      _ = |3 * S ^ 2 - 4 * t ^ 2 * R ^ 2| / (4 * R ^ 5) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 4 * R ^ 5)]
      _ ≤ (64 * H ^ 2) / (4 * (H / 2) ^ 5) := by gcongr
      _ = 512 / H ^ 3 := by field_simp; ring

private theorem period_integrand_bounds {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) (1 / 2))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / (32 * (h + 1 - t) ^ 2) ≤ -periodIntegrand₁ (h, t) ∧
      -periodIntegrand₁ (h, t) ≤ 16 / (h + 1 - t) ^ 2 ∧
      |periodIntegrand₂ (h, t)| ≤ 512 / (h + 1 - t) ^ 3 := by
  obtain ⟨hRlo, hRhi, hSlo, hShi⟩ := period_root_slope_bounds hh ht
  have he : -periodIntegrand₁ (h, t) = periodSlope (h, t) /
      (2 * sqrt (periodDenom (h, t)) ^ 3) := by simp only [periodIntegrand₁, neg_div, neg_neg]
  rw [he]
  exact period_integrand_bounds_algebra (by linarith [hh.1, ht.2]) hRlo hRhi hSlo hShi
    (by nlinarith [ht.1, ht.2])

private theorem inverse_power_integrals {h : ℝ} (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 2) = 1 / h - 1 / (h + 1) ∧
      (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 3) =
        1 / (2 * h ^ 2) - 1 / (2 * (h + 1) ^ 2) := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < h + 1 - t := by linarith [ht.2]
  have hc (n : ℕ) : ContinuousOn (fun t ↦ 1 / (h + 1 - t) ^ n) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht ↦ pow_ne_zero n (hp t ht).ne')
  have hd (t : ℝ) : HasDerivAt (fun t ↦ h + 1 - t) (-1) t := by
    simpa using! (hasDerivAt_const t (h + 1)).sub (hasDerivAt_id t)
  have hd1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t ↦ 1 / (h + 1 - t)) (1 / (h + 1 - t) ^ 2) t := by
    convert! (hd t).inv (hp t ht).ne' using 1
    · funext s; simp only [one_div, Pi.inv_apply]
    · simp
  have hd2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t ↦ 1 / (2 * (h + 1 - t) ^ 2)) (1 / (h + 1 - t) ^ 3) t := by
    convert! (((hd t).pow 2).const_mul 2).inv
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 (hp t ht).ne')) using 1
    · funext s; simp only [one_div, Pi.inv_apply, Pi.pow_apply]
    · simp only [Pi.pow_apply]
      field_simp [(hp t ht).ne']
      ring
  constructor
  · simpa using integral_eq_sub_of_hasDerivAt (fun t ht ↦
      hd1 t (by simpa only [uIcc_of_le zero_le_one] using ht))
        ((hc 2).intervalIntegrable_of_Icc zero_le_one)
  · simpa using integral_eq_sub_of_hasDerivAt (fun t ht ↦
      hd2 t (by simpa only [uIcc_of_le zero_le_one] using ht))
        ((hc 3).intervalIntegrable_of_Icc zero_le_one)

/-- Coarse period derivative bounds; smoothness and strict decrease are already in
`Period.lean` (`lem:period-derivative-bounds`). -/
theorem eighthPeriod_derivative_bounds : ∃ c C h₀ : ℝ,
    0 < c ∧ 0 < C ∧ 0 < h₀ ∧ h₀ < 1 ∧ ∀ h ∈ Ioo 0 h₀,
      c ≤ -h * deriv eighthPeriod h ∧ -h * deriv eighthPeriod h ≤ C ∧
      h ^ 2 * |deriv (deriv eighthPeriod) h| ≤ C := by
  refine ⟨1 / 64, 512, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro h hh
  have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, by linarith [hh.2]⟩
  have hplus : 0 < h + 1 := by linarith [hh.1]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < h + 1 - t := by linarith [hh.1, ht.2]
  have hc (n : ℕ) : ContinuousOn (fun t ↦ 1 / (h + 1 - t) ^ n) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht ↦ pow_ne_zero n (hp t ht).ne')
  have hD1 : ContinuousOn (fun t ↦ periodIntegrand₁ (h, t)) (Icc (0 : ℝ) 1) :=
    contDiffOn_periodIntegrand₁.continuousOn.comp (by fun_prop)
      (fun t ht ↦ periodDenom_pos hh1 ht)
  have hD2 : ContinuousOn (fun t ↦ periodIntegrand₂ (h, t)) (Icc (0 : ℝ) 1) :=
    contDiffOn_periodIntegrand₂.continuousOn.comp (by fun_prop)
      (fun t ht ↦ periodDenom_pos hh1 ht)
  have hlo : (1 / 32) * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 2) ≤
      -deriv eighthPeriod h := by
    rw [(eighthPeriod_hasDerivAt_regular hh1).deriv, ← integral_neg, ← integral_const_mul]
    apply integral_mono_on zero_le_one
      (((hc 2).const_mul (1 / 32)).intervalIntegrable_of_Icc zero_le_one)
      (hD1.neg.intervalIntegrable_of_Icc zero_le_one)
    intro t ht
    simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm, Pi.neg_apply] using
      (period_integrand_bounds hh ht).1
  have hhi : -deriv eighthPeriod h ≤
      16 * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 2) := by
    rw [(eighthPeriod_hasDerivAt_regular hh1).deriv, ← integral_neg, ← integral_const_mul]
    apply integral_mono_on zero_le_one (hD1.neg.intervalIntegrable_of_Icc zero_le_one)
      (((hc 2).const_mul 16).intervalIntegrable_of_Icc zero_le_one)
    intro t ht
    simpa only [div_eq_mul_inv, one_mul, Pi.neg_apply] using (period_integrand_bounds hh ht).2.1
  have hsecond : |deriv (deriv eighthPeriod) h| ≤
      512 * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 3) := by
    rw [(eighthPeriod_deriv_hasDerivAt_regular hh1).deriv, ← integral_const_mul]
    apply (abs_integral_le_integral_abs zero_le_one).trans
    apply integral_mono_on zero_le_one (hD2.abs.intervalIntegrable_of_Icc zero_le_one)
      (((hc 3).const_mul 512).intervalIntegrable_of_Icc zero_le_one)
    intro t ht
    simpa only [div_eq_mul_inv, one_mul] using (period_integrand_bounds hh ht).2.2
  obtain ⟨hI2, hI3⟩ := inverse_power_integrals hh.1
  have he2 : h * (1 / h - 1 / (h + 1)) = 1 / (h + 1) := by
    field_simp [hh.1.ne', hplus.ne']
    ring
  have hI2w : 1 / 2 ≤ h * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 2) ∧
      h * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 2) ≤ 1 := by
    rw [hI2, he2]
    constructor
    · apply (le_div_iff₀ hplus).2
      linarith [hh.2]
    · apply (div_le_iff₀ hplus).2
      linarith [hh.1]
  have hI3w : h ^ 2 * (∫ t in (0 : ℝ)..1, 1 / (h + 1 - t) ^ 3) ≤ 1 := by
    rw [hI3]
    calc
      _ ≤ h ^ 2 * (1 / (2 * h ^ 2)) := mul_le_mul_of_nonneg_left
        (sub_le_self _ (by positivity)) (sq_nonneg h)
      _ = 1 / 2 := by field_simp [hh.1.ne']
      _ ≤ 1 := by norm_num
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hlo hh.1.le, hI2w.1],
    by nlinarith [mul_le_mul_of_nonneg_left hhi hh.1.le, hI2w.2],
    by nlinarith [mul_le_mul_of_nonneg_left hsecond (sq_nonneg h), hI3w]⟩

end EulerDipoleEigenvalues
