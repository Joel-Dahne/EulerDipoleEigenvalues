import NoEmbeddedEigenvalues.Geometry.Flow.DipoleFlow

/-! # The positive-cell orbit and its period -/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Set Filter Metric
open scoped NNReal Topology

/-! ### The orbit through `(a, b) = (0, arccos h)` -/

/-- The orbit `γ_h` through `(arccos h, -arccos h)`, that is `(a, b) = (0, arccos h)`. -/
def dipoleOrbit (h : ℝ) : ℝ → ℝ × ℝ := dipoleFlow (arccos h, -arccos h)

/-- The diagonal coordinate `a(t)` of `γ_h(t)`. -/
def orbitA (h t : ℝ) : ℝ := (diagCoord (dipoleOrbit h t)).1

/-- The diagonal coordinate `b(t)` of `γ_h(t)`. -/
def orbitB (h t : ℝ) : ℝ := (diagCoord (dipoleOrbit h t)).2

/-- The flow time `∫_α^0 da / √(cos² a - h²)` from `a = 0` to `a = α` on the level
    `{Ψ = 2h}`, as long as `b > 0`. -/
def orbitTime (h α : ℝ) : ℝ := ∫ a in α..0, 1 / √(cos a ^ 2 - h ^ 2)

section Orbit

variable {h : ℝ}

theorem orbitA_zero : orbitA h 0 = 0 := by
  simp [orbitA, dipoleOrbit, dipoleFlow_zero, diagCoord]

theorem orbitB_zero : orbitB h 0 = arccos h := by
  simp [orbitB, dipoleOrbit, dipoleFlow_zero, diagCoord]

theorem hasDerivAt_orbitA (h t : ℝ) :
    HasDerivAt (orbitA h) (-cos (orbitA h t) * sin (orbitB h t)) t :=
  hasDerivAt_diag_fst _ t

theorem hasDerivAt_orbitB (h t : ℝ) :
    HasDerivAt (orbitB h) (sin (orbitA h t) * cos (orbitB h t)) t :=
  hasDerivAt_diag_snd _ t

theorem continuous_orbitA (h : ℝ) : Continuous (orbitA h) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_orbitA h t).continuousAt

theorem continuous_orbitB (h : ℝ) : Continuous (orbitB h) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_orbitB h t).continuousAt

/-- `γ_h` stays on the level `{Ψ = 2h}`. -/
theorem dipoleLift_dipoleOrbit (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    dipoleLift (dipoleOrbit h t) = 2 * h := by
  rw [dipoleOrbit, dipoleLift_dipoleFlow, dipoleLift, cos_neg, cos_arccos (by linarith) h1.le]
  ring

/-- `cos a cos b = h` along `γ_h`. -/
theorem cos_orbitA_mul_cos_orbitB (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    cos (orbitA h t) * cos (orbitB h t) = h := by
  have := dipoleLift_dipoleOrbit h0 h1 t
  rw [dipoleLift_eq_diag] at this
  rw [orbitA, orbitB]
  linarith

theorem abs_orbitA_lt (h0 : 0 < h) (h1 : h < 1) (t : ℝ) : |orbitA h t| < π / 2 := by
  have hne : ∀ s, cos (orbitA h s) ≠ 0 := fun s hc ↦ by
    have := cos_orbitA_mul_cos_orbitB h0 h1 s
    rw [hc, zero_mul] at this
    linarith
  refine abs_lt.2 ⟨?_, ?_⟩
  · have := lt_of_forall_ne (continuous_orbitA h).neg (v := π / 2)
      (fun s hs ↦ hne s (by rw [show orbitA h s = -(π / 2) by simp at hs; linarith, cos_neg,
        cos_pi_div_two]))
      (by simp [orbitA_zero, pi_pos]) t
    simp at this
    linarith
  · exact lt_of_forall_ne (continuous_orbitA h) (fun s hs ↦ hne s (by rw [hs, cos_pi_div_two]))
      (by simp [orbitA_zero, pi_pos]) t

theorem abs_orbitB_lt (h0 : 0 < h) (h1 : h < 1) (t : ℝ) : |orbitB h t| < π / 2 := by
  have hne : ∀ s, cos (orbitB h s) ≠ 0 := fun s hc ↦ by
    have := cos_orbitA_mul_cos_orbitB h0 h1 s
    rw [hc, mul_zero] at this
    linarith
  have hb0 : 0 < arccos h := arccos_pos.2 h1
  have hb1 : arccos h < π / 2 := arccos_lt_pi_div_two.2 h0
  refine abs_lt.2 ⟨?_, ?_⟩
  · have := lt_of_forall_ne (continuous_orbitB h).neg (v := π / 2)
      (fun s hs ↦ hne s (by rw [show orbitB h s = -(π / 2) by simp at hs; linarith, cos_neg,
        cos_pi_div_two]))
      (by simp [orbitB_zero]; linarith) t
    simp at this
    linarith
  · exact lt_of_forall_ne (continuous_orbitB h) (fun s hs ↦ hne s (by rw [hs, cos_pi_div_two]))
      (by simp [orbitB_zero]; linarith) t

/-- `γ_h` stays in the open square `|a|, |b| < π/2`, which covers the positive cell. -/
theorem dipoleOrbit_mem_cellSquare (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    dipoleOrbit h t ∈ cellSquare :=
  ⟨abs_orbitA_lt h0 h1 t, abs_orbitB_lt h0 h1 t⟩

theorem cos_orbitA_pos (h0 : 0 < h) (h1 : h < 1) (t : ℝ) : 0 < cos (orbitA h t) := by
  have := abs_lt.1 (abs_orbitA_lt h0 h1 t)
  exact cos_pos_of_mem_Ioo ⟨this.1, this.2⟩

theorem cos_orbitB_pos (h0 : 0 < h) (h1 : h < 1) (t : ℝ) : 0 < cos (orbitB h t) := by
  have := abs_lt.1 (abs_orbitB_lt h0 h1 t)
  exact cos_pos_of_mem_Ioo ⟨this.1, this.2⟩

/-- Where `b ≥ 0`, the speed of `a` is `cos a sin b = √(cos² a - h²)`. -/
theorem cos_orbitA_mul_sin_orbitB (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (hb : 0 ≤ orbitB h t) :
    cos (orbitA h t) * sin (orbitB h t) = √(cos (orbitA h t) ^ 2 - h ^ 2) := by
  have hs : 0 ≤ sin (orbitB h t) :=
    sin_nonneg_of_nonneg_of_le_pi hb (by linarith [abs_lt.1 (abs_orbitB_lt h0 h1 t), pi_pos])
  rw [← sqrt_sq (mul_nonneg (cos_orbitA_pos h0 h1 t).le hs)]
  congr 1
  linear_combination cos (orbitA h t) ^ 2 * sin_sq_add_cos_sq (orbitB h t) -
    (cos (orbitA h t) * cos (orbitB h t) + h) * cos_orbitA_mul_cos_orbitB h0 h1 t

/-- Where `b ≠ 0`, `cos a > h`. -/
theorem lt_cos_orbitA (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (hb : orbitB h t ≠ 0) :
    h < cos (orbitA h t) := by
  have hB := abs_lt.1 (abs_orbitB_lt h0 h1 t)
  have hc : cos (orbitB h t) < 1 := lt_of_le_of_ne (cos_le_one _) fun hc ↦
    hb ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 hc)
  have := cos_orbitA_mul_cos_orbitB h0 h1 t
  nlinarith [cos_orbitA_pos h0 h1 t]

theorem lt_cos_of_abs_lt_arccos {α : ℝ} (h0 : 0 < h) (h1 : h < 1) (hα : |α| < arccos h) :
    h < cos α := by
  rw [← cos_abs]
  have := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg α) (arccos_le_pi h) hα
  rwa [cos_arccos (by linarith) h1.le] at this

theorem abs_lt_arccos_of_lt_cos {α : ℝ} (h0 : 0 < h) (hα : |α| ≤ π) (hc : h < cos α) :
    |α| < arccos h := by
  rw [← cos_abs] at hc
  rw [← arccos_cos (abs_nonneg α) hα]
  exact arccos_lt_arccos (by linarith) hc (cos_le_one _)

theorem orbitA_mem_of_ne (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (hb : orbitB h t ≠ 0) :
    orbitA h t ∈ Ioo (-arccos h) (arccos h) := by
  have := abs_lt_arccos_of_lt_cos h0
    (by linarith [abs_orbitA_lt h0 h1 t, pi_pos]) (lt_cos_orbitA h0 h1 hb)
  exact ⟨by linarith [neg_abs_le (orbitA h t)], by linarith [le_abs_self (orbitA h t)]⟩

theorem continuousOn_orbitTime_integrand (h0 : 0 < h) (h1 : h < 1) :
    ContinuousOn (fun a ↦ 1 / √(cos a ^ 2 - h ^ 2)) (Ioo (-arccos h) (arccos h)) := by
  intro α hα
  have hc := lt_cos_of_abs_lt_arccos h0 h1 (abs_lt.2 hα)
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div continuousAt_const (by fun_prop)
  exact (sqrt_pos.2 (by nlinarith)).ne'

theorem orbitTime_strictAntiOn (h0 : 0 < h) (h1 : h < 1) :
    StrictAntiOn (orbitTime h) (Ioo (-arccos h) (arccos h)) := by
  have hcont := continuousOn_orbitTime_integrand h0 h1
  have hii : ∀ α ∈ Ioo (-arccos h) (arccos h), ∀ β ∈ Ioo (-arccos h) (arccos h),
      IntervalIntegrable (fun a ↦ 1 / √(cos a ^ 2 - h ^ 2)) MeasureTheory.volume α β :=
    fun α hα β hβ ↦ (hcont.mono (ordConnected_Ioo.uIcc_subset hα hβ)).intervalIntegrable
  have h0D : (0 : ℝ) ∈ Ioo (-arccos h) (arccos h) := by
    have := arccos_pos.2 h1
    constructor <;> linarith
  intro α hα β hβ hlt
  rw [orbitTime, orbitTime, ← intervalIntegral.integral_add_adjacent_intervals (hii α hα β hβ)
    (hii β hβ 0 h0D)]
  have : 0 < ∫ a in α..β, 1 / √(cos a ^ 2 - h ^ 2) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hii α hα β hβ) (fun x hx ↦ ?_) hlt
    have hxD : x ∈ Ioo (-arccos h) (arccos h) := ⟨hα.1.trans hx.1, hx.2.trans hβ.2⟩
    have hc := lt_cos_of_abs_lt_arccos h0 h1 (abs_lt.2 hxD)
    exact one_div_pos.2 (sqrt_pos.2 (by nlinarith))
  linarith

theorem orbitTime_zero : orbitTime h 0 = 0 := intervalIntegral.integral_same

/-- The flow time to the diagonal is `L(h)`. -/
theorem orbitTime_neg_arccos_sqrt : orbitTime h (-arccos √h) = eighthPeriod h := by
  have := intervalIntegral.integral_comp_neg (a := 0) (b := arccos √h)
    (fun a ↦ 1 / √(cos a ^ 2 - h ^ 2))
  simp only [cos_neg, neg_zero] at this
  rw [orbitTime, eighthPeriod, this]

theorem arccos_lt_arccos_sqrt (h0 : 0 < h) (h1 : h < 1) : arccos √h < arccos h :=
  arccos_lt_arccos (by linarith) ((lt_sqrt h0.le).2 (by nlinarith)) (sqrt_le_one.2 h1.le)

theorem neg_arccos_sqrt_mem (h0 : 0 < h) (h1 : h < 1) :
    -arccos √h ∈ Ioo (-arccos h) (arccos h) := by
  have := arccos_lt_arccos_sqrt h0 h1
  have := arccos_nonneg √h
  constructor <;> linarith

/-- While `b > 0`, the flow time from `a = 0` to `a(t)` is `t`. -/
theorem orbitTime_orbitA (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (ht : 0 ≤ t)
    (hb : ∀ s ∈ Icc 0 t, 0 < orbitB h s) : orbitTime h (orbitA h t) = t := by
  have hcov := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := t)
    (g := fun a ↦ 1 / √(cos a ^ 2 - h ^ 2)) (fun s _ ↦ hasDerivAt_orbitA h s)
    ((continuous_cos.comp (continuous_orbitA h)).neg.mul
      (continuous_sin.comp (continuous_orbitB h))).continuousOn
    (by
      rintro _ ⟨s, hs, rfl⟩
      rw [uIcc_of_le ht] at hs
      have hm := orbitA_mem_of_ne h0 h1 (hb s hs).ne'
      exact ((continuousOn_orbitTime_integrand h0 h1).continuousAt
        (Ioo_mem_nhds hm.1 hm.2)).continuousWithinAt)
  have hint : ∫ s in (0 : ℝ)..t, ((fun a ↦ 1 / √(cos a ^ 2 - h ^ 2)) ∘ orbitA h) s *
      (-cos (orbitA h s) * sin (orbitB h s)) = ∫ _ in (0 : ℝ)..t, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht] at hs
    have hc := lt_cos_orbitA h0 h1 (hb s hs).ne'
    have hpos : 0 < √(cos (orbitA h s) ^ 2 - h ^ 2) := sqrt_pos.2 (by nlinarith)
    simp only [Function.comp_apply, neg_mul]
    rw [cos_orbitA_mul_sin_orbitB h0 h1 (hb s hs).le]
    field_simp
  rw [orbitA_zero, hint, intervalIntegral.integral_symm (orbitA h t) 0] at hcov
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg, mul_one,
    neg_inj] at hcov
  rw [orbitTime, ← hcov]

theorem cos_arccos_sqrt (h0 : 0 < h) (h1 : h < 1) : cos (arccos √h) = √h :=
  cos_arccos (by linarith [sqrt_nonneg h]) (sqrt_le_one.2 h1.le)

theorem lt_sqrt_self (h0 : 0 < h) (h1 : h < 1) : h < √h := (lt_sqrt h0.le).2 (by nlinarith)

/-- `b > 0` up to time `L(h)`: if `b` vanished first at `t* ≤ L(h)`, then before `t*` the
    flow time gives `-arccos √h < a ≤ 0`, hence `cos a(t*) ≥ √h > h` and `b(t*) ≠ 0`. -/
theorem orbitB_pos (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (ht : t ∈ Icc 0 (eighthPeriod h)) :
    0 < orbitB h t := by
  by_contra hB₁
  rw [not_lt] at hB₁
  set Z := Icc 0 t ∩ {s | orbitB h s ≤ 0}
  have hZc : IsClosed Z := isClosed_Icc.inter (isClosed_le (continuous_orbitB h) continuous_const)
  have hZne : Z.Nonempty := ⟨t, ⟨ht.1, le_rfl⟩, hB₁⟩
  have hZb : BddBelow Z := ⟨0, fun s hs ↦ hs.1.1⟩
  set ts := sInf Z
  have hts : ts ∈ Z := hZc.csInf_mem hZne hZb
  have hb0 : 0 < orbitB h 0 := by rw [orbitB_zero]; exact arccos_pos.2 h1
  have hbefore : ∀ s ∈ Ico 0 ts, 0 < orbitB h s := by
    intro s hs
    by_contra hle
    rw [not_lt] at hle
    have := csInf_le hZb ⟨⟨hs.1, hs.2.le.trans hts.1.2⟩, hle⟩
    linarith [hs.2]
  have hts0 : 0 < ts := lt_of_le_of_ne hts.1.1 fun h ↦ by
    have := hts.2
    rw [← h] at this
    simp only [mem_ofPred_eq] at this
    linarith
  have hF : ∀ s ∈ Ico 0 ts, orbitTime h (orbitA h s) = s := fun s hs ↦
    orbitTime_orbitA h0 h1 hs.1 fun u hu ↦ hbefore u ⟨hu.1, hu.2.trans_lt hs.2⟩
  have hanti := orbitTime_strictAntiOn h0 h1
  have hmem : ∀ s ∈ Ico 0 ts, orbitA h s ∈ Ioo (-arccos h) (arccos h) := fun s hs ↦
    orbitA_mem_of_ne h0 h1 (hbefore s hs).ne'
  have h0D : (0 : ℝ) ∈ Ioo (-arccos h) (arccos h) := by
    have := arccos_pos.2 h1
    constructor <;> linarith
  have hAgt : ∀ s ∈ Ico 0 ts, -arccos √h ≤ orbitA h s := by
    intro s hs
    by_contra hlt
    rw [not_le] at hlt
    have := hanti (hmem s hs) (neg_arccos_sqrt_mem h0 h1) hlt
    rw [hF s hs, orbitTime_neg_arccos_sqrt] at this
    linarith [hs.2, hts.1.2, ht.2]
  have hAle : ∀ s ∈ Ico 0 ts, orbitA h s ≤ 0 := by
    intro s hs
    by_contra hlt
    rw [not_le] at hlt
    have := hanti h0D (hmem s hs) hlt
    rw [hF s hs, orbitTime_zero] at this
    linarith [hs.1]
  have hlim : Tendsto (orbitA h) (𝓝[<] ts) (𝓝 (orbitA h ts)) :=
    ((continuous_orbitA h).tendsto ts).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] ts, s ∈ Ico 0 ts :=
    mem_of_superset (Ioo_mem_nhdsLT hts0) Ioo_subset_Ico_self
  have hlo := ge_of_tendsto hlim (hev.mono hAgt)
  have hhi := le_of_tendsto hlim (hev.mono hAle)
  -- `cos a(t*) ≥ √h > h`, so `b(t*) ≠ 0`.
  have hcos : √h ≤ cos (orbitA h ts) := by
    rw [← cos_neg (orbitA h ts), ← cos_arccos_sqrt h0 h1]
    exact cos_le_cos_of_nonneg_of_le_pi (by linarith) (arccos_le_pi _) (by linarith)
  have hne : orbitB h ts ≠ 0 := fun hz ↦ by
    have := cos_orbitA_mul_cos_orbitB h0 h1 ts
    rw [hz, cos_zero, mul_one] at this
    linarith [lt_sqrt_self h0 h1]
  have hneg : orbitB h ts < 0 := lt_of_le_of_ne hts.2 hne
  obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hts.1.1 (continuous_orbitB h).continuousOn
    (show (0 : ℝ) ∈ Icc (orbitB h ts) (orbitB h 0) from ⟨hneg.le, hb0.le⟩)
  have hut : u ≠ ts := fun h ↦ by rw [h] at hu0; linarith
  have := hbefore u ⟨hu.1, lt_of_le_of_ne hu.2 hut⟩
  linarith

/-- `a < 0` on `(0, L(h)]`. -/
theorem orbitA_neg (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (ht : t ∈ Ioc 0 (eighthPeriod h)) :
    orbitA h t < 0 := by
  have hF := orbitTime_orbitA h0 h1 ht.1.le fun s hs ↦ orbitB_pos h0 h1 ⟨hs.1, hs.2.trans ht.2⟩
  have h0D : (0 : ℝ) ∈ Ioo (-arccos h) (arccos h) := by
    have := arccos_pos.2 h1
    constructor <;> linarith
  by_contra hle
  rw [not_lt] at hle
  have := (orbitTime_strictAntiOn h0 h1).antitoneOn h0D
    (orbitA_mem_of_ne h0 h1 (orbitB_pos h0 h1 ⟨ht.1.le, ht.2⟩).ne') hle
  rw [hF, orbitTime_zero] at this
  linarith [ht.1]

/-- At time `L(h)` the orbit reaches the diagonal: `a = -arccos √h`. -/
theorem orbitA_eighthPeriod (h0 : 0 < h) (h1 : h < 1) :
    orbitA h (eighthPeriod h) = -arccos √h := by
  have hL := (eighthPeriod_pos h0 h1).le
  have hF := orbitTime_orbitA h0 h1 hL fun s hs ↦ orbitB_pos h0 h1 hs
  conv_rhs at hF => rw [← orbitTime_neg_arccos_sqrt]
  exact (orbitTime_strictAntiOn h0 h1).injOn
    (orbitA_mem_of_ne h0 h1 (orbitB_pos h0 h1 ⟨hL, le_rfl⟩).ne') (neg_arccos_sqrt_mem h0 h1) hF

/-- At time `L(h)`, `b = arccos √h`. -/
theorem orbitB_eighthPeriod (h0 : 0 < h) (h1 : h < 1) :
    orbitB h (eighthPeriod h) = arccos √h := by
  have hL := (eighthPeriod_pos h0 h1).le
  have hb := orbitB_pos h0 h1 ⟨hL, le_rfl⟩
  have hprod := cos_orbitA_mul_cos_orbitB h0 h1 (eighthPeriod h)
  rw [orbitA_eighthPeriod h0 h1, cos_neg, cos_arccos_sqrt h0 h1] at hprod
  have hs : 0 < √h := sqrt_pos.2 h0
  have hcos : cos (orbitB h (eighthPeriod h)) = √h := by
    apply mul_left_cancel₀ hs.ne'
    rw [hprod, mul_self_sqrt h0.le]
  rw [← hcos, arccos_cos hb.le (by linarith [abs_lt.1 (abs_orbitB_lt h0 h1 (eighthPeriod h)),
    pi_pos])]

/-! #### Symmetries and the period -/

/-- The reflection `(x, y) ↦ (-y, -x)`, that is `a ↦ -a`. -/
def reflA : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The reflection `(x, y) ↦ (-x, y)`, that is `(a, b) ↦ (-b, -a)`. -/
def reflX : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem reflA_apply (p : ℝ × ℝ) : reflA p = (-p.2, -p.1) := rfl

@[simp] theorem reflX_apply (p : ℝ × ℝ) : reflX p = (-p.1, p.2) := rfl

theorem dipoleVelocity_reflA (p : ℝ × ℝ) :
    dipoleVelocity (reflA p) = -reflA (dipoleVelocity p) := by
  simp [dipoleVelocity, sin_neg]

theorem dipoleVelocity_reflX (p : ℝ × ℝ) :
    dipoleVelocity (reflX p) = -reflX (dipoleVelocity p) := by
  simp [dipoleVelocity, sin_neg]

/-- `γ_h(-t) = σ γ_h(t)` with `σ : a ↦ -a`. -/
theorem dipoleOrbit_neg (h t : ℝ) : dipoleOrbit h (-t) = reflA (dipoleOrbit h t) := by
  have := dipoleFlow_reverse dipoleVelocity_reflA (arccos h, -arccos h) (-t)
  rw [neg_neg] at this
  simpa [dipoleOrbit] using this

theorem orbitA_neg' (h t : ℝ) : orbitA h (-t) = -orbitA h t := by
  simp only [orbitA, dipoleOrbit_neg, reflA_apply, diagCoord]
  ring

theorem orbitB_neg' (h t : ℝ) : orbitB h (-t) = orbitB h t := by
  simp only [orbitB, dipoleOrbit_neg, reflA_apply, diagCoord]
  ring

theorem dipoleOrbit_fst (h t : ℝ) : (dipoleOrbit h t).1 = orbitA h t + orbitB h t := by
  simp only [orbitA, orbitB, diagCoord]
  ring

/-- `γ_h(L + u) = τ γ_h(L - u)` with `τ : (x, y) ↦ (-x, y)`, the reflection in the diagonal
    `a = -b` through `γ_h(L)`. -/
theorem dipoleOrbit_eighthPeriod_add (h0 : 0 < h) (h1 : h < 1) (u : ℝ) :
    dipoleOrbit h (eighthPeriod h + u) = reflX (dipoleOrbit h (eighthPeriod h - u)) := by
  have hp : reflX (dipoleOrbit h (eighthPeriod h)) = dipoleOrbit h (eighthPeriod h) := by
    have : (dipoleOrbit h (eighthPeriod h)).1 = 0 := by
      rw [dipoleOrbit_fst, orbitA_eighthPeriod h0 h1, orbitB_eighthPeriod h0 h1]
      ring
    ext <;> simp [this]
  calc dipoleOrbit h (eighthPeriod h + u)
      = dipoleFlow (dipoleOrbit h (eighthPeriod h)) u := dipoleFlow_add _ _ _
    _ = dipoleFlow (reflX (dipoleOrbit h (eighthPeriod h))) u := by rw [hp]
    _ = reflX (dipoleFlow (dipoleOrbit h (eighthPeriod h)) (-u)) :=
      dipoleFlow_reverse dipoleVelocity_reflX _ _
    _ = reflX (dipoleOrbit h (eighthPeriod h - u)) := by
      rw [dipoleOrbit, ← dipoleFlow_add, sub_eq_add_neg]

/-- A quarter period `2L(h)` rotates the orbit: `γ_h(t + 2L) = (y, -x)`, that is
    `(a, b) ↦ (-b, a)`. -/
theorem dipoleOrbit_add_quarter (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    dipoleOrbit h (t + 2 * eighthPeriod h) = ((dipoleOrbit h t).2, -(dipoleOrbit h t).1) := by
  rw [show t + 2 * eighthPeriod h = eighthPeriod h + (eighthPeriod h + t) by ring,
    dipoleOrbit_eighthPeriod_add h0 h1, show eighthPeriod h - (eighthPeriod h + t) = -t by ring,
    dipoleOrbit_neg]
  simp

theorem orbitA_add_quarter (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    orbitA h (t + 2 * eighthPeriod h) = -orbitB h t := by
  simp only [orbitA, orbitB, dipoleOrbit_add_quarter h0 h1, diagCoord]
  ring

theorem orbitB_add_quarter (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    orbitB h (t + 2 * eighthPeriod h) = orbitA h t := by
  simp only [orbitA, orbitB, dipoleOrbit_add_quarter h0 h1, diagCoord]
  ring

/-- `γ_h` is periodic with period `S(h) = 8L(h)`. -/
theorem dipoleOrbit_periodic (h0 : 0 < h) (h1 : h < 1) :
    Function.Periodic (dipoleOrbit h) (orbitPeriod h) := by
  intro t
  rw [orbitPeriod, show t + 8 * eighthPeriod h = t + 2 * eighthPeriod h + 2 * eighthPeriod h +
    2 * eighthPeriod h + 2 * eighthPeriod h by ring]
  simp only [dipoleOrbit_add_quarter h0 h1, neg_neg]

/-- On `[L, 2L]` the orbit is the reflection of `[0, L]`: `a(s) = -b(2L - s)`. -/
theorem orbitA_of_reflX (h0 : 0 < h) (h1 : h < 1) (s : ℝ) :
    orbitA h s = -orbitB h (2 * eighthPeriod h - s) := by
  have := dipoleOrbit_eighthPeriod_add h0 h1 (s - eighthPeriod h)
  rw [show eighthPeriod h + (s - eighthPeriod h) = s by ring,
    show eighthPeriod h - (s - eighthPeriod h) = 2 * eighthPeriod h - s by ring] at this
  simp only [orbitA, orbitB, this, reflX_apply, diagCoord]
  ring

theorem orbitB_of_reflX (h0 : 0 < h) (h1 : h < 1) (s : ℝ) :
    orbitB h s = -orbitA h (2 * eighthPeriod h - s) := by
  have := dipoleOrbit_eighthPeriod_add h0 h1 (s - eighthPeriod h)
  rw [show eighthPeriod h + (s - eighthPeriod h) = s by ring,
    show eighthPeriod h - (s - eighthPeriod h) = 2 * eighthPeriod h - s by ring] at this
  simp only [orbitA, orbitB, this, reflX_apply, diagCoord]
  ring

/-- `a < 0` on `(0, 2L)`. -/
theorem orbitA_neg_of_mem (h0 : 0 < h) (h1 : h < 1) {t : ℝ}
    (ht : t ∈ Ioo 0 (2 * eighthPeriod h)) : orbitA h t < 0 := by
  rcases le_or_gt t (eighthPeriod h) with hle | hlt
  · exact orbitA_neg h0 h1 ⟨ht.1, hle⟩
  · rw [orbitA_of_reflX h0 h1, neg_lt_zero]
    exact orbitB_pos h0 h1 ⟨by linarith [ht.2], by linarith⟩

/-- `b > 0` on `[0, 2L)`. -/
theorem orbitB_pos_of_mem (h0 : 0 < h) (h1 : h < 1) {t : ℝ}
    (ht : t ∈ Ico 0 (2 * eighthPeriod h)) : 0 < orbitB h t := by
  rcases le_or_gt t (eighthPeriod h) with hle | hlt
  · exact orbitB_pos h0 h1 ⟨ht.1, hle⟩
  · rw [orbitB_of_reflX h0 h1, neg_pos]
    exact orbitA_neg h0 h1 ⟨by linarith [ht.2], by linarith⟩

/-- `S(h)` is the minimal period: `γ_h(t) ≠ γ_h(0)` for `0 < t < S(h)`. -/
theorem dipoleOrbit_ne_zero (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (ht : t ∈ Ioo 0 (orbitPeriod h)) :
    dipoleOrbit h t ≠ dipoleOrbit h 0 := by
  intro heq
  have hA : orbitA h t = 0 := by rw [orbitA, heq, ← orbitA, orbitA_zero]
  have hB : orbitB h t = arccos h := by rw [orbitB, heq, ← orbitB, orbitB_zero]
  have hc := arccos_pos.2 h1
  have hL := eighthPeriod_pos h0 h1
  set Q := 2 * eighthPeriod h with hQ
  have ht2 : t < 4 * Q := by rw [hQ]; have := ht.2; rw [orbitPeriod] at this; linarith
  have hmem : ∀ s, 0 ≤ s → s < Q → s ∈ Ico 0 Q := fun s h1 h2 ↦ ⟨h1, h2⟩
  rcases lt_or_ge t Q with h₁ | h₁
  · linarith [orbitA_neg_of_mem h0 h1 ⟨ht.1, h₁⟩]
  rcases lt_or_ge t (2 * Q) with h₂ | h₂
  · have := orbitB_pos_of_mem h0 h1 (hmem (t - Q) (by linarith) (by linarith))
    rw [show t = (t - Q) + Q by ring, orbitA_add_quarter h0 h1] at hA
    linarith
  rcases lt_or_ge t (3 * Q) with h₃ | h₃
  · have := orbitB_pos_of_mem h0 h1 (hmem (t - 2 * Q) (by linarith) (by linarith))
    rw [show t = (t - 2 * Q) + Q + Q by ring, orbitB_add_quarter h0 h1,
      orbitA_add_quarter h0 h1] at hB
    linarith
  · have := orbitB_pos_of_mem h0 h1 (hmem (t - 3 * Q) (by linarith) (by linarith))
    rw [show t = (t - 3 * Q) + Q + Q + Q by ring, orbitA_add_quarter h0 h1,
      orbitB_add_quarter h0 h1, orbitA_add_quarter h0 h1] at hA
    linarith

/-- At times `±L(h)` the orbit reaches the diagonals `a = ∓b`. -/
theorem diagCoord_dipoleOrbit_eighthPeriod (h0 : 0 < h) (h1 : h < 1) :
    diagCoord (dipoleOrbit h (eighthPeriod h)) = (-arccos √h, arccos √h) ∧
      diagCoord (dipoleOrbit h (-eighthPeriod h)) = (arccos √h, arccos √h) := by
  have hA := orbitA_eighthPeriod h0 h1
  have hB := orbitB_eighthPeriod h0 h1
  constructor
  · exact Prod.ext hA hB
  · refine Prod.ext ?_ ?_
    · change orbitA h _ = _
      rw [orbitA_neg', hA, neg_neg]
    · change orbitB h _ = _
      rw [orbitB_neg', hB]

end Orbit

end NoEmbeddedEigenvalues
