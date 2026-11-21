module

public import NoEmbeddedEigenvalues.Transport.Transport

/-! # Good phase windows and selection of levels -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Complex

/-! ### Good windows (`lem:good-windows`) -/

open Filter Topology in
/-- The good windows `|λS(h) - 2π(j + ½)| < π/3` have positive measure near `h = 0`. -/
theorem volume_goodWindows_pos {lam : ℝ} (hlam : lam ≠ 0) {η : ℝ} (hη : 0 < η) :
    0 < volume {h ∈ Set.Ioo 0 η |
      ∃ j : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3} := by
  have hpi := Real.pi_pos
  set η' := min η (1 / 2)
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hη'1 : η' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcont : ContinuousOn orbitPeriod (Set.Ioo 0 1) := continuousOn_orbitPeriod
  -- A level `hs ∈ (0, η')` where `λS` is exactly a phase centre.
  obtain ⟨hs, hs0, hsη, j, hj⟩ : ∃ hs, 0 < hs ∧ hs < η' ∧ ∃ j : ℤ,
      lam * orbitPeriod hs = 2 * Real.pi * (j + 1 / 2) := by
    set μ := |lam|
    have hμ : 0 < μ := abs_pos.2 hlam
    set h₀ := η' / 2
    have h₀0 : 0 < h₀ := by positivity
    have h₀η : h₀ < η' := half_lt_self hη'
    set j₀ : ℤ := ⌈μ * orbitPeriod h₀ / (2 * Real.pi)⌉
    set c := 2 * Real.pi * (j₀ + 1 / 2)
    have hc₀ : μ * orbitPeriod h₀ ≤ c := by
      have h1 : μ * orbitPeriod h₀ / (2 * Real.pi) ≤ j₀ := Int.le_ceil _
      have h2 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 h1
      simp only [c]
      linarith
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), c ≤ μ * orbitPeriod h ∧ h < h₀ :=
      ((tendsto_orbitPeriod_atTop.const_mul_atTop hμ).eventually_ge_atTop c).and
        (Filter.eventually_of_mem (Ioo_mem_nhdsGT h₀0) fun h hh ↦ hh.2)
    obtain ⟨h₁, ⟨hc₁, h₁h₀⟩, h₁0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hsub : Set.Icc h₁ h₀ ⊆ Set.Ioo 0 1 :=
      fun h hh ↦ ⟨(show (0 : ℝ) < h₁ from h₁0).trans_le hh.1, by linarith [hh.2]⟩
    obtain ⟨hs, hsI, hsc⟩ := intermediate_value_Icc' h₁h₀.le
      ((hcont.mono hsub).const_smul μ) ⟨hc₀, hc₁⟩
    refine ⟨hs, (show (0 : ℝ) < h₁ from h₁0).trans_le hsI.1, hsI.2.trans_lt h₀η, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul] at hsc
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · refine ⟨-j₀ - 1, ?_⟩
      have : lam = -μ := by simp only [μ, abs_of_neg hneg, neg_neg]
      rw [this, neg_mul, hsc]
      push_cast
      ring
    · refine ⟨j₀, ?_⟩
      have : lam = μ := by simp only [μ, abs_of_pos hpos]
      rw [this, hsc]
  -- A neighbourhood of `hs` lies in the good windows.
  have hca : ContinuousAt (fun h ↦ lam * orbitPeriod h) hs :=
    continuousAt_const.mul (hcont.continuousAt (Ioo_mem_nhds hs0 (hsη.trans hη'1)))
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hca (Real.pi / 3) (by positivity)
  set ε := min δ (min hs (η - hs))
  have hε : 0 < ε := lt_min hδ (lt_min hs0 (by linarith [min_le_left η (1 / 2)]))
  have hsubset : Set.Ioo (hs - ε) (hs + ε) ⊆ {h ∈ Set.Ioo 0 η |
      ∃ j : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3} := by
    intro h hh
    have e1 : ε ≤ δ := min_le_left _ _
    have e2 : ε ≤ hs := (min_le_right _ _).trans (min_le_left _ _)
    have e3 : ε ≤ η - hs := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨⟨by linarith [hh.1], by linarith [hh.2]⟩, j, ?_⟩
    have hd : dist h hs < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hh.1, hh.2]
    have := hδc hd
    rwa [Real.dist_eq, hj] at this
  refine lt_of_lt_of_le ?_ (measure_mono hsubset)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

open Filter Topology in
/-- Good levels approaching zero can avoid any null set and satisfy an arbitrary
    almost-everywhere level property. No measurability of that property is required. -/
theorem exists_goodLevels_avoiding {lam : ℝ} (hlam : lam ≠ 0) {P : ℝ → Prop}
    (hP : ∀ᵐ h ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), P h)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j < 1 / ((j : ℝ) + 1) ∧
        hs j ∉ N ∧ P (hs j) ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) := by
  have hbad : volume {h | h ∈ Set.Ioo (0 : ℝ) 1 ∧ ¬P h} = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' measurableSet_Ioo).1 hP
  let B := N ∪ {h | h ∈ Set.Ioo (0 : ℝ) 1 ∧ ¬P h}
  have hB : volume B = 0 := measure_union_null hN hbad
  have heach (j : ℕ) : ∃ h : ℝ, h ∈ Set.Ioo 0 1 ∧ h < 1 / ((j : ℝ) + 1) ∧
      h ∉ N ∧ P h ∧
      ∃ m : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3 := by
    let η : ℝ := min (1 / ((j : ℝ) + 1)) 1
    have hη : 0 < η := lt_min (by positivity) zero_lt_one
    have hpos : 0 < volume ({h ∈ Set.Ioo 0 η |
        ∃ m : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3} \ B) := by
      rw [measure_sdiff_null hB]
      exact volume_goodWindows_pos hlam hη
    obtain ⟨h, ⟨hh, hw⟩, hnB⟩ := nonempty_of_measure_ne_zero hpos.ne'
    have h1 : h < 1 := hh.2.trans_le (min_le_right _ _)
    refine ⟨h, ⟨hh.1, h1⟩, hh.2.trans_le (min_le_left _ _),
      fun hn ↦ hnB (Or.inl hn), ?_, hw⟩
    by_contra hnP
    exact hnB (Or.inr ⟨⟨hh.1, h1⟩, hnP⟩)
  choose hs hhs using heach
  refine ⟨hs, hhs, squeeze_zero (fun j ↦ (hhs j).1.1.le)
    (fun j ↦ (hhs j).2.1.le) tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- On a good window `e^{iλS(h)/4}` stays at distance at least `2 sin(π/12)` from `κ = ±1`. -/
theorem norm_exp_sub_ge_of_goodWindow {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3) {κ : ℂ}
    (hκ : κ = 1 ∨ κ = -1) :
    2 * Real.sin (Real.pi / 12) ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ := by
  set θ : ℝ := lam * orbitPeriod h / 4
  set ε := lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)
  have hpi := Real.pi_pos
  -- `cos 2θ = ∓ sin(ε/2)` is at most `1/2` in absolute value.
  have h2θ : 2 * θ = (j : ℝ) * Real.pi + Real.pi / 2 + ε / 2 := by simp only [θ, ε]; ring
  have hsin : |Real.sin (ε / 2)| ≤ 1 / 2 := by
    rw [abs_lt] at hj
    have hb : |ε / 2| ≤ Real.pi / 6 := by rw [abs_le]; constructor <;> linarith
    rw [← Real.sin_pi_div_six, abs_le]
    constructor
    · rw [← neg_le_neg_iff, neg_neg, ← Real.sin_neg]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [(abs_le.1 hb).2])
        (by linarith) (by linarith [(abs_le.1 hb).2])
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [(abs_le.1 hb).1])
        (by linarith) (by linarith [(abs_le.1 hb).2])
  have hcos2 : |Real.cos (2 * θ)| ≤ 1 / 2 := by
    rw [h2θ, Real.cos_add, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.sin_int_mul_pi]
    simp only [neg_zero, zero_mul, zero_sub, abs_neg, abs_mul, Real.abs_cos_int_mul_pi,
      one_mul]
    exact hsin
  have hcos : Real.cos θ ^ 2 ≤ 3 / 4 := by
    have := Real.cos_sq θ
    rw [abs_le] at hcos2
    linarith [hcos2.2]
  -- `|e^{iθ} - κ|² = 2 - 2κ cos θ ≥ 2 - √3 = 4 sin²(π/12)`.
  have hκc : κ = ((κ.re : ℝ) : ℂ) := by rcases hκ with rfl | rfl <;> simp
  have hκ2 : κ.re ^ 2 = 1 := by rcases hκ with rfl | rfl <;> simp
  have hexp : exp (I * (lam * orbitPeriod h / 4)) = exp ((θ : ℂ) * I) := by
    simp only [θ]; push_cast; ring_nf
  have hnorm : ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ ^ 2 = 2 - 2 * κ.re * Real.cos θ := by
    rw [hexp, Complex.sq_norm, Complex.normSq_apply, hκc]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs3 : (2 * Real.sin (Real.pi / 12)) ^ 2 = 2 - √3 := by
    have h2 := Real.cos_two_mul (Real.pi / 12)
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at h2
    rw [mul_pow, Real.sin_sq]
    linarith
  have hkc : κ.re * Real.cos θ ≤ √3 / 2 := by
    have h3 : (κ.re * Real.cos θ) ^ 2 ≤ (√3 / 2) ^ 2 := by
      rw [mul_pow, hκ2, one_mul, div_pow, Real.sq_sqrt (by norm_num)]
      linarith
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
  have hsq : (2 * Real.sin (Real.pi / 12)) ^ 2 ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ ^ 2 := by
    rw [hs3, hnorm]
    linarith
  exact (abs_le_of_sq_le_sq' hsq (norm_nonneg _)).2

/-- The good windows work for all four quarter-rotation characters. A uniform
gap for the full-period phase gives a gap for each fourth root of unity. -/
theorem norm_exp_sub_ge_of_goodWindow_fourthRoot {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3)
    {κ : ℂ} (hκ : κ ^ 4 = 1) :
    (1 / 4 : ℝ) ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ := by
  let q := exp (I * (lam * orbitPeriod h / 4))
  have hq : ‖q‖ = 1 := by simp [q, Complex.norm_exp]
  have hkpow := congrArg norm hκ
  rw [norm_pow, norm_one] at hkpow
  have hk : ‖κ‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (4 : ℕ) ≠ 0)).mp
      (hkpow.trans (one_pow 4).symm)
  have hsq (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
      ‖x ^ 2 - y ^ 2‖ ≤ 2 * ‖x - y‖ := by
    rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, norm_mul, mul_comm 2]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [hx, hy, one_add_one_eq_two] using norm_add_le x y
  have hbound : ‖q ^ 4 - 1‖ ≤ 4 * ‖q - κ‖ := by
    have hb := hsq (q ^ 2) (κ ^ 2) (by simp [norm_pow, hq]) (by simp [norm_pow, hk])
    rw [← pow_mul, ← pow_mul, show (2 : ℕ) * 2 = 4 by decide, hκ] at hb
    linarith [hsq q κ hq hk]
  let err := lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)
  have he : |err| < Real.pi / 3 := hj
  have hc : 0 ≤ Real.cos err := Real.cos_nonneg_of_mem_Icc
    ⟨by have := (abs_lt.mp he).1; linarith [Real.pi_pos],
      by have := (abs_lt.mp he).2; linarith [Real.pi_pos]⟩
  have hq4 : q ^ 4 = -exp ((err : ℂ) * I) := by
    rw [show q = exp ((lam * orbitPeriod h / 4 : ℝ) * I) by
      unfold q
      push_cast
      ring, ← exp_nat_mul]
    have hangle : (4 : ℂ) * ((lam * orbitPeriod h / 4 : ℝ) * I) =
        (j : ℂ) * (2 * Real.pi * I) + Real.pi * I + (err : ℂ) * I := by
      dsimp [err]
      push_cast
      ring
    rw [Nat.cast_ofNat, hangle, exp_add, exp_add, exp_int_mul_two_pi_mul_I, exp_pi_mul_I]
    ring
  have hre : (q ^ 4 - 1).re ≤ -1 := by
    rw [hq4]
    simpa using (show -Real.cos err - 1 ≤ -1 by linarith)
  have habs : 1 ≤ |(q ^ 4 - 1).re| := by
    have hnonpos : (q ^ 4 - 1).re ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  change (1 / 4 : ℝ) ≤ ‖q - κ‖
  linarith [habs.trans (abs_re_le_norm (q ^ 4 - 1)), hbound]

open Filter Topology in
/-- A good window is also nonresonant for the full period. -/
theorem exp_orbitPeriod_ne_one_of_goodWindow {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3) :
    exp (I * lam * orbitPeriod h) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
  have ht : lam * orbitPeriod h = (n : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hn
  rw [ht, abs_lt] at hj
  rcases le_or_gt n j with hle | hgt
  · have hle' : (n : ℝ) ≤ j := by exact_mod_cast hle
    nlinarith [mul_le_mul_of_nonneg_left hle' Real.pi_pos.le]
  · have hle' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hgt
    nlinarith [mul_le_mul_of_nonneg_left hle' Real.pi_pos.le]

end NoEmbeddedEigenvalues
