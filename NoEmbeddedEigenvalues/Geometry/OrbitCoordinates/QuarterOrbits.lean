import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.OrbitCoordinates
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quarter orbits and the arc in diagonal coordinates

Blueprint: `lem:quarter-orbit-decomposition`, `lem:quarter-orbit-diagonal`, `lem:arc-diagonal`.

A level `{Ψ = 2h}` is the union of four quarter orbits `Rᵏ γ_h([-L, L])`, since
`γ_h(t + 2L) = R γ_h(t)`. In the diagonal coordinates `(a, b)` the quarter orbit
`γ_h([-L, L])` is the graph `b = β_h(a) = arccos(h / cos a)` over `|a| ≤ arccos √h`, traversed
with `ȧ = -√(cos² a - h²)`, so flow-time integrals over it are integrals in `a` with the weight
`1/√(cos² a - h²)`. The separatrix arc is the segment `b = π/2`, `a = arcAngle s - π/2`, with
`cos a = sech s`, so arc integrals in `s` are integrals in `a` with the weight `1/cos a`. These
explicit formulas are used for the level traces at the separatrix instead of comparisons of
orbits.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Set
open scoped ENNReal

/-! ### The arc -/

/-- The arc angle `2 arctan e^{-s}` lies in `(0, π)`. -/
theorem arcAngle_mem_Ioo (s : ℝ) : arcAngle s ∈ Ioo 0 π := by
  have h1 := Real.arctan_lt_pi_div_two (Real.exp (-s))
  have h0 := Real.arctan_pos.2 (Real.exp_pos (-s))
  exact ⟨by unfold arcAngle; linarith, by unfold arcAngle; linarith⟩

theorem antitone_arcAngle : Antitone arcAngle := fun s t hst ↦ by
  unfold arcAngle
  have := Real.arctan_strictMono.monotone (Real.exp_le_exp.2 (neg_le_neg hst))
  linarith

theorem lipschitzWith_arcAngle : LipschitzWith 1 arcAngle := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun s ↦ (hasDerivAt_arcAngle s).differentiableAt)
    fun s ↦ ?_
  rw [(hasDerivAt_arcAngle s).deriv, ← NNReal.coe_le_coe, coe_nnnorm, norm_neg, norm_div,
    norm_one, Real.norm_of_nonneg (Real.cosh_pos s).le, NNReal.coe_one,
    div_le_one (Real.cosh_pos s)]
  exact Real.one_le_cosh s

theorem strictAnti_arcAngle : StrictAnti arcAngle := fun s t hst ↦ by
  unfold arcAngle
  have := Real.arctan_strictMono (Real.exp_lt_exp.2 (neg_lt_neg hst))
  linarith

/-- The arc angle takes every value in `(0, π)`: `arcAngle (-log tan (c/2)) = c`. -/
theorem arcAngle_surjOn {c : ℝ} (hc : c ∈ Ioo 0 π) : arcAngle (-Real.log (tan (c / 2))) = c := by
  have h1 : 0 < c / 2 := by linarith [hc.1]
  have h2 : c / 2 < π / 2 := by linarith [hc.2]
  have ht : 0 < tan (c / 2) := tan_pos_of_pos_of_lt_pi_div_two h1 h2
  rw [arcAngle, neg_neg, Real.exp_log ht, Real.arctan_tan (by linarith) h2]
  ring

/-- The arc in diagonal coordinates (`lem:arc-diagonal`): with `a = arcAngle s - π/2`, `b = π/2`
    and `cos a = sech s`, `∫ F(γ(s)) ds = ∫_{-π/2}^{π/2} F(a, π/2) da / cos a`. -/
theorem integral_separatrixArc_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × ℝ → E) :
    ∫ s, F (separatrixArc s) =
      ∫ a in Ioo (-(π / 2)) (π / 2), (1 / cos a) • F (diagInv (a, π / 2)) := by
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - π / 2 with hφ
  have hφ' (s : ℝ) : HasDerivAt φ (-(1 / cosh s)) s := (hasDerivAt_arcAngle s).sub_const _
  have hinj : InjOn φ univ := fun s _ t _ hst ↦
    strictAnti_arcAngle.injective (by simpa [hφ] using hst)
  have himg : φ '' univ = Ioo (-(π / 2)) (π / 2) := by
    ext a
    constructor
    · rintro ⟨s, -, rfl⟩
      have := arcAngle_mem_Ioo s
      exact ⟨by simp only [hφ]; linarith [this.1], by simp only [hφ]; linarith [this.2]⟩
    · intro ha
      refine ⟨-Real.log (tan ((a + π / 2) / 2)), mem_univ _, ?_⟩
      simp only [hφ]
      rw [arcAngle_surjOn ⟨by linarith [ha.1], by linarith [ha.2]⟩]
      ring
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun s _ ↦ (hφ' s).hasDerivWithinAt) hinj
    (fun a ↦ (1 / cos a) • F (diagInv (a, π / 2)))
  rw [himg, Measure.restrict_univ] at h
  rw [h]
  congr 1
  funext s
  have hc := cosh_pos s
  have hcos : cos (φ s) = 1 / cosh s := by
    simp only [hφ, cos_sub_pi_div_two, sin_arcAngle]
  have hpt : diagInv (φ s, π / 2) = separatrixArc s := by
    simp only [hφ, diagInv_apply, separatrixArc]
    congr 1 <;> ring
  rw [smul_smul, hcos, hpt, abs_neg, abs_of_pos (by positivity)]
  field_simp
  simp

/-- The arc in diagonal coordinates for nonnegative functions (`lem:arc-diagonal`):
    `∫⁻ F(γ(s)) ds = ∫⁻_{-π/2}^{π/2} F(a, π/2) da / cos a`, for every `F`. -/
theorem lintegral_separatrixArc_eq (F : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ s, F (separatrixArc s) =
      ∫⁻ a in Ioo (-(π / 2)) (π / 2), ENNReal.ofReal (1 / cos a) * F (diagInv (a, π / 2)) := by
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - π / 2 with hφ
  have hφ' (s : ℝ) : HasDerivAt φ (-(1 / cosh s)) s := (hasDerivAt_arcAngle s).sub_const _
  have hinj : InjOn φ univ := fun s _ t _ hst ↦
    strictAnti_arcAngle.injective (by simpa [hφ] using hst)
  have himg : φ '' univ = Ioo (-(π / 2)) (π / 2) := by
    ext a
    constructor
    · rintro ⟨s, -, rfl⟩
      have := arcAngle_mem_Ioo s
      exact ⟨by simp only [hφ]; linarith [this.1], by simp only [hφ]; linarith [this.2]⟩
    · intro ha
      refine ⟨-Real.log (tan ((a + π / 2) / 2)), mem_univ _, ?_⟩
      simp only [hφ]
      rw [arcAngle_surjOn ⟨by linarith [ha.1], by linarith [ha.2]⟩]
      ring
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun s _ ↦ (hφ' s).hasDerivWithinAt) hinj
    (fun a ↦ ENNReal.ofReal (1 / cos a) * F (diagInv (a, π / 2)))
  rw [himg, Measure.restrict_univ] at h
  rw [h]
  congr 1
  funext s
  have hc := cosh_pos s
  have hcos : cos (φ s) = 1 / cosh s := by
    simp only [hφ, cos_sub_pi_div_two, sin_arcAngle]
  have hpt : diagInv (φ s, π / 2) = separatrixArc s := by
    simp only [hφ, diagInv_apply, separatrixArc]
    congr 1 <;> ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hcos, hpt, abs_neg,
    abs_of_pos (by positivity), one_div_one_div, one_div_mul_cancel hc.ne', ENNReal.ofReal_one,
    one_mul]

/-! ### Quarter orbits -/

variable {h : ℝ}

/-- `γ_h(t + 2kL) = Rᵏ γ_h(t)`. -/
theorem dipoleOrbit_add_mul_quarter (h0 : 0 < h) (h1 : h < 1) (k : ℕ) (t : ℝ) :
    dipoleOrbit h (t + k * (2 * eighthPeriod h)) = rotLift^[k] (dipoleOrbit h t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show t + ((k + 1 : ℕ) : ℝ) * (2 * eighthPeriod h) =
      (t + k * (2 * eighthPeriod h)) + 2 * eighthPeriod h by push_cast; ring,
      dipoleOrbit_add_quarter h0 h1, ih, Function.iterate_succ_apply']
    rfl

/-- The four quarter orbits (`lem:quarter-orbit-decomposition`):
    `∮ f dt = ∑_{k < 4} ∫_{-L}^{L} f(Rᵏ γ_h(t)) dt`. -/
theorem levelIntegral_eq_sum_quarter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h0 : 0 < h) (h1 : h < 1) {f : ℝ × ℝ → E}
    (hf : ∀ c d, IntervalIntegrable (fun t ↦ f (dipoleOrbit h t)) volume c d) :
    levelIntegral h f = ∑ k ∈ Finset.range 4,
      ∫ t in (-eighthPeriod h)..eighthPeriod h, f (rotLift^[k] (dipoleOrbit h t)) := by
  set L := eighthPeriod h
  set φ : ℝ → E := fun t ↦ f (dipoleOrbit h t) with hφ
  have hper : Function.Periodic φ (orbitPeriod h) := fun t ↦
    congrArg f (dipoleOrbit_periodic h0 h1 t)
  set a : ℕ → ℝ := fun k ↦ -L + k * (2 * L) with ha
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ) (a := a)
    (n := 4) fun k _ ↦ hf _ _
  have ha0 : a 0 = -L := by simp [ha]
  have ha4 : a 4 = -L + orbitPeriod h := by simp only [ha, orbitPeriod, L]; push_cast; ring
  have hend : ∫ x in (-L)..(-L + orbitPeriod h), φ x = ∫ x in (a 0)..(a 4), φ x := by
    rw [ha0, ha4]
  rw [levelIntegral, ← zero_add (orbitPeriod h), hper.intervalIntegral_add_eq 0 (-L), hend,
    ← hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk := intervalIntegral.integral_comp_add_right (f := φ) (a := -L) (b := L)
    (k * (2 * L))
  have hak : a k = -L + k * (2 * L) := rfl
  have hak1 : a (k + 1) = L + k * (2 * L) := by simp only [ha]; push_cast; ring
  rw [hak, hak1, ← hk]
  congr 1
  funext t
  exact congrArg f (dipoleOrbit_add_mul_quarter h0 h1 k t)

/-- The height `β_h(a) = arccos(h / cos a)` of the quarter orbit over `a`. -/
def quarterHeight (h a : ℝ) : ℝ := arccos (h / cos a)

/-- The quarter orbit approaches the arc `b = π/2` (`lem:quarter-height-limit`): for
    `0 ≤ h ≤ cos a`, `0 ≤ π/2 - β_h(a) ≤ (π/2) h / cos a`, since `π/2 - arccos z = arcsin z` and
    `arcsin z ≤ (π/2) z` on `[0, 1]` (Jordan's inequality `sin x ≥ (2/π) x`). -/
theorem pi_div_two_sub_quarterHeight_le {h a : ℝ} (h0 : 0 ≤ h) (hc0 : 0 < cos a)
    (hc : h ≤ cos a) :
    0 ≤ π / 2 - quarterHeight h a ∧ π / 2 - quarterHeight h a ≤ π / 2 * (h / cos a) := by
  set z := h / cos a with hz
  have hz0 : 0 ≤ z := div_nonneg h0 hc0.le
  have hz1 : z ≤ 1 := (div_le_one hc0).2 hc
  rw [quarterHeight, ← hz, arccos_eq_pi_div_two_sub_arcsin, sub_sub_cancel]
  have hx0 : 0 ≤ arcsin z := arcsin_nonneg.2 hz0
  have hj := mul_le_sin hx0 (arcsin_le_pi_div_two z)
  rw [sin_arcsin (by linarith) hz1] at hj
  refine ⟨hx0, ?_⟩
  calc arcsin z = π / 2 * (2 / π * arcsin z) := by field_simp
    _ ≤ π / 2 * z := by gcongr

/-- Uniform version: on `|a| ≤ π/2 - δ`, `cos a ≥ sin δ`, so
    `0 ≤ π/2 - β_h(a) ≤ (π/2) h / sin δ` for `h ≤ sin δ`. -/
theorem pi_div_two_sub_quarterHeight_le_of_abs_le {h a δ : ℝ} (h0 : 0 ≤ h) (hδ : 0 < δ)
    (hδπ : δ ≤ π / 2) (ha : |a| ≤ π / 2 - δ) (hh : h ≤ sin δ) :
    0 ≤ π / 2 - quarterHeight h a ∧ π / 2 - quarterHeight h a ≤ π / 2 * (h / sin δ) := by
  have hsin : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ (by linarith [pi_pos])
  have hcos : sin δ ≤ cos a := by
    rw [← cos_abs, ← cos_pi_div_two_sub]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith [pi_pos]) ha
  obtain ⟨hlo, hhi⟩ := pi_div_two_sub_quarterHeight_le h0 (hsin.trans_le hcos) (hh.trans hcos)
  refine ⟨hlo, hhi.trans ?_⟩
  gcongr

/-- The flow-time weight on the quarter orbit (`lem:quarter-weight`): for `0 ≤ h ≤ cos² a`
    (that is, `|a| ≤ arccos √h`), `cos² a - h² ≥ cos² a - cos⁴ a = cos² a sin² a`, so
    `1/√(cos² a - h²) ≤ 1/(cos a |sin a|)`. -/
theorem one_div_sqrt_cos_sq_sub_le {h a : ℝ} (h0 : 0 ≤ h) (hc : 0 < cos a) (hh : h ≤ cos a ^ 2)
    (hs : sin a ≠ 0) : 1 / √(cos a ^ 2 - h ^ 2) ≤ 1 / (cos a * |sin a|) := by
  have hs' : 0 < |sin a| := abs_pos.2 hs
  have hprod : 0 < cos a * |sin a| := mul_pos hc hs'
  have hlow : (cos a * |sin a|) ^ 2 ≤ cos a ^ 2 - h ^ 2 := by
    rw [mul_pow, sq_abs]
    have h2 : h ^ 2 ≤ (cos a ^ 2) ^ 2 := pow_le_pow_left₀ h0 hh 2
    nlinarith [sin_sq_add_cos_sq a]
  apply one_div_le_one_div_of_le hprod
  rw [← Real.sqrt_sq hprod.le]
  exact Real.sqrt_le_sqrt hlow

/-- Near the corners, where `|sin a| ≥ 1/2`, the weight is at most `2 / cos a`: in `u = cos a`,
    `dt ≤ 2 da / u`. -/
theorem one_div_sqrt_cos_sq_sub_le_corner {h a : ℝ} (h0 : 0 ≤ h) (hc : 0 < cos a)
    (hh : h ≤ cos a ^ 2) (hs : 1 / 2 ≤ |sin a|) : 1 / √(cos a ^ 2 - h ^ 2) ≤ 2 / cos a := by
  have hs0 : sin a ≠ 0 := fun h ↦ by rw [h, abs_zero] at hs; linarith
  refine (one_div_sqrt_cos_sq_sub_le h0 hc hh hs0).trans ?_
  rw [div_le_div_iff₀ (mul_pos hc (abs_pos.2 hs0)) hc]
  nlinarith

theorem orbitB_pos_of_abs_le (h0 : 0 < h) (h1 : h < 1) {t : ℝ} (ht : |t| ≤ eighthPeriod h) :
    0 < orbitB h t := by
  rcases le_total 0 t with h0t | h0t
  · exact orbitB_pos h0 h1 ⟨h0t, (le_abs_self t).trans ht⟩
  · rw [← orbitB_neg']
    exact orbitB_pos h0 h1 ⟨by linarith, (neg_le_abs t).trans ht⟩

theorem dipoleOrbit_eq_diagInv (h t : ℝ) :
    dipoleOrbit h t = diagInv (orbitA h t, orbitB h t) := by
  simp only [orbitA, orbitB, diagCoord, diagInv_apply]
  ext <;> ring

theorem orbitB_eq_quarterHeight (h0 : 0 < h) (h1 : h < 1) {t : ℝ}
    (ht : |t| ≤ eighthPeriod h) : orbitB h t = quarterHeight h (orbitA h t) := by
  have hb := orbitB_pos_of_abs_le h0 h1 ht
  have hB := abs_lt.1 (abs_orbitB_lt h0 h1 t)
  have hca := cos_orbitA_pos h0 h1 t
  have hprod := cos_orbitA_mul_cos_orbitB h0 h1 t
  rw [quarterHeight, show h / cos (orbitA h t) = cos (orbitB h t) by
    field_simp; linarith, arccos_cos hb.le (by linarith [pi_pos])]

theorem hasDerivAt_orbitA_quarter (h0 : 0 < h) (h1 : h < 1) {t : ℝ}
    (ht : |t| ≤ eighthPeriod h) :
    HasDerivAt (orbitA h) (-√(cos (orbitA h t) ^ 2 - h ^ 2)) t := by
  rw [← cos_orbitA_mul_sin_orbitB h0 h1 (orbitB_pos_of_abs_le h0 h1 ht).le]
  simpa only [neg_mul] using hasDerivAt_orbitA h t

theorem strictAntiOn_orbitA (h0 : 0 < h) (h1 : h < 1) :
    StrictAntiOn (orbitA h) (Icc (-eighthPeriod h) (eighthPeriod h)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_orbitA h).continuousOn
    fun t ht ↦ ?_
  rw [interior_Icc] at ht
  have htL : |t| ≤ eighthPeriod h := abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have hb := orbitB_pos_of_abs_le h0 h1 htL
  have hB := abs_lt.1 (abs_orbitB_lt h0 h1 t)
  rw [(hasDerivAt_orbitA h t).deriv]
  have := cos_orbitA_pos h0 h1 t
  have := sin_pos_of_pos_of_lt_pi hb (by linarith [pi_pos])
  nlinarith

theorem orbitA_neg_eighthPeriod (h0 : 0 < h) (h1 : h < 1) :
    orbitA h (-eighthPeriod h) = arccos √h := by
  rw [orbitA_neg', orbitA_eighthPeriod h0 h1, neg_neg]

theorem image_orbitA_quarter (h0 : 0 < h) (h1 : h < 1) :
    orbitA h '' Ioo (-eighthPeriod h) (eighthPeriod h) = Ioo (-arccos √h) (arccos √h) := by
  have hL := (eighthPeriod_pos h0 h1).le
  rw [(continuous_orbitA h).continuousOn.image_Ioo_of_strictAntiOn (by linarith)
    (strictAntiOn_orbitA h0 h1), orbitA_eighthPeriod h0 h1, orbitA_neg_eighthPeriod h0 h1]

/-- A quarter orbit in diagonal coordinates (`lem:quarter-orbit-diagonal`):
    `∫_{-L}^{L} f(γ_h(t)) dt = ∫_{-a_h}^{a_h} f(a, β_h(a)) da / √(cos² a - h²)` with
    `a_h = arccos √h`, for every `f` (both sides are Bochner integrals). -/
theorem integral_quarter_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h0 : 0 < h) (h1 : h < 1) (f : ℝ × ℝ → E) :
    ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), f (dipoleOrbit h t) =
      ∫ a in Ioo (-arccos √h) (arccos √h),
        (1 / √(cos a ^ 2 - h ^ 2)) • f (diagInv (a, quarterHeight h a)) := by
  have hderiv : ∀ t ∈ Ioo (-eighthPeriod h) (eighthPeriod h),
      HasDerivWithinAt (orbitA h) (-√(cos (orbitA h t) ^ 2 - h ^ 2))
        (Ioo (-eighthPeriod h) (eighthPeriod h)) t := fun t ht ↦
    (hasDerivAt_orbitA_quarter h0 h1 (abs_le.2 ⟨ht.1.le, ht.2.le⟩)).hasDerivWithinAt
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv
    ((strictAntiOn_orbitA h0 h1).injOn.mono Ioo_subset_Icc_self)
    (fun a ↦ (1 / √(cos a ^ 2 - h ^ 2)) • f (diagInv (a, quarterHeight h a)))
  rw [image_orbitA_quarter h0 h1] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have htL : |t| ≤ eighthPeriod h := abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have hb := orbitB_pos_of_abs_le h0 h1 htL
  have hlt := lt_cos_orbitA h0 h1 hb.ne'
  have hpos : 0 < √(cos (orbitA h t) ^ 2 - h ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [cos_orbitA_pos h0 h1 t])
  rw [smul_smul, abs_neg, abs_of_pos hpos, mul_one_div_cancel hpos.ne', one_smul,
    ← orbitB_eq_quarterHeight h0 h1 htL, ← dipoleOrbit_eq_diagInv]

end NoEmbeddedEigenvalues
