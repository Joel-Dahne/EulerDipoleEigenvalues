import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedComparison
import NoEmbeddedEigenvalues.Analysis.Inequalities.Picone

/-!
# Regular currents for mixed Robin comparison

The ground function is positive away from the odd axis. Its classical
Picone current does not involve any boundary derivative of the test function.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set ComplexConjugate
open scoped ContDiff

/-- The logarithmic multiplier hypotheses in `(h,k)`. Smoothness includes the
regular Robin edge `k=0, h>0`, but does not prescribe derivatives at the corner. -/
structure MixedRobinMultiplier (ρ : ℝ × ℝ → ℝ) : Prop where
  smooth : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ U ∧
    ContDiffOn ℝ ∞ ρ U
  continuous : ContinuousOn ρ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  bounded : ∃ m M : ℝ, 0 < m ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
    m ≤ ρ q ∧ ρ q ≤ M
  derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |partialX ρ q| + |partialY ρ q| ≤ C * (1 + |Real.log q.1|)

/-- The actual interior comparison built from a multiplier. -/
def mixedRobinComparison (oddA : Bool) (ρ : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (if oddA then Real.sin q.1 else Real.sin q.2) * ρ (Real.cos q.1, Real.cos q.2)

/-- The cosine coordinates used in the ground function. -/
private def robinCos (q : ℝ × ℝ) : ℝ × ℝ := (Real.cos q.1, Real.cos q.2)

private theorem robinCos_mem {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2)) :
    robinCos q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  exact ⟨⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩,
    Real.cos_le_one _⟩, ⟨Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩, Real.cos_le_one _⟩⟩

private theorem robin_pos_sin {x : ℝ} (hx : x ∈ Ioc 0 (Real.pi / 2)) : 0 < Real.sin x :=
  Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt (half_lt_self Real.pi_pos))

theorem MixedRobinMultiplier.contDiffAt {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {q : ℝ × ℝ} (hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ ρ q := by
  obtain ⟨U, hU, hsub, hρU⟩ := hρ.smooth
  exact hρU.contDiffAt (hU.mem_nhds (hsub hq))

theorem MixedRobinMultiplier.pos {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {q : ℝ × ℝ} (hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : 0 < ρ q := by
  obtain ⟨m, M, hm, hb⟩ := hρ.bounded
  exact hm.trans_le (hb q ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩).1

theorem mixed_robin_ground_contDiffAt (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2)) :
    ContDiffAt ℝ ∞ (mixedRobinComparison oddA ρ) q := by
  have hr := hρ.contDiffAt (robinCos_mem hq)
  have hcos : ContDiffAt ℝ ∞ robinCos q := by unfold robinCos; fun_prop
  have hc := hr.comp q hcos
  cases oddA
  · exact (show ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sin p.2) q by fun_prop).mul hc
  · exact (show ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sin p.1) q by fun_prop).mul hc

theorem mixed_robin_ground_pos (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2))
    (haxis : 0 < if oddA then q.1 else q.2) :
    0 < mixedRobinComparison oddA ρ q := by
  have hr := hρ.pos (robinCos_mem hq)
  have ha := hq.1.2.le
  have hb := hq.2.2
  cases oddA <;> simp only [mixedRobinComparison, Bool.false_eq_true, ite_false, ite_true] at *
  · exact mul_pos (robin_pos_sin ⟨haxis, hb⟩) hr
  · exact mul_pos (robin_pos_sin ⟨haxis, ha⟩) hr

/-- The two components of the logarithmic derivative of the ground function. -/
theorem mixed_robin_ground_logPartials (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2))
    (haxis : 0 < if oddA then q.1 else q.2) :
    let g := mixedRobinComparison oddA ρ
    let p := (Real.cos q.1, Real.cos q.2)
    partialX g q / g q = (if oddA then Real.cos q.1 / Real.sin q.1 else 0) -
        Real.sin q.1 * (partialX ρ p / ρ p) ∧
    partialY g q / g q = (if oddA then 0 else Real.cos q.2 / Real.sin q.2) -
        Real.sin q.2 * (partialY ρ p / ρ p) := by
  have hr := hρ.pos (robinCos_mem hq)
  have hd := (hρ.contDiffAt (robinCos_mem hq)).differentiableAt (by simp)
  have hx : HasDerivAt (fun t ↦ ρ (robinCos (t, q.2)))
      (partialX ρ (robinCos q) * -Real.sin q.1) q.1 := by
    simpa only [Function.comp_def, robinCos] using
      (hasDerivAt_partialX hd).comp q.1 (Real.hasDerivAt_cos _)
  have hy : HasDerivAt (fun t ↦ ρ (robinCos (q.1, t)))
      (partialY ρ (robinCos q) * -Real.sin q.2) q.2 := by
    simpa only [Function.comp_def, robinCos] using
      (hasDerivAt_partialY hd).comp q.2 (Real.hasDerivAt_cos _)
  dsimp only
  cases oddA
  · have hs : Real.sin q.2 ≠ 0 := (robin_pos_sin ⟨haxis, hq.2.2⟩).ne'
    have hX : partialX (mixedRobinComparison false ρ) q = _ :=
      (hx.const_mul (Real.sin q.2)).deriv
    have hY : partialY (mixedRobinComparison false ρ) q = _ :=
      ((Real.hasDerivAt_sin q.2).mul hy).deriv
    rw [hX, hY]
    change _ / (Real.sin q.2 * ρ (robinCos q)) =
        0 - Real.sin q.1 * (partialX ρ (robinCos q) / ρ (robinCos q)) ∧
      _ / (Real.sin q.2 * ρ (robinCos q)) =
        Real.cos q.2 / Real.sin q.2 - Real.sin q.2 * (partialY ρ (robinCos q) / ρ (robinCos q))
    constructor <;> field_simp [hs, hr.ne'] <;> ring
  · have hs : Real.sin q.1 ≠ 0 := (robin_pos_sin ⟨haxis, hq.1.2.le⟩).ne'
    have hX : partialX (mixedRobinComparison true ρ) q = _ :=
      ((Real.hasDerivAt_sin q.1).mul hx).deriv
    have hY : partialY (mixedRobinComparison true ρ) q = _ :=
      (hy.const_mul (Real.sin q.1)).deriv
    rw [hX, hY]
    change _ / (Real.sin q.1 * ρ (robinCos q)) =
        Real.cos q.1 / Real.sin q.1 - Real.sin q.1 * (partialX ρ (robinCos q) / ρ (robinCos q)) ∧
      _ / (Real.sin q.1 * ρ (robinCos q)) =
        0 - Real.sin q.2 * (partialY ρ (robinCos q) / ρ (robinCos q))
    constructor <;> field_simp [hs, hr.ne'] <;> ring

/-- Horizontal component of the mixed Picone current. -/
abbrev mixedRobinCurrentA (g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ :=
  piconeCurrent₁ mixedComparisonDiagonal mixedComparisonOffDiagonal g z

/-- Vertical component of the mixed Picone current. -/
abbrev mixedRobinCurrentB (g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ :=
  piconeCurrent₂ mixedComparisonOffDiagonal mixedComparisonDiagonal g z

/-- On the regular Robin side, the outward Picone current and the form's
boundary density combine into the prescribed numerator. -/
theorem mixed_robin_top_current (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {a : ℝ} (ha : a ∈ Ioo 0 (Real.pi / 2))
    (z : ℝ × ℝ → ℂ) :
    let q := (a, Real.pi / 2)
    let h := Real.cos a
    let g := mixedRobinComparison oddA ρ
    mixedRobinCurrentB g z q + h * ‖z q‖ ^ 2 =
      mixedRobinNumerator oddA ρ h / ρ (h, 0) * ‖z q‖ ^ 2 := by
  dsimp only
  let q := (a, Real.pi / 2)
  let h := Real.cos a
  have hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2) :=
    ⟨⟨ha.1.le, ha.2⟩, ⟨(half_pos Real.pi_pos).le, le_rfl⟩⟩
  have hh : 0 < h := (robinCos_mem hq).1.1
  have hs : 0 < Real.sin a := robin_pos_sin ⟨ha.1, ha.2.le⟩
  have hr : 0 < ρ (h, 0) := hρ.pos ⟨(robinCos_mem hq).1, by simp⟩
  have hd : mixedComparisonDiagonal q = 2 - h ^ 2 := by
    unfold mixedComparisonDiagonal mixedD
    simp only [q, ← show h = Real.cos a from rfl, Real.cos_pi_div_two, add_zero]
    field_simp [hh.ne']
    ring
  have hj : mixedComparisonOffDiagonal q = 2 * Real.sin a := by
    unfold mixedComparisonOffDiagonal mixedC
    simp only [q, ← show h = Real.cos a from rfl, Real.cos_pi_div_two, Real.sin_pi_div_two,
      add_zero, mul_one]
    field_simp [hh.ne']
  have haxis : 0 < if oddA then q.1 else q.2 := by
    cases oddA <;> simp [q, ha.1, Real.pi_pos]
  obtain ⟨hx, hy⟩ := mixed_robin_ground_logPartials oddA hρ hq haxis
  have hr' : ρ (Real.cos a, 0) ≠ 0 := hr.ne'
  change mixedRobinCurrentB _ z q + h * ‖z q‖ ^ 2 = _
  unfold mixedRobinCurrentB piconeCurrent₂ piconeGroundFlux₂
  rw [add_div, mul_div_assoc, mul_div_assoc, hd, hj, hx, hy]
  simp only [mixedRobinNumerator, q, h, Real.sin_pi_div_two, Real.cos_pi_div_two,
    one_mul]
  cases oddA <;> simp only [Bool.false_eq_true, ite_false, ite_true, zero_div, zero_sub]
  all_goals
    field_simp [hs.ne', hr']
    ring_nf
    rw [Real.sin_sq a]
    ring

/-- The even axis has zero conormal current: for odd-in-b data this is
the left side, and for odd-in-a data it is the bottom. -/
theorem mixed_robin_even_axis_current {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (z : ℝ × ℝ → ℂ) :
    mixedRobinCurrentA (mixedRobinComparison false ρ) z (0, t) = 0 ∧
      mixedRobinCurrentB (mixedRobinComparison true ρ) z (t, 0) = 0 := by
  have hπ := half_pos Real.pi_pos
  have hq₁ : (0, t) ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2) :=
    ⟨⟨le_rfl, hπ⟩, ⟨ht.1.le, ht.2.le⟩⟩
  have hq₂ : (t, 0) ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2) :=
    ⟨⟨ht.1.le, ht.2⟩, ⟨le_rfl, hπ.le⟩⟩
  have h₁ := (mixed_robin_ground_logPartials false hρ hq₁ ht.1).1
  have h₂ := (mixed_robin_ground_logPartials true hρ hq₂ ht.1).2
  constructor
  · unfold mixedRobinCurrentA piconeCurrent₁ piconeGroundFlux₁
    rw [add_div, mul_div_assoc, mul_div_assoc, h₁]
    simp [mixedComparisonOffDiagonal]
  · unfold mixedRobinCurrentB piconeCurrent₂ piconeGroundFlux₂
    rw [add_div, mul_div_assoc, mul_div_assoc, h₂]
    simp [mixedComparisonOffDiagonal]

/-- The gradient and potential density, using the supplied derivatives. -/
def mixedRobinBulk (z za zb : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℝ :=
  mixedComparisonDiagonal q * (‖za q‖ ^ 2 + ‖zb q‖ ^ 2) +
    2 * mixedComparisonOffDiagonal q * (za q * conj (zb q)).re +
    mixedComparisonPotential q * ‖z q‖ ^ 2

theorem mixed_robin_coefficients_contDiffAt {n : ℕ∞ω} {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2)) :
    ContDiffAt ℝ n mixedComparisonDiagonal q ∧
      ContDiffAt ℝ n mixedComparisonOffDiagonal q := by
  have hh := (robinCos_mem hq).1.1
  have hk := (robinCos_mem hq).2.1
  have hs : 0 < Real.cos q.1 + Real.cos q.2 := add_pos_of_pos_of_nonneg hh hk
  constructor
  · unfold mixedComparisonDiagonal mixedD
    fun_prop (disch := positivity)
  · unfold mixedComparisonOffDiagonal mixedC
    fun_prop (disch := positivity)

private theorem mixed_robin_energy_nonneg {q : ℝ × ℝ} (hq : q ∈ mixedOpenCell)
    (z : ℝ × ℝ → ℂ) :
    0 ≤ piconeEnergy mixedComparisonDiagonal mixedComparisonOffDiagonal
      mixedComparisonDiagonal z q := by
  obtain ⟨hd, hdet, _⟩ := mixed_comparison_matrix_positive hq
  let d := mixedComparisonDiagonal q
  let j := mixedComparisonOffDiagonal q
  have hab : |j| ≤ d := by
    by_contra! h
    have hp : 0 < (|j| - d) * (|j| + d) := mul_pos (sub_pos.mpr h)
      (add_pos_of_nonneg_of_pos (abs_nonneg j) hd)
    nlinarith only [hp, hdet, sq_abs j]
  have hp : 0 ≤ d + j := by linarith [(abs_le.mp hab).1]
  have hm : 0 ≤ d - j := sub_nonneg.mpr (abs_le.mp hab).2
  let x := partialX z q
  let y := partialY z q
  have heq : piconeEnergy mixedComparisonDiagonal mixedComparisonOffDiagonal
      mixedComparisonDiagonal z q =
      (d + j) / 2 * ((x.re + y.re) ^ 2 + (x.im + y.im) ^ 2) +
      (d - j) / 2 * ((x.re - y.re) ^ 2 + (x.im - y.im) ^ 2) := by
    change piconeMatrixForm d j d x y = _
    simp only [piconeMatrixForm, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [heq]
  positivity

/-- Pointwise Picone inequality. It uses only the abstract supersolution
hypothesis, not the sign certificates of either explicit ground function. -/
theorem mixed_robin_picone (oddA : Bool) {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    {z : ℝ × ℝ → ℂ} (hz : ContDiffOn ℝ 1 z mixedQuarterCell)
    {q : ℝ × ℝ} (hq : q ∈ mixedQuarterCell) :
    let g := mixedRobinComparison oddA ρ
    c * Real.cos q.1 ^ 2 * ‖z q‖ ^ 2 +
        divergence (mixedRobinCurrentA g z) (mixedRobinCurrentB g z) q ≤
      mixedRobinBulk z (partialX z) (partialY z) q := by
  let g := mixedRobinComparison oddA ρ
  let d := mixedComparisonDiagonal
  let j := mixedComparisonOffDiagonal
  have hreg (p : ℝ × ℝ) (hp : p ∈ mixedQuarterCell) :
      p ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2) :=
    ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hpos (p : ℝ × ℝ) (hp : p ∈ mixedQuarterCell) : 0 < g p :=
    mixed_robin_ground_pos oddA hρ (hreg p hp)
      (by
        cases oddA
        · exact hp.2.1
        · exact hp.1.1)
  have hg : ContDiffOn ℝ 2 g mixedQuarterCell := fun p hp ↦
    ((mixed_robin_ground_contDiffAt oddA hρ (hreg p hp)).of_le (by simp)).contDiffWithinAt
  have hD : ContDiffOn ℝ 1 d mixedQuarterCell := fun p hp ↦
    (mixed_robin_coefficients_contDiffAt (hreg p hp)).1.contDiffWithinAt
  have hJ : ContDiffOn ℝ 1 j mixedQuarterCell := fun p hp ↦
    (mixed_robin_coefficients_contDiffAt (hreg p hp)).2.contDiffWithinAt
  have hP := picone_divergence (isOpen_Ioo.prod isOpen_Ioo) hD hJ hD
    (V := fun p ↦ -mixedComparisonPotential p) hg hz hpos hq
  have hres : piconeResidual d j d (fun p ↦ -mixedComparisonPotential p) g q =
      mixedComparisonOperator g q := by
    unfold piconeResidual divergence piconeGroundFlux₁ piconeGroundFlux₂
      mixedComparisonOperator
    ring
  have hbulk : piconeEnergy d j d z q - -mixedComparisonPotential q * ‖z q‖ ^ 2 =
      mixedRobinBulk z (partialX z) (partialY z) q := by
    unfold piconeEnergy piconeMatrixForm mixedRobinBulk
    dsimp only [d, j]
    ring
  rw [hres, hbulk] at hP
  change _ ≤ mixedRobinBulk z (partialX z) (partialY z) q
  rw [hP]
  have hdom : q ∈ mixedOpenCell := ⟨⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩,
    ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩⟩
  have hgrad := mul_nonneg (sq_nonneg (g q))
    (mixed_robin_energy_nonneg hdom (fun p ↦ z p / (g p : ℂ)))
  have hbound := mul_le_mul_of_nonneg_right ((le_div_iff₀ (hpos q hq)).mpr
    (hinterior q hq)) (sq_nonneg ‖z q‖)
  linarith only [hbound, hgrad]

end NoEmbeddedEigenvalues
