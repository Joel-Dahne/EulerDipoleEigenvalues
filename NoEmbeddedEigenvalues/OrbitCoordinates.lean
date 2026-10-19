import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.DiagonalCalculus
import NoEmbeddedEigenvalues.SeparatrixArc
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Orbit coordinates and integrals over levels

Blueprint: `def:orbit-coordinates`, `lem:orbit-coordinates-inverse`, `def:action-angle`,
`def:level-integral`, `def:normal-tangent`, `def:cell-arcs`, `def:corner-chart`,
`lem:corner-coordinates`, `lem:orbit-coordinates-smooth`, `lem:action-angle-regularity`,
`lem:orbit-coordinates-area`, `lem:action-angle-chart`, `lem:coarea-level-cutoff`,
`lem:orbit-saddle-distance`, `lem:period-coarse`;
stated: `lem:orbit-comparison`, `lem:orbit-level-derivatives`,
`lem:orbit-coordinate-gradients`, `lem:orbit-time-integrals`.

On the positive cell minus its center, the orbit coordinates are the level `h = Ψ/2` and the
flow time `t` along the orbit `γ_h`, measured from its point `(a, b) = (0, arccos h)`. The
time coordinate is explicit: where `b ≥ 0` it is the flow time `∫_a^0 dα / √(cos² α - h²)` of
`DipoleFlow.lean`, and where `b < 0` the half-period rotation `(a, b) ↦ (-a, -b)` gives
`4L(h) - ∫_a^0 …`. It takes values in `[-2L(h), 6L(h))`, with a cut along `b = 0, a > 0`.
Working with this explicit inverse avoids smooth dependence of the flow on its initial
point, which Mathlib does not provide.

The inverse identities are proved, including the turning points: monotone change of variables
along the closed upper half-orbit pulls the singular quadrature back to the constant `-1`
away from the endpoints. The intermediate value theorem in `a`, together with conservation of
`cos a cos b`, gives surjectivity there; a half-period rotation treats the lower half.
The time coordinate is smooth off the cut: scale the regular incomplete integral to `[0, 1]`
and use `SmoothIntervalIntegral.lean`. Near the left turning point, a backward quarter rotation
gives the regular expression `2 L(h(p)) + timeCoord (backQuarter p)`.
Smoothness of the inverse parametrization follows from scalar implicit inversion of the regular
quadrature, then quarter rotations. Periodic functions of the angle are smooth across the cut:
negation moves the cut to a regular point and shifts the angle by `1/2` modulo an integer.
These regularity proofs do not use the area formula or parameter-dependent ODE regularity.
The area formula then follows from the smooth orbit map's constant Jacobian `2`, change of
variables on the measurable half-open orbit domain, and Tonelli/Fubini. Only the center is
removed, not the cut or the time-window endpoint graphs.

The saddle-distance estimate uses a bounded integrating factor rather than corner entry times.
On a positive half-quarter, `a ≤ 0`, `b ≥ -a` and (for `h < 1/2`) `sin b ≥ 1/2`.
Thus `exp t * cos a` increases, whereas `exp t * cos a * exp (2 sin a)` decreases.
This gives `exp (-t) ≤ cos a ≤ exp 2 * exp (-t)`; the saddle distance is between
`cos a` and `π * cos a` in the product norm. Reflection handles negative times.
At the endpoints `cos a = √h`. No coarse period estimate or other admission is used.
Conversely these endpoint cosine estimates prove `0 ≤ L(h) - log(1/h)/2 ≤ 2` for
`0 < h < 1/2`, and the exponential comparison with `√h`. The elementary bound `L ≤ 1/h`
handles the remaining levels, giving `exp L * √h ≤ exp 2` globally. The theorem
`exp_eighthPeriod_le` lives here (not in `Period.lean`) to avoid an import cycle.

Integrals over a level are in flow time, `∫_0^{S(h)} g(γ_h(t)) dt`; arclength is `ρ dt`.
Periodicity identifies this integral with the half-open orbit window, without any
integrability assumption. For coarea with a level cutoff, first truncate to the closed band;
the area formula and Fubini give integrability of the level integral, and conservation of the
level pulls the bounded measurable cutoff out of the inner time integral.
The normal and tangential derivatives use the outward normal `n = -∇Ψ/ρ` of `{Ψ > 2h}` and
the unit tangent `Y/ρ`.

The action-angle coordinates are `(h, θ)` with `θ = t/S(h) ∈ [-1/4, 3/4)`; the
parametrization `P(h, θ) = γ_h(θ S(h))` is defined on the strip `(0, 1) × ℝ` and is
`1`-periodic in `θ`, so functions in these coordinates are periodic in `θ` rather than
functions on a circle.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Set
open scoped ContDiff ENNReal

/-! ### Orbit coordinates -/

/-- The level coordinate `h = Ψ/2`. -/
def levelCoord (p : ℝ × ℝ) : ℝ := dipoleLift p / 2

/-- The flow-time coordinate: `∫_a^0 dα / √(cos² α - h²)` where `b ≥ 0`, and
    `4L(h) - ∫_a^0 dα / √(cos² α - h²)` where `b < 0`. -/
def timeCoord (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ (diagCoord p).2 then orbitTime (levelCoord p) (diagCoord p).1
  else 4 * eighthPeriod (levelCoord p) - orbitTime (levelCoord p) (diagCoord p).1

/-- The punctured cell: the open square minus the center. -/
def puncturedCell : Set (ℝ × ℝ) := cellSquare \ {0}

/-- The range of the orbit coordinates: `0 < h < 1` and `-2L(h) ≤ t < 6L(h)`. -/
def orbitDomain : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioo 0 1 ∧ q.2 ∈ Ico (-2 * eighthPeriod q.1) (6 * eighthPeriod q.1)}

/-- The open orbit annulus `{h₁ < h < h₂}` in the punctured cell. -/
def orbitAnnulus (h₁ h₂ : ℝ) : Set (ℝ × ℝ) := {p | p ∈ puncturedCell ∧ levelCoord p ∈ Ioo h₁ h₂}

/-- The angle coordinate `θ = t / S(h)`, with values in `[-1/4, 3/4)`; it is an angle
    modulo 1, with a cut where `t` has one. -/
def angleCoord (p : ℝ × ℝ) : ℝ := timeCoord p / orbitPeriod (levelCoord p)

/-- The action-angle coordinates `(h, θ)` on the punctured cell. -/
def actionAngle (p : ℝ × ℝ) : ℝ × ℝ := (levelCoord p, angleCoord p)

/-- The parametrization `(h, θ) ↦ γ_h(θ S(h))`, `1`-periodic in `θ`. -/
def actionAngleInv (q : ℝ × ℝ) : ℝ × ℝ := dipoleOrbit q.1 (q.2 * orbitPeriod q.1)

/-- The strip `0 < h < 1` of action-angle coordinates. -/
def actionStrip : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ univ

theorem levelCoord_dipoleOrbit {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    levelCoord (dipoleOrbit h t) = h := by
  rw [levelCoord, dipoleLift_dipoleOrbit h0 h1]
  ring

/-- The punctured positive cell has levels strictly between zero and one. -/
theorem levelCoord_mem_Ioo {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    levelCoord p ∈ Ioo (0 : ℝ) 1 := by
  have ha := abs_lt.1 hp.1.1
  have hb := abs_lt.1 hp.1.2
  have hca := cos_pos_of_mem_Ioo ha
  have hcb := cos_pos_of_mem_Ioo hb
  have hlevel : levelCoord p = cos (diagCoord p).1 * cos (diagCoord p).2 := by
    rw [levelCoord, dipoleLift_eq_diag]; ring
  rw [hlevel]
  refine ⟨mul_pos hca hcb, lt_of_le_of_ne ?_ ?_⟩
  · nlinarith [cos_le_one (diagCoord p).1, cos_le_one (diagCoord p).2]
  · intro he
    have hca1 : cos (diagCoord p).1 = 1 := by
      nlinarith [cos_le_one (diagCoord p).1, cos_le_one (diagCoord p).2]
    have hcb1 : cos (diagCoord p).2 = 1 := by nlinarith
    have ha0 : (diagCoord p).1 = 0 :=
      (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 hca1
    have hb0 : (diagCoord p).2 = 0 :=
      (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 hcb1
    apply hp.2
    rw [← diagInv_diagCoord p, show diagCoord p = 0 from Prod.ext ha0 hb0]
    exact map_zero diagInv

/-! #### The closed upper half-orbit, including the turning points -/

private theorem orbitA_two_eighthPeriod {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    orbitA h (2 * eighthPeriod h) = -arccos h := by
  simpa [orbitA_zero, orbitB_zero] using orbitA_add_quarter h0 h1 0

private theorem orbitB_two_eighthPeriod {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    orbitB h (2 * eighthPeriod h) = 0 := by
  simpa [orbitA_zero] using orbitB_add_quarter h0 h1 0

private theorem orbitB_pos_half {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Ioo (-2 * eighthPeriod h) (2 * eighthPeriod h)) : 0 < orbitB h t := by
  by_cases ht0 : 0 ≤ t
  · exact orbitB_pos_of_mem h0 h1 ⟨ht0, ht.2⟩
  · rw [← neg_neg t, orbitB_neg']
    exact orbitB_pos_of_mem h0 h1 ⟨by linarith, by linarith [ht.1]⟩

private theorem orbitB_nonneg_half {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Icc (-2 * eighthPeriod h) (2 * eighthPeriod h)) : 0 ≤ orbitB h t := by
  rcases eq_or_lt_of_le ht.1 with he | he
  · rw [← he, show -2 * eighthPeriod h = -(2 * eighthPeriod h) by ring,
      orbitB_neg', orbitB_two_eighthPeriod h0 h1]
  rcases eq_or_lt_of_le ht.2 with he' | he'
  · rw [he', orbitB_two_eighthPeriod h0 h1]
  · exact (orbitB_pos_half h0 h1 ⟨he, he'⟩).le

private theorem orbitTime_neg (h a : ℝ) : orbitTime h (-a) = -orbitTime h a := by
  have he := intervalIntegral.integral_comp_neg (a := -a) (b := 0)
    (fun x ↦ 1 / √(cos x ^ 2 - h ^ 2))
  calc orbitTime h (-a) = ∫ x in (0 : ℝ)..a, 1 / √(cos x ^ 2 - h ^ 2) := by
        simpa only [orbitTime, cos_neg, neg_zero, neg_neg] using he
    _ = -orbitTime h a := intervalIntegral.integral_symm _ _

/-- Monotone substitution remains valid at the turning point, where the integrand is
singular. The pulled-back integrand is `-1` on the open time interval. -/
private theorem orbitTime_orbitA_closed {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Icc 0 (2 * eighthPeriod h)) : orbitTime h (orbitA h t) = t := by
  have hb : ∀ s ∈ Ioo 0 t, 0 < orbitB h s := fun s hs ↦
    orbitB_pos_of_mem h0 h1 ⟨hs.1.le, hs.2.trans_le ht.2⟩
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := 0) (b := t) (f := orbitA h)
    (f' := fun s ↦ -cos (orbitA h s) * sin (orbitB h s))
    (g := fun a ↦ 1 / √(cos a ^ 2 - h ^ 2))
    (continuous_orbitA h).continuousOn
    (fun s _ ↦ hasDerivAt_orbitA h s) (by
      simp only [min_eq_left ht.1, max_eq_right ht.1]
      intro s hs
      rw [neg_mul, cos_orbitA_mul_sin_orbitB h0 h1 (hb s hs).le]
      exact neg_nonpos.2 (sqrt_nonneg _))
  have hint : ∫ s in (0 : ℝ)..t, ((fun a ↦ 1 / √(cos a ^ 2 - h ^ 2)) ∘ orbitA h) s *
      (-cos (orbitA h s) * sin (orbitB h s)) = ∫ _ in (0 : ℝ)..t, (-1 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hc := lt_cos_orbitA h0 h1 (hb s hs).ne'
    have hpos : 0 < √(cos (orbitA h s) ^ 2 - h ^ 2) := sqrt_pos.2 (by nlinarith)
    simp only [Function.comp_apply, neg_mul]
    rw [cos_orbitA_mul_sin_orbitB h0 h1 (hb s hs).le]
    field_simp
  rw [orbitA_zero, hint, intervalIntegral.integral_symm (orbitA h t) 0] at hcov
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg, mul_one,
    neg_inj] at hcov
  exact hcov.symm

private theorem orbitTime_orbitA_half {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Icc (-2 * eighthPeriod h) (2 * eighthPeriod h)) :
    orbitTime h (orbitA h t) = t := by
  by_cases ht0 : 0 ≤ t
  · exact orbitTime_orbitA_closed h0 h1 ⟨ht0, ht.2⟩
  · rw [← neg_neg t, orbitA_neg', orbitTime_neg,
      orbitTime_orbitA_closed h0 h1 ⟨by linarith, by linarith [ht.1]⟩]

private theorem dipoleOrbit_add_half {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    dipoleOrbit h (t + 4 * eighthPeriod h) = -dipoleOrbit h t := by
  rw [show t + 4 * eighthPeriod h = t + 2 * eighthPeriod h + 2 * eighthPeriod h by ring]
  simp only [dipoleOrbit_add_quarter h0 h1]
  rfl

/-- The orbit map inverts the orbit coordinates: `t(γ_h(t)) = t` on the orbit domain. -/
theorem timeCoord_dipoleOrbit {h t : ℝ} (hq : (h, t) ∈ orbitDomain) :
    timeCoord (dipoleOrbit h t) = t := by
  obtain ⟨hh, ht⟩ := hq
  by_cases hu : t ≤ 2 * eighthPeriod h
  · have hb := orbitB_nonneg_half hh.1 hh.2 ⟨ht.1, hu⟩
    change (if 0 ≤ orbitB h t then _ else _) = t
    rw [ite_eq_left hb, levelCoord_dipoleOrbit hh.1 hh.2]
    exact orbitTime_orbitA_half hh.1 hh.2 ⟨ht.1, hu⟩
  · let s := t - 4 * eighthPeriod h
    have hs : s ∈ Ioo (-2 * eighthPeriod h) (2 * eighthPeriod h) := by
      dsimp [s]; constructor <;> linarith [ht.2]
    have he : dipoleOrbit h t = -dipoleOrbit h s := by
      rw [show t = s + 4 * eighthPeriod h by dsimp [s]; ring]
      exact dipoleOrbit_add_half hh.1 hh.2 s
    have hA : orbitA h t = -orbitA h s := by
      simp only [orbitA, he, diagCoord, Prod.fst_neg, Prod.snd_neg]; ring
    have hB : orbitB h t = -orbitB h s := by
      simp only [orbitB, he, diagCoord, Prod.fst_neg, Prod.snd_neg]; ring
    have hb : ¬0 ≤ orbitB h t := by rw [hB]; linarith [orbitB_pos_half hh.1 hh.2 hs]
    change (if 0 ≤ orbitB h t then _ else _) = t
    rw [ite_eq_right hb, levelCoord_dipoleOrbit hh.1 hh.2]
    change 4 * eighthPeriod h - orbitTime h (orbitA h t) = t
    rw [hA, orbitTime_neg, orbitTime_orbitA_half hh.1 hh.2 (Ioo_subset_Icc_self hs)]
    dsimp [s]; ring

private theorem diagCoord_neg (p : ℝ × ℝ) : diagCoord (-p) = -diagCoord p := by
  ext <;> simp only [diagCoord, Prod.fst_neg, Prod.snd_neg] <;> ring

/-- The first diagonal coordinate traverses its whole level interval on the upper half. -/
private theorem exists_dipoleOrbit_eq_upper {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hh : levelCoord p ∈ Ioo (0 : ℝ) 1) (hb : 0 ≤ (diagCoord p).2) :
    ∃ t ∈ Icc (-2 * eighthPeriod (levelCoord p)) (2 * eighthPeriod (levelCoord p)),
      dipoleOrbit (levelCoord p) t = p := by
  let h := levelCoord p
  have hL := eighthPeriod_pos hh.1 hh.2
  have ha := abs_lt.1 hp.1
  have hbb := abs_lt.1 hp.2
  have hca : 0 < cos (diagCoord p).1 := cos_pos_of_mem_Ioo ha
  have hprod : cos (diagCoord p).1 * cos (diagCoord p).2 = h := by
    dsimp [h, levelCoord]; rw [dipoleLift_eq_diag]; ring
  have hcos : h ≤ cos (diagCoord p).1 := by
    nlinarith [mul_le_mul_of_nonneg_left (cos_le_one (diagCoord p).2) hca.le]
  have haabs : |(diagCoord p).1| ≤ arccos h := by
    have he := arccos_le_arccos hcos
    rw [← cos_abs, arccos_cos (abs_nonneg _) (by linarith [hp.1, pi_pos])] at he
    exact he
  have hend : orbitA h (-2 * eighthPeriod h) = arccos h := by
    rw [show -2 * eighthPeriod h = -(2 * eighthPeriod h) by ring,
      orbitA_neg', orbitA_two_eighthPeriod hh.1 hh.2, neg_neg]
  obtain ⟨t, ht, hAt⟩ := intermediate_value_Icc'
    (show -2 * eighthPeriod h ≤ 2 * eighthPeriod h by linarith)
    (continuous_orbitA h).continuousOn
    (show (diagCoord p).1 ∈ Icc (orbitA h (2 * eighthPeriod h))
      (orbitA h (-2 * eighthPeriod h)) by
      rw [orbitA_two_eighthPeriod hh.1 hh.2, hend]
      exact abs_le.1 haabs)
  have hBt : orbitB h t = (diagCoord p).2 := by
    apply injOn_cos ⟨orbitB_nonneg_half hh.1 hh.2 ht, by
      linarith [abs_lt.1 (abs_orbitB_lt hh.1 hh.2 t), pi_pos]⟩ ⟨hb, by linarith [pi_pos]⟩
    apply mul_left_cancel₀ hca.ne'
    rw [← hAt, cos_orbitA_mul_cos_orbitB hh.1 hh.2, hAt, hprod]
  refine ⟨t, ht, ?_⟩
  have hd : diagCoord (dipoleOrbit h t) = diagCoord p := Prod.ext hAt hBt
  simpa only [diagInv_diagCoord] using congrArg diagInv hd

/-- Every point of a positive level is reached in the chosen half-open time window. -/
private theorem exists_dipoleOrbit_eq {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    ∃ t ∈ Ico (-2 * eighthPeriod (levelCoord p)) (6 * eighthPeriod (levelCoord p)),
      dipoleOrbit (levelCoord p) t = p := by
  have hh := levelCoord_mem_Ioo hp
  have hL := eighthPeriod_pos hh.1 hh.2
  by_cases hb : 0 ≤ (diagCoord p).2
  · obtain ⟨t, ht, he⟩ := exists_dipoleOrbit_eq_upper hp.1 hh hb
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, he⟩
  · have hq : -p ∈ cellSquare := by
      simpa only [cellSquare, mem_ofPred_eq, diagCoord_neg, Prod.fst_neg, Prod.snd_neg,
        abs_neg] using hp.1
    have hl : levelCoord (-p) = levelCoord p := by
      simp [levelCoord, dipoleLift, cos_neg]
    obtain ⟨s, hs, he⟩ := exists_dipoleOrbit_eq_upper hq (by rwa [hl]) (by
      rw [diagCoord_neg, Prod.snd_neg]; linarith)
    rw [hl] at hs he
    have hBs : 0 < orbitB (levelCoord p) s := by
      rw [orbitB, he, diagCoord_neg, Prod.snd_neg]; linarith
    have hslt : s < 2 * eighthPeriod (levelCoord p) := by
      refine lt_of_le_of_ne hs.2 ?_
      intro hsEq
      rw [hsEq, orbitB_two_eighthPeriod hh.1 hh.2] at hBs
      exact lt_irrefl _ hBs
    refine ⟨s + 4 * eighthPeriod (levelCoord p), ⟨by linarith [hs.1], by linarith⟩, ?_⟩
    rw [dipoleOrbit_add_half hh.1 hh.2, he, neg_neg]

/-- The orbit coordinates take values in the orbit domain. -/
theorem mem_orbitDomain {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    (levelCoord p, timeCoord p) ∈ orbitDomain := by
  obtain ⟨t, ht, he⟩ := exists_dipoleOrbit_eq hp
  have hh := levelCoord_mem_Ioo hp
  have htime := timeCoord_dipoleOrbit (show (levelCoord p, t) ∈ orbitDomain from ⟨hh, ht⟩)
  rw [he] at htime
  exact ⟨hh, htime ▸ ht⟩

/-- The orbit coordinates invert the orbit map: `γ_{h(p)}(t(p)) = p`. -/
theorem dipoleOrbit_levelCoord_timeCoord {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    dipoleOrbit (levelCoord p) (timeCoord p) = p := by
  obtain ⟨t, ht, he⟩ := exists_dipoleOrbit_eq hp
  have htime := timeCoord_dipoleOrbit
    (show (levelCoord p, t) ∈ orbitDomain from ⟨levelCoord_mem_Ioo hp, ht⟩)
  rw [he] at htime
  rw [htime, he]

/-- The orbit coordinates are a bijection onto their half-open time domain. -/
theorem bijOn_orbitCoordinates :
    BijOn (fun p ↦ (levelCoord p, timeCoord p)) puncturedCell orbitDomain := by
  refine ⟨fun p hp ↦ mem_orbitDomain hp, ?_, ?_⟩
  · intro p hp q hq he
    exact (dipoleOrbit_levelCoord_timeCoord hp).symm.trans
      ((congrArg (fun r : ℝ × ℝ ↦ dipoleOrbit r.1 r.2) he).trans
        (dipoleOrbit_levelCoord_timeCoord hq))
  · intro q hq
    have hp : dipoleOrbit q.1 q.2 ∈ puncturedCell := by
      refine ⟨dipoleOrbit_mem_cellSquare hq.1.1 hq.1.2 _, ?_⟩
      intro he
      have hl := levelCoord_dipoleOrbit hq.1.1 hq.1.2 q.2
      rw [show dipoleOrbit q.1 q.2 = 0 from he] at hl
      norm_num [levelCoord, dipoleLift] at hl
      linarith [hq.1.2]
    exact ⟨_, hp, Prod.ext (levelCoord_dipoleOrbit hq.1.1 hq.1.2 _) (timeCoord_dipoleOrbit hq)⟩

/-! #### Local smoothness -/

open Filter Topology in
private theorem contDiffAt_orbitTime {h a : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ha : |a| < arccos h) : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ orbitTime q.1 q.2) (h, a) := by
  let Q : (ℝ × ℝ) × ℝ → ℝ := fun r ↦ cos (r.1.2 * r.2) ^ 2 - r.1.1 ^ 2
  let F : (ℝ × ℝ) × ℝ → ℝ := fun r ↦ 1 / √(Q r)
  have hQ : ContDiff ℝ ∞ Q := by dsimp [Q]; fun_prop
  have hU : IsOpen {r | 0 < Q r} := isOpen_lt continuous_const hQ.continuous
  have hF : ContDiffOn ℝ ∞ F {r | 0 < Q r} :=
    contDiffOn_const.div (hQ.contDiffOn.sqrt (fun r hr ↦ ne_of_gt hr))
      (fun r hr ↦ (sqrt_pos.2 hr).ne')
  have hi : ContDiffAt ℝ ∞ (fun q ↦ ∫ t in (0 : ℝ)..1, F (q, t)) (h, a) := by
    apply contDiffAt_integral_unitInterval hU hF
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    rcases mem_singleton_iff.1 hq with rfl
    have hat : |a * t| < arccos h := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_right (abs_nonneg a) ht.2).trans_lt ha
    have hc := lt_cos_of_abs_lt_arccos hh.1 hh.2 hat
    change 0 < cos (a * t) ^ 2 - h ^ 2
    nlinarith [hh.1]
  have hm : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ -q.2 * ∫ t in (0 : ℝ)..1, F (q, t)) (h, a) :=
    (contDiffAt_snd.neg).mul hi
  apply hm.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  have he := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun x ↦ 1 / √(cos x ^ 2 - q.1 ^ 2)) q.2
  simp only [smul_eq_mul, mul_zero, mul_one] at he
  change orbitTime q.1 q.2 = -q.2 * ∫ t in (0 : ℝ)..1, F (q, t)
  rw [orbitTime, intervalIntegral.integral_symm, ← he]
  dsimp [F, Q]; ring

private theorem isOpen_puncturedCell : IsOpen puncturedCell := by
  have h₁ : Continuous (fun q : ℝ × ℝ ↦ |(diagCoord q).1|) := by unfold diagCoord; fun_prop
  have h₂ : Continuous (fun q : ℝ × ℝ ↦ |(diagCoord q).2|) := by unfold diagCoord; fun_prop
  exact ((isOpen_lt h₁ continuous_const).inter (isOpen_lt h₂ continuous_const)).sdiff
    isClosed_singleton

private theorem contDiffAt_levelCoord (p : ℝ × ℝ) : ContDiffAt ℝ ∞ levelCoord p := by
  unfold levelCoord dipoleLift; fun_prop

private theorem contDiffAt_levelEighthPeriod {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    ContDiffAt ℝ ∞ (fun q ↦ eighthPeriod (levelCoord q)) p :=
  (contDiffOn_eighthPeriod.contDiffAt
    (Ioo_mem_nhds (levelCoord_mem_Ioo hp).1 (levelCoord_mem_Ioo hp).2)).comp p
      (contDiffAt_levelCoord p)

/-- Away from `b = 0`, the endpoint of the incomplete quadrature stays regular. -/
private theorem contDiffAt_timeCoord_of_ne {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hb : (diagCoord p).2 ≠ 0) : ContDiffAt ℝ ∞ timeCoord p := by
  have hh := levelCoord_mem_Ioo hp
  have he := dipoleOrbit_levelCoord_timeCoord hp
  have ha := orbitA_mem_of_ne hh.1 hh.2 (t := timeCoord p) (by
    simpa only [orbitB, he] using hb)
  simp only [orbitA, he] at ha
  have hdc : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ (diagCoord q).1) p := by
    unfold diagCoord; fun_prop
  have hr : ContDiffAt ℝ ∞ (fun q ↦ orbitTime (levelCoord q) (diagCoord q).1) p :=
    (contDiffAt_orbitTime hh (abs_lt.2 ha)).comp
      (g := fun q : ℝ × ℝ ↦ orbitTime q.1 q.2)
      (f := fun q ↦ (levelCoord q, (diagCoord q).1)) p
      ((contDiffAt_levelCoord p).prodMk hdc)
  have hbc : Continuous (fun q : ℝ × ℝ ↦ (diagCoord q).2) := by unfold diagCoord; fun_prop
  rcases hb.lt_or_gt with hb | hb
  · have hs := ((contDiffAt_const (c := (4 : ℝ))).mul
      (contDiffAt_levelEighthPeriod hp)).sub hr
    apply hs.congr_of_eventuallyEq
    filter_upwards [hbc.continuousAt.eventually (gt_mem_nhds hb)] with q hq
    exact ite_eq_right (not_le.mpr hq)
  · apply hr.congr_of_eventuallyEq
    filter_upwards [hbc.continuousAt.eventually (lt_mem_nhds hb)] with q hq
    exact ite_eq_left hq.le

private def backQuarter (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, p.1)

private theorem diagCoord_backQuarter (p : ℝ × ℝ) :
    diagCoord (backQuarter p) = ((diagCoord p).2, -(diagCoord p).1) := by
  ext <;> dsimp [backQuarter, diagCoord] <;> ring

private theorem backQuarter_mem {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    backQuarter p ∈ puncturedCell := by
  refine ⟨?_, ?_⟩
  · simpa only [cellSquare, mem_ofPred_eq, diagCoord_backQuarter, abs_neg] using hp.1.symm
  · intro hz
    apply hp.2
    have hz : backQuarter p = 0 := hz
    have h1 : p.1 = 0 := by simpa [backQuarter] using congrArg Prod.snd hz
    have h2 : p.2 = 0 := by simpa [backQuarter] using congrArg Prod.fst hz
    exact Prod.ext h1 h2

private theorem levelCoord_backQuarter (p : ℝ × ℝ) : levelCoord (backQuarter p) = levelCoord p := by
  simp only [levelCoord, backQuarter, dipoleLift, cos_neg]; ring

/-- On the left half of the cell, shifting back a quarter puts the point in the
regular upper patch. No angular wrap occurs in this identity. -/
private theorem timeCoord_eq_backQuarter {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (ha : (diagCoord p).1 < 0) :
    timeCoord p = 2 * eighthPeriod (levelCoord p) + timeCoord (backQuarter p) := by
  have hh := levelCoord_mem_Ioo hp
  have hL := eighthPeriod_pos hh.1 hh.2
  have hq := backQuarter_mem hp
  obtain ⟨s, hs, he⟩ := exists_dipoleOrbit_eq_upper hq.1 (levelCoord_mem_Ioo hq) (by
    rw [diagCoord_backQuarter]; exact (neg_pos.2 ha).le)
  rw [levelCoord_backQuarter] at hs he
  have hsq : (levelCoord p, s) ∈ orbitDomain := ⟨hh, hs.1, by linarith [hs.2]⟩
  have hts := timeCoord_dipoleOrbit hsq
  rw [he] at hts
  have hshift : dipoleOrbit (levelCoord p) (s + 2 * eighthPeriod (levelCoord p)) = p := by
    rw [dipoleOrbit_add_quarter hh.1 hh.2, he]
    simp [backQuarter]
  have hshiftq : (levelCoord p, s + 2 * eighthPeriod (levelCoord p)) ∈ orbitDomain :=
    ⟨hh, by linarith [hs.1], by linarith [hs.2]⟩
  have htp := timeCoord_dipoleOrbit hshiftq
  rw [hshift] at htp
  rw [htp, hts]; ring

/-- The global time coordinate is smooth off its cut. There is no uniform
    `C / saddleDist` bound for its derivative on the whole cell as the level tends to zero. -/
theorem contDiffAt_timeCoord {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) :
    ContDiffAt ℝ ∞ timeCoord p := by
  by_cases hb : (diagCoord p).2 = 0
  · have ha : (diagCoord p).1 < 0 := by
      have hnot : ¬0 < (diagCoord p).1 := fun ha ↦ hcut ⟨hb, ha⟩
      have hne : (diagCoord p).1 ≠ 0 := by
        intro ha
        apply hp.2
        rw [← diagInv_diagCoord p, show diagCoord p = 0 from Prod.ext ha hb]
        exact map_zero diagInv
      exact lt_of_le_of_ne (not_lt.1 hnot) hne
    have hq := backQuarter_mem hp
    have hqb : (diagCoord (backQuarter p)).2 ≠ 0 := by
      rw [diagCoord_backQuarter]; exact (neg_pos.2 ha).ne'
    have hr : ContDiffAt ℝ ∞ (fun q ↦ timeCoord (backQuarter q)) p :=
      (contDiffAt_timeCoord_of_ne hq hqb).comp (f := backQuarter) p (by
        unfold backQuarter; fun_prop)
    have hs : ContDiffAt ℝ ∞
        (fun q ↦ 2 * eighthPeriod (levelCoord q) + timeCoord (backQuarter q)) p :=
      ((contDiffAt_const (c := (2 : ℝ))).mul (contDiffAt_levelEighthPeriod hp)).add hr
    apply hs.congr_of_eventuallyEq
    have hac : Continuous (fun q : ℝ × ℝ ↦ (diagCoord q).1) := by unfold diagCoord; fun_prop
    filter_upwards [isOpen_puncturedCell.mem_nhds hp,
      hac.continuousAt.eventually (gt_mem_nhds ha)] with q hq hqa
    exact timeCoord_eq_backQuarter hq hqa
  · exact contDiffAt_timeCoord_of_ne hp hb

/-- The pair of orbit coordinates is smooth off the time cut. -/
theorem contDiffAt_orbitCoordinates {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) :
    ContDiffAt ℝ ∞ (fun q ↦ (levelCoord q, timeCoord q)) p :=
  (contDiffAt_levelCoord p).prodMk (contDiffAt_timeCoord hp hcut)

/-! ### The action-angle chart (`lem:action-angle-chart`) -/

theorem actionAngleInv_mem_puncturedCell {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (θ : ℝ) :
    actionAngleInv (h, θ) ∈ puncturedCell := by
  refine ⟨dipoleOrbit_mem_cellSquare h0 h1 _, fun h0' ↦ ?_⟩
  have e := dipoleLift_dipoleOrbit h0 h1 (θ * orbitPeriod h)
  rw [show dipoleOrbit h (θ * orbitPeriod h) = 0 from h0'] at e
  simp only [dipoleLift, Prod.fst_zero, Prod.snd_zero, Real.cos_zero] at e
  linarith

theorem levelCoord_actionAngleInv {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (θ : ℝ) :
    levelCoord (actionAngleInv (h, θ)) = h :=
  levelCoord_dipoleOrbit h0 h1 _

/-- The parametrization is `1`-periodic in the angle. -/
theorem actionAngleInv_add_one {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (θ : ℝ) :
    actionAngleInv (h, θ + 1) = actionAngleInv (h, θ) := by
  simp only [actionAngleInv, add_mul, one_mul]
  exact dipoleOrbit_periodic h0 h1 _

theorem actionAngleInv_actionAngle {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    actionAngleInv (actionAngle p) = p := by
  have hd := (mem_orbitDomain hp).1
  have hS : orbitPeriod (levelCoord p) ≠ 0 := (orbitPeriod_pos hd.1 hd.2).ne'
  simp only [actionAngleInv, actionAngle, angleCoord, div_mul_cancel₀ _ hS]
  exact dipoleOrbit_levelCoord_timeCoord hp

theorem actionAngle_actionAngleInv {h θ : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (hθ : θ ∈ Ico (-1 / 4 : ℝ) (3 / 4)) : actionAngle (actionAngleInv (h, θ)) = (h, θ) := by
  have hL := eighthPeriod_pos h0 h1
  have hS : orbitPeriod h ≠ 0 := (orbitPeriod_pos h0 h1).ne'
  have hq : (h, θ * orbitPeriod h) ∈ orbitDomain := by
    refine ⟨⟨h0, h1⟩, ?_, ?_⟩ <;> simp only [orbitPeriod] <;> nlinarith [hθ.1, hθ.2]
  have hl := levelCoord_actionAngleInv h0 h1 θ
  simp only [actionAngleInv] at hl
  simp only [actionAngle, angleCoord, actionAngleInv, hl, timeCoord_dipoleOrbit hq,
    mul_div_cancel_right₀ _ hS]

/-- `∂_θ` of the parametrization is `S(h) Y`. -/
theorem hasDerivAt_actionAngleInv_snd (h θ : ℝ) :
    HasDerivAt (fun θ ↦ actionAngleInv (h, θ))
      (orbitPeriod h • dipoleVelocity (actionAngleInv (h, θ))) θ := by
  exact (hasDerivAt_dipoleFlow (arccos h, -arccos h) (θ * orbitPeriod h)).scomp θ
    (hasDerivAt_mul_const (orbitPeriod h))

/-! #### Smooth inversion on a regular upper-half patch -/

private theorem hasDerivAt_orbitTime_snd {h a : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ha : |a| < arccos h) :
    HasDerivAt (orbitTime h) (-(1 / √(cos a ^ 2 - h ^ 2))) a := by
  have h0 : (0 : ℝ) ∈ Ioo (-arccos h) (arccos h) := by
    have hc := arccos_pos.2 hh.2
    constructor <;> linarith
  have hc := continuousOn_orbitTime_integrand hh.1 hh.2
  exact intervalIntegral.integral_hasDerivAt_left
    ((hc.mono (ordConnected_Ioo.uIcc_subset (abs_lt.1 ha) h0)).intervalIntegrable)
    ((by fun_prop : Measurable (fun x : ℝ ↦ 1 / √(cos x ^ 2 - h ^ 2))).stronglyMeasurable
      |>.stronglyMeasurableAtFilter)
    (hc.continuousAt (Ioo_mem_nhds (abs_lt.1 ha).1 (abs_lt.1 ha).2))

/-- Scalar implicit inversion needs only a nonzero derivative in the last variable. -/
private theorem exists_smooth_implicit_scalar {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] {f : P × ℝ → ℝ} {p : P} {a d : ℝ}
    (hf : ContDiffAt ℝ ∞ f (p, a)) (hd : HasDerivAt (fun y ↦ f (p, y)) d a) (hne : d ≠ 0) :
    ∃ φ : P → ℝ, ContDiffAt ℝ ∞ φ p ∧ φ p = a ∧
      ∀ᶠ x in nhds p, f (x, φ x) = f (p, a) := by
  let L := (fderiv ℝ f (p, a)).comp (ContinuousLinearMap.inr ℝ P ℝ)
  have hL1 : L 1 = d := by
    have hdf := ((hf.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt a
      ((hasDerivAt_const a p).prodMk (hasDerivAt_id a))
    exact hdf.unique hd
  have hLe : L = d • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext_ring
    simpa using hL1
  have hLi : L.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext_ring; simp [hLe, hne]
    · apply ContinuousLinearMap.ext_ring; simp [hLe, hne]
  exact ⟨hf.implicitFunction (by simp) hLi,
    hf.contDiffAt_implicitFunction (by simp) hLi,
    hf.implicitFunction_apply_self (by simp) hLi,
    hf.eventually_apply_implicitFunction (by simp) hLi⟩

private theorem contDiffAt_actionAngleInv_upper {h θ : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioo (-1 / 4 : ℝ) (1 / 4)) : ContDiffAt ℝ ∞ actionAngleInv (h, θ) := by
  let t := θ * orbitPeriod h
  let a := orbitA h t
  have hL := eighthPeriod_pos hh.1 hh.2
  have ht : t ∈ Ioo (-2 * eighthPeriod h) (2 * eighthPeriod h) := by
    dsimp [t, orbitPeriod]; constructor <;> nlinarith [hθ.1, hθ.2]
  have hb := orbitB_pos_half hh.1 hh.2 ht
  have ha : |a| < arccos h := abs_lt.2 (orbitA_mem_of_ne hh.1 hh.2 hb.ne')
  have hca : 0 < cos a := cos_orbitA_pos hh.1 hh.2 t
  have htime : orbitTime h a = t := orbitTime_orbitA_half hh.1 hh.2 (Ioo_subset_Icc_self ht)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun r ↦ orbitTime r.1.1 r.2 - r.1.2 * orbitPeriod r.1.1
  have hS : ContDiffAt ℝ ∞ orbitPeriod h :=
    contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hh.1 hh.2)
  have hf : ContDiffAt ℝ ∞ f ((h, θ), a) := by
    have hT := (contDiffAt_orbitTime hh ha).comp
      (g := fun q : ℝ × ℝ ↦ orbitTime q.1 q.2)
      (f := fun r : (ℝ × ℝ) × ℝ ↦ (r.1.1, r.2)) ((h, θ), a) (by fun_prop)
    have hSp := hS.comp (f := fun r : (ℝ × ℝ) × ℝ ↦ r.1.1) ((h, θ), a) (by fun_prop)
    exact hT.sub ((by fun_prop : ContDiffAt ℝ ∞
      (fun r : (ℝ × ℝ) × ℝ ↦ r.1.2) ((h, θ), a)).mul hSp)
  have hdf : HasDerivAt (fun y ↦ f ((h, θ), y)) (-(1 / √(cos a ^ 2 - h ^ 2))) a :=
    (hasDerivAt_orbitTime_snd hh ha).sub_const (θ * orbitPeriod h)
  have hpos : 0 < √(cos a ^ 2 - h ^ 2) := by
    have hc := lt_cos_of_abs_lt_arccos hh.1 hh.2 ha
    exact sqrt_pos.2 (by nlinarith [hh.1])
  obtain ⟨φ, hφ, hφ0, hφeq⟩ := exists_smooth_implicit_scalar hf hdf
    (neg_ne_zero.mpr (one_div_ne_zero hpos.ne'))
  have hf0 : f ((h, θ), a) = 0 := by dsimp [f]; rw [htime]; simp [t]
  let c : ℝ × ℝ → ℝ := fun q ↦ q.1 / cos (φ q)
  have hc0 : c (h, θ) ∈ Ioo (0 : ℝ) 1 := by
    dsimp [c]; rw [hφ0]
    exact ⟨div_pos hh.1 hca, (div_lt_one hca).2 (lt_cos_orbitA hh.1 hh.2 hb.ne')⟩
  have hc : ContDiffAt ℝ ∞ c (h, θ) :=
    contDiffAt_fst.div hφ.cos (by rw [hφ0]; exact hca.ne')
  have hβ : ContDiffAt ℝ ∞ (fun q ↦ arccos (c q)) (h, θ) :=
    (contDiffAt_arccos (by linarith [hc0.1]) (ne_of_lt hc0.2)).comp (f := c) (h, θ) hc
  let R : ℝ × ℝ → ℝ × ℝ := fun q ↦ diagInv (φ q, arccos (c q))
  have hR : ContDiffAt ℝ ∞ R (h, θ) :=
    diagInv.contDiff.contDiffAt.comp (f := fun q ↦ (φ q, arccos (c q))) (h, θ) (hφ.prodMk hβ)
  have hcB : c (h, θ) = cos (orbitB h t) := by
    dsimp [c]; rw [hφ0]
    apply (div_eq_iff hca.ne').2
    nlinarith [cos_orbitA_mul_cos_orbitB hh.1 hh.2 t]
  have hR0 : R (h, θ) = actionAngleInv (h, θ) := by
    dsimp only [R]
    rw [hφ0, hcB, arccos_cos hb.le (by linarith [abs_lt.1 (abs_orbitB_lt hh.1 hh.2 t), pi_pos])]
    exact diagInv_diagCoord _
  have hnear : ∀ᶠ q in nhds (h, θ), R q ∈ puncturedCell := by
    apply hR.continuousAt.eventually
    rw [hR0]
    exact isOpen_puncturedCell.mem_nhds (actionAngleInv_mem_puncturedCell hh.1 hh.2 θ)
  apply hR.congr_of_eventuallyEq
  filter_upwards [hnear, hc.continuousAt.eventually (Ioo_mem_nhds hc0.1 hc0.2), hφeq]
    with q hRq hcq hEq
  have hdiag : diagCoord (R q) = (φ q, arccos (c q)) := diagCoord_diagInv _
  have hcaq : cos (φ q) ≠ 0 := by
    have ha := hRq.1.1
    rw [hdiag] at ha
    exact (cos_pos_of_mem_Ioo (abs_lt.1 ha)).ne'
  have hlevel : levelCoord (R q) = q.1 := by
    rw [levelCoord, dipoleLift_eq_diag, hdiag]
    change 2 * cos (φ q) * cos (arccos (c q)) / 2 = q.1
    rw [cos_arccos (by linarith [hcq.1]) hcq.2.le]
    dsimp [c]; field_simp
  have hTime : timeCoord (R q) = q.2 * orbitPeriod q.1 := by
    rw [timeCoord, hdiag, ite_eq_left (arccos_nonneg (c q)), hlevel]
    have hEq' : orbitTime q.1 (φ q) - q.2 * orbitPeriod q.1 = 0 := by
      simpa only [f, hf0] using hEq
    linarith
  have hinv := dipoleOrbit_levelCoord_timeCoord hRq
  rw [hlevel, hTime] at hinv
  exact hinv

private theorem actionAngleInv_add_quarter {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    actionAngleInv (h, θ + 1 / 4) =
      ((actionAngleInv (h, θ)).2, -(actionAngleInv (h, θ)).1) := by
  change dipoleOrbit h ((θ + 1 / 4) * orbitPeriod h) = _
  rw [show (θ + 1 / 4) * orbitPeriod h = θ * orbitPeriod h + 2 * eighthPeriod h by
    unfold orbitPeriod; ring]
  exact dipoleOrbit_add_quarter hh.1 hh.2 _

/-- Rotation transports local smoothness between consecutive quarter patches. -/
private theorem contDiffAt_actionAngleInv_add_quarter_iff {h θ : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ actionAngleInv (h, θ + 1 / 4) ↔ ContDiffAt ℝ ∞ actionAngleInv (h, θ) := by
  have hnear (α : ℝ) : ∀ᶠ q : ℝ × ℝ in nhds (h, α), q.1 ∈ Ioo (0 : ℝ) 1 :=
    continuous_fst.continuousAt.eventually (Ioo_mem_nhds hh.1 hh.2)
  constructor
  · intro hs
    have hi : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ actionAngleInv (q.1, q.2 + 1 / 4)) (h, θ) :=
      hs.comp (f := fun q : ℝ × ℝ ↦ (q.1, q.2 + 1 / 4)) (h, θ) (by fun_prop)
    apply (hi.snd.neg.prodMk hi.fst).congr_of_eventuallyEq
    filter_upwards [hnear θ] with q hq
    simp only [actionAngleInv_add_quarter hq, neg_neg, Prod.eta]
  · intro hs
    have hs' : ContDiffAt ℝ ∞ actionAngleInv (h, (θ + 1 / 4) - 1 / 4) := by
      simpa only [add_sub_cancel_right] using hs
    have hi : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ actionAngleInv (q.1, q.2 - 1 / 4))
        (h, θ + 1 / 4) :=
      hs'.comp (f := fun q : ℝ × ℝ ↦ (q.1, q.2 - 1 / 4)) (h, θ + 1 / 4) (by fun_prop)
    apply (hi.snd.prodMk hi.fst.neg).congr_of_eventuallyEq
    filter_upwards [hnear (θ + 1 / 4)] with q hq
    simpa only [sub_add_cancel] using actionAngleInv_add_quarter hq (q.2 - 1 / 4)

/-- The parametrization is smooth on the strip. -/
theorem contDiffOn_actionAngleInv : ContDiffOn ℝ ∞ actionAngleInv actionStrip := by
  rintro ⟨h, θ⟩ hq
  apply ContDiffAt.contDiffWithinAt
  have hh : h ∈ Ioo (0 : ℝ) 1 := hq.1
  have hp : Function.Periodic (fun α : ℝ ↦ ContDiffAt ℝ ∞ actionAngleInv (h, α)) (1 / 4) := by
    intro α
    exact propext (contDiffAt_actionAngleInv_add_quarter_iff hh)
  let n : ℤ := ⌊4 * θ⌋
  have hs : ContDiffAt ℝ ∞ actionAngleInv (h, θ - (n : ℝ) * (1 / 4)) := by
    apply contDiffAt_actionAngleInv_upper hh
    have hlo := Int.floor_le (4 * θ)
    have hhi := Int.lt_floor_add_one (4 * θ)
    dsimp [n]; constructor <;> linarith
  exact hp.sub_int_mul_eq (x := θ) n ▸ hs

/-- The angle is smooth off the cut. -/
theorem contDiffAt_angleCoord {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) : ContDiffAt ℝ ∞ angleCoord p := by
  have hd := (mem_orbitDomain hp).1
  have hl : ContDiff ℝ ∞ levelCoord := by
    unfold levelCoord dipoleLift
    fun_prop
  have hS : ContDiffAt ℝ ∞ (fun q ↦ orbitPeriod (levelCoord q)) p :=
    (contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hd.1 hd.2)).comp (f := levelCoord) p
      hl.contDiffAt
  exact (contDiffAt_timeCoord hp hcut).div hS (orbitPeriod_pos hd.1 hd.2).ne'

private theorem periodic_comp_actionAngleInv {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {q : ℝ × ℝ}
    (hq : q ∈ actionStrip) : F (actionAngle (actionAngleInv q)) = F q := by
  let n : ℤ := ⌊q.2 + 1 / 4⌋
  have hnlo := Int.floor_le (q.2 + 1 / 4)
  have hnhi := Int.lt_floor_add_one (q.2 + 1 / 4)
  have hθ : q.2 - (n : ℝ) ∈ Ico (-1 / 4 : ℝ) (3 / 4) := by
    constructor <;> dsimp [n] <;> linarith
  have hp : Function.Periodic (fun θ ↦ actionAngleInv (q.1, θ)) 1 :=
    actionAngleInv_add_one hq.1.1 hq.1.2
  have hF : Function.Periodic (fun θ ↦ F (q.1, θ)) 1 := fun θ ↦ hper (q.1, θ)
  have he : actionAngleInv (q.1, q.2 - (n : ℝ)) = actionAngleInv q := by
    simpa only [mul_one] using hp.sub_int_mul_eq (x := q.2) n
  rw [← he, actionAngle_actionAngleInv hq.1.1 hq.1.2 hθ]
  simpa only [mul_one] using hF.sub_int_mul_eq (x := q.2) n

private theorem neg_mem_puncturedCell {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    -p ∈ puncturedCell := by
  refine ⟨?_, ?_⟩
  · simpa only [cellSquare, mem_ofPred_eq, diagCoord_neg, Prod.fst_neg, Prod.snd_neg,
      abs_neg] using hp.1
  · intro hz
    apply hp.2
    exact neg_eq_zero.mp (show -p = 0 from hz)

/-- Half-period rotation changes the lifted angle by one half modulo an integer. -/
private theorem periodic_comp_actionAngle_neg {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {p : ℝ × ℝ}
    (hp : p ∈ puncturedCell) :
    F (actionAngle p) = F (levelCoord p, angleCoord (-p) + 1 / 2) := by
  have hh := levelCoord_mem_Ioo hp
  have hn := neg_mem_puncturedCell hp
  have hl : levelCoord (-p) = levelCoord p := by simp [levelCoord, dipoleLift, cos_neg]
  have he : actionAngleInv (levelCoord p, angleCoord (-p) + 1 / 2) = p := by
    have hi := actionAngleInv_actionAngle hn
    change dipoleOrbit (levelCoord (-p))
      (angleCoord (-p) * orbitPeriod (levelCoord (-p))) = -p at hi
    rw [hl] at hi
    change dipoleOrbit (levelCoord p)
      ((angleCoord (-p) + 1 / 2) * orbitPeriod (levelCoord p)) = p
    rw [show (angleCoord (-p) + 1 / 2) * orbitPeriod (levelCoord p) =
        angleCoord (-p) * orbitPeriod (levelCoord p) + 4 * eighthPeriod (levelCoord p) by
      unfold orbitPeriod; ring]
    rw [dipoleOrbit_add_half hh.1 hh.2, hi, neg_neg]
  have hEq := periodic_comp_actionAngleInv hper
    (show (levelCoord p, angleCoord (-p) + 1 / 2) ∈ actionStrip from ⟨hh, mem_univ _⟩)
  rwa [he] at hEq

/-- The angle is smooth modulo 1 on the whole punctured cell: a smooth function on the strip
    that is `1`-periodic in `θ` is smooth in the original coordinates. -/
theorem contDiffOn_comp_actionAngle {F : ℝ × ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F actionStrip)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) :
    ContDiffOn ℝ ∞ (F ∘ actionAngle) puncturedCell := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hh := levelCoord_mem_Ioo hp
  have hstrip : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  by_cases hcut : (diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1
  · have hn := neg_mem_puncturedCell hp
    have hncut : ¬((diagCoord (-p)).2 = 0 ∧ 0 < (diagCoord (-p)).1) := by
      rw [diagCoord_neg]
      simp only [Prod.fst_neg, Prod.snd_neg]
      intro hc
      linarith [hcut.2]
    have hθ : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ angleCoord (-q) + 1 / 2) p :=
      ((contDiffAt_angleCoord hn hncut).comp (f := fun q : ℝ × ℝ ↦ -q) p
        (by fun_prop)).add (contDiffAt_const (c := (1 / 2 : ℝ)))
    have hmap : ContDiffAt ℝ ∞
        (fun q ↦ (levelCoord q, angleCoord (-q) + 1 / 2)) p :=
      (contDiffAt_levelCoord p).prodMk hθ
    have hs : ContDiffAt ℝ ∞
        (fun q ↦ F (levelCoord q, angleCoord (-q) + 1 / 2)) p :=
      (hF.contDiffAt (hstrip.mem_nhds ⟨hh, mem_univ _⟩)).comp
        (f := fun q ↦ (levelCoord q, angleCoord (-q) + 1 / 2)) p hmap
    apply hs.congr_of_eventuallyEq
    filter_upwards [isOpen_puncturedCell.mem_nhds hp] with q hq
    exact periodic_comp_actionAngle_neg hper hq
  · exact (hF.contDiffAt (hstrip.mem_nhds ⟨hh, mem_univ _⟩)).comp
      (f := actionAngle) p ((contDiffAt_levelCoord p).prodMk (contDiffAt_angleCoord hp hcut))

/-! ### The area formula -/

private theorem contDiffAt_orbitMap {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) (h, t) := by
  have hS := contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hh.1 hh.2)
  have hSp : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ orbitPeriod q.1) (h, t) :=
    hS.comp (f := Prod.fst) (h, t) contDiffAt_fst
  have hmap : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ (q.1, q.2 / orbitPeriod q.1)) (h, t) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.div hSp (orbitPeriod_pos hh.1 hh.2).ne')
  have hP := contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (h, t / orbitPeriod h) ∈ actionStrip from ⟨hh, mem_univ _⟩))
  have hc := hP.comp (f := fun q : ℝ × ℝ ↦ (q.1, q.2 / orbitPeriod q.1)) (h, t) hmap
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (Ioo_mem_nhds hh.1 hh.2)] with q hq
  change dipoleOrbit q.1 q.2 = dipoleOrbit q.1 ((q.2 / orbitPeriod q.1) * orbitPeriod q.1)
  rw [div_mul_cancel₀ _ (orbitPeriod_pos hq.1 hq.2).ne']

/-- Conservation of the level fixes the normal column, and the flow fixes the time column. -/
private theorem det_fderiv_orbitMap {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) (h, t)).det = 2 := by
  let G : ℝ × ℝ → ℝ × ℝ := fun q ↦ dipoleOrbit q.1 q.2
  let A := fderiv ℝ G (h, t)
  have hd : HasFDerivAt G A (h, t) :=
    ((contDiffAt_orbitMap hh).differentiableAt (by simp)).hasFDerivAt
  have htime : A (0, 1) = dipoleVelocity (G (h, t)) := by
    have hc := hd.comp_hasDerivAt t ((hasDerivAt_const t h).prodMk (hasDerivAt_id t))
    exact hc.unique (hasDerivAt_dipoleFlow (arccos h, -arccos h) t)
  have hcol := hd.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h t))
  have hdx : HasDerivAt (fun s ↦ (G (s, t)).1) (A (1, 0)).1 h :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt h hcol
  have hdy : HasDerivAt (fun s ↦ (G (s, t)).2) (A (1, 0)).2 h :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt h hcol
  have hlevel := (hdx.cos.add hdy.cos).div_const 2
  have he : (fun s ↦ (cos (G (s, t)).1 + cos (G (s, t)).2) / 2) =ᶠ[nhds h] id := by
    filter_upwards [Ioo_mem_nhds hh.1 hh.2] with s hs
    exact levelCoord_dipoleOrbit hs.1 hs.2 t
  have hnormal := (hlevel.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id h)
  change LinearMap.det (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = 2
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change (A (1, 0)).1 * (A (0, 1)).2 - (A (0, 1)).1 * (A (1, 0)).2 = 2
  rw [htime]
  dsimp [dipoleVelocity] at *
  linarith

/-- Measurability of the period, including the total integral values outside `(0,1)`. -/
theorem measurable_eighthPeriod : Measurable eighthPeriod := by
  let A : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ Real.arccos (√q.1)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  have hm : Measurable (fun q : ℝ × ℝ ↦ 1 / √(cos q.2 ^ 2 - q.1 ^ 2)) := by fun_prop
  have hh := (hm.indicator hA).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hh.measurable using 1
  funext h
  rw [eighthPeriod, intervalIntegral.integral_of_le (Real.arccos_nonneg _)]
  rw [← integral_indicator measurableSet_Ioc]
  rfl

private theorem measurableSet_orbitDomain : MeasurableSet orbitDomain := by
  exact (measurableSet_Ioo.preimage measurable_fst).inter
    ((measurableSet_le (measurable_const.mul (measurable_eighthPeriod.comp measurable_fst))
      measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_const.mul (measurable_eighthPeriod.comp measurable_fst))))

private theorem orbitMap_hasFDerivWithin (q : ℝ × ℝ) (hq : q ∈ orbitDomain) :
    HasFDerivWithinAt (fun r : ℝ × ℝ ↦ dipoleOrbit r.1 r.2)
      (fderiv ℝ (fun r : ℝ × ℝ ↦ dipoleOrbit r.1 r.2) q) orbitDomain q :=
  ((contDiffAt_orbitMap hq.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt

private theorem injOn_orbitMap : InjOn (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) orbitDomain := by
  intro q hq r hr he
  have ht := congrArg timeCoord he
  rw [timeCoord_dipoleOrbit hq, timeCoord_dipoleOrbit hr] at ht
  have hl := congrArg levelCoord he
  rw [levelCoord_dipoleOrbit hq.1.1 hq.1.2, levelCoord_dipoleOrbit hr.1.1 hr.1.2] at hl
  exact Prod.ext hl ht

private theorem image_orbitMap :
    (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) '' orbitDomain = puncturedCell := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hp := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 (q.2 / orbitPeriod q.1)
    simpa only [actionAngleInv, div_mul_cancel₀ _ (orbitPeriod_pos hq.1.1 hq.1.2).ne'] using hp
  · intro hp
    exact ⟨(levelCoord p, timeCoord p), mem_orbitDomain hp, dipoleOrbit_levelCoord_timeCoord hp⟩

private theorem puncturedCell_ae_eq : puncturedCell =ᵐ[volume] cellSquare := by
  have h0 : (volume : Measure (ℝ × ℝ)) {(0 : ℝ × ℝ)} = 0 := by
    rw [Measure.volume_eq_prod]; simp
  exact sdiff_null_ae_eq_self h0

private theorem lintegral_orbitDomain {g : ℝ × ℝ → ℝ≥0∞}
    (hg : Measurable (orbitDomain.indicator g)) :
    ∫⁻ q in orbitDomain, g q =
      ∫⁻ h in Ioo (0 : ℝ) 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), g (h, t) := by
  rw [← lintegral_indicator measurableSet_orbitDomain, Measure.volume_eq_prod,
    lintegral_prod _ hg.aemeasurable, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro h
  by_cases hh : h ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hh, ← lintegral_indicator measurableSet_Ico]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
    · rw [indicator_of_mem (show (h, t) ∈ orbitDomain from ⟨hh, ht⟩), indicator_of_mem ht]
    · rw [indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ ht hq.2),
        indicator_of_notMem ht]
  · rw [indicator_of_notMem hh]
    have hz : (fun t ↦ orbitDomain.indicator g (h, t)) = 0 := by
      ext t
      exact indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ hh hq.1) g
    rw [hz]
    exact lintegral_zero

/-- `dx dy = 2 dh dt`: integrals over the cell in orbit coordinates. -/
theorem lintegral_cellSquare_eq {f : ℝ × ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ p in cellSquare, f p =
      2 * ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := by
  classical
  let G : ℝ × ℝ → ℝ × ℝ := fun q ↦ dipoleOrbit q.1 q.2
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hGc : ContinuousOn G orbitDomain := fun q hq ↦
    (contDiffAt_orbitMap hq.1).continuousAt.continuousWithinAt
  have hGm : Measurable (orbitDomain.piecewise G (fun _ ↦ 0)) :=
    hGc.measurable_piecewise continuousOn_const measurableSet_orbitDomain
  have hm : Measurable (orbitDomain.indicator (fun q ↦ f (G q))) := by
    convert (hf.comp hGm).indicator measurableSet_orbitDomain using 1
    ext q
    by_cases hq : q ∈ orbitDomain <;> simp [indicator, piecewise, hq]
  calc (∫⁻ p in cellSquare, f p) = ∫⁻ p in puncturedCell, f p :=
        (setLIntegral_congr puncturedCell_ae_eq).symm
    _ = ∫⁻ q in orbitDomain, ENNReal.ofReal |(fderiv ℝ G q).det| * f (G q) := by
      rw [← image_orbitMap]
      exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_orbitDomain
        orbitMap_hasFDerivWithin injOn_orbitMap f
    _ = 2 * ∫⁻ q in orbitDomain, f (G q) := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      apply setLIntegral_congr_fun measurableSet_orbitDomain
      intro q hq
      have hdet : (fderiv ℝ G q).det = 2 :=
        det_fderiv_orbitMap (h := q.1) (t := q.2) hq.1
      change ENNReal.ofReal |(fderiv ℝ G q).det| * f (G q) = 2 * f (G q)
      rw [hdet]
      norm_num
    _ = 2 * ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := congrArg (2 * ·) (lintegral_orbitDomain hm)

private theorem integral_orbitDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} (hg : IntegrableOn g orbitDomain) :
    (∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun t ↦ g (h, t)) (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))) ∧
    IntegrableOn (fun h ↦ ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), g (h, t))
      (Ioo (0 : ℝ) 1) ∧
    ∫ q in orbitDomain, g q =
      ∫ h in Ioo (0 : ℝ) 1, ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), g (h, t) := by
  have hi : Integrable (orbitDomain.indicator g) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg.integrable_indicator measurableSet_orbitDomain
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hi.prod_right_ae,
      ae_restrict_mem measurableSet_Ioo] with h hh hlevel
    have he : (fun t ↦ orbitDomain.indicator g (h, t)) =
        (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)).indicator (fun t ↦ g (h, t)) := by
      ext t
      by_cases ht : t ∈ Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
      · rw [indicator_of_mem (show (h, t) ∈ orbitDomain from ⟨hlevel, ht⟩), indicator_of_mem ht]
      · rw [indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ ht hq.2),
          indicator_of_notMem ht]
    rw [he] at hh
    exact (integrable_indicator_iff measurableSet_Ico).mp hh
  · apply hi.integral_prod_left.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [← integral_indicator measurableSet_Ico]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    by_cases ht : t ∈ Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
    · rw [indicator_of_mem (show (h, t) ∈ orbitDomain from ⟨hh, ht⟩), indicator_of_mem ht]
    · rw [indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ ht hq.2),
        indicator_of_notMem ht]
  · rw [← integral_indicator measurableSet_orbitDomain, Measure.volume_eq_prod,
      integral_prod _ hi, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro h
    by_cases hh : h ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hh, ← integral_indicator measurableSet_Ico]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      by_cases ht : t ∈ Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
      · rw [indicator_of_mem (show (h, t) ∈ orbitDomain from ⟨hh, ht⟩), indicator_of_mem ht]
      · rw [indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ ht hq.2),
          indicator_of_notMem ht]
    · rw [indicator_of_notMem hh]
      change (∫ t, orbitDomain.indicator g (h, t)) = 0
      have hz : (fun t ↦ orbitDomain.indicator g (h, t)) = 0 := by
        ext t
        exact indicator_of_notMem (show (h, t) ∉ orbitDomain from fun hq ↦ hh hq.1) g
      rw [hz]
      exact integral_zero _ _

private theorem integrableOn_comp_orbitMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : IntegrableOn f cellSquare) :
    IntegrableOn (fun q : ℝ × ℝ ↦ f (dipoleOrbit q.1 q.2)) orbitDomain := by
  let G : ℝ × ℝ → ℝ × ℝ := fun q ↦ dipoleOrbit q.1 q.2
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hJ : IntegrableOn (fun q ↦ |(fderiv ℝ G q).det| • f (G q)) orbitDomain := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      measurableSet_orbitDomain orbitMap_hasFDerivWithin injOn_orbitMap f).mp
    rw [image_orbitMap]
    exact hf.mono_set sdiff_subset
  have hJ' : IntegrableOn (fun q ↦ (2 : ℝ) • f (G q)) orbitDomain := by
    apply hJ.congr
    filter_upwards [ae_restrict_mem measurableSet_orbitDomain] with q hq
    have hdet : (fderiv ℝ G q).det = 2 :=
      det_fderiv_orbitMap (h := q.1) (t := q.2) hq.1
    rw [hdet]
    norm_num
  exact (integrable_smul_iff (by norm_num : (2 : ℝ) ≠ 0) (fun q ↦ f (G q))).mp hJ'

/-- `dx dy = 2 dh dt` for integrable functions; the restriction to almost every level is
    integrable in flow time. -/
theorem integral_cellSquare_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : IntegrableOn f cellSquare) :
    (∀ᵐ h ∂(volume.restrict (Ioo 0 1)), IntegrableOn (fun t ↦ f (dipoleOrbit h t))
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))) ∧
    ∫ p in cellSquare, f p =
      (2 : ℝ) • ∫ h in Ioo 0 1, ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := by
  let G : ℝ × ℝ → ℝ × ℝ := fun q ↦ dipoleOrbit q.1 q.2
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  obtain ⟨hAE, _, hFubini⟩ := integral_orbitDomain (integrableOn_comp_orbitMap hf)
  refine ⟨hAE, ?_⟩
  calc (∫ p in cellSquare, f p) = ∫ p in puncturedCell, f p :=
        (setIntegral_congr_set puncturedCell_ae_eq).symm
    _ = ∫ q in orbitDomain, |(fderiv ℝ G q).det| • f (G q) := by
      rw [← image_orbitMap]
      exact integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_orbitDomain
        orbitMap_hasFDerivWithin injOn_orbitMap f
    _ = (2 : ℝ) • ∫ q in orbitDomain, f (G q) := by
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_orbitDomain
      intro q hq
      have hdet : (fderiv ℝ G q).det = 2 :=
        det_fderiv_orbitMap (h := q.1) (t := q.2) hq.1
      change |(fderiv ℝ G q).det| • f (G q) = (2 : ℝ) • f (G q)
      rw [hdet]
      norm_num
    _ = (2 : ℝ) • ∫ h in Ioo 0 1, ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := congrArg ((2 : ℝ) • ·) hFubini

/-- `dx dy = 2 S(h) dh dθ`. -/
theorem lintegral_cellSquare_actionAngle {f : ℝ × ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ p in cellSquare, f p =
      ∫⁻ h in Ioo 0 1, ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4),
        ENNReal.ofReal (2 * orbitPeriod h) * f (actionAngleInv (h, θ)) := by
  rw [lintegral_cellSquare_eq hf, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioo fun h hh ↦ ?_
  have hS := orbitPeriod_pos hh.1 hh.2
  have hI : (fun θ ↦ θ * orbitPeriod h) '' Ico (-1 / 4 : ℝ) (3 / 4) =
      Ico (-2 * eighthPeriod h) (6 * eighthPeriod h) := by
    rw [image_mul_right_Ico _ _ hS, orbitPeriod]
    congr 1 <;> ring
  rw [← hI, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ico
    (fun θ _ ↦ (hasDerivAt_mul_const (orbitPeriod h)).hasDerivWithinAt)
    ((mul_left_injective₀ hS.ne').injOn), ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ico fun θ _ ↦ ?_
  rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    abs_of_pos hS]
  rfl

/-! ### Integrals over levels -/

section Level

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flow-time integral `∫_0^{S(h)} g(γ_h(t)) dt` over the level `{Ψ = 2h}`. -/
def levelIntegral (h : ℝ) (g : ℝ × ℝ → E) : E :=
  ∫ t in (0 : ℝ)..orbitPeriod h, g (dipoleOrbit h t)

/-- Integrating a level over the half-open orbit window gives the same value as
    integrating from zero to the period. No integrability hypothesis is needed. -/
theorem levelIntegral_eq_integral_orbitWindow {h : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (g : ℝ × ℝ → E) :
    levelIntegral h g =
      ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), g (dipoleOrbit h t) := by
  have hp : Function.Periodic (fun t ↦ g (dipoleOrbit h t)) (orbitPeriod h) :=
    (dipoleOrbit_periodic h0 h1).comp g
  have hend : -2 * eighthPeriod h + orbitPeriod h = 6 * eighthPeriod h := by
    rw [orbitPeriod]; ring
  have hle : -2 * eighthPeriod h ≤ 6 * eighthPeriod h := by
    have hS := orbitPeriod_pos h0 h1
    rw [orbitPeriod] at hS
    linarith
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle, ← hend]
  simpa only [levelIntegral, zero_add] using
    (hp.intervalIntegral_add_eq (-2 * eighthPeriod h) 0).symm

/-- The flow-time integral `∫_{-L}^{L} g(γ_h(t)) dt` over the quarter orbit `γ_h([-L, L])`. -/
def quarterIntegral (h : ℝ) (g : ℝ × ℝ → E) : E :=
  ∫ t in (-eighthPeriod h)..eighthPeriod h, g (dipoleOrbit h t)

/-- The angular Fourier mode `g_k(h) = S(h)⁻¹ ∫_0^{S(h)} e^{-ik b(h) t} g(γ_h(t)) dt` with
    respect to the orbital frequency `b(h)`. -/
def angularMode (h : ℝ) (k : ℤ) (g : ℝ × ℝ → ℂ) : ℂ :=
  (orbitPeriod h : ℂ)⁻¹ *
    ∫ t in (0 : ℝ)..orbitPeriod h, Complex.exp (-(Complex.I * k * orbitFrequency h * t)) *
      g (dipoleOrbit h t)

end Level

/-! ### Coarea with a cutoff in the level (`lem:coarea-level-cutoff`) -/

private theorem measurableSet_levelBand (a b : ℝ) :
    MeasurableSet {p : ℝ × ℝ | levelCoord p ∈ Icc a b} :=
  measurableSet_Icc.preimage (by unfold levelCoord dipoleLift; fun_prop)

private theorem integrableOn_levelIndicator {F : ℝ × ℝ → ℝ} {a b : ℝ}
    (hF : IntegrableOn F {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b}) :
    IntegrableOn ({p | levelCoord p ∈ Icc a b}.indicator F) cellSquare := by
  rw [integrableOn_indicator_iff (measurableSet_levelBand a b)]
  have hset : {p | levelCoord p ∈ Icc a b} ∩ cellSquare =
      {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, levelCoord]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨hp, by linarith, by linarith⟩
    · rintro ⟨hp, hlo, hhi⟩
      exact ⟨⟨by linarith, by linarith⟩, hp⟩
  rw [hset]
  exact hF

private theorem levelIntegral_indicator_levelBand {h a b : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (F : ℝ × ℝ → ℝ) :
    levelIntegral h ({p | levelCoord p ∈ Icc a b}.indicator F) =
      (Icc a b).indicator (fun h ↦ levelIntegral h F) h := by
  by_cases hb : h ∈ Icc a b
  · rw [indicator_of_mem hb]
    unfold levelIntegral
    apply intervalIntegral.integral_congr
    intro t _
    exact indicator_of_mem (by simpa only [mem_ofPred_eq, levelCoord_dipoleOrbit hh.1 hh.2]
      using hb) F
  · rw [indicator_of_notMem hb]
    have hz : (fun t ↦ {p | levelCoord p ∈ Icc a b}.indicator F (dipoleOrbit h t)) = 0 := by
      ext t
      exact indicator_of_notMem (by
        simpa only [mem_ofPred_eq, levelCoord_dipoleOrbit hh.1 hh.2] using hb) F
    change (∫ t in (0 : ℝ)..orbitPeriod h,
      {p | levelCoord p ∈ Icc a b}.indicator F (dipoleOrbit h t)) = 0
    rw [hz]
    exact intervalIntegral.integral_zero

private theorem integrableOn_levelIntegral_cellSquare {F : ℝ × ℝ → ℝ}
    (hF : IntegrableOn F cellSquare) :
    IntegrableOn (fun h ↦ levelIntegral h F) (Ioo (0 : ℝ) 1) := by
  obtain ⟨_, hI, _⟩ := integral_orbitDomain (integrableOn_comp_orbitMap hF)
  apply hI.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  exact (levelIntegral_eq_integral_orbitWindow hh.1 hh.2 F).symm

/-- On a closed annulus `{2a ≤ Ψ ≤ 2b}` of the cell, the level integrals of an integrable
    function are integrable in `h ∈ [a, b]`. -/
theorem integrableOn_levelIntegral {F : ℝ × ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hF : IntegrableOn F {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b}) :
    IntegrableOn (fun h ↦ levelIntegral h F) (Icc a b) := by
  have hI := integrableOn_levelIntegral_cellSquare (integrableOn_levelIndicator hF)
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun h hh ↦
    ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩
  apply (hI.mono_set hsub).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
  rw [levelIntegral_indicator_levelBand (hsub hh), indicator_of_mem hh]

/-- Coarea with a cutoff in the level: if `φ` is bounded, measurable and vanishes outside
    `[a, b] ⊂ (0, 1)`, then `∫_cell φ(Ψ/2) F = 2 ∫_a^b φ(h) ∮_{Ψ = 2h} F dt dh`. -/
theorem integral_cellSquare_level_mul {F : ℝ × ℝ → ℝ} {φ : ℝ → ℝ} (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ s, |φ s| ≤ C) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b)
    (hF : IntegrableOn F {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b}) :
    ∫ p in cellSquare, φ (dipoleLift p / 2) * F p =
      2 * ∫ h in Icc a b, φ h * levelIntegral h F := by
  classical
  have hm : Measurable levelCoord := by unfold levelCoord dipoleLift; fun_prop
  have hw : IntegrableOn (fun p ↦ φ (levelCoord p) * F p) cellSquare := by
    have hG := (integrableOn_levelIndicator hF).bdd_mul
      (hφ.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (levelCoord p))
    apply hG.congr
    apply Filter.Eventually.of_forall
    intro p
    dsimp only [Function.comp_apply]
    by_cases hp : φ (levelCoord p) = 0
    · simp [hp]
    · rw [indicator_of_mem (show p ∈ {p | levelCoord p ∈ Icc a b} from hsupp _ hp)]
  change (∫ p in cellSquare, φ (levelCoord p) * F p) = _
  rw [(integral_cellSquare_eq hw).2]
  simp only [smul_eq_mul]
  congr 1
  calc
    (∫ h in Ioo (0 : ℝ) 1,
        ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
          φ (levelCoord (dipoleOrbit h t)) * F (dipoleOrbit h t)) =
        ∫ h in Ioo (0 : ℝ) 1, φ h * levelIntegral h F := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro h hh
      simp_rw [levelCoord_dipoleOrbit hh.1 hh.2]
      rw [integral_const_mul, ← levelIntegral_eq_integral_orbitWindow hh.1 hh.2 F]
    _ = ∫ h in Ioo (0 : ℝ) 1,
        (Icc a b).indicator (fun h ↦ φ h * levelIntegral h F) h := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro h _
      by_cases hh : h ∈ Icc a b
      · rw [indicator_of_mem hh]
      · rw [indicator_of_notMem hh]
        have hz : φ h = 0 := not_ne_iff.mp (fun hn ↦ hh (hsupp h hn))
        simp only [hz, zero_mul]
    _ = ∫ h in Icc a b, φ h * levelIntegral h F := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (show Icc a b ⊆ Ioo (0 : ℝ) 1 from
          fun h hh ↦ ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩)]

/-! ### Normal and tangential derivatives -/

/-- `ρ = |∇Ψ|`. -/
def gradNorm (p : ℝ × ℝ) : ℝ := √(sin p.1 ^ 2 + sin p.2 ^ 2)

/-- The outward normal derivative `ψₙ = ∇ψ · n` of `{Ψ > 2h}`, with `n = -∇Ψ/ρ =
    (sin x, sin y)/ρ`, for a function with partial derivatives `ψx, ψy`. -/
def normalDeriv (ψx ψy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (sin p.1 * ψx p + sin p.2 * ψy p) / gradNorm p

/-- The tangential derivative `ψₜ = ∇ψ · Y/ρ` along the flow, `Y = (sin y, -sin x)`. -/
def tangentDeriv (ψx ψy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (sin p.2 * ψx p - sin p.1 * ψy p) / gradNorm p

/-! ### The cell arcs, the saddle distance and corner coordinates -/

/-- The quarter rotation `R(x, y) = (y, -x)` on the lift. -/
def rotLift (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -p.1)

/-- The four separatrix arcs `R^k ∘ γ`, `k = 0, …, 3`, bounding the cell, parametrized by
    flow time. -/
def cellArc (k : ℕ) (s : ℝ) : ℝ × ℝ := rotLift^[k] (separatrixArc s)

/-- Time recentered on the `k`-th quarter-orbit patch: `tₖ(p) = t(R⁻ᵏ p)`. Since `R⁴ = id`,
    `R^(3k)` is `R⁻ᵏ`. On `Rᵏ(γ_h([-L(h), L(h)]))` this measures time from that arc's midpoint,
    rather than accumulating the level-dependent time spent on previous quarters. -/
def quarterTimeCoord (k : ℕ) (p : ℝ × ℝ) : ℝ := timeCoord (rotLift^[3 * k] p)

/-- The saddles `(mπ, nπ)` with `m + n` odd. -/
def saddleSet : Set (ℝ × ℝ) := {p | ∃ m n : ℤ, Odd (m + n) ∧ p = (m * π, n * π)}

/-- The distance `d` to the saddle set. -/
def saddleDist (p : ℝ × ℝ) : ℝ := Metric.infDist p saddleSet

/-- The corner chart `(u, v) ↦ (a, b) = (arccos u, arccos v)` in `(x, y)` coordinates; near the
    corner `(a, b) = (π/2, π/2)`, `u = sin α`, `v = sin β` with `α, β` the distances to the two
    edges. -/
def cornerChart (q : ℝ × ℝ) : ℝ × ℝ := diagInv (arccos q.1, arccos q.2)

/-- `Ψ/2 = uv` in corner coordinates. -/
theorem dipoleLift_cornerChart {q : ℝ × ℝ} (hu : q.1 ∈ Icc (-1) 1) (hv : q.2 ∈ Icc (-1) 1) :
    dipoleLift (cornerChart q) = 2 * q.1 * q.2 := by
  rw [dipoleLift_eq_diag, cornerChart, diagCoord_diagInv, cos_arccos hu.1 hu.2,
    cos_arccos hv.1 hv.2]

/-- The partial derivatives of the corner chart: `∂_u = -(1 - u²)^{-1/2} (1, 1)` and
    `∂_v = (1 - v²)^{-1/2} (-1, 1)`, orthogonal, so the metric is
    `2 du²/(1 - u²) + 2 dv²/(1 - v²)`. -/
theorem hasDerivAt_cornerChart {u v : ℝ} (hu : u ∈ Ioo (-1) 1) (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (fun u ↦ cornerChart (u, v)) (-(1 / √(1 - u ^ 2)), -(1 / √(1 - u ^ 2))) u ∧
      HasDerivAt (fun v ↦ cornerChart (u, v)) (-(1 / √(1 - v ^ 2)), 1 / √(1 - v ^ 2)) v := by
  have hu' := hasDerivAt_arccos (x := u) (by linarith [hu.1]) (by linarith [hu.2])
  have hv' := hasDerivAt_arccos (x := v) (by linarith [hv.1]) (by linarith [hv.2])
  constructor
  · simp only [cornerChart, diagInv_apply]
    have := (hu'.add_const (arccos v)).prodMk (hu'.sub_const (arccos v))
    simpa [neg_div] using this
  · simp only [cornerChart, diagInv_apply]
    have := (hv'.const_add (arccos u)).prodMk (hv'.const_sub (arccos u))
    simpa [neg_div] using this

/-- Along the flow, `u = cos a` satisfies `u̇ = u sin a sin b`. -/
theorem hasDerivAt_cos_diag_fst (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ cos (diagCoord (dipoleFlow x s)).1)
      (cos (diagCoord (dipoleFlow x t)).1 * (sin (diagCoord (dipoleFlow x t)).1 *
        sin (diagCoord (dipoleFlow x t)).2)) t := by
  convert (hasDerivAt_diag_fst x t).cos using 1
  ring

/-- Along the flow, `v = cos b` satisfies `v̇ = -v sin a sin b`. -/
theorem hasDerivAt_cos_diag_snd (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ cos (diagCoord (dipoleFlow x s)).2)
      (-(cos (diagCoord (dipoleFlow x t)).2 * (sin (diagCoord (dipoleFlow x t)).1 *
        sin (diagCoord (dipoleFlow x t)).2))) t := by
  convert (hasDerivAt_diag_snd x t).cos using 1
  ring

/-- On the corner `|u|, |v| ≤ 1/2` (with `a, b ∈ [0, π]`), `3/4 ≤ sin a sin b ≤ 1`, so flow
    time `dt = du / (u sin a sin b)` is comparable to `du/u`. -/
theorem sin_mul_sin_mem_of_corner {a b : ℝ} (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π)
    (hu : |cos a| ≤ 1 / 2) (hv : |cos b| ≤ 1 / 2) : sin a * sin b ∈ Icc (3 / 4) 1 := by
  have hsa := sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2
  have hsb := sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2
  have hca : cos a ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg (cos a), sq_abs (cos a)]
  have hcb : cos b ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg (cos b), sq_abs (cos b)]
  have h1 : 3 / 4 ≤ sin a ^ 2 := by nlinarith [sin_sq_add_cos_sq a]
  have h2 : 3 / 4 ≤ sin b ^ 2 := by nlinarith [sin_sq_add_cos_sq b]
  have hprod : 9 / 16 ≤ (sin a * sin b) ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul h1 h2 (by norm_num) (sq_nonneg _)]
  have hnn : 0 ≤ sin a * sin b := mul_nonneg hsa hsb
  constructor
  · nlinarith [sq_nonneg (sin a * sin b + 3 / 4)]
  · nlinarith [sin_le_one a, sin_le_one b]

/-! ### Orbits near the separatrix (`lem:orbit-comparison`, split; stated) -/

/-- On the quarter orbit, `γ_h` stays within `C√h` of the separatrix arc `γ`, both centered at
    `a = 0` at time `0`. -/
theorem orbit_close_arc : ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, ∀ t, |t| ≤ eighthPeriod h →
    ‖dipoleOrbit h t - separatrixArc t‖ ≤ C * √h := by
  sorry

/-- A saddle has vanishing cosine of its first diagonal coordinate. -/
private theorem cos_diag_fst_of_mem_saddleSet {p : ℝ × ℝ} (hp : p ∈ saddleSet) :
    cos (diagCoord p).1 = 0 := by
  obtain ⟨m, n, ⟨k, hk⟩, rfl⟩ := hp
  have he : ((m : ℝ) * π + n * π) / 2 = (k : ℝ) * π + π / 2 := by
    have hk' : (m : ℝ) + n = 2 * k + 1 := by exact_mod_cast hk
    nlinarith [congrArg (fun x : ℝ ↦ x * π) hk']
  simp only [diagCoord, he, cos_add, cos_pi_div_two, sin_pi_div_two,
    sin_int_mul_pi, mul_zero, zero_sub, zero_mul, neg_zero]

/-- The diagonal cosine is a one-Lipschitz function vanishing at every saddle. -/
private theorem cos_diag_fst_le_saddleDist (p : ℝ × ℝ) :
    cos (diagCoord p).1 ≤ saddleDist p := by
  have hne : saddleSet.Nonempty := ⟨(0, -π), 0, -1, by decide, by simp⟩
  apply (Metric.le_infDist hne).2
  intro q hq
  have hc := abs_cos_sub_cos_le (diagCoord p).1 (diagCoord q).1
  rw [cos_diag_fst_of_mem_saddleSet hq, sub_zero] at hc
  apply (le_abs_self _).trans (hc.trans ?_)
  have hx : |p.1 - q.1| ≤ dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hy : |p.2 - q.2| ≤ dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
  calc |(diagCoord p).1 - (diagCoord q).1| =
      |(p.1 - q.1) + (p.2 - q.2)| / 2 := by
        rw [show (diagCoord p).1 - (diagCoord q).1 =
          ((p.1 - q.1) + (p.2 - q.2)) / 2 by simp [diagCoord]; ring,
          abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (|p.1 - q.1| + |p.2 - q.2|) / 2 := by gcongr; exact abs_add_le _ _
    _ ≤ dist p q := by linarith

/-- Bounds from the two ends of a half-quarter. -/
private theorem orbit_half_quarter_bounds {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Icc 0 (eighthPeriod h)) :
    -arccos √h ≤ orbitA h t ∧ orbitA h t ≤ 0 ∧
      arccos √h ≤ orbitB h t ∧ orbitB h t < π / 2 := by
  have ha : ∀ s ∈ Icc 0 (eighthPeriod h), orbitA h s ≤ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · simp [orbitA_zero]
    · exact (orbitA_neg h0 h1 ⟨hs0, hs.2⟩).le
  have hb : ∀ s ∈ Icc 0 (eighthPeriod h), 0 ≤ sin (orbitB h s) := by
    intro s hs
    exact sin_nonneg_of_nonneg_of_le_pi (orbitB_pos h0 h1 hs).le
      (by linarith [abs_lt.1 (abs_orbitB_lt h0 h1 s), pi_pos])
  have hantiA : AntitoneOn (orbitA h) (Icc 0 (eighthPeriod h)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (continuous_orbitA h).continuousOn
      (fun s _ ↦ (hasDerivAt_orbitA h s).hasDerivWithinAt) (fun s hs ↦ by
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (cos_orbitA_pos h0 h1 s).le)
          (hb s (interior_subset hs)))
  have hantiB : AntitoneOn (orbitB h) (Icc 0 (eighthPeriod h)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (continuous_orbitB h).continuousOn
      (fun s _ ↦ (hasDerivAt_orbitB h s).hasDerivWithinAt) (fun s hs ↦ by
        have hs' := interior_subset hs
        exact mul_nonpos_of_nonpos_of_nonneg
          (sin_nonpos_of_nonpos_of_neg_pi_le (ha s hs')
            (by linarith [abs_lt.1 (abs_orbitA_lt h0 h1 s), pi_pos]))
          (cos_orbitB_pos h0 h1 s).le)
  have hL : eighthPeriod h ∈ Icc 0 (eighthPeriod h) :=
    ⟨(eighthPeriod_pos h0 h1).le, le_rfl⟩
  refine ⟨?_, ha t ht, ?_, (abs_lt.1 (abs_orbitB_lt h0 h1 t)).2⟩
  · simpa only [orbitA_eighthPeriod h0 h1] using hantiA ht hL ht.2
  · simpa only [orbitB_eighthPeriod h0 h1] using hantiB ht hL ht.2

/-- The geometric comparison on the positive half-quarter, in the product norm. -/
private theorem saddleDist_le_cos_orbitA {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : t ∈ Icc 0 (eighthPeriod h)) :
    saddleDist (dipoleOrbit h t) ≤ π * cos (orbitA h t) := by
  obtain ⟨ha0, ha, hb, hb1⟩ := orbit_half_quarter_bounds h0 h1 ht
  have ha1 := (abs_lt.1 (abs_orbitA_lt h0 h1 t)).1
  have hab : -orbitA h t ≤ orbitB h t := by linarith
  have hc := one_add_mul_le_cos (x := orbitA h t) ha1.le ha
  have hw : π + 2 * orbitA h t ≤ π * cos (orbitA h t) := by
    have := (mul_le_mul_of_nonneg_left hc pi_pos.le)
    field_simp at this
    nlinarith
  apply (Metric.infDist_le_dist_of_mem
    (show (0, -π) ∈ saddleSet from ⟨0, -1, by decide, by simp⟩)).trans
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have hx : (dipoleOrbit h t).1 = orbitA h t + orbitB h t := dipoleOrbit_fst h t
  have hy : (dipoleOrbit h t).2 = orbitA h t - orbitB h t := by
    simp [orbitA, orbitB, diagCoord]; ring
  rw [hx, hy]
  apply max_le <;> rw [abs_le] <;> constructor <;> linarith

/-- A bounded exponential correction gives the exact unit decay rate, without a period bound. -/
private theorem cos_orbitA_exp_bounds {h t : ℝ} (h0 : 0 < h) (h1 : h < 1 / 2)
    (ht : t ∈ Icc 0 (eighthPeriod h)) :
    exp (-t) ≤ cos (orbitA h t) ∧ cos (orbitA h t) ≤ exp 2 * exp (-t) := by
  have h1' : h < 1 := by linarith
  have hs : ∀ s ∈ Icc 0 (eighthPeriod h),
      1 / 2 ≤ sin (orbitB h s) ∧ -sin (orbitA h s) ≤ sin (orbitB h s) := by
    intro s hs
    obtain ⟨ha0, ha, hb, hb1⟩ := orbit_half_quarter_bounds h0 h1' hs
    have hb0 := (orbitB_pos h0 h1' hs).le
    have hr := sin_nonneg_of_nonneg_of_le_pi hb0 (by linarith [pi_pos])
    have hc : cos (orbitB h s) ≤ √h := by
      rw [← cos_arccos_sqrt h0 h1']
      exact cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg _) (by linarith [pi_pos]) hb
    have hcs := cos_orbitB_pos h0 h1' s
    constructor
    · nlinarith [sin_sq_add_cos_sq (orbitB h s), sq_sqrt h0.le,
        mul_self_le_mul_self hcs.le hc]
    · rw [← sin_neg]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hb1.le (by linarith)
  have hd (s : ℝ) : HasDerivAt (fun s ↦ exp s * cos (orbitA h s))
      (exp s * cos (orbitA h s) * (1 + sin (orbitA h s) * sin (orbitB h s))) s := by
    convert (hasDerivAt_exp s).mul (hasDerivAt_orbitA h s).cos using 1; ring
  have hdw (s : ℝ) : HasDerivAt
      (fun s ↦ exp s * cos (orbitA h s) * exp (2 * sin (orbitA h s)))
      (exp s * cos (orbitA h s) * exp (2 * sin (orbitA h s)) *
        (1 + sin (orbitA h s) * sin (orbitB h s) -
          2 * cos (orbitA h s) ^ 2 * sin (orbitB h s))) s := by
    convert (hd s).mul (((hasDerivAt_orbitA h s).sin.const_mul 2).exp) using 1; ring
  have hmono : MonotoneOn (fun s ↦ exp s * cos (orbitA h s))
      (Icc 0 (eighthPeriod h)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (by have := continuous_orbitA h; fun_prop) (fun s _ ↦ (hd s).hasDerivWithinAt) (fun s _ ↦ by
        have hprod : -1 ≤ sin (orbitA h s) * sin (orbitB h s) := by
          have := mul_le_mul (abs_sin_le_one (orbitA h s)) (abs_sin_le_one (orbitB h s))
            (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          rw [← abs_mul] at this
          linarith [(abs_le.1 this).1]
        exact mul_nonneg (mul_nonneg (exp_pos _).le (cos_orbitA_pos h0 h1' s).le)
          (by linarith))
  have hanti : AntitoneOn
      (fun s ↦ exp s * cos (orbitA h s) * exp (2 * sin (orbitA h s)))
      (Icc 0 (eighthPeriod h)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (by have := continuous_orbitA h; fun_prop)
      (fun s _ ↦ (hdw s).hasDerivWithinAt) (fun s hs' ↦ by
        have hs' := interior_subset hs'
        obtain ⟨hr, hsr⟩ := hs s hs'
        have ha := (orbit_half_quarter_bounds h0 h1' hs').2.1
        have hsa : sin (orbitA h s) ≤ 0 :=
          sin_nonpos_of_nonpos_of_neg_pi_le ha
            (by linarith [abs_lt.1 (abs_orbitA_lt h0 h1' s), pi_pos])
        have hdef : 1 + sin (orbitA h s) * sin (orbitB h s) ≤ cos (orbitA h s) ^ 2 := by
          nlinarith [mul_le_mul_of_nonpos_left hsr hsa, sin_sq_add_cos_sq (orbitA h s)]
        apply mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (mul_nonneg (exp_pos _).le (cos_orbitA_pos h0 h1' s).le) (exp_pos _).le)
        nlinarith [mul_nonneg (sq_nonneg (cos (orbitA h s)))
          (show 0 ≤ 2 * sin (orbitB h s) - 1 by linarith)])
  have ht0 : (0 : ℝ) ∈ Icc 0 (eighthPeriod h) := ⟨le_rfl, ht.1.trans ht.2⟩
  have hlo := hmono ht0 ht ht.1
  have hhi := hanti ht0 ht ht.1
  simp only [orbitA_zero, sin_zero, cos_zero, exp_zero, mul_one, mul_zero] at hlo hhi
  have hweight : exp (-2) ≤ exp (2 * sin (orbitA h t)) :=
    exp_le_exp.2 (by linarith [neg_one_le_sin (orbitA h t)])
  have hupper : exp t * cos (orbitA h t) * exp (-2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (exp_pos _).le (cos_orbitA_pos h0 h1' t).le)).trans hhi
  constructor
  · have := mul_le_mul_of_nonneg_left hlo (exp_pos (-t)).le
    simpa only [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul, mul_one] using this
  · have := mul_le_mul_of_nonneg_right hupper (exp_pos (2 - t)).le
    have he : exp t * exp (-2) * exp (2 - t) = 1 := by
      rw [← exp_add, ← exp_add, show t + -2 + (2 - t) = 0 by ring, exp_zero]
    have he' : exp (2 - t) = exp 2 * exp (-t) := by rw [← exp_add]; rfl
    rw [show exp t * cos (orbitA h t) * exp (-2) * exp (2 - t) =
      cos (orbitA h t) * (exp t * exp (-2) * exp (2 - t)) by ring, he, mul_one,
      one_mul, he'] at this
    exact this

/-- Reflection in the arc midpoint preserves the saddle lattice and its distance. -/
private theorem saddleDist_reflA (p : ℝ × ℝ) : saddleDist (reflA p) = saddleDist p := by
  have hmem : ∀ q ∈ saddleSet, reflA q ∈ saddleSet := by
    rintro q ⟨m, n, ho, rfl⟩
    refine ⟨-n, -m, ?_, ?_⟩
    · simpa [add_comm] using ho.neg
    · simp [reflA_apply]
  have himage : reflA '' saddleSet = saddleSet := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩; exact hmem q hq
    · intro q hq
      exact ⟨reflA q, hmem q hq, by simp⟩
  have hiso : Isometry reflA := Isometry.of_dist_eq fun p q ↦ by
    simp [reflA_apply, Prod.dist_eq, max_comm]
  unfold saddleDist
  simpa only [himage] using (Metric.infDist_image hiso (x := p) (t := saddleSet))

/-- On the quarter orbit the distance to the saddles is `d(γ_h(t)) ∼ e^{-|t|}`; at the endpoints
    `t = ±L(h)` it is `∼ √h`. -/
theorem saddleDist_dipoleOrbit : ∃ c C h₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, ∀ t,
    |t| ≤ eighthPeriod h →
      c * exp (-|t|) ≤ saddleDist (dipoleOrbit h t) ∧
        saddleDist (dipoleOrbit h t) ≤ C * exp (-|t|) := by
  refine ⟨1, π * exp 2, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro h hh t ht
  have h1 : h < 1 := by linarith [hh.2]
  have ht' : |t| ∈ Icc 0 (eighthPeriod h) := ⟨abs_nonneg t, ht⟩
  obtain ⟨hlo, hhi⟩ := cos_orbitA_exp_bounds hh.1 hh.2 ht'
  have hd : saddleDist (dipoleOrbit h t) = saddleDist (dipoleOrbit h |t|) := by
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0]
    · rw [abs_of_nonpos ht0, dipoleOrbit_neg, saddleDist_reflA]
  rw [hd, one_mul]
  refine ⟨hlo.trans (cos_diag_fst_le_saddleDist _), ?_⟩
  exact (saddleDist_le_cos_orbitA hh.1 h1 ht').trans
    (by nlinarith [mul_le_mul_of_nonneg_left hhi pi_pos.le])

/-- The quarter-orbit endpoints have saddle distance comparable to `√h`, on all levels. -/
theorem saddleDist_dipoleOrbit_endpoints {h t : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (ht : |t| = eighthPeriod h) :
    √h ≤ saddleDist (dipoleOrbit h t) ∧ saddleDist (dipoleOrbit h t) ≤ π * √h := by
  have hd : saddleDist (dipoleOrbit h t) = saddleDist (dipoleOrbit h (eighthPeriod h)) := by
    rw [← ht]
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0]
    · rw [abs_of_nonpos ht0, dipoleOrbit_neg, saddleDist_reflA]
  have hc : cos (orbitA h (eighthPeriod h)) = √h := by
    rw [orbitA_eighthPeriod h0 h1, cos_neg, cos_arccos_sqrt h0 h1]
  rw [hd]
  constructor
  · simpa only [orbitA, ← hc] using cos_diag_fst_le_saddleDist
      (dipoleOrbit h (eighthPeriod h))
  · simpa only [hc] using saddleDist_le_cos_orbitA h0 h1
      (show eighthPeriod h ∈ Icc 0 (eighthPeriod h) from
        ⟨(eighthPeriod_pos h0 h1).le, le_rfl⟩)

/-! ### Coarse period bounds from the half-quarter endpoint -/

/-- A quantified coarse logarithmic bound, independent of elliptic-integral asymptotics. -/
theorem eighthPeriod_sub_log_bounds {h : ℝ} (h0 : 0 < h) (h1 : h < 1 / 2) :
    0 ≤ eighthPeriod h - log (1 / h) / 2 ∧
      eighthPeriod h - log (1 / h) / 2 ≤ 2 := by
  have h1' : h < 1 := by linarith
  have hL : eighthPeriod h ∈ Icc 0 (eighthPeriod h) :=
    ⟨(eighthPeriod_pos h0 h1').le, le_rfl⟩
  have hu := (cos_orbitA_exp_bounds h0 h1 hL).2
  rw [orbitA_eighthPeriod h0 h1', cos_neg, cos_arccos_sqrt h0 h1', ← exp_add] at hu
  have hlog := (log_le_iff_le_exp (sqrt_pos.2 h0)).2 hu
  rw [log_sqrt h0.le] at hlog
  simp only [one_div, log_inv]
  constructor
  · have := log_le_eighthPeriod h0 h1'
    simpa only [one_div, log_inv, sub_nonneg] using this
  · linarith

/-- The full coarse logarithmic statement with explicit constants available above. -/
theorem eighthPeriod_coarse : ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧ h₀ < 1 ∧
    ∀ h ∈ Ioo 0 h₀, |eighthPeriod h - log (1 / h) / 2| ≤ C := by
  refine ⟨2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro h hh
  obtain ⟨hlo, hhi⟩ := eighthPeriod_sub_log_bounds hh.1 hh.2
  rwa [abs_of_nonneg hlo]

open Filter Topology in
/-- `L(h) → ∞` at the separatrix. -/
theorem tendsto_eighthPeriod_atTop : Tendsto eighthPeriod (𝓝[>] 0) atTop := by
  simpa [orbitPeriod] using
    tendsto_orbitPeriod_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 8)

/-- The exponential form of the two-sided coarse bound. -/
theorem exp_neg_eighthPeriod_bounds {h : ℝ} (h0 : 0 < h) (h1 : h < 1 / 2) :
    exp (-2) * √h ≤ exp (-eighthPeriod h) ∧ exp (-eighthPeriod h) ≤ √h := by
  obtain ⟨hlo, hhi⟩ := eighthPeriod_sub_log_bounds h0 h1
  simp only [one_div, log_inv] at hlo hhi
  have hroot := sqrt_pos.2 h0
  constructor
  · calc exp (-2) * √h = exp (-2 + log (√h)) := by rw [exp_add, exp_log hroot]
         _ ≤ exp (-eighthPeriod h) := by
           apply exp_le_exp.2
           rw [log_sqrt h0.le]
           linarith
  · apply (le_log_iff_exp_le hroot).1
    rw [log_sqrt h0.le]
    linarith

/-- A global upper exponential bound, with the explicit constant `e²`. -/
theorem exp_eighthPeriod_mul_sqrt_le {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    exp (eighthPeriod h) * √h ≤ exp 2 := by
  by_cases hh : h < 1 / 2
  · have hu := (cos_orbitA_exp_bounds h0 hh
      ⟨(eighthPeriod_pos h0 h1).le, le_rfl⟩).2
    rw [orbitA_eighthPeriod h0 h1, cos_neg, cos_arccos_sqrt h0 h1] at hu
    have := mul_le_mul_of_nonneg_left hu (exp_pos (eighthPeriod h)).le
    simpa only [← mul_assoc, mul_left_comm (exp (eighthPeriod h)),
      ← exp_add, add_neg_cancel, exp_zero, mul_one,
      show eighthPeriod h + (2 + -eighthPeriod h) = 2 by ring] using this
  · have hL : eighthPeriod h ≤ 2 := by
      apply (eighthPeriod_le_inv h0 h1).trans
      apply (div_le_iff₀ h0).2
      linarith
    calc exp (eighthPeriod h) * √h ≤ exp 2 * 1 :=
          mul_le_mul (exp_le_exp.2 hL) (sqrt_le_one.2 h1.le) (sqrt_nonneg _) (exp_pos _).le
       _ = exp 2 := mul_one _

/-- `e^{L(h)} ≤ C h^{-1/2}` on `(0, 1)`, proved from the orbit geometry. -/
theorem exp_eighthPeriod_le : ∃ C : ℝ, ∀ h ∈ Ioo (0 : ℝ) 1,
    exp (eighthPeriod h) ≤ C / √h := by
  exact ⟨exp 2, fun h hh ↦ (le_div_iff₀ (sqrt_pos.2 hh.1)).2
    (exp_eighthPeriod_mul_sqrt_le hh.1 hh.2)⟩

/-- `|∂_h γ_h(t)| ≤ C e^{|t|}` and `|∂_h² γ_h(t)| ≤ C e^{2|t|}` on the quarter orbit. -/
theorem deriv_dipoleOrbit_level_le : ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, ∀ t,
    |t| ≤ eighthPeriod h →
      DifferentiableAt ℝ (fun h' ↦ dipoleOrbit h' t) h ∧
      ‖deriv (fun h' ↦ dipoleOrbit h' t) h‖ ≤ C * exp |t| ∧
      DifferentiableAt ℝ (fun h' ↦ deriv (fun h'' ↦ dipoleOrbit h'' t) h') h ∧
      ‖deriv (fun h' ↦ deriv (fun h'' ↦ dipoleOrbit h'' t) h') h‖ ≤ C * exp (2 * |t|) := by
  sorry

/-- `|∇h| ≤ C d` on the cell. -/
theorem gradNorm_le_saddleDist :
    ∃ C : ℝ, ∀ p ∈ cellSquare, gradNorm p / 2 ≤ C * saddleDist p := by
  sorry

/-- The inverse-time gradient bound holds on each separately recentered quarter-orbit
    patch, not for the single global unwrapped time coordinate on the entire cell. -/
theorem norm_fderiv_quarterTimeCoord_le : ∃ C h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 ∧
    ∀ k < 4, ∀ h ∈ Ioo 0 h₀, ∀ t, |t| ≤ eighthPeriod h →
      DifferentiableAt ℝ (quarterTimeCoord k) (rotLift^[k] (dipoleOrbit h t)) ∧
        ‖fderiv ℝ (quarterTimeCoord k) (rotLift^[k] (dipoleOrbit h t))‖ ≤
          C / saddleDist (rotLift^[k] (dipoleOrbit h t)) := by
  sorry

/-- Flow-time integrals of powers of `d` over the quarter orbit. -/
theorem integral_saddleDist_rpow_le : ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀,
    ∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ (-2 : ℝ) ≤ C / h ∧
    ∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ (-4 : ℝ) ≤
      C / h ^ 2 := by
  sorry

theorem integral_saddleDist_rpow_pos_le {p : ℝ} (hp : 0 < p) : ∃ C h₀ : ℝ, 0 < h₀ ∧
    ∀ h ∈ Ioo 0 h₀,
      ∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ p ≤ C := by
  sorry

end NoEmbeddedEigenvalues
