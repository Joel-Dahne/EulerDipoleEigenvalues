import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.DiagonalCalculus
import NoEmbeddedEigenvalues.SeparatrixArc

/-!
# Orbit coordinates and integrals over levels

Blueprint: `def:orbit-coordinates`, `lem:orbit-coordinates` (stated), `def:level-integral`,
`def:normal-tangent`, `def:cell-arcs`, `def:corner-chart`, `lem:corner-coordinates`; stated:
`lem:orbit-comparison`, `lem:orbit-saddle-distance`, `lem:orbit-level-derivatives`,
`lem:orbit-coordinate-gradients`, `lem:orbit-time-integrals`.

On the positive cell minus its center, the orbit coordinates are the level `h = Ψ/2` and the
flow time `t` along the orbit `γ_h`, measured from its point `(a, b) = (0, arccos h)`. The
time coordinate is explicit: where `b ≥ 0` it is the flow time `∫_a^0 dα / √(cos² α - h²)` of
`DipoleFlow.lean`, and where `b < 0` the half-period rotation `(a, b) ↦ (-a, -b)` gives
`4L(h) - ∫_a^0 …`. It takes values in `[-2L(h), 6L(h))`, with a cut along `b = 0, a > 0`.
Working with this explicit inverse avoids smooth dependence of the flow on its initial
point, which Mathlib does not provide.

Integrals over a level are in flow time, `∫_0^{S(h)} g(γ_h(t)) dt`; arclength is `ρ dt`.
The normal and tangential derivatives use the outward normal `n = -∇Ψ/ρ` of `{Ψ > 2h}` and
the unit tangent `Y/ρ`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Set
open scoped ContDiff

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

/-- The orbit coordinates take values in the orbit domain. -/
theorem mem_orbitDomain {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    (levelCoord p, timeCoord p) ∈ orbitDomain := by
  sorry

/-- The orbit coordinates invert the orbit map: `γ_{h(p)}(t(p)) = p`. -/
theorem dipoleOrbit_levelCoord_timeCoord {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    dipoleOrbit (levelCoord p) (timeCoord p) = p := by
  sorry

/-- The orbit map inverts the orbit coordinates: `t(γ_h(t)) = t` on the orbit domain. -/
theorem timeCoord_dipoleOrbit {h t : ℝ} (hq : (h, t) ∈ orbitDomain) :
    timeCoord (dipoleOrbit h t) = t := by
  sorry

/-- The global time coordinate is smooth off its cut. There is no uniform
    `C / saddleDist` bound for its derivative on the whole cell as the level tends to zero. -/
theorem contDiffAt_timeCoord {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) :
    ContDiffAt ℝ ∞ timeCoord p := by
  sorry

theorem levelCoord_dipoleOrbit {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    levelCoord (dipoleOrbit h t) = h := by
  rw [levelCoord, dipoleLift_dipoleOrbit h0 h1]
  ring

/-- `dx dy = 2 dh dt`: integrals over the cell in orbit coordinates. -/
theorem lintegral_cellSquare_eq {f : ℝ × ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ p in cellSquare, f p =
      2 * ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := by
  sorry

/-- `dx dy = 2 dh dt` for integrable functions; the restriction to almost every level is
    integrable in flow time. -/
theorem integral_cellSquare_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : IntegrableOn f cellSquare) :
    (∀ᵐ h ∂(volume.restrict (Ioo 0 1)), IntegrableOn (fun t ↦ f (dipoleOrbit h t))
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))) ∧
    ∫ p in cellSquare, f p =
      (2 : ℝ) • ∫ h in Ioo 0 1, ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        f (dipoleOrbit h t) := by
  sorry

/-! ### Integrals over levels -/

section Level

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flow-time integral `∫_0^{S(h)} g(γ_h(t)) dt` over the level `{Ψ = 2h}`. -/
def levelIntegral (h : ℝ) (g : ℝ × ℝ → E) : E :=
  ∫ t in (0 : ℝ)..orbitPeriod h, g (dipoleOrbit h t)

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

/-- On the quarter orbit the distance to the saddles is `d(γ_h(t)) ∼ e^{-|t|}`; at the endpoints
    `t = ±L(h)` it is `∼ √h`. -/
theorem saddleDist_dipoleOrbit : ∃ c C h₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, ∀ t,
    |t| ≤ eighthPeriod h →
      c * exp (-|t|) ≤ saddleDist (dipoleOrbit h t) ∧
        saddleDist (dipoleOrbit h t) ≤ C * exp (-|t|) := by
  sorry

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
