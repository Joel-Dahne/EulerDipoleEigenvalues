import NoEmbeddedEigenvalues.DipoleFlow

/-!
# Orbit coordinates and integrals over levels

Blueprint: `def:orbit-coordinates`, `lem:orbit-coordinates` (stated), `def:level-integral`,
`def:normal-tangent`.

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

end NoEmbeddedEigenvalues
