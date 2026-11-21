import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The heteroclinic separatrix arc

Blueprint: `def:separatrix-arc`, `lem:separatrix-arc`.

`γ(s) = (2 arctan e^{-s}, 2 arctan e^{-s} - π)` is an integral curve of the dipole
velocity `(sin y, -sin x)` on the line `x - y = π`, from the saddle `(π, 0)` to
`(0, -π)`, with speed `√2 / cosh s`. The variable `ξ = tanh s` has
`dξ/ds = 1 - ξ²`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Filter
open scoped Topology

/-- The first coordinate `2 arctan e^{-s}` of the separatrix arc. -/
def arcAngle (s : ℝ) : ℝ := 2 * arctan (exp (-s))

/-- The separatrix arc `γ(s) = (2 arctan e^{-s}, 2 arctan e^{-s} - π)`. -/
def separatrixArc (s : ℝ) : ℝ × ℝ := (arcAngle s, arcAngle s - π)

/-- `cosh s = (e^{-s} + 1/e^{-s}) / 2`, in terms of `u = e^{-s}`. -/
theorem cosh_eq_exp_neg (s : ℝ) : cosh s = (exp (-s) + (exp (-s))⁻¹) / 2 := by
  rw [cosh_eq, exp_neg, inv_inv]
  ring

theorem sin_arcAngle (s : ℝ) : sin (arcAngle s) = 1 / cosh s := by
  have hu := exp_pos (-s)
  have hs : 0 < 1 + exp (-s) ^ 2 := by positivity
  have hq : √(1 + exp (-s) ^ 2) ^ 2 = 1 + exp (-s) ^ 2 := sq_sqrt hs.le
  have hne : √(1 + exp (-s) ^ 2) ≠ 0 := (sqrt_pos.2 hs).ne'
  rw [arcAngle, sin_two_mul, sin_arctan, cos_arctan, cosh_eq_exp_neg]
  field_simp
  rw [hq]
  ring

theorem hasDerivAt_arcAngle (s : ℝ) : HasDerivAt arcAngle (-(1 / cosh s)) s := by
  have h1 : HasDerivAt (fun s ↦ exp (-s)) (-exp (-s)) s := by
    simpa using (hasDerivAt_neg s).exp
  have hu := exp_pos (-s)
  convert (h1.arctan).const_mul 2 using 1
  · rfl
  · rw [cosh_eq_exp_neg]
    field_simp
    ring

/-- The velocity along `γ` is `(-1/cosh s, -1/cosh s)`. -/
theorem separatrixArc_velocity (s : ℝ) :
    (sin (separatrixArc s).2, -sin (separatrixArc s).1) = (-(1 / cosh s), -(1 / cosh s)) := by
  simp only [separatrixArc, sin_sub_pi, sin_arcAngle]

/-- `γ` is an integral curve of the velocity `(sin y, -sin x)`. -/
theorem hasDerivAt_separatrixArc (s : ℝ) :
    HasDerivAt separatrixArc
      (sin (separatrixArc s).2, -sin (separatrixArc s).1) s := by
  rw [separatrixArc_velocity]
  exact (hasDerivAt_arcAngle s).prodMk ((hasDerivAt_arcAngle s).sub_const π)


/-- The arc speed is `√2 sech s`. -/
theorem separatrixArc_speed (s : ℝ) :
    √(sin (separatrixArc s).2 ^ 2 + sin (separatrixArc s).1 ^ 2) = √2 / cosh s := by
  have hc := cosh_pos s
  simp only [separatrixArc, sin_sub_pi, sin_arcAngle]
  rw [show (-(1 / cosh s)) ^ 2 + (1 / cosh s) ^ 2 = 2 / cosh s ^ 2 by ring,
    sqrt_div (by norm_num : (0 : ℝ) ≤ 2), sqrt_sq hc.le]

/-- `γ` lies on the line `x - y = π`. -/
theorem separatrixArc_fst_sub_snd (s : ℝ) : (separatrixArc s).1 - (separatrixArc s).2 = π := by
  simp [separatrixArc]

/-- As `s → -∞`, `γ` tends to the saddle `(π, 0)`. -/
theorem tendsto_separatrixArc_atBot : Tendsto separatrixArc atBot (𝓝 (π, 0)) := by
  have he : Tendsto (fun s ↦ exp (-s)) atBot atTop :=
    tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have h : Tendsto arcAngle atBot (𝓝 π) := by
    have := (((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp he).const_mul 2)
    rwa [show 2 * (π / 2) = π by ring] at this
  have h' : Tendsto (fun s ↦ arcAngle s - π) atBot (𝓝 0) := by
    simpa using h.sub_const π
  exact h.prodMk_nhds h'

/-- As `s → +∞`, `γ` tends to the saddle `(0, -π)`. -/
theorem tendsto_separatrixArc_atTop : Tendsto separatrixArc atTop (𝓝 (0, -π)) := by
  have h : Tendsto arcAngle atTop (𝓝 0) := by
    have := ((continuous_arctan.tendsto 0).comp tendsto_exp_neg_atTop_nhds_zero).const_mul 2
    simp only [arctan_zero, mul_zero] at this
    exact this
  have h' : Tendsto (fun s ↦ arcAngle s - π) atTop (𝓝 (-π)) := by
    simpa using h.sub_const π
  exact h.prodMk_nhds h'

theorem one_sub_tanh_sq (s : ℝ) : 1 - tanh s ^ 2 = 1 / cosh s ^ 2 := by
  have hc := (cosh_pos s).ne'
  rw [tanh_eq_sinh_div_cosh]
  field_simp
  linarith [cosh_sq s]

/-- In the variable `ξ = tanh s`, `dξ = (1 - ξ²) ds`. -/
theorem hasDerivAt_tanh (s : ℝ) : HasDerivAt tanh (1 - tanh s ^ 2) s := by
  have hc := (cosh_pos s).ne'
  have h : HasDerivAt tanh ((cosh s * cosh s - sinh s * sinh s) / cosh s ^ 2) s := by
    rw [show tanh = fun x ↦ sinh x / cosh x from funext tanh_eq_sinh_div_cosh]
    exact (hasDerivAt_sinh s).div (hasDerivAt_cosh s) hc
  convert h using 1
  rw [one_sub_tanh_sq]
  field_simp
  linarith [cosh_sq s]

end NoEmbeddedEigenvalues
