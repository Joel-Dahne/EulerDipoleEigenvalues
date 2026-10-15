import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The canonical transport profile

Blueprint: `def:canonical-profile`, `lem:canonical-profile-ode`; `lem:canonical-profile`
(stated, uniqueness and decay).

For a trace `g` on a separatrix arc with `g' ∈ L¹(ℝ)`, the canonical profile is
`Ω(s) = e^{iλs} ∫_s^∞ g'(t) e^{-iλt} dt` and the canonical transport unknown is
`z = -(Ω + g)/λ`. Lebesgue differentiation gives `Ω' = iλΩ - g'` almost everywhere, hence
`Pz = -Ω` and `(P - λ)z = g` for `P = -i∂ₛ` wherever `g` is differentiable. The profile
tends to `0` at `+∞`; it tends to `0` at `-∞` exactly when the Melnikov condition
`∫ g'(t) e^{-iλt} dt = 0` holds, and then it equals `-e^{iλs} ∫_{-∞}^s g'(t) e^{-iλt} dt`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Topology

/-- The integrand `g'(t) e^{-iλt}` of the canonical profile. -/
def profileIntegrand (lam : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ := deriv g t * exp (-(I * lam * t))

/-- The canonical profile `Ω(s) = e^{iλs} ∫_s^∞ g'(t) e^{-iλt} dt`. -/
def canonicalProfile (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  exp (I * lam * s) * ∫ t in Ioi s, profileIntegrand lam g t

/-- The canonical transport unknown `z = -(Ω + g)/λ`. -/
def canonicalUnknown (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  -(canonicalProfile lam g s + g s) / lam

theorem norm_exp_I_mul (lam s : ℝ) : ‖exp (I * lam * s)‖ = 1 := by
  rw [show I * lam * s = ((lam * s : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

theorem norm_exp_neg_I_mul (lam s : ℝ) : ‖exp (-(I * lam * s))‖ = 1 := by
  rw [show -(I * lam * s) = ((-(lam * s) : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

section Profile

variable {lam : ℝ} {g : ℝ → ℂ}

theorem integrable_profileIntegrand (hg : Integrable (deriv g)) :
    Integrable (profileIntegrand lam g) := by
  refine hg.mono (hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
    exp (-(I * lam * t))).aestronglyMeasurable) (Eventually.of_forall fun t ↦ ?_)
  rw [profileIntegrand, norm_mul, norm_exp_neg_I_mul, mul_one]

/-- The tail integral `∫_s^∞` as a constant minus an indefinite integral. -/
theorem integral_Ioi_profileIntegrand (hg : Integrable (deriv g)) (s : ℝ) :
    ∫ t in Ioi s, profileIntegrand lam g t =
      (∫ t in Ioi 0, profileIntegrand lam g t) - ∫ t in (0 : ℝ)..s, profileIntegrand lam g t := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  rw [← intervalIntegral.integral_interval_add_Ioi hq.integrableOn hq.integrableOn,
    intervalIntegral.integral_symm 0 s]
  ring

theorem norm_canonicalProfile (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) :
    ‖canonicalProfile lam g s‖ = ‖∫ t in Ioi s, profileIntegrand lam g t‖ := by
  rw [canonicalProfile, norm_mul, norm_exp_I_mul, one_mul]

/-- `Ω' = iλΩ - g'` almost everywhere. -/
theorem ae_hasDerivAt_canonicalProfile (hg : Integrable (deriv g)) :
    ∀ᵐ s, HasDerivAt (canonicalProfile lam g)
      (I * lam * canonicalProfile lam g s - deriv g s) s := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hq.locallyIntegrable] with s hs
  have hJ : HasDerivAt (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t)
      (-profileIntegrand lam g s) s := by
    have := (hs 0).const_sub (∫ t in Ioi 0, profileIntegrand lam g t)
    convert this using 1
    · funext s
      exact integral_Ioi_profileIntegrand hg s
  have hE : HasDerivAt (fun s : ℝ ↦ exp (I * lam * s)) (exp (I * lam * s) * (I * lam)) s := by
    have := ((hasDerivAt_id (s : ℂ)).const_mul (I * lam)).cexp.comp_ofReal
    simpa [mul_comm] using this
  convert hE.mul hJ using 1
  · rfl
  rw [canonicalProfile, profileIntegrand]
  have : exp (I * lam * s) * exp (-(I * lam * s)) = 1 := by rw [← exp_add]; simp
  linear_combination (deriv g s) * this

/-- `Pz = -Ω` for `P = -i∂ₛ`: `z' = -iΩ` wherever `g` is differentiable and the profile
    equation holds. -/
theorem ae_hasDerivAt_canonicalUnknown (hlam : lam ≠ 0) (hg : Integrable (deriv g))
    (hgd : ∀ᵐ s, DifferentiableAt ℝ g s) :
    ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (I * -canonicalProfile lam g s) s := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam
  filter_upwards [ae_hasDerivAt_canonicalProfile (lam := lam) hg, hgd] with s hΩ hgs
  have := (hΩ.add hgs.hasDerivAt).neg.div_const (lam : ℂ)
  convert this using 1
  · rfl
  field_simp
  ring

/-- `(P - λ)z = g`: `z' = i(λz + g)` wherever `g` is differentiable and the profile equation
    holds. -/
theorem ae_hasDerivAt_canonicalUnknown_sub (hlam : lam ≠ 0) (hg : Integrable (deriv g))
    (hgd : ∀ᵐ s, DifferentiableAt ℝ g s) :
    ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (I * (lam * canonicalUnknown lam g s + g s)) s := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam
  filter_upwards [ae_hasDerivAt_canonicalUnknown hlam hg hgd] with s hs
  convert hs using 1
  rw [canonicalUnknown]
  field_simp
  ring

/-- The profile tends to `0` at `+∞`. -/
theorem tendsto_canonicalProfile_atTop (hg : Integrable (deriv g)) :
    Tendsto (canonicalProfile lam g) atTop (𝓝 0) := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have hJ : Tendsto (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) atTop (𝓝 0) := by
    have := (intervalIntegral_tendsto_integral_Ioi 0 hq.integrableOn tendsto_id).const_sub
      (∫ t in Ioi 0, profileIntegrand lam g t)
    rw [sub_self] at this
    refine this.congr fun s ↦ ?_
    exact (integral_Ioi_profileIntegrand hg s).symm
  rw [tendsto_zero_iff_norm_tendsto_zero] at hJ ⊢
  simpa only [norm_canonicalProfile] using hJ

/-- The profile tends to `0` at `-∞` exactly under the Melnikov condition
    `∫ g'(t) e^{-iλt} dt = 0`. -/
theorem tendsto_canonicalProfile_atBot_iff (hg : Integrable (deriv g)) :
    Tendsto (canonicalProfile lam g) atBot (𝓝 0) ↔ ∫ t, profileIntegrand lam g t = 0 := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have hJ : Tendsto (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) atBot
      (𝓝 (∫ t, profileIntegrand lam g t)) := by
    have := (intervalIntegral_tendsto_integral_Iic 0 hq.integrableOn tendsto_id).add_const
      (∫ t in Ioi 0, profileIntegrand lam g t)
    rw [intervalIntegral.integral_Iic_add_Ioi hq.integrableOn hq.integrableOn] at this
    refine this.congr fun s ↦ ?_
    rw [integral_Ioi_profileIntegrand hg s, intervalIntegral.integral_symm]
    simp only [id]
    ring
  have hN := hJ.norm
  simp only [← norm_canonicalProfile] at hN
  rw [tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    exact norm_eq_zero.1 (tendsto_nhds_unique hN h)
  · intro h
    rwa [h, norm_zero] at hN

/-- Under the Melnikov condition the profile is also `-e^{iλs} ∫_{-∞}^s g'(t) e^{-iλt} dt`. -/
theorem canonicalProfile_eq_Iic (hg : Integrable (deriv g))
    (hM : ∫ t, profileIntegrand lam g t = 0) (s : ℝ) :
    canonicalProfile lam g s = -(exp (I * lam * s) * ∫ t in Iic s, profileIntegrand lam g t) := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have := intervalIntegral.integral_Iic_add_Ioi (b := s) hq.integrableOn hq.integrableOn
  rw [hM] at this
  rw [canonicalProfile, eq_neg_of_add_eq_zero_right this]
  ring

end Profile

/-! ### Uniqueness and decay (`lem:canonical-profile`, stated) -/

section Decay

variable {lam : ℝ} {g : ℝ → ℂ}

/-- Under the Melnikov condition, `Ω` is the only locally absolutely continuous solution of
    `Ω' = iλΩ - g'` that tends to `0` at both ends. -/
theorem canonicalProfile_unique (hg : Integrable (deriv g))
    (hM : ∫ t, profileIntegrand lam g t = 0) {Ω : ℝ → ℂ}
    (hac : ∀ c d, AbsolutelyContinuousOnInterval Ω c d)
    (hode : ∀ᵐ s, HasDerivAt Ω (I * lam * Ω s - deriv g s) s)
    (htop : Tendsto Ω atTop (𝓝 0)) (hbot : Tendsto Ω atBot (𝓝 0)) :
    Ω = canonicalProfile lam g := by
  sorry

/-- If `g` approaches its end values `c±` at rate `e^{-α|s|}`, so does `Ω` approach `0`. -/
theorem norm_canonicalProfile_le_exp (hgac : ∀ c d, AbsolutelyContinuousOnInterval g c d)
    (hg : Integrable (deriv g)) (hM : ∫ t, profileIntegrand lam g t = 0) {α C : ℝ} {cp cm : ℂ}
    (hα : 0 < α) (hp : ∀ s, 0 ≤ s → ‖g s - cp‖ ≤ C * Real.exp (-α * s))
    (hn : ∀ s, s ≤ 0 → ‖g s - cm‖ ≤ C * Real.exp (α * s)) :
    ∃ C', ∀ s, ‖canonicalProfile lam g s‖ ≤ C' * Real.exp (-α * |s|) := by
  sorry

/-- The weighted bound `‖e^{|s|} Ω‖_{L²} ≤ ‖e^{|s|} g'‖_{L²}`: on each half line `e^{|s|}Ω` is
    bounded by a one-sided convolution of `e^{|s|}|g'|` with `e^{-t} 1_{t>0}`. -/
theorem eLpNorm_exp_mul_canonicalProfile_le (hg : Integrable (deriv g))
    (hM : ∫ t, profileIntegrand lam g t = 0) :
    eLpNorm (fun s ↦ (Real.exp |s| : ℂ) * canonicalProfile lam g s) 2 volume ≤
      eLpNorm (fun s ↦ (Real.exp |s| : ℂ) * deriv g s) 2 volume := by
  sorry

end Decay

end NoEmbeddedEigenvalues
