import NoEmbeddedEigenvalues.LiftIntegration

/-!
# The normal field of the even–even sector

Blueprint: `def:normal-field`, `lem:normal-field-algebra`, `lem:ee-density`;
`lem:normal-field-annulus`, `lem:normal-coeff-bound`, `lem:normal-field-cutoff-algebra`. The
center is cut out of the truncated virial identity, so only cutoffs to an annulus are needed;
no regularity at the center is used.

On the positive cell minus its center, `W = (Ψ - 2) ∇Ψ / ρ²` is adapted with
coefficient `f = Ψ (2 - Ψ) δ² / ρ⁴`, has divergence `f + 1`, and in the frame
`(∇Ψ, ∇⊥Ψ)` the symmetric matrix `2 sym DW - f I` is `diag(2 - c, c)` with
`c = Ψ (2 - Ψ) / ρ²`. The identities hold wherever `ρ² ≠ 0`; they are rational
identities in `sin` and `cos`, proved by explicit differentiation and
`linear_combination` with `sin² + cos² = 1` and `ρ² · ρ⁻² = 1`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real

/-- The first component of the normal field `W = (Ψ - 2) ∇Ψ / ρ²`. -/
def normalField₁ (p : ℝ × ℝ) : ℝ :=
  (dipoleLift p - 2) * partialX dipoleLift p / gradSq dipoleLift p

/-- The second component of the normal field `W = (Ψ - 2) ∇Ψ / ρ²`. -/
def normalField₂ (p : ℝ × ℝ) : ℝ :=
  (dipoleLift p - 2) * partialY dipoleLift p / gradSq dipoleLift p

/-- The commutator coefficient `f = Ψ (2 - Ψ) δ² / ρ⁴`, with `δ = cos x - cos y`. -/
def normalCoeff (p : ℝ × ℝ) : ℝ :=
  dipoleLift p * (2 - dipoleLift p) * (cos p.1 - cos p.2) ^ 2 / gradSq dipoleLift p ^ 2

/-- The tangential coefficient `c = Ψ (2 - Ψ) / ρ²`. -/
def normalC (p : ℝ × ℝ) : ℝ := dipoleLift p * (2 - dipoleLift p) / gradSq dipoleLift p

/-- The quadratic form `u · DW v` of the Jacobian of the normal field. -/
def normalJacForm (p : ℝ × ℝ) (u v : ℝ × ℝ) : ℝ :=
  u.1 * (partialX normalField₁ p * v.1 + partialY normalField₁ p * v.2) +
    u.2 * (partialX normalField₂ p * v.1 + partialY normalField₂ p * v.2)

/-- `ρ⁻²`, written as an atom for the polynomial identities below. -/
def invGradSq (p : ℝ × ℝ) : ℝ := (sin p.1 ^ 2 + sin p.2 ^ 2)⁻¹

theorem normalField₁_eq :
    normalField₁ = fun p ↦ (cos p.1 + cos p.2 - 2) * -sin p.1 / (sin p.1 ^ 2 + sin p.2 ^ 2) := by
  funext p
  simp only [normalField₁, partialX_dipoleLift, gradSq_dipoleLift, dipoleLift]

theorem normalField₂_eq :
    normalField₂ = fun p ↦ (cos p.1 + cos p.2 - 2) * -sin p.2 / (sin p.1 ^ 2 + sin p.2 ^ 2) := by
  funext p
  simp only [normalField₂, partialY_dipoleLift, gradSq_dipoleLift, dipoleLift]

theorem normalField₁_apply (p : ℝ × ℝ) :
    normalField₁ p = (cos p.1 + cos p.2 - 2) * -sin p.1 * invGradSq p := by
  simp only [normalField₁_eq, invGradSq, div_eq_mul_inv]

theorem normalField₂_apply (p : ℝ × ℝ) :
    normalField₂ p = (cos p.1 + cos p.2 - 2) * -sin p.2 * invGradSq p := by
  simp only [normalField₂_eq, invGradSq, div_eq_mul_inv]

theorem normalCoeff_apply (p : ℝ × ℝ) :
    normalCoeff p = (cos p.1 + cos p.2) * (2 - (cos p.1 + cos p.2)) *
      (cos p.1 - cos p.2) ^ 2 * invGradSq p ^ 2 := by
  simp only [normalCoeff, gradSq_dipoleLift, dipoleLift, invGradSq, div_eq_mul_inv, inv_pow]

theorem normalC_apply (p : ℝ × ℝ) :
    normalC p = (cos p.1 + cos p.2) * (2 - (cos p.1 + cos p.2)) * invGradSq p := by
  simp only [normalC, gradSq_dipoleLift, dipoleLift, invGradSq, div_eq_mul_inv]

theorem mul_invGradSq {p : ℝ × ℝ} (hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0) :
    (sin p.1 ^ 2 + sin p.2 ^ 2) * invGradSq p = 1 :=
  mul_inv_cancel₀ hρ

/-! ### Partial derivatives of the normal field -/

theorem partialX_normalField₁ {p : ℝ × ℝ} (hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0) :
    partialX normalField₁ p =
      invGradSq p*(2*cos p.1^2*invGradSq p*sin p.1^2 - cos p.1^2 + 2*cos p.1*cos p.2*invGradSq
        p*sin p.1^2 - cos p.1*cos p.2 - 4*cos p.1*invGradSq p*sin p.1^2 + 2*cos p.1 + sin
        p.1^2) := by
  have hnum := (((hasDerivAt_cos p.1).add_const (cos p.2)).sub_const 2).mul
    (hasDerivAt_sin p.1).neg
  have hden := ((hasDerivAt_sin p.1).pow 2).add_const (sin p.2 ^ 2)
  have h : HasDerivAt
      (fun t ↦ (cos t + cos p.2 - 2) * -sin t / (sin t ^ 2 + sin p.2 ^ 2)) _ p.1 :=
    hnum.div hden hρ
  rw [normalField₁_eq]
  change deriv (fun t ↦ (cos t + cos p.2 - 2) * -sin t / (sin t ^ 2 + sin p.2 ^ 2)) p.1 = _
  rw [h.deriv, invGradSq]
  simp only [Pi.mul_apply, Pi.neg_apply]
  field_simp
  ring

theorem partialY_normalField₁ {p : ℝ × ℝ} (hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0) :
    partialY normalField₁ p =
      invGradSq p*sin p.1*sin p.2*(2*cos p.1*cos p.2*invGradSq p + 2*cos p.2^2*invGradSq p -
        4*cos p.2*invGradSq p + 1) := by
  have hnum := (((hasDerivAt_cos p.2).const_add (cos p.1)).sub_const 2).mul_const
    (-sin p.1)
  have hden := ((hasDerivAt_sin p.2).pow 2).const_add (sin p.1 ^ 2)
  have h : HasDerivAt
      (fun t ↦ (cos p.1 + cos t - 2) * -sin p.1 / (sin p.1 ^ 2 + sin t ^ 2)) _ p.2 :=
    hnum.div hden hρ
  rw [normalField₁_eq]
  change deriv (fun t ↦ (cos p.1 + cos t - 2) * -sin p.1 / (sin p.1 ^ 2 + sin t ^ 2)) p.2 = _
  rw [h.deriv, invGradSq]
  field_simp
  ring

theorem partialX_normalField₂ {p : ℝ × ℝ} (hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0) :
    partialX normalField₂ p =
      invGradSq p*sin p.1*sin p.2*(2*cos p.1^2*invGradSq p + 2*cos p.1*cos p.2*invGradSq p -
        4*cos p.1*invGradSq p + 1) := by
  have hnum := (((hasDerivAt_cos p.1).add_const (cos p.2)).sub_const 2).mul_const
    (-sin p.2)
  have hden := ((hasDerivAt_sin p.1).pow 2).add_const (sin p.2 ^ 2)
  have h : HasDerivAt
      (fun t ↦ (cos t + cos p.2 - 2) * -sin p.2 / (sin t ^ 2 + sin p.2 ^ 2)) _ p.1 :=
    hnum.div hden hρ
  rw [normalField₂_eq]
  change deriv (fun t ↦ (cos t + cos p.2 - 2) * -sin p.2 / (sin t ^ 2 + sin p.2 ^ 2)) p.1 = _
  rw [h.deriv, invGradSq]
  field_simp
  ring

theorem partialY_normalField₂ {p : ℝ × ℝ} (hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0) :
    partialY normalField₂ p =
      invGradSq p*(2*cos p.1*cos p.2*invGradSq p*sin p.2^2 - cos p.1*cos p.2 + 2*cos
        p.2^2*invGradSq p*sin p.2^2 - cos p.2^2 - 4*cos p.2*invGradSq p*sin p.2^2 + 2*cos
        p.2 + sin p.2^2) := by
  have hnum := (((hasDerivAt_cos p.2).const_add (cos p.1)).sub_const 2).mul
    (hasDerivAt_sin p.2).neg
  have hden := ((hasDerivAt_sin p.2).pow 2).const_add (sin p.1 ^ 2)
  have h : HasDerivAt
      (fun t ↦ (cos p.1 + cos t - 2) * -sin t / (sin p.1 ^ 2 + sin t ^ 2)) _ p.2 :=
    hnum.div hden hρ
  rw [normalField₂_eq]
  change deriv (fun t ↦ (cos p.1 + cos t - 2) * -sin t / (sin p.1 ^ 2 + sin t ^ 2)) p.2 = _
  rw [h.deriv, invGradSq]
  simp only [Pi.mul_apply, Pi.neg_apply]
  field_simp
  ring

/-! ### The normal field algebra -/

/-- `W` is adapted with coefficient `f` wherever `ρ² ≠ 0`. -/
theorem isAdaptedOn_normalField :
    IsAdaptedOn normalField₁ normalField₂ normalCoeff {p | gradSq dipoleLift p ≠ 0} := by
  intro p hp
  change gradSq dipoleLift p ≠ 0 at hp
  simp only [gradSq_dipoleLift] at hp
  have h3 := mul_invGradSq hp
  simp only [classicalL0, smul_eq_mul, partialX_normalField₁ hp, partialY_normalField₁ hp,
    partialX_normalField₂ hp, partialY_normalField₂ hp, normalField₁_apply,
    normalField₂_apply, normalCoeff_apply]
  constructor
  · linear_combination
      (invGradSq p*sin p.2*(cos p.1^2*invGradSq p - 2*cos p.1*invGradSq p - 2*cos
        p.2^2*invGradSq p + 2*cos p.2*invGradSq p + invGradSq p*sin p.1^2 + invGradSq p -
        1)) * sin_sq_add_cos_sq p.1 + (invGradSq p*sin p.2*(2*cos p.1*invGradSq p + cos
        p.2^2*invGradSq p - 2*cos p.2*invGradSq p - invGradSq p*sin p.2^2 - invGradSq p +
        1)) * sin_sq_add_cos_sq p.2 + (-invGradSq p*sin p.2*(2*cos p.1 - 2*cos p.2 + sin
        p.1^2 - sin p.2^2)) * h3
  · linear_combination
      (-invGradSq p*sin p.1*(cos p.1^2*invGradSq p - 2*cos p.1*invGradSq p - 2*cos
        p.2^2*invGradSq p + 2*cos p.2*invGradSq p - invGradSq p*sin p.1^2 - 2*invGradSq
        p*sin p.2^2 + invGradSq p + 1)) * sin_sq_add_cos_sq p.1 + (-invGradSq p*sin
        p.1*(2*cos p.1*invGradSq p + cos p.2^2*invGradSq p - 2*cos p.2*invGradSq p +
        2*invGradSq p*sin p.1^2 + invGradSq p*sin p.2^2 - invGradSq p - 1)) *
        sin_sq_add_cos_sq p.2 + (-invGradSq p*sin p.1*(2*cos p.1 - 2*cos p.2 + sin p.1^2 -
        sin p.2^2)) * h3

/-- `div W = f + 1` wherever `ρ² ≠ 0`. -/
theorem div_normalField {p : ℝ × ℝ} (hp : gradSq dipoleLift p ≠ 0) :
    partialX normalField₁ p + partialY normalField₂ p = normalCoeff p + 1 := by
  simp only [gradSq_dipoleLift] at hp
  have h3 := mul_invGradSq hp
  rw [partialX_normalField₁ hp, partialY_normalField₂ hp, normalCoeff_apply]
  linear_combination
    (invGradSq p*(cos p.1^2*invGradSq p - 2*cos p.1*invGradSq p - 2*cos p.2^2*invGradSq p +
      2*cos p.2*invGradSq p + invGradSq p*sin p.1^2 + invGradSq p - 1)) * sin_sq_add_cos_sq
      p.1 + (invGradSq p*(2*cos p.1*invGradSq p + cos p.2^2*invGradSq p - 2*cos
      p.2*invGradSq p + 2*invGradSq p*sin p.1^2 + invGradSq p*sin p.2^2 - invGradSq p - 1))
      * sin_sq_add_cos_sq p.2 + (2*cos p.1*cos p.2*invGradSq p - 2*cos p.1*invGradSq p -
      2*cos p.2*invGradSq p - invGradSq p*sin p.1^2 - invGradSq p*sin p.2^2 + 2*invGradSq p
      + 1) * h3

/-- In the frame `n = ∇Ψ`, `t = ∇⊥Ψ` (both of squared length `ρ²`), the form
    `2 sym DW - f I` is `diag(2 - c, c)`: normal entry. -/
theorem normalJacForm_normal {p : ℝ × ℝ} (hp : gradSq dipoleLift p ≠ 0) :
    2 * normalJacForm p (partialX dipoleLift p, partialY dipoleLift p)
        (partialX dipoleLift p, partialY dipoleLift p) - normalCoeff p * gradSq dipoleLift p =
      (2 - normalC p) * gradSq dipoleLift p := by
  simp only [gradSq_dipoleLift] at hp ⊢
  have h3 := mul_invGradSq hp
  simp only [normalJacForm, partialX_dipoleLift, partialY_dipoleLift,
    partialX_normalField₁ hp, partialY_normalField₁ hp, partialX_normalField₂ hp,
    partialY_normalField₂ hp, normalCoeff_apply, normalC_apply]
  linear_combination
    (invGradSq p*(cos p.1^2*invGradSq p*sin p.1^2 + cos p.1^2*invGradSq p*sin p.2^2 - 2*cos
      p.1*invGradSq p*sin p.1^2 - 2*cos p.1*invGradSq p*sin p.2^2 - 2*cos p.2^2*invGradSq
      p*sin p.1^2 - 2*cos p.2^2*invGradSq p*sin p.2^2 + 2*cos p.2*invGradSq p*sin p.1^2 +
      2*cos p.2*invGradSq p*sin p.2^2 + 3*invGradSq p*sin p.1^4 + 3*invGradSq p*sin
      p.1^2*sin p.2^2 + invGradSq p*sin p.1^2 + invGradSq p*sin p.2^2 - 3*sin p.1^2 - sin
      p.2^2)) * sin_sq_add_cos_sq p.1 + (invGradSq p*(2*cos p.1*invGradSq p*sin p.1^2 +
      2*cos p.1*invGradSq p*sin p.2^2 + cos p.2^2*invGradSq p*sin p.1^2 + cos
      p.2^2*invGradSq p*sin p.2^2 - 2*cos p.2*invGradSq p*sin p.1^2 - 2*cos p.2*invGradSq
      p*sin p.2^2 + 2*invGradSq p*sin p.1^4 + 5*invGradSq p*sin p.1^2*sin p.2^2 - invGradSq
      p*sin p.1^2 + 3*invGradSq p*sin p.2^4 - invGradSq p*sin p.2^2 - sin p.1^2 - 3*sin
      p.2^2)) * sin_sq_add_cos_sq p.2 + (4*cos p.1*cos p.2*invGradSq p*sin p.1^2 + 4*cos
      p.1*cos p.2*invGradSq p*sin p.2^2 - 6*cos p.1*invGradSq p*sin p.1^2 - 2*cos
      p.1*invGradSq p*sin p.2^2 - 2*cos p.2*invGradSq p*sin p.1^2 - 6*cos p.2*invGradSq
      p*sin p.2^2 - 3*invGradSq p*sin p.1^4 - 2*invGradSq p*sin p.1^2*sin p.2^2 +
      4*invGradSq p*sin p.1^2 - 3*invGradSq p*sin p.2^4 + 4*invGradSq p*sin p.2^2 + 2*sin
      p.1^2 + 2*sin p.2^2) * h3

/-- Tangential entry of `2 sym DW - f I` in the frame `(∇Ψ, ∇⊥Ψ)`. -/
theorem normalJacForm_tangent {p : ℝ × ℝ} (hp : gradSq dipoleLift p ≠ 0) :
    2 * normalJacForm p (-partialY dipoleLift p, partialX dipoleLift p)
        (-partialY dipoleLift p, partialX dipoleLift p) - normalCoeff p * gradSq dipoleLift p =
      normalC p * gradSq dipoleLift p := by
  simp only [gradSq_dipoleLift] at hp ⊢
  have h3 := mul_invGradSq hp
  simp only [normalJacForm, partialX_dipoleLift, partialY_dipoleLift,
    partialX_normalField₁ hp, partialY_normalField₁ hp, partialX_normalField₂ hp,
    partialY_normalField₂ hp, normalCoeff_apply, normalC_apply]
  linear_combination
    (invGradSq p*(cos p.1^2*invGradSq p*sin p.1^2 + cos p.1^2*invGradSq p*sin p.2^2 - 2*cos
      p.1*invGradSq p*sin p.1^2 - 2*cos p.1*invGradSq p*sin p.2^2 - 2*cos p.2^2*invGradSq
      p*sin p.1^2 - 2*cos p.2^2*invGradSq p*sin p.2^2 + 2*cos p.2*invGradSq p*sin p.1^2 +
      2*cos p.2*invGradSq p*sin p.2^2 - invGradSq p*sin p.1^4 - invGradSq p*sin p.1^2*sin
      p.2^2 + invGradSq p*sin p.1^2 + invGradSq p*sin p.2^2 + sin p.1^2 - sin p.2^2)) *
      sin_sq_add_cos_sq p.1 + (invGradSq p*(2*cos p.1*invGradSq p*sin p.1^2 + 2*cos
      p.1*invGradSq p*sin p.2^2 + cos p.2^2*invGradSq p*sin p.1^2 + cos p.2^2*invGradSq
      p*sin p.2^2 - 2*cos p.2*invGradSq p*sin p.1^2 - 2*cos p.2*invGradSq p*sin p.2^2 +
      2*invGradSq p*sin p.1^4 + invGradSq p*sin p.1^2*sin p.2^2 - invGradSq p*sin p.1^2 -
      invGradSq p*sin p.2^4 - invGradSq p*sin p.2^2 - sin p.1^2 + sin p.2^2)) *
      sin_sq_add_cos_sq p.2 + (invGradSq p*(sin p.1 - sin p.2)*(sin p.1 + sin p.2)*(2*cos
      p.1 - 2*cos p.2 + sin p.1^2 - sin p.2^2)) * h3

/-- Off-diagonal entry of `2 sym DW - f I` in the frame `(∇Ψ, ∇⊥Ψ)`. -/
theorem normalJacForm_mixed {p : ℝ × ℝ} (hp : gradSq dipoleLift p ≠ 0) :
    normalJacForm p (partialX dipoleLift p, partialY dipoleLift p)
        (-partialY dipoleLift p, partialX dipoleLift p) +
      normalJacForm p (-partialY dipoleLift p, partialX dipoleLift p)
        (partialX dipoleLift p, partialY dipoleLift p) = 0 := by
  simp only [gradSq_dipoleLift] at hp
  have h3 := mul_invGradSq hp
  simp only [normalJacForm, partialX_dipoleLift, partialY_dipoleLift,
    partialX_normalField₁ hp, partialY_normalField₁ hp, partialX_normalField₂ hp,
    partialY_normalField₂ hp]
  linear_combination
    (-2*invGradSq p*sin p.1*sin p.2*(invGradSq p*sin p.1^2 + invGradSq p*sin p.2^2 - 1)) *
      sin_sq_add_cos_sq p.1 + (2*invGradSq p*sin p.1*sin p.2*(invGradSq p*sin p.1^2 +
      invGradSq p*sin p.2^2 - 1)) * sin_sq_add_cos_sq p.2 + (2*invGradSq p*sin p.1*sin
      p.2*(2*cos p.1 - 2*cos p.2 + sin p.1^2 - sin p.2^2)) * h3

/-- On the positive cell minus its center (`0 < Ψ < 2`), `ρ² > 0`. -/
theorem gradSq_dipoleLift_pos {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2) :
    0 < gradSq dipoleLift p :=
  (mul_pos h0 (by linarith)).trans_le (dipoleLift_mul_le_gradSq p)

/-- On the positive cell minus its center, `0 < c ≤ 1`. -/
theorem normalC_pos_le_one {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2) :
    0 < normalC p ∧ normalC p ≤ 1 := by
  have hρ := gradSq_dipoleLift_pos h0 h2
  refine ⟨div_pos (mul_pos h0 (by linarith)) hρ, ?_⟩
  rw [normalC, div_le_one hρ]
  exact dipoleLift_mul_le_gradSq p

/-! ### The bulk density -/

/-- The bulk density `J = f |ω|² + (2 - c) |ψₙ|² + c |ψₜ|²` of the even–even virial
    identity at `p`, for given values of `ω` and of the normal and tangential derivatives
    `ψₙ`, `ψₜ` of the stream function. -/
def eeDensity (p : ℝ × ℝ) (ω ψn ψt : ℂ) : ℝ :=
  normalCoeff p * ‖ω‖ ^ 2 + (2 - normalC p) * ‖ψn‖ ^ 2 + normalC p * ‖ψt‖ ^ 2

/-- On the positive cell minus its center, `f ≥ 0`. -/
theorem normalCoeff_nonneg {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2) :
    0 ≤ normalCoeff p := by
  have h2' : 0 ≤ 2 - dipoleLift p := by linarith
  unfold normalCoeff
  positivity

/-- On the positive cell minus its center, `f ≤ (2 - Ψ)/Ψ`. With `δ² = 4 - 2ρ² - Ψ²` this is
    `(ρ² + Ψ²)² ≥ 4Ψ²`, that is `ρ² ≥ Ψ(2 - Ψ)`. In particular `f` is bounded on `{Ψ ≥ ε}`, and
    tends to zero at the center, with no series expansion. -/
theorem normalCoeff_le {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2) :
    normalCoeff p ≤ (2 - dipoleLift p) / dipoleLift p := by
  have hg := gradSq_dipoleLift_pos h0 h2
  have hle := dipoleLift_mul_le_gradSq p
  have hδ : (cos p.1 - cos p.2) ^ 2 =
      4 - 2 * gradSq dipoleLift p - dipoleLift p ^ 2 := by
    simp only [gradSq_dipoleLift, dipoleLift]
    linear_combination (2 : ℝ) * sin_sq_add_cos_sq p.1 + 2 * sin_sq_add_cos_sq p.2
  unfold normalCoeff
  rw [hδ, div_le_div_iff₀ (by positivity) h0]
  set g := gradSq dipoleLift p
  set s := dipoleLift p
  have hkey : s ^ 2 * (4 - 2 * g - s ^ 2) ≤ g ^ 2 := by nlinarith [sq_nonneg (g + s ^ 2 - 2 * s)]
  have h2s : 0 ≤ 2 - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hkey h2s]

/-- The bulk density is nonnegative on the positive cell minus its center. -/
theorem eeDensity_nonneg {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2)
    (ω ψn ψt : ℂ) : 0 ≤ eeDensity p ω ψn ψt := by
  obtain ⟨hc0, hc1⟩ := normalC_pos_le_one h0 h2
  have hf := normalCoeff_nonneg h0 h2
  have h2c : 0 ≤ 2 - normalC p := by linarith
  unfold eeDensity
  positivity

/-- The gradient part of the bulk density is positive where `∇ψ ≠ 0`. -/
theorem eeDensity_gradient_pos {p : ℝ × ℝ} (h0 : 0 < dipoleLift p) (h2 : dipoleLift p < 2)
    {ψn ψt : ℂ} (hψ : ψn ≠ 0 ∨ ψt ≠ 0) :
    0 < (2 - normalC p) * ‖ψn‖ ^ 2 + normalC p * ‖ψt‖ ^ 2 := by
  obtain ⟨hc0, hc1⟩ := normalC_pos_le_one h0 h2
  have h2c : 0 < 2 - normalC p := by linarith
  rcases hψ with h | h
  · have := norm_pos_iff.2 h
    positivity
  · have := norm_pos_iff.2 h
    positivity

/-! ### Cutoff to an annulus (`lem:normal-field-annulus`) -/

section Annulus

open scoped ContDiff

private theorem normalCoeff_eq : normalCoeff = fun p ↦
    (cos p.1 + cos p.2) * (2 - (cos p.1 + cos p.2)) * (cos p.1 - cos p.2) ^ 2 /
      (sin p.1 ^ 2 + sin p.2 ^ 2) ^ 2 := by
  funext p
  simp only [normalCoeff, gradSq_dipoleLift, dipoleLift]

/-- The normal field and its coefficient are smooth wherever `ρ² ≠ 0`. -/
private theorem contDiffAt_normal {p : ℝ × ℝ} (hp : gradSq dipoleLift p ≠ 0) :
    ContDiffAt ℝ ∞ normalField₁ p ∧ ContDiffAt ℝ ∞ normalField₂ p ∧
      ContDiffAt ℝ ∞ normalCoeff p := by
  rw [gradSq_dipoleLift] at hp
  refine ⟨?_, ?_, ?_⟩
  · rw [normalField₁_eq]
    exact (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦
      (cos p.1 + cos p.2 - 2) * (-sin p.1)).contDiffAt.div
      (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ sin p.1 ^ 2 + sin p.2 ^ 2).contDiffAt hp
  · rw [normalField₂_eq]
    exact (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦
      (cos p.1 + cos p.2 - 2) * (-sin p.2)).contDiffAt.div
      (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ sin p.1 ^ 2 + sin p.2 ^ 2).contDiffAt hp
  · rw [normalCoeff_eq]
    exact (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦
      (cos p.1 + cos p.2) * (2 - (cos p.1 + cos p.2)) * (cos p.1 - cos p.2) ^ 2).contDiffAt.div
      (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ (sin p.1 ^ 2 + sin p.2 ^ 2) ^ 2).contDiffAt
      (pow_ne_zero 2 hp)

/-- `L₀(χ(Ψ)) = 0`, since `Ψ` is constant along the flow. -/
private theorem classicalL0_comp_dipoleLift {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (p : ℝ × ℝ) : classicalL0 (fun q ↦ χ (dipoleLift q)) p = 0 := by
  have hx : partialX (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -sin p.1 := by
    have h := (hχ (dipoleLift p)).hasDerivAt.comp p.1
      ((hasDerivAt_cos p.1).add_const (cos p.2))
    exact h.deriv
  have hy : partialY (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -sin p.2 := by
    have h := (hχ (dipoleLift p)).hasDerivAt.comp p.2
      ((hasDerivAt_cos p.2).const_add (cos p.1))
    exact h.deriv
  simp only [classicalL0, hx, hy, smul_eq_mul]
  ring

/-- Multiplying a field component by `χ(Ψ)` passes through `L₀`. -/
private theorem classicalL0_cutoff_mul {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {u : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} (hu : DifferentiableAt ℝ u p) :
    classicalL0 (fun q ↦ χ (dipoleLift q) * u q) p =
      χ (dipoleLift p) * classicalL0 u p := by
  have hc : DifferentiableAt ℝ (fun q ↦ χ (dipoleLift q)) p :=
    (hχ _).comp p (by unfold dipoleLift; fun_prop)
  have h0 := classicalL0_comp_dipoleLift hχ p
  simp only [classicalL0, smul_eq_mul] at h0 ⊢
  rw [show (fun q ↦ χ (dipoleLift q) * u q) = fun q ↦ χ (dipoleLift q) • u q from rfl,
    partialX_smul hc hu, partialY_smul hc hu]
  simp only [smul_eq_mul]
  linear_combination u p * h0

/-- The normal field cut off to an annulus: if `χ` is smooth and vanishes outside
    `[ε₁, ε₂] ⊂ (0, 2)`, then `χ(Ψ)W` and `χ(Ψ)f` are smooth and periodic on the lift, and
    `χ(Ψ)W` is adapted everywhere with coefficient `χ(Ψ)f`. On `{0 < Ψ < 2}` we have
    `ρ² ≥ Ψ(2 - Ψ) > 0`, and `L₀(χ(Ψ)) = 0`. -/
theorem annularCutoff_normalField {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : ε₂ < 2) (hχ0 : ∀ s, χ s ≠ 0 → ε₁ ≤ s ∧ s ≤ ε₂) :
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * normalField₁ p) ∧
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * normalField₂ p) ∧
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * normalCoeff p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * normalField₁ p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * normalField₂ p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * normalCoeff p) ∧
    IsAdaptedOn (fun p ↦ χ (dipoleLift p) * normalField₁ p)
      (fun p ↦ χ (dipoleLift p) * normalField₂ p)
      (fun p ↦ χ (dipoleLift p) * normalCoeff p) Set.univ := by
  have hΨ : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hcs : ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p)) :=
    hχ.comp (by unfold dipoleLift; fun_prop)
  -- Away from the closed set `K = {ε₁ ≤ Ψ ≤ ε₂}` the cutoff vanishes near each point.
  let K : Set (ℝ × ℝ) := {p | ε₁ ≤ dipoleLift p ∧ dipoleLift p ≤ ε₂}
  have hK : IsClosed K := (isClosed_le continuous_const hΨ).inter (isClosed_le hΨ continuous_const)
  have hvan {p : ℝ × ℝ} (hp : p ∉ K) : ∀ᶠ q in nhds p, χ (dipoleLift q) = 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hp] with q hq
    by_contra hne
    exact hq (hχ0 _ hne)
  have hρ {p : ℝ × ℝ} (hp : p ∈ K) : gradSq dipoleLift p ≠ 0 :=
    (gradSq_dipoleLift_pos (hε₁.trans_le hp.1) (hp.2.trans_lt hε₂)).ne'
  have hsmooth {F : ℝ × ℝ → ℝ} (hF : ∀ p, gradSq dipoleLift p ≠ 0 → ContDiffAt ℝ ∞ F p) :
      ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * F p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ K
    · exact hcs.contDiffAt.mul (hF p (hρ hp))
    · apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hvan hp] with q hq
      simp [hq]
  have hper {F : ℝ × ℝ → ℝ} (hF : IsPeriodicLift F) :
      IsPeriodicLift (fun p ↦ χ (dipoleLift p) * F p) := by
    intro p
    simp only [dipoleLift, Real.cos_add_two_pi, (hF p).1, (hF p).2, and_self]
  have hp₁ : IsPeriodicLift normalField₁ := by
    intro p; rw [normalField₁_eq]; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hp₂ : IsPeriodicLift normalField₂ := by
    intro p; rw [normalField₂_eq]; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hpf : IsPeriodicLift normalCoeff := by
    intro p; rw [normalCoeff_eq]; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  refine ⟨hsmooth fun p hp ↦ (contDiffAt_normal hp).1,
    hsmooth fun p hp ↦ (contDiffAt_normal hp).2.1, hsmooth fun p hp ↦ (contDiffAt_normal hp).2.2,
    hper hp₁, hper hp₂, hper hpf, ?_⟩
  intro p _
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  by_cases hp : p ∈ K
  · have hd := contDiffAt_normal (hρ hp)
    have had := isAdaptedOn_normalField p (hρ hp)
    rw [classicalL0_cutoff_mul hχd (hd.1.differentiableAt (by simp)),
      classicalL0_cutoff_mul hχd (hd.2.1.differentiableAt (by simp))]
    constructor
    · linear_combination χ (dipoleLift p) * had.1
    · linear_combination χ (dipoleLift p) * had.2
  · have hz := hvan hp
    have hc0 : χ (dipoleLift p) = 0 := hz.self_of_nhds
    have hL {F : ℝ × ℝ → ℝ} : classicalL0 (fun q ↦ χ (dipoleLift q) * F q) p = 0 := by
      have hzF : ∀ᶠ q in nhds p, χ (dipoleLift q) * F q = 0 := by
        filter_upwards [hz] with q hq
        simp [hq]
      simp [classicalL0, partialX_eq_zero_of_eventually hzF,
        partialY_eq_zero_of_eventually hzF]
    simp [hL, hc0]

/-- The cutoff algebra (`lem:normal-field-cutoff-algebra`): for `W_χ = χ(Ψ)W` with coefficient
    `f_χ = χ(Ψ)f`, (1) `f_χ - div W_χ = -χ(Ψ) - (Ψ - 2)χ'(Ψ)`, using `f - div W = -1` and
    `W·∇Ψ = Ψ - 2`; (2) the gradient form of `2 sym DW_χ - f_χ I` on `(X, Y)` is
    `χ(Ψ)((2 - c)|n|² + c|t|²) + 2χ'(Ψ)(Ψ - 2)|n|²`, with `n, t` the normal and tangential
    components, since `D(χW) = χ DW + χ'(Ψ) W ⊗ ∇Ψ` and `W ∥ ∇Ψ`. -/
theorem cutoff_normalField_algebra {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : ε₂ < 2) (hχ0 : ∀ s, χ s ≠ 0 → ε₁ ≤ s ∧ s ≤ ε₂) (p : ℝ × ℝ) :
    χ (dipoleLift p) * normalCoeff p -
        divergence (fun q ↦ χ (dipoleLift q) * normalField₁ q)
          (fun q ↦ χ (dipoleLift q) * normalField₂ q) p =
      -χ (dipoleLift p) - (dipoleLift p - 2) * deriv χ (dipoleLift p) ∧
    ∀ X Y : ℂ,
      2 * (partialX (fun q ↦ χ (dipoleLift q) * normalField₁ q) p * ‖X‖ ^ 2 +
          partialX (fun q ↦ χ (dipoleLift q) * normalField₂ q) p *
            (Y * (starRingEnd ℂ) X).re +
          partialY (fun q ↦ χ (dipoleLift q) * normalField₁ q) p *
            (X * (starRingEnd ℂ) Y).re +
          partialY (fun q ↦ χ (dipoleLift q) * normalField₂ q) p * ‖Y‖ ^ 2) -
        χ (dipoleLift p) * normalCoeff p * (‖X‖ ^ 2 + ‖Y‖ ^ 2) =
      χ (dipoleLift p) *
          ((2 - normalC p) * ‖((sin p.1 : ℂ) * X + (sin p.2 : ℂ) * Y) / (√(sin p.1 ^ 2 +
              sin p.2 ^ 2) : ℂ)‖ ^ 2 +
            normalC p * ‖((sin p.2 : ℂ) * X - (sin p.1 : ℂ) * Y) / (√(sin p.1 ^ 2 +
              sin p.2 ^ 2) : ℂ)‖ ^ 2) +
        2 * deriv χ (dipoleLift p) * (dipoleLift p - 2) *
          ‖((sin p.1 : ℂ) * X + (sin p.2 : ℂ) * Y) / (√(sin p.1 ^ 2 + sin p.2 ^ 2) : ℂ)‖ ^ 2 := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hΨc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  by_cases hp : ε₁ ≤ dipoleLift p ∧ dipoleLift p ≤ ε₂
  · have hg : gradSq dipoleLift p ≠ 0 :=
      (gradSq_dipoleLift_pos (hε₁.trans_le hp.1) (hp.2.trans_lt hε₂)).ne'
    have hρ : sin p.1 ^ 2 + sin p.2 ^ 2 ≠ 0 := by rwa [gradSq_dipoleLift] at hg
    have h3 := mul_invGradSq hρ
    have hd := contDiffAt_normal hg
    have hd₁ : DifferentiableAt ℝ normalField₁ p := hd.1.differentiableAt (by simp)
    have hd₂ : DifferentiableAt ℝ normalField₂ p := hd.2.1.differentiableAt (by simp)
    have hc : DifferentiableAt ℝ (fun q ↦ χ (dipoleLift q)) p :=
      (hχd _).comp p (by unfold dipoleLift; fun_prop)
    have hcx : partialX (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -sin p.1 :=
      ((hχd (dipoleLift p)).hasDerivAt.comp p.1
        ((hasDerivAt_cos p.1).add_const (cos p.2))).deriv
    have hcy : partialY (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -sin p.2 :=
      ((hχd (dipoleLift p)).hasDerivAt.comp p.2
        ((hasDerivAt_cos p.2).const_add (cos p.1))).deriv
    have hpx {u : ℝ × ℝ → ℝ} (hu : DifferentiableAt ℝ u p) :
        partialX (fun q ↦ χ (dipoleLift q) * u q) p =
          χ (dipoleLift p) * partialX u p + deriv χ (dipoleLift p) * -sin p.1 * u p := by
      rw [show (fun q ↦ χ (dipoleLift q) * u q) = fun q ↦ χ (dipoleLift q) • u q from rfl,
        partialX_smul hc hu, hcx]
      simp only [smul_eq_mul]
    have hpy {u : ℝ × ℝ → ℝ} (hu : DifferentiableAt ℝ u p) :
        partialY (fun q ↦ χ (dipoleLift q) * u q) p =
          χ (dipoleLift p) * partialY u p + deriv χ (dipoleLift p) * -sin p.2 * u p := by
      rw [show (fun q ↦ χ (dipoleLift q) * u q) = fun q ↦ χ (dipoleLift q) • u q from rfl,
        partialY_smul hc hu, hcy]
      simp only [smul_eq_mul]
    constructor
    · rw [divergence, hpx hd₁, hpy hd₂, partialX_normalField₁ hρ, partialY_normalField₂ hρ,
        normalField₁_apply, normalField₂_apply, normalCoeff_apply]
      set k0 := χ (dipoleLift p)
      set k1 := deriv χ (dipoleLift p)
      set iG := invGradSq p
      simp only [dipoleLift]
      linear_combination
        (-iG*k0*(iG*cos p.1^2 - 2*iG*cos p.1 - 2*iG*cos p.2^2 + 2*iG*cos p.2 + iG*sin p.1^2 + iG -
          1)) * sin_sq_add_cos_sq p.1 + (-iG*k0*(2*iG*cos p.1 + iG*cos p.2^2 - 2*iG*cos p.2 +
          2*iG*sin p.1^2 + iG*sin p.2^2 - iG - 1)) * sin_sq_add_cos_sq p.2 + (-2*iG*cos p.1*cos
          p.2*k0 + 2*iG*cos p.1*k0 + 2*iG*cos p.2*k0 + iG*k0*sin p.1^2 + iG*k0*sin p.2^2 - 2*iG*k0 -
          cos p.1*k1 - cos p.2*k1 - k0 + 2*k1) * h3
    · intro X Y
      have hR : √(sin p.1 ^ 2 + sin p.2 ^ 2) ^ 2 = sin p.1 ^ 2 + sin p.2 ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hnorm (z : ℂ) :
          ‖z / (√(sin p.1 ^ 2 + sin p.2 ^ 2) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * invGradSq p := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, hR,
          invGradSq, div_eq_mul_inv]
      have hsum (a b : ℝ) : ‖(a : ℂ) * X + (b : ℂ) * Y‖ ^ 2 =
          a ^ 2 * ‖X‖ ^ 2 + 2 * a * b * (X * (starRingEnd ℂ) Y).re + b ^ 2 * ‖Y‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add,
          Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
          map_mul, Complex.conj_ofReal,
          show (a : ℂ) * X * ((b : ℂ) * (starRingEnd ℂ) Y) =
            ((a * b : ℝ) : ℂ) * (X * (starRingEnd ℂ) Y) by push_cast; ring,
          Complex.re_ofReal_mul]
        ring
      have hsub : (sin p.2 : ℂ) * X - (sin p.1 : ℂ) * Y =
          (sin p.2 : ℂ) * X + ((-sin p.1 : ℝ) : ℂ) * Y := by push_cast; ring
      have hYX : (Y * (starRingEnd ℂ) X).re = (X * (starRingEnd ℂ) Y).re := by
        rw [show Y * (starRingEnd ℂ) X = (starRingEnd ℂ) (X * (starRingEnd ℂ) Y) by
          simp [mul_comm]]
        exact Complex.conj_re _
      rw [hpx hd₁, hpx hd₂, hpy hd₁, hpy hd₂, partialX_normalField₁ hρ,
        partialY_normalField₁ hρ, partialX_normalField₂ hρ, partialY_normalField₂ hρ,
        normalField₁_apply, normalField₂_apply, normalCoeff_apply, normalC_apply, hnorm, hnorm,
        hsub, hsum, hsum, hYX]
      set k0 := χ (dipoleLift p)
      set k1 := deriv χ (dipoleLift p)
      set iG := invGradSq p
      set X2 := ‖X‖ ^ 2
      set Y2 := ‖Y‖ ^ 2
      set m := (X * (starRingEnd ℂ) Y).re
      simp only [dipoleLift]
      linear_combination
        (iG*k0*(iG*X2*cos p.1^2 - 2*iG*X2*cos p.1 - 2*iG*X2*cos p.2^2 + 2*iG*X2*cos p.2 +
          2*iG*X2*sin p.1^2 + iG*X2*sin p.2^2 + iG*X2 + iG*Y2*cos p.1^2 - 2*iG*Y2*cos p.1 -
          2*iG*Y2*cos p.2^2 + 2*iG*Y2*cos p.2 - iG*Y2*sin p.2^2 + iG*Y2 - 2*X2)) * sin_sq_add_cos_sq
          p.1 + (iG*k0*(2*iG*X2*cos p.1 + iG*X2*cos p.2^2 - 2*iG*X2*cos p.2 + iG*X2*sin p.1^2 -
          iG*X2 + 2*iG*Y2*cos p.1 + iG*Y2*cos p.2^2 - 2*iG*Y2*cos p.2 + 3*iG*Y2*sin p.1^2 +
          2*iG*Y2*sin p.2^2 - iG*Y2 - 2*Y2)) * sin_sq_add_cos_sq p.2 + (-2*iG*k0*(-X2*cos p.1*cos
          p.2 + 2*X2*cos p.1 + X2*sin p.1^2 - X2 - Y2*cos p.1*cos p.2 + 2*Y2*cos p.2 + Y2*sin p.2^2
          - Y2)) * h3
  · -- The cutoff vanishes near `p` and near `Ψ(p)`.
    have hout : dipoleLift p ∈ (Set.Icc ε₁ ε₂)ᶜ := hp
    have hevs : ∀ᶠ s in nhds (dipoleLift p), χ s = 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with s hs
      by_contra hne
      exact hs (hχ0 s hne)
    have hk1 : deriv χ (dipoleLift p) = 0 := by
      have hfe : χ =ᶠ[nhds (dipoleLift p)] fun _ ↦ (0 : ℝ) := hevs
      rw [hfe.deriv_eq, deriv_const]
    have hev : ∀ᶠ q in nhds p, χ (dipoleLift q) = 0 := hΨc.continuousAt.eventually hevs
    have hk0 : χ (dipoleLift p) = 0 := hev.self_of_nhds
    have hz {u : ℝ × ℝ → ℝ} : ∀ᶠ q in nhds p, χ (dipoleLift q) * u q = 0 := by
      filter_upwards [hev] with q hq
      simp [hq]
    simp only [divergence, partialX_eq_zero_of_eventually hz, partialY_eq_zero_of_eventually hz,
      hk0, hk1]
    refine ⟨by ring, fun X Y ↦ by ring⟩

end Annulus

end NoEmbeddedEigenvalues
