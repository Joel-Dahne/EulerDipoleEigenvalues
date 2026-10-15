import NoEmbeddedEigenvalues.DipoleCalculus

/-!
# The normal field of the even–even sector

Blueprint: `def:normal-field`, `lem:normal-field-algebra`.

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

end NoEmbeddedEigenvalues
