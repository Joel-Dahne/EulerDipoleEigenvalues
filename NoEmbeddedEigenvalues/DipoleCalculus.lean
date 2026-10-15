import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import NoEmbeddedEigenvalues.Symmetry

/-!
# Classical calculus on the real lift and the dipole identities

Blueprint: `lem:dipole-identities`, `def:adapted-field`.

Pointwise differential identities are stated for functions on the real lift
`ℝ × ℝ` of the torus, as for `IsSmoothTorusTest`. `partialX` and `partialY` are
ordinary partial derivatives along the coordinate lines; `classicalL0` is the
transport operator `sin y ∂ₓ - sin x ∂_y` acting on them. Periodicity plays no
role in pointwise identities.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real

/-! ### Classical operators on the lift -/

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial derivative in the first coordinate. -/
def partialX (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E := deriv (fun t ↦ u (t, p.2)) p.1

/-- Partial derivative in the second coordinate. -/
def partialY (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E := deriv (fun t ↦ u (p.1, t)) p.2

/-- The Laplacian `∂ₓ² + ∂_y²`. -/
def laplacian (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  partialX (partialX u) p + partialY (partialY u) p

/-- The transport operator `L₀ = sin y ∂ₓ - sin x ∂_y` of the dipole. -/
def classicalL0 (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  sin p.2 • partialX u p - sin p.1 • partialY u p

theorem partialX_eq_of_hasDerivAt {u d : ℝ × ℝ → E}
    (h : ∀ x y, HasDerivAt (fun t ↦ u (t, y)) (d (x, y)) x) : partialX u = d :=
  funext fun p ↦ (h p.1 p.2).deriv

theorem partialY_eq_of_hasDerivAt {u d : ℝ × ℝ → E}
    (h : ∀ x y, HasDerivAt (fun t ↦ u (x, t)) (d (x, y)) y) : partialY u = d :=
  funext fun p ↦ (h p.1 p.2).deriv

end Operators

/-- A planar vector field `W = (W₁, W₂)` is adapted on `U` with commutator coefficient `f`
    if `[Y, W] = f Y` there, for the dipole velocity `Y = (sin y, -sin x)`. Written in
    components, `(Y·∇)W - (W·∇)Y = f Y`. For smooth `W` this is `[L₀, W·∇] = f L₀`. -/
def IsAdaptedOn (W₁ W₂ f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ U, classicalL0 W₁ p - cos p.2 * W₂ p = f p * sin p.2 ∧
    classicalL0 W₂ p + cos p.1 * W₁ p = -(f p * sin p.1)

/-- The gradient pairing `∇u · ∇v` of real functions. -/
def gradDot (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialX u p * partialX v p + partialY u p * partialY v p

/-- The squared gradient `|∇u|²` of a real function. -/
def gradSq (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := gradDot u u p

/-! ### The dipole -/

/-- The dipole stream function on the real lift. -/
def dipoleLift (p : ℝ × ℝ) : ℝ := cos p.1 + cos p.2

theorem Ψ_coe (x y : ℝ) : Ψ ((x : Angle), (y : Angle)) = dipoleLift (x, y) := by
  simp [Ψ, dipoleLift, Angle.cos_coe]

theorem partialX_dipoleLift : partialX dipoleLift = fun p ↦ -sin p.1 :=
  partialX_eq_of_hasDerivAt fun x y ↦ by
    simpa [dipoleLift] using (hasDerivAt_cos x).add_const (cos y)

theorem partialY_dipoleLift : partialY dipoleLift = fun p ↦ -sin p.2 :=
  partialY_eq_of_hasDerivAt fun x y ↦ by
    simpa [dipoleLift] using (hasDerivAt_cos y).const_add (cos x)

/-- `|∇Ψ|² = sin² x + sin² y`. -/
theorem gradSq_dipoleLift : gradSq dipoleLift = fun p ↦ sin p.1 ^ 2 + sin p.2 ^ 2 := by
  funext p
  simp only [gradSq, gradDot, partialX_dipoleLift, partialY_dipoleLift]
  ring

theorem partialX_gradSq_dipoleLift :
    partialX (gradSq dipoleLift) = fun p ↦ 2 * sin p.1 * cos p.1 := by
  rw [gradSq_dipoleLift]
  exact partialX_eq_of_hasDerivAt fun x y ↦ by
    convert ((hasDerivAt_sin x).pow 2).add_const (sin y ^ 2) using 1
    ring

theorem partialY_gradSq_dipoleLift :
    partialY (gradSq dipoleLift) = fun p ↦ 2 * sin p.2 * cos p.2 := by
  rw [gradSq_dipoleLift]
  exact partialY_eq_of_hasDerivAt fun x y ↦ by
    convert ((hasDerivAt_sin y).pow 2).const_add (sin x ^ 2) using 1
    ring

/-- Algebraic identities for the dipole `Ψ = cos x + cos y`, with `s = Ψ`,
    `ρ² = |∇Ψ|²` and `δ = cos x - cos y`. -/
theorem laplacian_dipoleLift (p : ℝ × ℝ) : laplacian dipoleLift p = -dipoleLift p := by
  have hx : partialX (fun p : ℝ × ℝ ↦ -sin p.1) = fun p ↦ -cos p.1 :=
    partialX_eq_of_hasDerivAt fun x y ↦ (hasDerivAt_sin x).neg
  have hy : partialY (fun p : ℝ × ℝ ↦ -sin p.2) = fun p ↦ -cos p.2 :=
    partialY_eq_of_hasDerivAt fun x y ↦ (hasDerivAt_sin y).neg
  simp only [laplacian, partialX_dipoleLift, partialY_dipoleLift, hx, hy, dipoleLift]
  ring

theorem classicalL0_dipoleLift (p : ℝ × ℝ) : classicalL0 dipoleLift p = 0 := by
  simp only [classicalL0, partialX_dipoleLift, partialY_dipoleLift, smul_eq_mul]
  ring

theorem gradSq_dipoleLift_sub (p : ℝ × ℝ) :
    gradSq dipoleLift p - dipoleLift p * (2 - dipoleLift p) =
      2 * (1 - cos p.1) * (1 - cos p.2) := by
  simp only [gradSq_dipoleLift, dipoleLift]
  linear_combination sin_sq_add_cos_sq p.1 + sin_sq_add_cos_sq p.2

theorem dipoleLift_mul_le_gradSq (p : ℝ × ℝ) :
    dipoleLift p * (2 - dipoleLift p) ≤ gradSq dipoleLift p := by
  have h := gradSq_dipoleLift_sub p
  have h1 := cos_le_one p.1
  have h2 := cos_le_one p.2
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

theorem sq_cos_sub_cos (p : ℝ × ℝ) :
    (cos p.1 - cos p.2) ^ 2 = 4 - 2 * gradSq dipoleLift p - dipoleLift p ^ 2 := by
  simp only [gradSq_dipoleLift, dipoleLift]
  linear_combination 2 * sin_sq_add_cos_sq p.1 + 2 * sin_sq_add_cos_sq p.2

theorem gradDot_dipoleLift_gradSq (p : ℝ × ℝ) :
    gradDot dipoleLift (gradSq dipoleLift) p =
      dipoleLift p * (4 - dipoleLift p ^ 2 - 3 * gradSq dipoleLift p) := by
  simp only [gradDot, partialX_dipoleLift, partialY_dipoleLift, partialX_gradSq_dipoleLift,
    partialY_gradSq_dipoleLift]
  simp only [gradSq_dipoleLift, dipoleLift]
  linear_combination (cos p.1 + 3 * cos p.2) * sin_sq_add_cos_sq p.1 +
    (3 * cos p.1 + cos p.2) * sin_sq_add_cos_sq p.2

theorem laplacian_gradSq_dipoleLift (p : ℝ × ℝ) :
    laplacian (gradSq dipoleLift) p = 4 * (1 - gradSq dipoleLift p) := by
  have hx : partialX (fun p : ℝ × ℝ ↦ 2 * sin p.1 * cos p.1) =
      fun p ↦ 2 * (cos p.1 ^ 2 - sin p.1 ^ 2) :=
    partialX_eq_of_hasDerivAt fun x y ↦ by
      convert ((hasDerivAt_sin x).mul (hasDerivAt_cos x)).const_mul 2 using 1
      · ext t
        simp only [Pi.mul_apply]
        ring
      · ring
  have hy : partialY (fun p : ℝ × ℝ ↦ 2 * sin p.2 * cos p.2) =
      fun p ↦ 2 * (cos p.2 ^ 2 - sin p.2 ^ 2) :=
    partialY_eq_of_hasDerivAt fun x y ↦ by
      convert ((hasDerivAt_sin y).mul (hasDerivAt_cos y)).const_mul 2 using 1
      · ext t
        simp only [Pi.mul_apply]
        ring
      · ring
  simp only [laplacian, partialX_gradSq_dipoleLift, partialY_gradSq_dipoleLift, hx, hy]
  simp only [gradSq_dipoleLift]
  linear_combination 2 * sin_sq_add_cos_sq p.1 + 2 * sin_sq_add_cos_sq p.2

theorem gradSq_gradSq_dipoleLift (p : ℝ × ℝ) :
    gradSq (gradSq dipoleLift) p =
      4 * gradSq dipoleLift p - 2 * gradSq dipoleLift p ^ 2 +
        4 * gradSq dipoleLift p * dipoleLift p ^ 2 + 2 * dipoleLift p ^ 4 -
        8 * dipoleLift p ^ 2 := by
  rw [gradSq, gradDot, partialX_gradSq_dipoleLift, partialY_gradSq_dipoleLift]
  simp only [gradSq_dipoleLift, dipoleLift]
  linear_combination
    (-2 * (cos p.1 ^ 2 + 4 * cos p.1 * cos p.2 + 2 * cos p.2 ^ 2 - sin p.1 ^ 2 -
      2 * sin p.2 ^ 2 + 1)) * sin_sq_add_cos_sq p.1 +
    (-2 * (4 * cos p.1 ^ 2 + 4 * cos p.1 * cos p.2 + cos p.2 ^ 2 - sin p.2 ^ 2 - 1)) *
      sin_sq_add_cos_sq p.2

/-- The coefficients of `L₀` are first Laplace eigenfunctions. -/
theorem laplacian_sin_fst (p : ℝ × ℝ) :
    laplacian (fun q : ℝ × ℝ ↦ sin q.1) p = -sin p.1 := by
  have h1 : partialX (fun q : ℝ × ℝ ↦ sin q.1) = fun q ↦ cos q.1 :=
    partialX_eq_of_hasDerivAt fun x y ↦ hasDerivAt_sin x
  have h2 : partialX (fun q : ℝ × ℝ ↦ cos q.1) = fun q ↦ -sin q.1 :=
    partialX_eq_of_hasDerivAt fun x y ↦ hasDerivAt_cos x
  have h3 : partialY (fun q : ℝ × ℝ ↦ sin q.1) = fun _ ↦ 0 :=
    partialY_eq_of_hasDerivAt fun x y ↦ hasDerivAt_const y (sin x)
  have h4 : partialY (fun _ : ℝ × ℝ ↦ (0 : ℝ)) = fun _ ↦ 0 :=
    partialY_eq_of_hasDerivAt fun x y ↦ hasDerivAt_const y 0
  simp only [laplacian, h1, h2, h3, h4]
  ring

theorem laplacian_sin_snd (p : ℝ × ℝ) :
    laplacian (fun q : ℝ × ℝ ↦ sin q.2) p = -sin p.2 := by
  have h1 : partialY (fun q : ℝ × ℝ ↦ sin q.2) = fun q ↦ cos q.2 :=
    partialY_eq_of_hasDerivAt fun x y ↦ hasDerivAt_sin y
  have h2 : partialY (fun q : ℝ × ℝ ↦ cos q.2) = fun q ↦ -sin q.2 :=
    partialY_eq_of_hasDerivAt fun x y ↦ hasDerivAt_cos y
  have h3 : partialX (fun q : ℝ × ℝ ↦ sin q.2) = fun _ ↦ 0 :=
    partialX_eq_of_hasDerivAt fun x y ↦ hasDerivAt_const x (sin y)
  have h4 : partialX (fun _ : ℝ × ℝ ↦ (0 : ℝ)) = fun _ ↦ 0 :=
    partialX_eq_of_hasDerivAt fun x y ↦ hasDerivAt_const x 0
  simp only [laplacian, h1, h2, h3, h4]
  ring

end NoEmbeddedEigenvalues
