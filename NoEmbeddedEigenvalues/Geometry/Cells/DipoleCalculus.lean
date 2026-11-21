module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import NoEmbeddedEigenvalues.Symmetry.Symmetry

/-!
# Classical calculus on the real lift and the dipole identities

Blueprint: `def:lift-operators`, `lem:lift-calculus`, `lem:dipole-identities`,
`def:adapted-field`.

Pointwise differential identities are stated for functions on the real lift
`ℝ × ℝ` of the torus, as for `IsSmoothTorusTest`. `partialX` and `partialY` are
ordinary partial derivatives along the coordinate lines; `classicalL0` is the
transport operator `sin y ∂ₓ - sin x ∂_y` acting on them. Periodicity plays no
role in pointwise identities.
-/

@[expose] public section

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

/-! ### Calculus rules -/

section Rules

variable {u v : ℝ × ℝ → E} {p : ℝ × ℝ}

theorem classicalL0_eq (u : ℝ × ℝ → E) :
    classicalL0 u = fun q ↦ sin q.2 • partialX u q - sin q.1 • partialY u q := rfl

theorem hasDerivAt_partialX (hu : DifferentiableAt ℝ u p) :
    HasDerivAt (fun t ↦ u (t, p.2)) (partialX u p) p.1 :=
  (hu.comp p.1 (differentiableAt_id.prodMk (differentiableAt_const p.2))).hasDerivAt

theorem hasDerivAt_partialY (hu : DifferentiableAt ℝ u p) :
    HasDerivAt (fun t ↦ u (p.1, t)) (partialY u p) p.2 :=
  (hu.comp p.2 ((differentiableAt_const p.1).prodMk differentiableAt_id)).hasDerivAt

theorem partialX_eq_fderiv (hu : DifferentiableAt ℝ u p) : partialX u p = fderiv ℝ u p (1, 0) :=
  (hu.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem partialY_eq_fderiv (hu : DifferentiableAt ℝ u p) : partialY u p = fderiv ℝ u p (0, 1) :=
  (hu.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem partialX_add (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialX (fun q ↦ u q + v q) p = partialX u p + partialX v p :=
  ((hasDerivAt_partialX hu).add (hasDerivAt_partialX hv)).deriv

theorem partialY_add (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialY (fun q ↦ u q + v q) p = partialY u p + partialY v p :=
  ((hasDerivAt_partialY hu).add (hasDerivAt_partialY hv)).deriv

theorem partialX_sub (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialX (fun q ↦ u q - v q) p = partialX u p - partialX v p :=
  ((hasDerivAt_partialX hu).sub (hasDerivAt_partialX hv)).deriv

theorem partialY_sub (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialY (fun q ↦ u q - v q) p = partialY u p - partialY v p :=
  ((hasDerivAt_partialY hu).sub (hasDerivAt_partialY hv)).deriv

theorem partialX_smul {c : ℝ × ℝ → ℝ} (hc : DifferentiableAt ℝ c p) (hu : DifferentiableAt ℝ u p) :
    partialX (fun q ↦ c q • u q) p = c p • partialX u p + partialX c p • u p :=
  ((hasDerivAt_partialX hc).smul (hasDerivAt_partialX hu)).deriv

theorem partialY_smul {c : ℝ × ℝ → ℝ} (hc : DifferentiableAt ℝ c p) (hu : DifferentiableAt ℝ u p) :
    partialY (fun q ↦ c q • u q) p = c p • partialY u p + partialY c p • u p :=
  ((hasDerivAt_partialY hc).smul (hasDerivAt_partialY hu)).deriv

theorem partialX_const_smul (c : ℝ) (hu : DifferentiableAt ℝ u p) :
    partialX (fun q ↦ c • u q) p = c • partialX u p :=
  ((hasDerivAt_partialX hu).const_smul c).deriv

theorem partialY_const_smul (c : ℝ) (hu : DifferentiableAt ℝ u p) :
    partialY (fun q ↦ c • u q) p = c • partialY u p :=
  ((hasDerivAt_partialY hu).const_smul c).deriv

/-- A function vanishing near `p` has vanishing partial derivatives at `p`. -/
theorem partialX_eq_zero_of_eventually (hu : ∀ᶠ q in nhds p, u q = 0) : partialX u p = 0 := by
  have hl : Filter.Tendsto (fun t : ℝ ↦ ((t, p.2) : ℝ × ℝ)) (nhds p.1) (nhds p) :=
    (continuous_id.prodMk continuous_const).tendsto' p.1 p rfl
  have h : (fun t ↦ u (t, p.2)) =ᶠ[nhds p.1] fun _ ↦ 0 := hl.eventually hu
  rw [partialX, h.deriv_eq, deriv_const]

theorem partialY_eq_zero_of_eventually (hu : ∀ᶠ q in nhds p, u q = 0) : partialY u p = 0 := by
  have hl : Filter.Tendsto (fun t : ℝ ↦ ((p.1, t) : ℝ × ℝ)) (nhds p.2) (nhds p) :=
    (continuous_const.prodMk continuous_id).tendsto' p.2 p rfl
  have h : (fun t ↦ u (p.1, t)) =ᶠ[nhds p.2] fun _ ↦ 0 := hl.eventually hu
  rw [partialY, h.deriv_eq, deriv_const]

/-- Symmetry of mixed partial derivatives of a `C²` function. -/
theorem partialY_partialX (hu : ContDiff ℝ 2 u) (p : ℝ × ℝ) :
    partialY (partialX u) p = partialX (partialY u) p := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hX : partialX u = fun q ↦ fderiv ℝ u q (1, 0) :=
    funext fun q ↦ partialX_eq_fderiv (hd q)
  have hY : partialY u = fun q ↦ fderiv ℝ u q (0, 1) :=
    funext fun q ↦ partialY_eq_fderiv (hd q)
  rw [hX, hY, partialY_eq_fderiv ((hfd p).clm_apply (differentiableAt_const _)),
    partialX_eq_fderiv ((hfd p).clm_apply (differentiableAt_const _)),
    fderiv_clm_apply (hfd p) (differentiableAt_const _),
    fderiv_clm_apply (hfd p) (differentiableAt_const _)]
  simpa using (hu.contDiffAt.isSymmSndFDerivAt (by simp)) (0, 1) (1, 0)

/-- Partial derivatives of a `C^(n+1)` function are `C^n`. -/
theorem contDiff_partialX {n : ℕ} (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (partialX u) := by
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  rw [show partialX u = fun q ↦ fderiv ℝ u q (1, 0) from
    funext fun q ↦ partialX_eq_fderiv (hd q)]
  exact (hu.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_partialY {n : ℕ} (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (partialY u) := by
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  rw [show partialY u = fun q ↦ fderiv ℝ u q (0, 1) from
    funext fun q ↦ partialY_eq_fderiv (hd q)]
  exact (hu.fderiv_right le_rfl).clm_apply contDiff_const

end Rules

end Operators

section Coordinates

variable {p : ℝ × ℝ}

@[simp] theorem partialX_sin_fst : partialX (fun q : ℝ × ℝ ↦ sin q.1) p = cos p.1 :=
  (hasDerivAt_sin p.1).deriv

@[simp] theorem partialX_cos_fst : partialX (fun q : ℝ × ℝ ↦ cos q.1) p = -sin p.1 :=
  (hasDerivAt_cos p.1).deriv

@[simp] theorem partialX_sin_snd : partialX (fun q : ℝ × ℝ ↦ sin q.2) p = 0 :=
  (hasDerivAt_const p.1 (sin p.2)).deriv

@[simp] theorem partialX_cos_snd : partialX (fun q : ℝ × ℝ ↦ cos q.2) p = 0 :=
  (hasDerivAt_const p.1 (cos p.2)).deriv

@[simp] theorem partialY_sin_snd : partialY (fun q : ℝ × ℝ ↦ sin q.2) p = cos p.2 :=
  (hasDerivAt_sin p.2).deriv

@[simp] theorem partialY_cos_snd : partialY (fun q : ℝ × ℝ ↦ cos q.2) p = -sin p.2 :=
  (hasDerivAt_cos p.2).deriv

@[simp] theorem partialY_sin_fst : partialY (fun q : ℝ × ℝ ↦ sin q.1) p = 0 :=
  (hasDerivAt_const p.2 (sin p.1)).deriv

@[simp] theorem partialY_cos_fst : partialY (fun q : ℝ × ℝ ↦ cos q.1) p = 0 :=
  (hasDerivAt_const p.2 (cos p.1)).deriv

end Coordinates

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
