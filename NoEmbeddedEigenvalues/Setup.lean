import Mathlib.Analysis.Fourier.AddCircle
import NoEmbeddedEigenvalues.Symmetry

/-!
# The setting and the main theorem

The space `L²(𝕋²)` on the torus `𝕋² = (ℝ/2πℤ)²`, Fourier coefficients, the inverse Laplacian,
the transport operator `L₀ = sin y ∂ₓ - sin x ∂_y`, its domain and the main theorem
(blueprint: chapter `chap:setup`).

## Model

`L²` is Mathlib's `Lp ℂ 2` for Lebesgue measure on `Torus = Angle × Angle` (total mass `4π²`).
The operators are defined through the characters `e_k(x, y) = exp(i(k₁x + k₂y))`, `k ∈ ℤ²`:

* `L₀` is not a function on `L²` but a relation: `HasL0 g h` says that `L₀ g = h` weakly, tested
  against all characters. Since `L₀ e_k` is an explicit trigonometric polynomial, this is the
  same as the Fourier formula of the blueprint (`hasL0_iff_fourierCoeff`).
* `Δ⁻¹` is the Fourier series `∑_{k ≠ 0} (-ω̂_k / |k|²) e_k`, a `tsum` in `L²`.

Mathlib's inner product `⟪f, g⟫ = ∫ conj f * g` is conjugate linear in the *first* argument, the
opposite of the blueprint's convention.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Complex
open scoped InnerProductSpace

instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-! ### Measure on the torus -/

/-- Lebesgue measure on `ℝ/2πℤ`, of total mass `2π`. -/
instance : MeasureSpace Angle := inferInstanceAs (MeasureSpace (AddCircle (2 * π)))

instance : BorelSpace Angle := inferInstanceAs (BorelSpace (AddCircle (2 * π)))

instance : IsFiniteMeasure (volume : Measure Angle) :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure (AddCircle (2 * π))))

instance : CompactSpace Angle := inferInstanceAs (CompactSpace (AddCircle (2 * π)))

theorem volume_univ_torus : volume (Set.univ : Set Torus) = ENNReal.ofReal ((2 * π) ^ 2) := by
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, pow_two,
    ENNReal.ofReal_mul (by positivity)]
  exact congr_arg₂ _ (AddCircle.measure_univ (2 * π)) (AddCircle.measure_univ (2 * π))

/-- `L²(𝕋²; ℂ)` with respect to Lebesgue measure `dx dy`. -/
abbrev L2 := Lp ℂ 2 (volume : Measure Torus)

/-! ### Characters and Fourier coefficients -/

/-- The character `e_k(x, y) = exp(i(k₁x + k₂y))`, see `char_coe`. -/
def char (k : ℤ × ℤ) : C(Torus, ℂ) :=
  ((fourier k.1 : C(AddCircle (2 * π), ℂ)).comp ⟨Prod.fst, continuous_fst⟩) *
    ((fourier k.2 : C(AddCircle (2 * π), ℂ)).comp ⟨Prod.snd, continuous_snd⟩)

theorem char_coe (k : ℤ × ℤ) (x y : ℝ) :
    char k ((x : Angle), (y : Angle)) = exp (I * (k.1 * x + k.2 * y)) := by
  have h (n : ℤ) (t : ℝ) : fourier (T := 2 * π) n (t : AddCircle (2 * π)) = exp (I * (n * t)) := by
    rw [fourier_coe_apply]
    congr 1
    field_simp
    push_cast
    ring
  change fourier k.1 (x : AddCircle (2 * π)) * fourier k.2 (y : AddCircle (2 * π)) = _
  rw [h, h, ← Complex.exp_add, mul_add]

/-- The character `e_k` as an element of `L²`. -/
def charLp (k : ℤ × ℤ) : L2 := ContinuousMap.toLp 2 volume ℂ (char k)

/-- The Fourier coefficient `ĝ_k = (2π)⁻² ∫ g(x) exp(-ik·x) dx`. -/
def fourierCoeff (g : L2) (k : ℤ × ℤ) : ℂ := ((2 * π : ℂ) ^ 2)⁻¹ * ⟪charLp k, g⟫_ℂ

/-- `g ∈ L²₀`: `g` has mean zero. -/
def MeanZero (g : L2) : Prop := fourierCoeff g 0 = 0

/-! ### The inverse Laplacian -/

/-- `|k|² = k₁² + k₂²`. -/
def normSq (k : ℤ × ℤ) : ℤ := k.1 ^ 2 + k.2 ^ 2

/-- The inverse Laplacian `Δ⁻¹ω = ∑_{k ≠ 0} (-ω̂_k / |k|²) e_k`. It ignores the mean of `ω`, so
it is defined on all of `L²`; the blueprint only uses it on `L²₀`. -/
def invLap (ω : L2) : L2 :=
  ∑' k : ℤ × ℤ, (if k = 0 then 0 else -fourierCoeff ω k / normSq k) • charLp k

/-! ### The transport operator `L₀` -/

/-- `L₀ e_k = i(k₁ sin y - k₂ sin x) e_k`, where `L₀ = sin y ∂ₓ - sin x ∂_y`. -/
def L0char (k : ℤ × ℤ) : C(Torus, ℂ) :=
  ⟨fun p => I * (k.1 * Angle.sin p.2 - k.2 * Angle.sin p.1), by
    have := Angle.continuous_sin; fun_prop⟩ * char k

/-- `L0char k` is `L₀ = sin y ∂ₓ - sin x ∂_y` applied to `e_k`, written with derivatives of the
lift `(x, y) ↦ exp(i(k₁x + k₂y))` of `e_k` to `ℝ²`. -/
theorem L0char_coe (k : ℤ × ℤ) (x y : ℝ) :
    L0char k ((x : Angle), (y : Angle)) =
      Real.sin y * deriv (fun s : ℝ => exp (I * (k.1 * s + k.2 * y))) x -
        Real.sin x * deriv (fun t : ℝ => exp (I * (k.1 * x + k.2 * t))) y := by
  have hx : HasDerivAt (fun s : ℝ => exp (I * (k.1 * s + k.2 * y)))
      (exp (I * (k.1 * x + k.2 * y)) * (I * k.1)) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (k.1 : ℂ)).add_const ((k.2 : ℂ) * y)
      |>.const_mul I |>.cexp |>.comp_ofReal
    simpa using this
  have hy : HasDerivAt (fun t : ℝ => exp (I * (k.1 * x + k.2 * t)))
      (exp (I * (k.1 * x + k.2 * y)) * (I * k.2)) y := by
    have := ((hasDerivAt_id (y : ℂ)).const_mul (k.2 : ℂ)).const_add ((k.1 : ℂ) * x)
      |>.const_mul I |>.cexp |>.comp_ofReal
    simpa using this
  change I * (k.1 * Angle.sin (y : Angle) - k.2 * Angle.sin (x : Angle)) * char k (x, y) = _
  rw [hx.deriv, hy.deriv, char_coe, Angle.sin_coe, Angle.sin_coe]
  ring

/-- `L₀ e_k` as an element of `L²`. -/
def L0charLp (k : ℤ × ℤ) : L2 := ContinuousMap.toLp 2 volume ℂ (L0char k)

/-- `L₀ g = h` in the weak sense, tested against the characters: since `L₀` is a real vector
field with zero divergence, `∫ (L₀ g) φ = -∫ g L₀φ`; with `φ = conj e_k` this reads
`⟪e_k, h⟫ = -⟪L₀ e_k, g⟫`. -/
def HasL0 (g h : L2) : Prop := ∀ k : ℤ × ℤ, ⟪charLp k, h⟫_ℂ = -⟪L0charLp k, g⟫_ℂ

/-- The weak definition of `L₀` agrees with the Fourier formula of the blueprint
(`def:dipole`). -/
theorem hasL0_iff_fourierCoeff (g h : L2) :
    HasL0 g h ↔ ∀ k : ℤ × ℤ, fourierCoeff h k =
      (k.1 * (fourierCoeff g (k - (0, 1)) - fourierCoeff g (k + (0, 1))) -
        k.2 * (fourierCoeff g (k - (1, 0)) - fourierCoeff g (k + (1, 0)))) / 2 := by
  sorry

/-! ### The domain, the linearized operator and the main theorem -/

/-- The operator domain `𝒟 = {g ∈ L²₀ : L₀ g ∈ L²}`. -/
def Dom : Set L2 := {g | MeanZero g ∧ ∃ h, HasL0 g h}

/-- The stream function is in the domain of `L₀` (blueprint: `lem:L0-stream`). -/
theorem exists_hasL0_invLap (ω : L2) : ∃ h, HasL0 (invLap ω) h := by
  sorry

/-- `L ω = h` for the linearized operator `L = L₀(I + Δ⁻¹)` with domain `𝒟`. -/
def HasL (ω h : L2) : Prop := ω ∈ Dom ∧ HasL0 (ω + invLap ω) h

/-- **Main theorem.** The linearized operator has no nonzero purely imaginary eigenvalues
`iλ`, `λ ≠ 0` (blueprint: `thm:main`). -/
theorem main (lam : ℝ) (hlam : lam ≠ 0) (ω : L2) (h : HasL ω ((I * lam) • ω)) : ω = 0 := by
  sorry

/-- `ω` solves the eigenvalue problem `H(ω + ψ) = λω`, `ψ = Δ⁻¹ω`, `H = -iL₀`, i.e.
`L₀(ω + ψ) = iλω` (blueprint: `def:eigen-problem`). -/
def IsEigenSolution (lam : ℝ) (ω : L2) : Prop :=
  MeanZero ω ∧ HasL0 (ω + invLap ω) ((I * lam) • ω)

/-- Reduction to the real-parameter equation (blueprint: `lem:reduction`). -/
theorem hasL_iff_isEigenSolution (lam : ℝ) (ω : L2) :
    HasL ω ((I * lam) • ω) ↔ IsEigenSolution lam ω := by
  sorry

end NoEmbeddedEigenvalues

end
