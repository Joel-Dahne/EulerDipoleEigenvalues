module

public import EulerDipoleEigenvalues.Setup.Setup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fourier derivatives and classical test functions

First and second partial derivatives and the Laplacian, defined as relations through Fourier
multipliers, and the derivatives of the stream function `Δ⁻¹ω` (blueprint:
`def:fourier-derivatives`, `lem:fourier-derivative-composition`,
`lem:inverse-laplacian-derivatives`, `def:stream-derivatives`).

Classical periodic tests are represented by continuous torus functions and their
continuous coordinate derivatives. Both all-C1 and all-smooth bilinear weak
testing are equivalent to the first Fourier derivative relation. The proof
uses periodic one-dimensional integration by parts, Fubini and Parseval,
not pointwise differentiation of a Fourier series.

Smoothness means `ContDiff ℝ ∞` of the real periodic lift; in this Mathlib
version `ContDiff ℝ ⊤` would mean analyticity instead. Tests are pairs of a
continuous function and its continuous classical coordinate derivative.
We do not introduce a separate differentiation operator on torus functions,
or assert the existence of such a derivative for arbitrary continuous tests.
Transport, second-order and Laplace weak-testing bridges are not proved here.

The last section multiplies `L²` functions by continuous functions (`mulL2`) and proves the
product rule `∂ⱼ(c g) = (∂ⱼc) g + c ∂ⱼg` for classically differentiable `c`, by weak
testing, and the integration by parts `⟪b, ∂ⱼa⟫ = -⟪∂ⱼb, a⟫`, by Parseval
(`lem:l2-product-rule`).
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-! ### Derivatives defined by Fourier multipliers -/

/-- Coordinate frequency: `j = 0` is the x coordinate, `j = 1` the y coordinate. -/
def frequencyComponent (k : ℤ × ℤ) (j : Fin 2) : ℤ := if j = 0 then k.1 else k.2

/-- A first partial derivative in the Fourier-multiplier sense, with output in `L²`.
This is a partial-operator relation, not an assertion that every `L²` input has a derivative.
Equivalence with testing against all smooth functions is not asserted here. -/
def HasFourierPartial (j : Fin 2) (g h : L2) : Prop :=
  ∀ k, fourierCoeff h k = (I * frequencyComponent k j) * fourierCoeff g k

/-- A second partial derivative in the Fourier-multiplier sense, with output in `L²`.
The intermediate first derivative is not assumed to be in `L²`; when it is,
`hasFourierPartial_iff_second` identifies this with successive differentiation. -/
def HasFourierSecondPartial (i j : Fin 2) (g h : L2) : Prop :=
  ∀ k, fourierCoeff h k =
    -((frequencyComponent k i : ℂ) * frequencyComponent k j) * fourierCoeff g k

/-- Differentiating a first derivative again agrees with the second-order multiplier. -/
theorem hasFourierPartial_iff_second {g d h : L2} {i j : Fin 2}
    (hd : HasFourierPartial j g d) :
    HasFourierPartial i d h ↔ HasFourierSecondPartial i j g h := by
  unfold HasFourierPartial HasFourierSecondPartial
  apply forall_congr'
  intro k
  rw [hd k]
  have hm : (I * frequencyComponent k i) *
      ((I * frequencyComponent k j) * fourierCoeff g k) =
      -((frequencyComponent k i : ℂ) * frequencyComponent k j) * fourierCoeff g k := by
    calc
      _ = (I * I) * ((frequencyComponent k i : ℂ) * frequencyComponent k j) *
          fourierCoeff g k := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hm]

/-- The Laplacian in the Fourier-multiplier sense. -/
def HasFourierLaplacian (g h : L2) : Prop :=
  ∀ k, fourierCoeff h k = -(normSq k : ℂ) * fourierCoeff g k

/-- The Fourier Laplacian is the sum of the two pure second partial derivatives. -/
theorem hasFourierLaplacian_of_second {g h₀ h₁ : L2}
    (h₀deriv : HasFourierSecondPartial 0 0 g h₀)
    (h₁deriv : HasFourierSecondPartial 1 1 g h₁) :
    HasFourierLaplacian g (h₀ + h₁) := by
  intro k
  rw [fourierCoeff_add, h₀deriv k, h₁deriv k]
  simp only [frequencyComponent, normSq]
  push_cast
  ring

/-- First and second coordinate multipliers are bounded by the Laplace frequency. -/
theorem abs_frequencyComponent_le_normSq (k : ℤ × ℤ) (j : Fin 2) :
    |frequencyComponent k j| ≤ normSq k := by
  unfold frequencyComponent
  split_ifs
  · exact (abs_components_le_normSq k).1
  · exact (abs_components_le_normSq k).2

theorem abs_frequencyProduct_le_normSq (k : ℤ × ℤ) (i j : Fin 2) :
    |frequencyComponent k i * frequencyComponent k j| ≤ normSq k := by
  have hcross : |k.1 * k.2| ≤ normSq k := by
    rw [abs_le]
    unfold normSq
    constructor <;> nlinarith [sq_nonneg (k.1 + k.2), sq_nonneg (k.1 - k.2)]
  unfold frequencyComponent
  split_ifs
  · rw [← sq, abs_of_nonneg (sq_nonneg _)]
    unfold normSq
    nlinarith [sq_nonneg k.2]
  · exact hcross
  · simpa only [mul_comm] using hcross
  · rw [← sq, abs_of_nonneg (sq_nonneg _)]
    unfold normSq
    nlinarith [sq_nonneg k.1]

/-- The multiplier `i kⱼ · (-1/|k|²)` of `∂ⱼΔ⁻¹` is bounded by one. -/
theorem norm_streamPartialSymbol_le (j : Fin 2) (k : ℤ × ℤ) :
    ‖I * frequencyComponent k j * invLapSymbol k‖ ≤ 1 := by
  rw [mul_assoc, norm_mul, Complex.norm_I, one_mul]
  exact norm_intCast_mul_invLapSymbol_le k _ fun _ => abs_frequencyComponent_le_normSq k j

/-- The multiplier `-kᵢkⱼ · (-1/|k|²)` of `∂ᵢ∂ⱼΔ⁻¹` is bounded by one. -/
theorem norm_streamSecondPartialSymbol_le (i j : Fin 2) (k : ℤ × ℤ) :
    ‖-((frequencyComponent k i : ℂ) * frequencyComponent k j) * invLapSymbol k‖ ≤ 1 := by
  rw [neg_mul, norm_neg, ← Int.cast_mul]
  exact norm_intCast_mul_invLapSymbol_le k _ fun _ => abs_frequencyProduct_le_normSq k i j

/-- `∂ⱼΔ⁻¹`: the first derivatives `∂ⱼψ` of the stream function `ψ = Δ⁻¹ω`. -/
def streamPartial (j : Fin 2) : L2 →L[ℂ] L2 := fourierMultiplier (norm_streamPartialSymbol_le j)

/-- `∂ᵢ∂ⱼΔ⁻¹`: the second derivatives `∂ᵢ∂ⱼψ` of the stream function. -/
def streamSecondPartial (i j : Fin 2) : L2 →L[ℂ] L2 :=
  fourierMultiplier (norm_streamSecondPartialSymbol_le i j)

theorem hasFourierPartial_streamPartial (ω : L2) (j : Fin 2) :
    HasFourierPartial j (invLap ω) (streamPartial j ω) := fun k => by
  rw [streamPartial, fourierCoeff_fourierMultiplier, fourierCoeff_invLap_eq_mul]
  ring

theorem hasFourierSecondPartial_streamSecondPartial (ω : L2) (i j : Fin 2) :
    HasFourierSecondPartial i j (invLap ω) (streamSecondPartial i j ω) := fun k => by
  rw [streamSecondPartial, fourierCoeff_fourierMultiplier, fourierCoeff_invLap_eq_mul]
  ring

/-- Second derivatives are derivatives of the first derivatives. -/
theorem hasFourierPartial_streamPartial_streamSecondPartial (ω : L2) (i j : Fin 2) :
    HasFourierPartial i (streamPartial j ω) (streamSecondPartial i j ω) :=
  (hasFourierPartial_iff_second (hasFourierPartial_streamPartial ω j)).2
    (hasFourierSecondPartial_streamSecondPartial ω i j)

/-- The stream function has each first derivative in `L²`, defined by Fourier multipliers. -/
theorem exists_fourierPartial_invLap (ω : L2) (j : Fin 2) :
    ∃ h, HasFourierPartial j (invLap ω) h :=
  ⟨_, hasFourierPartial_streamPartial ω j⟩

/-- The stream function has each second derivative in `L²`, defined by Fourier multipliers. -/
theorem exists_fourierSecondPartial_invLap (ω : L2) (i j : Fin 2) :
    ∃ h, HasFourierSecondPartial i j (invLap ω) h :=
  ⟨_, hasFourierSecondPartial_streamSecondPartial ω i j⟩

/-- On mean-zero inputs the stream function solves the Fourier-defined Poisson equation. -/
theorem hasFourierLaplacian_invLap (ω : L2) (hω : MeanZero ω) :
    HasFourierLaplacian (invLap ω) ω := by
  intro k
  rw [fourierCoeff_invLap]
  by_cases hk : k = 0
  · subst k
    simpa [normSq, MeanZero] using hω
  · simp only [hk, ite_false]
    have hn : (normSq k : ℂ) ≠ 0 := by
      exact_mod_cast (normSq_pos k hk).ne'
    field_simp

/-! ### Classical test functions and weak derivatives -/

/-- A real coordinate line on the torus; coordinate 0 is x, coordinate 1 is y. -/
def coordinateLine (j : Fin 2) (p : Torus) (t : ℝ) : Torus :=
  if j = 0 then ((t : Angle), p.2) else (p.1, (t : Angle))

/-- A continuous classical coordinate derivative, defined through the periodic real lift. -/
def HasClassicalPartial (j : Fin 2) (φ dφ : C(Torus, ℂ)) : Prop :=
  ∀ p t, HasDerivAt (fun s => φ (coordinateLine j p s)) (dφ (coordinateLine j p t)) t

/-- Weak derivative tested against all periodic C1 coordinate-test pairs.
The bilinear distributional pairing has no complex conjugation. -/
def HasWeakPartial (j : Fin 2) (g h : L2) : Prop :=
  ∀ φ dφ : C(Torus, ℂ), HasClassicalPartial j φ dφ →
    (∫ p, h p * φ p) = -(∫ p, g p * dφ p)

/-- Integration by parts on one periodic circle, including the zero frequency. -/
theorem circle_integral_fourier_partial (f df : C(AddCircle (2 * π), ℂ))
    (hdf : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s : AddCircle (2 * π)))
      (df (t : AddCircle (2 * π))) t) (n : ℤ) :
    (∫ t : AddCircle (2 * π), fourier (-n) t * df t) =
      (I * n) * ∫ t : AddCircle (2 * π), fourier (-n) t * f t := by
  let u : ℝ → ℂ := fun t => fourier (-n) (t : AddCircle (2 * π))
  let v : ℝ → ℂ := fun t => f (t : AddCircle (2 * π))
  have hu : Continuous u := (fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)
  have hv : Continuous v := f.continuous.comp (AddCircle.continuous_mk' _)
  have hdu (t : ℝ) : HasDerivAt u ((-I * n) * u t) t := by
    convert hasDerivAt_fourier_neg (2 * π) n t using 1
    simp only [u]
    congr 1
    push_cast
    field_simp
  have hducont : Continuous (fun t => (-I * n) * u t) := continuous_const.mul hu
  have hdvcont : Continuous (fun t : ℝ => df (t : AddCircle (2 * π))) :=
    df.continuous.comp (AddCircle.continuous_mk' _)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * π) hu.continuousOn hv.continuousOn
    (fun t _ => hdu t) (fun t _ => hdf t)
    (hducont.intervalIntegrable _ _) (hdvcont.intervalIntegrable _ _)
  have hperiod : ((2 * π : ℝ) : AddCircle (2 * π)) = (0 : AddCircle (2 * π)) := by
    simp
  dsimp only [u, v] at hibp
  rw [hperiod] at hibp
  simp only [AddCircle.coe_zero, sub_self, zero_sub] at hibp
  have hl := AddCircle.intervalIntegral_preimage (2 * π) 0
    (fun t => fourier (-n) t * df t)
  have hr := AddCircle.intervalIntegral_preimage (2 * π) 0
    (fun t => fourier (-n) t * f t)
  simp only [zero_add] at hl hr
  rw [← hl, ← hr]
  simpa only [mul_assoc, neg_mul, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, neg_neg] using hibp

/-- The x derivative of a classical test has the expected Fourier coefficient. -/
theorem classicalPartial_integral_x (φ dφ : C(Torus, ℂ))
    (hd : HasClassicalPartial 0 φ dφ) (k : ℤ × ℤ) :
    (∫ p, char (-k) p * dφ p) = (I * k.1) * ∫ p, char (-k) p * φ p := by
  have hint (f : C(Torus, ℂ)) : Integrable (fun p => char (-k) p * f p) := by
    exact ((char (-k) * f).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hintφ := hint φ
  have hintd := hint dφ
  rw [Measure.volume_eq_prod] at hintφ hintd ⊢
  rw [integral_prod_symm _ hintd, integral_prod_symm _ hintφ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : C(AddCircle (2 * π), ℂ) :=
    ⟨fun x => φ (x, y), φ.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let df : C(AddCircle (2 * π), ℂ) :=
    ⟨fun x => dφ (x, y), dφ.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hdf (t : ℝ) : HasDerivAt (fun s : ℝ => f (s : AddCircle (2 * π)))
      (df (t : AddCircle (2 * π))) t := by
    convert! hd (0, y) t using 1
  have hs := circle_integral_fourier_partial f df hdf k.1
  change (∫ x : Angle, fourier (-k.1) x * fourier (-k.2) y * dφ (x, y)) =
    (I * k.1) * ∫ x : Angle, fourier (-k.1) x * fourier (-k.2) y * φ (x, y)
  have reorder (a b c : ℂ) : a * b * c = b * (a * c) := by ring
  simp_rw [reorder]
  rw [integral_const_mul, integral_const_mul]
  have hs' : (∫ x : Angle, fourier (-k.1) x * dφ (x, y)) =
      (I * k.1) * ∫ x : Angle, fourier (-k.1) x * φ (x, y) := hs
  rw [hs']
  ring

/-- The y derivative of a classical test has the expected Fourier coefficient. -/
theorem classicalPartial_integral_y (φ dφ : C(Torus, ℂ))
    (hd : HasClassicalPartial 1 φ dφ) (k : ℤ × ℤ) :
    (∫ p, char (-k) p * dφ p) = (I * k.2) * ∫ p, char (-k) p * φ p := by
  have hint (f : C(Torus, ℂ)) : Integrable (fun p => char (-k) p * f p) := by
    exact ((char (-k) * f).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hintφ := hint φ
  have hintd := hint dφ
  rw [Measure.volume_eq_prod] at hintφ hintd ⊢
  rw [integral_prod _ hintd, integral_prod _ hintφ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  let f : C(AddCircle (2 * π), ℂ) :=
    ⟨fun y => φ (x, y), φ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let df : C(AddCircle (2 * π), ℂ) :=
    ⟨fun y => dφ (x, y), dφ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hdf (t : ℝ) : HasDerivAt (fun s : ℝ => f (s : AddCircle (2 * π)))
      (df (t : AddCircle (2 * π))) t := by
    convert! hd (x, 0) t using 1
  have hs := circle_integral_fourier_partial f df hdf k.2
  change (∫ y : Angle, fourier (-k.1) x * fourier (-k.2) y * dφ (x, y)) =
    (I * k.2) * ∫ y : Angle, fourier (-k.1) x * fourier (-k.2) y * φ (x, y)
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  have hs' : (∫ y : Angle, fourier (-k.2) y * dφ (x, y)) =
      (I * k.2) * ∫ y : Angle, fourier (-k.2) y * φ (x, y) := hs
  rw [hs']
  ring

/-- The coefficient formula for a continuous function uses its actual continuous values. -/
theorem fourierCoeff_toLp_integral (φ : C(Torus, ℂ)) (k : ℤ × ℤ) :
    fourierCoeff (ContinuousMap.toLp 2 volume ℂ φ) k =
      ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, char (-k) p * φ p := by
  rw [fourierCoeff_eq_integral_char_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume φ] with p hp
  rw [hp]

/-- Classical continuous partial derivatives satisfy the Fourier multiplier relation. -/
theorem HasClassicalPartial.hasFourierPartial {j : Fin 2} {φ dφ : C(Torus, ℂ)}
    (hd : HasClassicalPartial j φ dφ) :
    HasFourierPartial j (ContinuousMap.toLp 2 volume ℂ φ)
      (ContinuousMap.toLp 2 volume ℂ dφ) := by
  intro k
  rw [fourierCoeff_toLp_integral, fourierCoeff_toLp_integral]
  have hs : (∫ p, char (-k) p * dφ p) =
      (I * frequencyComponent k j) * ∫ p, char (-k) p * φ p := by
    by_cases hj : j = 0
    · subst j
      exact classicalPartial_integral_x φ dφ hd k
    · have hj1 : j = 1 := by omega
      subst j
      exact classicalPartial_integral_y φ dφ hd k
  rw [hs]
  ring

/-- The Hermitian integration-by-parts identity for a classical C1 test. -/
theorem HasFourierPartial.integral_conj {j : Fin 2} {g h : L2}
    (hd : HasFourierPartial j g h) (φ dφ : C(Torus, ℂ))
    (hφ : HasClassicalPartial j φ dφ) :
    (∫ p, conj (φ p) * h p) = -(∫ p, conj (dφ p) * g p) := by
  let f : L2 := ContinuousMap.toLp 2 volume ℂ φ
  let df : L2 := ContinuousMap.toLp 2 volume ℂ dφ
  have hφFourier : HasFourierPartial j f df := hφ.hasFourierPartial
  have hs := torusFourierBasis.hasSum_inner_mul_inner f h
  have ht := (torusFourierBasis.hasSum_inner_mul_inner df g).neg
  have hterm (k : ℤ × ℤ) :
      -(⟪df, torusFourierBasis k⟫_ℂ * ⟪torusFourierBasis k, g⟫_ℂ) =
      ⟪f, torusFourierBasis k⟫_ℂ * ⟪torusFourierBasis k, h⟫_ℂ := by
    rw [← inner_conj_symm (𝕜 := ℂ) df (torusFourierBasis k),
      ← inner_conj_symm (𝕜 := ℂ) f (torusFourierBasis k)]
    simp only [← HilbertBasis.repr_apply_apply, torusFourierBasis_repr,
      hd k, hφFourier k, map_mul, Complex.conj_I, map_intCast,
      map_ofNat, Complex.conj_ofReal]
    ring
  have hinner : ⟪f, h⟫_ℂ = -⟪df, g⟫_ℂ :=
    hs.unique (HasSum.congr_fun ht (fun k => (hterm k).symm))
  have hf : (∫ p, conj (φ p) * h p) = -(∫ p, conj (dφ p) * g p) := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hinner
    convert hinner using 1
    · apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume φ] with p hp
      simp only [f, hp, RCLike.inner_apply, mul_comm]
    · congr 1
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume dφ] with p hp
      simp only [df, hp, RCLike.inner_apply, mul_comm]
  exact hf

/-- Complex conjugation preserves classical real-coordinate differentiation. -/
theorem HasClassicalPartial.conj {j : Fin 2} {φ dφ : C(Torus, ℂ)}
    (hd : HasClassicalPartial j φ dφ) :
    HasClassicalPartial j (star φ) (star dφ) := by
  intro p t
  convert! (Complex.conjCLE.hasFDerivAt).comp_hasDerivAt t (hd p t) using 1

/-- Fourier differentiation implies the bilinear integration-by-parts identity. -/
theorem HasFourierPartial.hasWeakPartial {j : Fin 2} {g h : L2}
    (hd : HasFourierPartial j g h) : HasWeakPartial j g h := by
  intro φ dφ hφ
  have hs := hd.integral_conj (star φ) (star dφ) hφ.conj
  simpa only [ContinuousMap.star_apply, star_def, starRingEnd_self_apply, mul_comm] using hs

/-- Characters have the classical coordinate derivatives used in character testing. -/
theorem classicalPartial_char (j : Fin 2) (k : ℤ × ℤ) :
    HasClassicalPartial j (char k) ((I * frequencyComponent k j : ℂ) • char k) := by
  intro p t
  rcases p with ⟨x, y⟩
  induction x using Angle.induction_on with
  | h x =>
    induction y using Angle.induction_on with
    | h y =>
      by_cases hj : j = 0
      · subst j
        have hx : HasDerivAt (fun s : ℝ => exp (I * (k.1 * s + k.2 * y)))
            (exp (I * (k.1 * t + k.2 * y)) * (I * k.1)) t := by
          simpa using ((hasDerivAt_id (t : ℂ)).const_mul (k.1 : ℂ)).add_const
            ((k.2 : ℂ) * y) |>.const_mul I |>.cexp |>.comp_ofReal
        convert! hx using 1 <;>
          simp [coordinateLine, frequencyComponent, ContinuousMap.smul_apply,
            char_coe, mul_comm]
      · have hj1 : j = 1 := by omega
        subst j
        have hy : HasDerivAt (fun s : ℝ => exp (I * (k.1 * x + k.2 * s)))
            (exp (I * (k.1 * x + k.2 * t)) * (I * k.2)) t := by
          simpa using ((hasDerivAt_id (t : ℂ)).const_mul (k.2 : ℂ)).const_add
            ((k.1 : ℂ) * x) |>.const_mul I |>.cexp |>.comp_ofReal
        convert! hy using 1 <;>
          simp [coordinateLine, frequencyComponent, ContinuousMap.smul_apply,
            char_coe, mul_comm]

open scoped ContDiff in
/-- A smooth torus test is a continuous function with a smooth periodic lift to real coordinates. -/
def IsSmoothTorusTest (φ : C(Torus, ℂ)) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ ((p.1 : Angle), (p.2 : Angle)))

/-- Weak differentiation against all smooth periodic tests and their classical derivatives. -/
def HasSmoothWeakPartial (j : Fin 2) (g h : L2) : Prop :=
  ∀ φ dφ : C(Torus, ℂ), IsSmoothTorusTest φ → HasClassicalPartial j φ dφ →
    (∫ p, h p * φ p) = -(∫ p, g p * dφ p)

open scoped ContDiff in
theorem isSmoothTorusTest_char (k : ℤ × ℤ) : IsSmoothTorusTest (char k) := by
  unfold IsSmoothTorusTest
  simp only [char_coe]
  have hx : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hy : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      I * ((k.1 : ℂ) * p.1 + (k.2 : ℂ) * p.2)) :=
    contDiff_const.mul ((contDiff_const.mul hx).add (contDiff_const.mul hy))
  exact hc.cexp

/-- The reverse implication needs only smooth characters as test functions. -/
theorem HasSmoothWeakPartial.hasFourierPartial {j : Fin 2} {g h : L2}
    (hw : HasSmoothWeakPartial j g h) : HasFourierPartial j g h := by
  intro k
  have hs := hw (char (-k)) ((I * frequencyComponent (-k) j : ℂ) • char (-k))
    (isSmoothTorusTest_char (-k)) (classicalPartial_char j (-k))
  simp only [ContinuousMap.smul_apply, smul_eq_mul] at hs
  have hr : (fun p => g p * ((I * frequencyComponent (-k) j) * char (-k) p)) =
      (fun p => (I * frequencyComponent (-k) j) * (char (-k) p * g p)) := by
    funext p
    ring
  rw [hr, integral_const_mul] at hs
  have hn : frequencyComponent (-k) j = -frequencyComponent k j := by
    unfold frequencyComponent
    split_ifs <;> rfl
  rw [fourierCoeff_eq_integral_char_neg, fourierCoeff_eq_integral_char_neg]
  calc
    _ = ((2 * π : ℂ) ^ 2)⁻¹ * (∫ p, h p * char (-k) p) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    _ = _ := by
      rw [hs, hn]
      push_cast
      ring

/-- Equivalence with integration by parts against arbitrary smooth periodic tests. -/
theorem hasFourierPartial_iff_smoothWeakPartial (j : Fin 2) (g h : L2) :
    HasFourierPartial j g h ↔ HasSmoothWeakPartial j g h := by
  constructor
  · intro hd φ dφ _ hφ
    exact hd.hasWeakPartial φ dφ hφ
  · exact HasSmoothWeakPartial.hasFourierPartial

/-- In fact the same equivalence holds for every continuous classical coordinate derivative. -/
theorem hasFourierPartial_iff_weakPartial (j : Fin 2) (g h : L2) :
    HasFourierPartial j g h ↔ HasWeakPartial j g h := by
  constructor
  · exact HasFourierPartial.hasWeakPartial
  · intro hw
    apply HasSmoothWeakPartial.hasFourierPartial
    intro φ dφ _ hφ
    exact hw φ dφ hφ

/-! ### Products with continuous functions and integration by parts in `L²` -/

theorem memLp_continuous_mul (c : C(Torus, ℂ)) (g : L2) :
    MemLp (fun t ↦ c t * g t) 2 (volume : Measure Torus) :=
  (Lp.memLp g).of_le_mul (c := ‖c‖)
    (c.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun t ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (c.norm_coe_le_norm t) (norm_nonneg _))

/-- Multiplication of an `L²` function by a continuous function. -/
def mulL2 (c : C(Torus, ℂ)) (g : L2) : L2 := (memLp_continuous_mul c g).toLp _

theorem mulL2_ae (c : C(Torus, ℂ)) (g : L2) : mulL2 c g =ᵐ[volume] fun t ↦ c t * g t :=
  (memLp_continuous_mul c g).coeFn_toLp

theorem integrable_mul_continuous (g : L2) (c : C(Torus, ℂ)) :
    Integrable (fun t ↦ g t * c t) :=
  (integrable_L2 g).mul_bdd c.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ c.norm_coe_le_norm t)

/-- `c ḡ h` is integrable for `g, h ∈ L²` and continuous `c`. -/
theorem integrable_continuous_mul_inner (c : C(Torus, ℂ)) (g h : L2) :
    Integrable (fun t ↦ c t * (conj (g t) * h t)) := by
  have hi : Integrable (fun t ↦ conj (g t) * h t) := by
    refine (L2.integrable_inner (𝕜 := ℂ) g h).congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [RCLike.inner_apply]
    ring
  exact hi.bdd_mul c.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ c.norm_coe_le_norm t)

/-- For real-valued `c`, `⟪c g, h⟫ = ∫ c ḡ h`. -/
theorem inner_mulL2 {c : C(Torus, ℂ)} (hr : ∀ t, conj (c t) = c t) (g h : L2) :
    ⟪mulL2 c g, h⟫_ℂ = ∫ t, c t * (conj (g t) * h t) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulL2_ae c g] with t ht
  rw [ht, RCLike.inner_apply, map_mul, hr]
  ring

/-- For real-valued `c`, `⟪c g, h⟫ = conj ⟪c h, g⟫`. -/
theorem inner_mulL2_swap {c : C(Torus, ℂ)} (hr : ∀ t, conj (c t) = c t) (g h : L2) :
    ⟪mulL2 c g, h⟫_ℂ = conj ⟪mulL2 c h, g⟫_ℂ := by
  rw [inner_mulL2 hr, inner_mulL2 hr, ← integral_conj]
  congr 1
  funext t
  simp only [map_mul, hr, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- Integration by parts in `L²`: `⟪b, ∂ⱼa⟫ = -⟪∂ⱼb, a⟫`, from Parseval. -/
theorem inner_swap_of_hasFourierPartial {j : Fin 2} {a da b db : L2}
    (ha : HasFourierPartial j a da) (hb : HasFourierPartial j b db) :
    ⟪b, da⟫_ℂ = -⟪db, a⟫_ℂ := by
  have hs := torusFourierBasis.hasSum_inner_mul_inner b da
  have ht := (torusFourierBasis.hasSum_inner_mul_inner db a).neg
  refine hs.unique (ht.congr_fun fun k ↦ ?_)
  rw [← inner_conj_symm (𝕜 := ℂ) db (torusFourierBasis k),
    ← inner_conj_symm (𝕜 := ℂ) b (torusFourierBasis k)]
  simp only [← HilbertBasis.repr_apply_apply, torusFourierBasis_repr, ha k, hb k, map_mul,
    Complex.conj_I, map_intCast, map_ofNat, Complex.conj_ofReal]
  ring

/-- Product rule for classical partial derivatives on the torus. -/
theorem HasClassicalPartial.mul {j : Fin 2} {φ dφ η dη : C(Torus, ℂ)}
    (hφ : HasClassicalPartial j φ dφ) (hη : HasClassicalPartial j η dη) :
    HasClassicalPartial j (φ * η) (dφ * η + φ * dη) := by
  intro p t
  exact (hφ p t).mul (hη p t)

/-- Product rule: `∂ⱼ(c g) = (∂ⱼc) g + c ∂ⱼg` for a classically differentiable `c`. -/
theorem hasFourierPartial_mulL2 {j : Fin 2} {c dc : C(Torus, ℂ)}
    (hc : HasClassicalPartial j c dc) {g dg : L2} (hg : HasFourierPartial j g dg) :
    HasFourierPartial j (mulL2 c g) (mulL2 dc g + mulL2 c dg) := by
  rw [hasFourierPartial_iff_weakPartial]
  intro η dη hη
  have hw := hg.hasWeakPartial (c * η) (dc * η + c * dη) (hc.mul hη)
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply] at hw
  have e1 : (∫ p, (mulL2 dc g + mulL2 c dg) p * η p) =
      ∫ p, g p * (dc * η) p + dg p * (c * η) p := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (mulL2 dc g) (mulL2 c dg), mulL2_ae dc g, mulL2_ae c dg]
      with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    simp only [ContinuousMap.mul_apply]
    ring
  have e2 : (∫ p, mulL2 c g p * dη p) = ∫ p, g p * (c * dη) p := by
    apply integral_congr_ae
    filter_upwards [mulL2_ae c g] with p h
    rw [h]
    simp only [ContinuousMap.mul_apply]
    ring
  have i1 := integrable_mul_continuous g (dc * η)
  have i2 := integrable_mul_continuous dg (c * η)
  have i3 := integrable_mul_continuous g (c * dη)
  simp only [ContinuousMap.mul_apply] at i1 i2 i3 e1 e2
  have hw' : (∫ p, dg p * (c p * η p)) =
      -((∫ p, g p * (dc p * η p)) + ∫ p, g p * (c p * dη p)) := by
    rw [hw, ← integral_add i1 i3]
    congr 2
    funext p
    ring
  rw [e1, e2, integral_add i1 i2, hw']
  ring

/-- `Δψ = ω` in `L²` for mean-zero `ω`. -/
theorem streamSecondPartial_add {ω : L2} (hω : MeanZero ω) :
    streamSecondPartial 0 0 ω + streamSecondPartial 1 1 ω = ω := by
  apply fourierCoeff_ext
  intro k
  rw [fourierCoeff_add, hasFourierSecondPartial_streamSecondPartial ω 0 0 k,
    hasFourierSecondPartial_streamSecondPartial ω 1 1 k, hasFourierLaplacian_invLap ω hω k]
  simp only [frequencyComponent, normSq]
  push_cast
  ring

end EulerDipoleEigenvalues
