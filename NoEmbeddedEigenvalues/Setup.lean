import NoEmbeddedEigenvalues.Fourier

/-!
# The setting and the eigenvalue equation

The space `L²(𝕋²)` on the torus `𝕋² = (ℝ/2πℤ)²`, Fourier coefficients, the inverse Laplacian,
the transport operator `L₀ = sin y ∂ₓ - sin x ∂_y`, its domain and reduction of the
eigenvalue equation (blueprint: chapter `chap:setup`). The main theorem is assembled
in `Main.lean` from the sector exclusions.

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
open scoped InnerProductSpace ENNReal

/-! ### The inverse Laplacian -/

/-- `|k|² = k₁² + k₂²`. -/
def normSq (k : ℤ × ℤ) : ℤ := k.1 ^ 2 + k.2 ^ 2

/-- The inverse Laplacian `Δ⁻¹ω = ∑_{k ≠ 0} (-ω̂_k / |k|²) e_k`. It ignores the mean of `ω`, so
it is defined on all of `L²`; the blueprint only uses it on `L²₀`. -/
def invLap (ω : L2) : L2 :=
  ∑' k : ℤ × ℤ, (if k = 0 then 0 else -fourierCoeff ω k / normSq k) • charLp k

/-- A nonzero integer frequency has squared length at least one. -/
theorem normSq_pos (k : ℤ × ℤ) (hk : k ≠ 0) : 0 < normSq k := by
  rcases k with ⟨a, b⟩
  unfold normSq
  dsimp
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hk
      simp [ha, hb]
    simpa [ha] using sq_pos_of_ne_zero hb
  · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]

/-- The inverse-Laplacian coefficient multiplier is bounded by one. -/
theorem norm_invLap_coeff_le (ω : L2) (k : ℤ × ℤ) :
    ‖(if k = 0 then 0 else -fourierCoeff ω k / normSq k : ℂ)‖ ≤ ‖fourierCoeff ω k‖ := by
  split_ifs with hk
  · simp
  · have hpos := normSq_pos k hk
    have hone : (1 : ℝ) ≤ (normSq k : ℝ) := by exact_mod_cast hpos
    rw [norm_div, norm_neg, Complex.norm_int_of_nonneg hpos.le]
    exact div_le_self (norm_nonneg _) hone

/-- The intended inverse-Laplacian coefficients are square summable. -/
theorem summable_sq_invLap_coeff (ω : L2) :
    Summable (fun k => ‖(if k = 0 then 0 else -fourierCoeff ω k / normSq k : ℂ)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_invLap_coeff_le ω k) 2)
    (summable_sq_fourierCoeff ω)

/-- The `invLap` series converges in `L²` (blueprint: `lem:inverse-laplacian-fourier`). -/
theorem hasSum_invLap (ω : L2) :
    HasSum (fun k : ℤ × ℤ =>
      (if k = 0 then 0 else -fourierCoeff ω k / normSq k) • charLp k) (invLap ω) :=
  (summable_fourier_series _ (summable_sq_invLap_coeff ω)).hasSum

/-- The inverse Laplacian has the intended Fourier coefficients, including its zero mode. -/
theorem fourierCoeff_invLap (ω : L2) (k : ℤ × ℤ) :
    fourierCoeff (invLap ω) k = if k = 0 then 0 else -fourierCoeff ω k / normSq k := by
  exact fourierCoeff_tsum _ (summable_sq_invLap_coeff ω) k

/-- The inverse Laplacian ignores the input mean and always has mean zero. -/
theorem meanZero_invLap (ω : L2) : MeanZero (invLap ω) := by
  simp [MeanZero, fourierCoeff_invLap]

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

/-- Expanding the sines gives four neighboring modes (blueprint: `lem:transport-fourier`). -/
theorem L0char_fourier (k : ℤ × ℤ) :
    L0char k =
      (k.1 / 2 : ℂ) • (char (k + (0, 1)) - char (k - (0, 1))) -
        (k.2 / 2 : ℂ) • (char (k + (1, 0)) - char (k - (1, 0))) := by
  ext ⟨x, y⟩
  induction x using Angle.induction_on with
  | h x =>
    induction y using Angle.induction_on with
    | h y =>
      change I * (k.1 * Angle.sin (y : Angle) - k.2 * Angle.sin (x : Angle)) *
        char k ((x : Angle), (y : Angle)) = _
      simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
        char_coe, Angle.sin_coe, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Int.cast_add, Int.cast_sub, Int.cast_one, add_zero, sub_zero]
      have yp : I * (k.1 * x + ((k.2 : ℂ) + 1) * y) =
          I * (k.1 * x + k.2 * y) + (y : ℂ) * I := by ring
      have ym : I * (k.1 * x + ((k.2 : ℂ) - 1) * y) =
          I * (k.1 * x + k.2 * y) + ((-y : ℝ) : ℂ) * I := by push_cast; ring
      have xp : I * (((k.1 : ℂ) + 1) * x + k.2 * y) =
          I * (k.1 * x + k.2 * y) + (x : ℂ) * I := by ring
      have xm : I * (((k.1 : ℂ) - 1) * x + k.2 * y) =
          I * (k.1 * x + k.2 * y) + ((-x : ℝ) : ℂ) * I := by push_cast; ring
      rw [yp, ym, xp, xm]
      simp only [Complex.exp_add]
      rw [Complex.exp_ofReal_mul_I y, Complex.exp_ofReal_mul_I (-y),
        Complex.exp_ofReal_mul_I x, Complex.exp_ofReal_mul_I (-x)]
      simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring

/-- `L₀ e_k` as an element of `L²`. -/
def L0charLp (k : ℤ × ℤ) : L2 := ContinuousMap.toLp 2 volume ℂ (L0char k)

/-- The same four-mode identity in `L²`. -/
theorem L0charLp_fourier (k : ℤ × ℤ) :
    L0charLp k =
      (k.1 / 2 : ℂ) • (charLp (k + (0, 1)) - charLp (k - (0, 1))) -
        (k.2 / 2 : ℂ) • (charLp (k + (1, 0)) - charLp (k - (1, 0))) := by
  unfold L0charLp charLp
  rw [L0char_fourier, map_sub, map_smul, map_smul, map_sub, map_sub]

/-- The weak transport pairing in Fourier coordinates. -/
theorem fourier_transport_pairing (g : L2) (k : ℤ × ℤ) :
    ((2 * π : ℂ) ^ 2)⁻¹ * (-⟪L0charLp k, g⟫_ℂ) =
      (k.1 * (fourierCoeff g (k - (0, 1)) - fourierCoeff g (k + (0, 1))) -
        k.2 * (fourierCoeff g (k - (1, 0)) - fourierCoeff g (k + (1, 0)))) / 2 := by
  rw [L0charLp_fourier]
  simp only [inner_sub_left, inner_smul_left, map_div₀, map_intCast, map_ofNat,
    fourierCoeff]
  ring

/-- `L₀ g = h` in the weak sense, tested against the characters: since `L₀` is a real vector
field with zero divergence, `∫ (L₀ g) φ = -∫ g L₀φ`; with `φ = conj e_k` this reads
`⟪e_k, h⟫ = -⟪L₀ e_k, g⟫`. -/
def HasL0 (g h : L2) : Prop := ∀ k : ℤ × ℤ, ⟪charLp k, h⟫_ℂ = -⟪L0charLp k, g⟫_ℂ

/-- Weak transport sends zero to zero. -/
theorem HasL0.zero : HasL0 0 0 := by
  intro k
  simp

/-- Weak transport is additive. -/
theorem HasL0.add {g₁ h₁ g₂ h₂ : L2} (h₁L0 : HasL0 g₁ h₁) (h₂L0 : HasL0 g₂ h₂) :
    HasL0 (g₁ + g₂) (h₁ + h₂) := by
  intro k
  rw [inner_add_right, inner_add_right, h₁L0 k, h₂L0 k, neg_add]

/-- Weak transport respects subtraction. -/
theorem HasL0.sub {g₁ h₁ g₂ h₂ : L2} (h₁L0 : HasL0 g₁ h₁) (h₂L0 : HasL0 g₂ h₂) :
    HasL0 (g₁ - g₂) (h₁ - h₂) := by
  intro k
  rw [inner_sub_right, inner_sub_right, h₁L0 k, h₂L0 k]
  ring

/-- Weak transport is complex linear, since the unknown occupies the second argument. -/
theorem HasL0.smul {g h : L2} (hL0 : HasL0 g h) (c : ℂ) :
    HasL0 (c • g) (c • h) := by
  intro k
  rw [inner_smul_right, inner_smul_right, hL0 k, mul_neg]

/-- The weak definition of `L₀` agrees with the Fourier formula of the blueprint
(`lem:transport-fourier`). -/
theorem hasL0_iff_fourierCoeff (g h : L2) :
    HasL0 g h ↔ ∀ k : ℤ × ℤ, fourierCoeff h k =
      (k.1 * (fourierCoeff g (k - (0, 1)) - fourierCoeff g (k + (0, 1))) -
        k.2 * (fourierCoeff g (k - (1, 0)) - fourierCoeff g (k + (1, 0)))) / 2 := by
  constructor
  · intro hL0 k
    rw [fourierCoeff, hL0 k]
    exact fourier_transport_pairing g k
  · intro hcoeff k
    have h := hcoeff k
    rw [← fourier_transport_pairing g k] at h
    unfold fourierCoeff at h
    exact mul_left_cancel₀ (by
      exact inv_ne_zero (pow_ne_zero 2 (by
        exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)))) h

/-- An integer component bounded by `|k|²` is absorbed by the inverse Laplacian. -/
theorem norm_mul_fourierCoeff_invLap_le (ω : L2) (k : ℤ × ℤ) (a : ℤ)
    (ha : |a| ≤ normSq k) :
    ‖(a : ℂ) * fourierCoeff (invLap ω) k‖ ≤ ‖fourierCoeff ω k‖ := by
  rw [fourierCoeff_invLap]
  split_ifs with hk
  · simp
  · have hpos := normSq_pos k hk
    have hposR : (0 : ℝ) < normSq k := by exact_mod_cast hpos
    have haR : |(a : ℝ)| ≤ (normSq k : ℝ) := by exact_mod_cast ha
    rw [norm_mul, norm_div, norm_neg, Complex.norm_intCast,
      Complex.norm_int_of_nonneg hpos.le, ← mul_div_assoc]
    apply (div_le_iff₀ hposR).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right haR (norm_nonneg _)

/-- Each component of an integer frequency is bounded by its squared length. -/
theorem abs_components_le_normSq (k : ℤ × ℤ) :
    |k.1| ≤ normSq k ∧ |k.2| ≤ normSq k := by
  have h1 := Int.natAbs_le_self_sq k.1
  have h2 := Int.natAbs_le_self_sq k.2
  rw [Int.natCast_natAbs] at h1 h2
  unfold normSq
  constructor <;> nlinarith [sq_nonneg k.1, sq_nonneg k.2]

/-- The transport coefficients of the stream function are square summable. -/
theorem summable_sq_transport_invLap (ω : L2) :
    Summable (fun k : ℤ × ℤ =>
      ‖(k.1 * (fourierCoeff (invLap ω) (k - (0, 1)) -
          fourierCoeff (invLap ω) (k + (0, 1))) -
        k.2 * (fourierCoeff (invLap ω) (k - (1, 0)) -
          fourierCoeff (invLap ω) (k + (1, 0)))) / 2‖ ^ 2) := by
  have hω : Memℓp (fourierCoeff ω) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summable_sq_fourierCoeff ω
  let f1 : (ℤ × ℤ) → ℂ := fun k => k.1 * fourierCoeff (invLap ω) k
  let f2 : (ℤ × ℤ) → ℂ := fun k => k.2 * fourierCoeff (invLap ω) k
  have hf1 : Memℓp f1 2 := hω.mono' fun k =>
    norm_mul_fourierCoeff_invLap_le ω k k.1 (abs_components_le_normSq k).1
  have hf2 : Memℓp f2 2 := hω.mono' fun k =>
    norm_mul_fourierCoeff_invLap_le ω k k.2 (abs_components_le_normSq k).2
  have shift (f : (ℤ × ℤ) → ℂ) (hf : Memℓp f 2) (a : ℤ × ℤ) :
      Memℓp (fun k => f (k + a)) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)] at hf ⊢
    exact (Equiv.addRight a).summable_iff.mpr hf
  have hc := (((shift f1 hf1 (-(0, 1))).sub (shift f1 hf1 (0, 1))).sub
    ((shift f2 hf2 (-(1, 0))).sub (shift f2 hf2 (1, 0)))).const_mul (2 : ℂ)⁻¹
  have ht : Memℓp (fun k : ℤ × ℤ =>
      (k.1 * (fourierCoeff (invLap ω) (k - (0, 1)) -
          fourierCoeff (invLap ω) (k + (0, 1))) -
        k.2 * (fourierCoeff (invLap ω) (k - (1, 0)) -
          fourierCoeff (invLap ω) (k + (1, 0)))) / 2) 2 := by
    convert hc using 1
    ext k
    dsimp only [f1, f2, Pi.sub_apply]
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      neg_zero, add_zero, sub_eq_add_neg]
    ring
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    ht.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

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
  have hadd : fourierCoeff (h₀ + h₁) k = fourierCoeff h₀ k + fourierCoeff h₁ k := by
    simp only [fourierCoeff, inner_add_right, mul_add]
  rw [hadd, h₀deriv k, h₁deriv k]
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

/-- Any integer multiplier dominated by `|k|²` yields square-summable stream coefficients. -/
theorem summable_sq_invLap_multiplier (ω : L2) (a : (ℤ × ℤ) → ℤ)
    (ha : ∀ k, |a k| ≤ normSq k) :
    Summable (fun k => ‖(a k : ℂ) * fourierCoeff (invLap ω) k‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _)
      (norm_mul_fourierCoeff_invLap_le ω k (a k) (ha k)) 2)
    (summable_sq_fourierCoeff ω)

/-- The stream function has each first derivative in `L²`, defined by Fourier multipliers. -/
theorem exists_fourierPartial_invLap (ω : L2) (j : Fin 2) :
    ∃ h, HasFourierPartial j (invLap ω) h := by
  have hs := summable_sq_invLap_multiplier ω (fun k => frequencyComponent k j)
    (fun k => abs_frequencyComponent_le_normSq k j)
  have hs' : Summable (fun k =>
      ‖(I * frequencyComponent k j) * fourierCoeff (invLap ω) k‖ ^ 2) := by
    simpa only [mul_assoc, norm_mul, Complex.norm_I, one_mul] using hs
  obtain ⟨h, hh⟩ := exists_fourierCoeff _ hs'
  exact ⟨h, hh⟩

/-- The stream function has each second derivative in `L²`, defined by Fourier multipliers. -/
theorem exists_fourierSecondPartial_invLap (ω : L2) (i j : Fin 2) :
    ∃ h, HasFourierSecondPartial i j (invLap ω) h := by
  have hs := summable_sq_invLap_multiplier ω
    (fun k => frequencyComponent k i * frequencyComponent k j)
    (fun k => abs_frequencyProduct_le_normSq k i j)
  have hs' : Summable (fun k =>
      ‖-((frequencyComponent k i : ℂ) * frequencyComponent k j) *
        fourierCoeff (invLap ω) k‖ ^ 2) := by
    simpa only [Int.cast_mul, neg_mul, norm_neg] using hs
  obtain ⟨h, hh⟩ := exists_fourierCoeff _ hs'
  exact ⟨h, hh⟩

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

/-! ### The domain, the linearized operator and the eigenvalue equation -/

/-- The operator domain `𝒟 = {g ∈ L²₀ : L₀ g ∈ L²}`. -/
def Dom : Set L2 := {g | MeanZero g ∧ ∃ h, HasL0 g h}

/-- The stream function is in the domain of `L₀` (blueprint: `lem:L0-stream`). -/
theorem exists_hasL0_invLap (ω : L2) : ∃ h, HasL0 (invLap ω) h := by
  obtain ⟨h, hh⟩ := exists_fourierCoeff _ (summable_sq_transport_invLap ω)
  exact ⟨h, (hasL0_iff_fourierCoeff _ _).mpr hh⟩

/-- `L ω = h` for the linearized operator `L = L₀(I + Δ⁻¹)` with domain `𝒟`. -/
def HasL (ω h : L2) : Prop := ω ∈ Dom ∧ HasL0 (ω + invLap ω) h

/-- `ω` solves the eigenvalue problem `H(ω + ψ) = λω`, `ψ = Δ⁻¹ω`, `H = -iL₀`, i.e.
`L₀(ω + ψ) = iλω` (blueprint: `def:eigen-problem`). -/
def IsEigenSolution (lam : ℝ) (ω : L2) : Prop :=
  MeanZero ω ∧ HasL0 (ω + invLap ω) ((I * lam) • ω)

/-- Reduction to the real-parameter equation (blueprint: `lem:reduction`). -/
theorem hasL_iff_isEigenSolution (lam : ℝ) (ω : L2) :
    HasL ω ((I * lam) • ω) ↔ IsEigenSolution lam ω := by
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · rintro ⟨hmean, heigen⟩
    obtain ⟨hψ, hψL0⟩ := exists_hasL0_invLap ω
    have hω : HasL0 ω ((I * lam) • ω - hψ) := by
      simpa only [add_sub_cancel_right] using heigen.sub hψL0
    exact ⟨⟨hmean, ⟨_, hω⟩⟩, heigen⟩

end NoEmbeddedEigenvalues

end
