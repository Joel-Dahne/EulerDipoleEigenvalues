import Mathlib.Analysis.Fourier.AddCircle
import NoEmbeddedEigenvalues.Symmetry

/-!
# Lebesgue and Fourier foundations on the torus

The measure, complex `L²` space, characters, Fourier coefficients and mean-zero
condition for `Torus = Angle × Angle` (blueprint: `def:torus`).
This lower-level module is shared by the Fourier infrastructure and Setup.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Complex
open scoped InnerProductSpace ComplexConjugate

instance : Fact (0 < 2 * π) := ⟨by positivity⟩

theorem two_pi_ne_zero_complex : (2 * π : ℂ) ≠ 0 := by
  exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)

/-- The normalization factor of the Fourier coefficients is nonzero. -/
theorem two_pi_sq_inv_ne_zero : ((2 * π : ℂ) ^ 2)⁻¹ ≠ 0 :=
  inv_ne_zero (pow_ne_zero 2 two_pi_ne_zero_complex)

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

/-- Character representatives agree almost everywhere with their continuous functions. -/
theorem charLp_ae_eq (k : ℤ × ℤ) : charLp k =ᵐ[volume] char k :=
  ContinuousMap.coeFn_toLp volume (char k)

/-- Conjugation of a character reverses its frequency. -/
theorem char_neg (k : ℤ × ℤ) (p : Torus) : char (-k) p = conj (char k p) := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change fourier (-k.1) p.1 * fourier (-k.2) p.2 =
    conj (fourier k.1 p.1 * fourier k.2 p.2)
  rw [fourier_neg, fourier_neg, map_mul]

/-- The zero-frequency character is the constant function one. -/
theorem char_zero (p : Torus) : char 0 p = 1 := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change fourier (T := 2 * π) 0 p.1 * fourier (T := 2 * π) 0 p.2 = 1
  rw [fourier_zero, fourier_zero, mul_one]

/-- The character of a sum of torus points is the product of their characters. -/
theorem char_add_point (k : ℤ × ℤ) (p q : Torus) :
    char k (p + q) = char k p * char k q := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p q
  change fourier k.1 (p.1 + q.1) * fourier k.2 (p.2 + q.2) =
    (fourier k.1 p.1 * fourier k.2 p.2) * (fourier k.1 q.1 * fourier k.2 q.2)
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  ring

theorem char_neg_point (k : ℤ × ℤ) (p : Torus) : char k (-p) = char (-k) p := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change fourier k.1 (-p.1) * fourier k.2 (-p.2) =
    fourier (-k.1) p.1 * fourier (-k.2) p.2
  simp only [fourier_apply, smul_neg, neg_smul]

theorem char_ne_zero (k : ℤ × ℤ) (p : Torus) : char k p ≠ 0 := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  have hn : ‖char k p‖ = 1 := by
    change ‖fourier k.1 p.1 * fourier k.2 p.2‖ = 1
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  intro hz
  rw [hz, norm_zero] at hn
  norm_num at hn

/-! ### Linearity of the coefficients -/

theorem fourierCoeff_add (g h : L2) (k : ℤ × ℤ) :
    fourierCoeff (g + h) k = fourierCoeff g k + fourierCoeff h k := by
  simp only [fourierCoeff, inner_add_right, mul_add]

theorem fourierCoeff_smul (c : ℂ) (g : L2) (k : ℤ × ℤ) :
    fourierCoeff (c • g) k = c * fourierCoeff g k := by
  simp only [fourierCoeff, inner_smul_right]
  ring

theorem fourierCoeff_sub (g h : L2) (k : ℤ × ℤ) :
    fourierCoeff (g - h) k = fourierCoeff g k - fourierCoeff h k := by
  simp only [fourierCoeff, inner_sub_right, mul_sub]

theorem MeanZero.add {g h : L2} (hg : MeanZero g) (hh : MeanZero h) : MeanZero (g + h) := by
  rw [MeanZero, fourierCoeff_add, hg, hh, add_zero]

theorem MeanZero.smul {g : L2} (hg : MeanZero g) (c : ℂ) : MeanZero (c • g) := by
  rw [MeanZero, fourierCoeff_smul, hg, mul_zero]

/-- An `L²` function on the finite-volume torus is integrable. -/
theorem integrable_L2 (g : L2) : Integrable g := by
  exact (Lp.memLp g).integrable (by norm_num)

/-- The character pairing in the Fourier integral is integrable. -/
theorem integrable_char_pairing (g : L2) (k : ℤ × ℤ) :
    Integrable (fun p => conj (char k p) * g p) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (charLp k) g
  apply h.congr
  filter_upwards [charLp_ae_eq k] with p hp
  simp only [hp, RCLike.inner_apply, mul_comm]

/-- The Hilbert-space coefficient is the normalized Lebesgue integral. -/
theorem fourierCoeff_eq_integral (g : L2) (k : ℤ × ℤ) :
    fourierCoeff g k = ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, conj (char k p) * g p := by
  unfold fourierCoeff
  congr 1
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [charLp_ae_eq k] with p hp
  simp only [hp, RCLike.inner_apply, mul_comm]

/-- The same integral formula with the negative-frequency character. -/
theorem fourierCoeff_eq_integral_char_neg (g : L2) (k : ℤ × ℤ) :
    fourierCoeff g k = ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, char (-k) p * g p := by
  simp only [fourierCoeff_eq_integral, char_neg]

/-- The zero coefficient is the normalized integral of the function. -/
theorem fourierCoeff_zero (g : L2) :
    fourierCoeff g 0 = ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, g p := by
  simp [fourierCoeff_eq_integral, char_zero]

/-- The coefficient definition of mean zero agrees with zero Lebesgue integral. -/
theorem meanZero_iff_integral_eq_zero (g : L2) :
    MeanZero g ↔ (∫ p, g p) = 0 := by
  rw [MeanZero, fourierCoeff_zero, mul_eq_zero]
  simp only [two_pi_sq_inv_ne_zero, false_or]

end NoEmbeddedEigenvalues

end
