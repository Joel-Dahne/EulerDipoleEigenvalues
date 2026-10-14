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

end NoEmbeddedEigenvalues

end
