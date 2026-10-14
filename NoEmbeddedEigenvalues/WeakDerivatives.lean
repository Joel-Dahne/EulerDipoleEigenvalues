import NoEmbeddedEigenvalues.Setup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fourier derivatives and classical test functions

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
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff

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

/-- A smooth torus test is a continuous function with a smooth periodic lift to real coordinates. -/
def IsSmoothTorusTest (φ : C(Torus, ℂ)) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ ((p.1 : Angle), (p.2 : Angle)))

/-- Weak differentiation against all smooth periodic tests and their classical derivatives. -/
def HasSmoothWeakPartial (j : Fin 2) (g h : L2) : Prop :=
  ∀ φ dφ : C(Torus, ℂ), IsSmoothTorusTest φ → HasClassicalPartial j φ dφ →
    (∫ p, h p * φ p) = -(∫ p, g p * dφ p)

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

end NoEmbeddedEigenvalues
