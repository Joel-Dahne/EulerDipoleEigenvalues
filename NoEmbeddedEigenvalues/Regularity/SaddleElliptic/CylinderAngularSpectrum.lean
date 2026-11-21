module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderData
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Allowed angular Fourier modes from axis parity

Coefficients use probability Haar measure on the angular circle. The reflections
are θ ↦ π - θ and θ ↦ -θ. They are identities of a.e. representatives on the
circle, not restrictions of arbitrary planar representatives to a fixed circle.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- The angular forms of the two Cartesian reflection identities. -/
def HasCircleAxisParity (ε : Fin 2 → Bool) (f : AddCircle (2 * Real.pi) → ℂ) : Prop :=
  (∀ᵐ θ ∂AddCircle.haarAddCircle,
    f ((Real.pi : AddCircle (2 * Real.pi)) - θ) = paritySign (ε 0) * f θ) ∧
  (∀ᵐ θ ∂AddCircle.haarAddCircle, f (-θ) = paritySign (ε 1) * f θ)

private theorem angularCharacter_add (n : ℤ) (x y : AddCircle (2 * Real.pi)) :
    _root_.fourier n (x + y) = _root_.fourier n x * _root_.fourier n y := by
  simp only [_root_.fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

private theorem angularCharacter_neg (n : ℤ) (x : AddCircle (2 * Real.pi)) :
    _root_.fourier n (-x) = _root_.fourier (-n) x := by
  simp only [_root_.fourier_apply, smul_neg, neg_smul]

private theorem angularCharacter_pi_nat (m : ℕ) :
    _root_.fourier (m : ℤ) (Real.pi : AddCircle (2 * Real.pi)) = (-1 : ℂ) ^ m := by
  have h1 : _root_.fourier (1 : ℤ) (Real.pi : AddCircle (2 * Real.pi)) = (-1 : ℂ) := by
    rw [_root_.fourier_coe_apply, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    field_simp
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_add_one, _root_.fourier_add, ih, h1, pow_succ]

theorem cylinderAngularCharacter_pi (n : ℤ) :
    _root_.fourier n (Real.pi : AddCircle (2 * Real.pi)) = (-1 : ℂ) ^ n.natAbs := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using angularCharacter_pi_nat m
  · simp only [_root_.fourier_neg, angularCharacter_pi_nat, map_pow, map_neg, map_one,
      Int.natAbs_neg, Int.natAbs_natCast]

/-- Translation of a scalar angular Fourier coefficient, with its phase. -/
theorem cylinderAngularCoeff_translate (f : AddCircle (2 * Real.pi) → ℂ)
    (a : AddCircle (2 * Real.pi)) (n : ℤ) :
    _root_.fourierCoeff (fun x ↦ f (x + a)) n =
      _root_.fourier n a * _root_.fourierCoeff f n := by
  unfold _root_.fourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ x, _root_.fourier (-n) x * f (x + a) ∂AddCircle.haarAddCircle) =
        ∫ x, _root_.fourier (-n) (x - a) * f x ∂AddCircle.haarAddCircle := by
      simpa only [add_sub_cancel_right] using integral_add_right_eq_self
        (μ := AddCircle.haarAddCircle) (fun x ↦ _root_.fourier (-n) (x - a) * f x) a
    _ = _root_.fourier n a * ∫ x, _root_.fourier (-n) x * f x
        ∂AddCircle.haarAddCircle := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [sub_eq_add_neg, angularCharacter_add, angularCharacter_neg, neg_neg]
      ring

/-- Angular reflection reverses the Fourier index. -/
theorem cylinderAngularCoeff_neg (f : AddCircle (2 * Real.pi) → ℂ) (n : ℤ) :
    _root_.fourierCoeff (fun x ↦ f (-x)) n = _root_.fourierCoeff f (-n) := by
  unfold _root_.fourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ x, _root_.fourier (-n) x * f (-x) ∂AddCircle.haarAddCircle) =
        ∫ x, _root_.fourier (-n) (-x) * f x ∂AddCircle.haarAddCircle := by
      simpa only [neg_neg] using integral_neg_eq_self
        (fun x : AddCircle (2 * Real.pi) ↦ _root_.fourier (-n) (-x) * f x) AddCircle.haarAddCircle
    _ = _ := by simp only [angularCharacter_neg, neg_neg]

/-- Composing the two a.e. axis parities gives the half-turn character. -/
theorem HasCircleAxisParity.half_turn {ε : Fin 2 → Bool} {f : AddCircle (2 * Real.pi) → ℂ}
    (hp : HasCircleAxisParity ε f) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle,
      f (θ + (Real.pi : AddCircle (2 * Real.pi))) =
        (paritySign (ε 0) * paritySign (ε 1)) * f θ := by
  have h := (Measure.measurePreserving_neg AddCircle.haarAddCircle).quasiMeasurePreserving.ae
    hp.1
  filter_upwards [h, hp.2] with θ h0 h1
  simpa only [sub_neg_eq_add, add_comm _ θ, h1, mul_assoc] using h0

/-- The half-turn and second-axis identities on the actual angular coefficients. -/
theorem HasCircleAxisParity.coeff_characters {ε : Fin 2 → Bool}
    {f : AddCircle (2 * Real.pi) → ℂ} (hp : HasCircleAxisParity ε f) (n : ℤ) :
    ((-1 : ℂ) ^ n.natAbs) * _root_.fourierCoeff f n =
        (paritySign (ε 0) * paritySign (ε 1)) * _root_.fourierCoeff f n ∧
      _root_.fourierCoeff f (-n) = paritySign (ε 1) * _root_.fourierCoeff f n := by
  constructor
  · rw [← cylinderAngularCharacter_pi, ← cylinderAngularCoeff_translate]
    calc
      _root_.fourierCoeff (fun x ↦ f (x + (Real.pi : AddCircle (2 * Real.pi)))) n =
          _root_.fourierCoeff
            (fun x ↦ (paritySign (ε 0) * paritySign (ε 1)) * f x) n := by
        apply integral_congr_ae
        filter_upwards [hp.half_turn] with x hx
        simp only [hx]
      _ = _ := _root_.fourierCoeff.const_mul _ _ _
  · rw [← cylinderAngularCoeff_neg]
    calc
      _root_.fourierCoeff (fun x ↦ f (-x)) n =
          _root_.fourierCoeff (fun x ↦ paritySign (ε 1) * f x) n := by
        apply integral_congr_ae
        filter_upwards [hp.2] with x hx
        simp only [hx]
      _ = _ := _root_.fourierCoeff.const_mul _ _ _

/-- Reflection characters eliminate every forbidden signed Fourier mode. -/
theorem HasCircleAxisParity.fourierCoeff_forbidden {ε : Fin 2 → Bool}
    {f : AddCircle (2 * Real.pi) → ℂ} (hp : HasCircleAxisParity ε f)
    (n : ℤ) (hn : ¬AllowedSaddleDegree ε n.natAbs) : _root_.fourierCoeff f n = 0 := by
  by_contra hne
  have hc := hp.coeff_characters n
  have hs : (-1 : ℂ) ^ n.natAbs = paritySign (ε 0) * paritySign (ε 1) :=
    mul_right_cancel₀ hne hc.1
  apply hn
  refine ⟨?_, ?_⟩
  · rw [← neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), hs]
    cases hε0 : ε 0 <;> cases hε1 : ε 1 <;> norm_num [paritySign, hε0, hε1]
  · intro hz
    have hn0 : n = 0 := Int.natAbs_eq_zero.mp hz
    subst n
    have hs1 : (1 : ℂ) = paritySign (ε 1) :=
      mul_right_cancel₀ hne (by simpa only [neg_zero, one_mul] using hc.2)
    have hs0 : (1 : ℂ) = paritySign (ε 0) := by
      simpa only [Int.natAbs_zero, pow_zero, hs1.symm, mul_one] using hs
    have htrue (b : Bool) (hb : (1 : ℂ) = paritySign b) : b = true := by
      cases b
      · norm_num [paritySign] at hb
      · rfl
    exact ⟨htrue _ hs0, htrue _ hs1⟩

/-- For integrable angular data, all coefficient integrals are genuine and their
support is contained in the prescribed allowed degrees. -/
theorem HasCircleAxisParity.fourierCoeff_support {ε : Fin 2 → Bool}
    {f : AddCircle (2 * Real.pi) → ℂ} (hp : HasCircleAxisParity ε f)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∀ n : ℤ, Integrable (fun θ ↦ _root_.fourier (-n) θ * f θ) AddCircle.haarAddCircle) ∧
      ∀ n : ℤ, ¬AllowedSaddleDegree ε n.natAbs → _root_.fourierCoeff f n = 0 :=
  ⟨fun n ↦ by simpa only [smul_eq_mul] using hf.fourier_smul (-n),
    hp.fourierCoeff_forbidden⟩

end NoEmbeddedEigenvalues
