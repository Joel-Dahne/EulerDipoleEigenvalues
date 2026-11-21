import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The even–even boundary quadratic form

Blueprint nodes: `def:boundary-form-xi`, `def:boundary-jet`, `lem:boundary-flux`,
`lem:trace-completion-classical`, `lem:affine-splitting-classical`, and
`lem:ee-trace-positivity-classical`.

Derivatives are explicit arguments, so the same form serves classical jets and weighted
triples. The derivative identities `hasDerivAt_boundaryFlux` and
`hasDerivAt_boundaryPrimitive` are pointwise; `WeightedBoundaryForm.lean` uses them
almost everywhere to extend the results here to the weighted domain.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex ComplexConjugate MeasureTheory Set
open scoped Interval

/-- The degenerate weight on the separatrix interval. -/
def boundaryWeight (x : ℝ) : ℝ := 1 - x ^ 2

/-- The boundary form in the `ξ = tanh s` variable, with explicit first and second
    derivatives. This definition alone imposes no derivative or integrability conditions. -/
def boundaryForm (lam : ℝ) (F D E : ℝ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1,
    normSq ((boundaryWeight x : ℂ) * E x - (2 * x : ℂ) * D x - I * lam * D x)) -
  (∫ x in (-1 : ℝ)..1, boundaryWeight x * normSq (D x)) +
  lam * (∫ x in (-1 : ℝ)..1, (D x * conj (F x)).im)

/-- The expression appearing in the completed square. -/
def boundarySquare (lam : ℝ) (F D E : ℝ → ℂ) (x : ℝ) : ℂ :=
  (boundaryWeight x : ℂ) * E x - (x : ℂ) * D x + F x - I * lam * D x

/-- A classical twice differentiable jet on the closed interval. This is a smooth
    subcase of the eventual weighted Sobolev domain, not a definition of that domain. -/
structure BoundaryJet where
  value : ℝ → ℂ
  first : ℝ → ℂ
  second : ℝ → ℂ
  continuous_value : ContinuousOn value (Icc (-1) 1)
  continuous_first : ContinuousOn first (Icc (-1) 1)
  continuous_second : ContinuousOn second (Icc (-1) 1)
  deriv_value : ∀ x ∈ Icc (-1) 1, HasDerivAt value (first x) x
  deriv_first : ∀ x ∈ Icc (-1) 1, HasDerivAt first (second x) x

/-- The exact flux whose derivative is the difference between the original and
    completed-square densities. -/
def boundaryFlux (F D : ℝ → ℂ) (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * boundaryWeight x * x * normSq (D x) -
  boundaryWeight x * (D x * conj (F x)).re - (1 / 2 : ℝ) * x * normSq (F x)

/-- The derivative of `boundaryFlux`, written without derivative operators. -/
def boundaryFluxDerivative (F D E : ℝ → ℂ) (x : ℝ) : ℝ :=
  ((5 / 2 : ℝ) * x ^ 2 - 3 / 2) * normSq (D x) +
  x * (D x * conj (F x)).re - (1 / 2 : ℝ) * normSq (F x) -
  boundaryWeight x * x * (E x * conj (D x)).re -
  boundaryWeight x * (E x * conj (F x)).re

/-- The pointwise algebra behind the sum of squares, including the exact flux term. -/
theorem boundary_density_completion (lam x : ℝ) (f d e : ℂ) :
    (1 / 2 : ℝ) * normSq ((boundaryWeight x : ℂ) * e - (2 * x : ℂ) * d - I * lam * d) -
        boundaryWeight x * normSq d + lam * (d * conj f).im =
      (1 / 2 : ℝ) * normSq ((boundaryWeight x : ℂ) * e - (x : ℂ) * d + f - I * lam * d) +
        (1 / 2 : ℝ) * normSq d +
        (((5 / 2 : ℝ) * x ^ 2 - 3 / 2) * normSq d + x * (d * conj f).re -
          (1 / 2 : ℝ) * normSq f - boundaryWeight x * x * (e * conj d).re -
          boundaryWeight x * (e * conj f).re) := by
  simp [normSq_apply, boundaryWeight, Complex.mul_re, Complex.mul_im, -ofReal_pow]
  ring

theorem hasDerivAt_boundaryWeight (x : ℝ) : HasDerivAt boundaryWeight (-2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
  · ext y
    rfl
  · simp

/-- The flux identity at a single point, from pointwise first and second derivatives. -/
theorem hasDerivAt_boundaryFlux {F D E : ℝ → ℂ} {x : ℝ}
    (hf : HasDerivAt F (D x) x) (hd : HasDerivAt D (E x) x) :
    HasDerivAt (boundaryFlux F D) (boundaryFluxDerivative F D E x) x := by
  have hfr : HasDerivAt (fun y ↦ (F y).re) (D x).re x := by
    simpa using! reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hfi : HasDerivAt (fun y ↦ (F y).im) (D x).im x := by
    simpa using! imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hdr : HasDerivAt (fun y ↦ (D y).re) (E x).re x := by
    simpa using! reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hdi : HasDerivAt (fun y ↦ (D y).im) (E x).im x := by
    simpa using! imCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hw := hasDerivAt_boundaryWeight x
  have hdn := (hdr.mul hdr).add (hdi.mul hdi)
  have hfn := (hfr.mul hfr).add (hfi.mul hfi)
  have hdf := (hdr.mul hfr).add (hdi.mul hfi)
  have h := (((hw.const_mul (-(1 / 2 : ℝ))).mul (hasDerivAt_id x)).mul hdn).sub
    (hw.mul hdf) |>.sub (((hasDerivAt_id x).const_mul (1 / 2 : ℝ)).mul hfn)
  convert h using 1
  · ext y
    simp [boundaryFlux, normSq_apply, mul_re]
  · simp [boundaryFluxDerivative, normSq_apply, mul_re, boundaryWeight]
    ring

/-- The flux identity is a genuine derivative identity for a classical jet. -/
theorem BoundaryJet.hasDerivAt_flux (J : BoundaryJet) (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    HasDerivAt (boundaryFlux J.value J.first)
      (boundaryFluxDerivative J.value J.first J.second x) x :=
  hasDerivAt_boundaryFlux (J.deriv_value x hx) (J.deriv_first x hx)

/-- A primitive of the completed-square expression `boundarySquare`. -/
def boundaryPrimitive (lam : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℂ :=
  (boundaryWeight x : ℂ) * D x + (x : ℂ) * F x - I * lam * F x

/-- `boundaryPrimitive` differentiates to `boundarySquare`, pointwise. -/
theorem hasDerivAt_boundaryPrimitive (lam : ℝ) {F D E : ℝ → ℂ} {x : ℝ}
    (hf : HasDerivAt F (D x) x) (hd : HasDerivAt D (E x) x) :
    HasDerivAt (boundaryPrimitive lam F D) (boundarySquare lam F D E x) x := by
  have h := (((hasDerivAt_boundaryWeight x).ofReal_comp.mul hd).add
    ((hasDerivAt_id x).ofReal_comp.mul hf)).sub (hf.const_mul (I * lam))
  convert h using 1
  · ext y
    simp [boundaryPrimitive, boundaryWeight]
  · simp [boundarySquare, boundaryWeight, -ofReal_pow]
    ring

/-- Completion of squares with the endpoint correction retained. -/
theorem BoundaryJet.completion (J : BoundaryJet) (lam : ℝ) :
    boundaryForm lam J.value J.first J.second =
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1,
        normSq (boundarySquare lam J.value J.first J.second x)) +
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (J.first x)) -
      (1 / 2 : ℝ) * (normSq (J.value 1) + normSq (J.value (-1))) := by
  have hle : (-1 : ℝ) ≤ 1 := by linarith
  have hcF := J.continuous_value
  have hcD := J.continuous_first
  have hcE := J.continuous_second
  have hA : IntervalIntegrable (fun x ↦
      normSq ((boundaryWeight x : ℂ) * J.second x - (2 * x : ℂ) * J.first x -
        I * lam * J.first x)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    unfold boundaryWeight
    fun_prop
  have hB : IntervalIntegrable (fun x ↦ boundaryWeight x * normSq (J.first x))
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    unfold boundaryWeight
    fun_prop
  have hC : IntervalIntegrable (fun x ↦ (J.first x * conj (J.value x)).im)
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    fun_prop
  have hS : IntervalIntegrable (fun x ↦
      normSq (boundarySquare lam J.value J.first J.second x)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    unfold boundarySquare boundaryWeight
    fun_prop
  have hD : IntervalIntegrable (fun x ↦ normSq (J.first x)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    fun_prop
  have hK : IntervalIntegrable (boundaryFluxDerivative J.value J.first J.second)
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    unfold boundaryFluxDerivative boundaryWeight
    fun_prop
  have hflux := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ J.hasDerivAt_flux x (by simpa [uIcc_of_le hle] using hx)) hK
  have hid := intervalIntegral.integral_congr (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (fun x _ ↦ boundary_density_completion lam x (J.value x) (J.first x) (J.second x))
  change (∫ x in (-1 : ℝ)..1,
      (1 / 2 : ℝ) * normSq ((boundaryWeight x : ℂ) * J.second x -
        (2 * x : ℂ) * J.first x - I * lam * J.first x) -
        boundaryWeight x * normSq (J.first x) + lam * (J.first x * conj (J.value x)).im) =
    (∫ x in (-1 : ℝ)..1,
      (1 / 2 : ℝ) * normSq (boundarySquare lam J.value J.first J.second x) +
        (1 / 2 : ℝ) * normSq (J.first x) +
        boundaryFluxDerivative J.value J.first J.second x) at hid
  rw [intervalIntegral.integral_add ((hA.const_mul (1 / 2)).sub hB) (hC.const_mul lam),
    intervalIntegral.integral_sub (hA.const_mul (1 / 2)) hB,
    intervalIntegral.integral_add ((hS.const_mul (1 / 2)).add (hD.const_mul (1 / 2))) hK,
    intervalIntegral.integral_add (hS.const_mul (1 / 2)) (hD.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hflux] at hid
  simpa [boundaryForm, boundaryFlux, boundaryWeight, mul_add, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hid

/-- The smooth sum-of-squares identity for zero endpoint values. -/
theorem BoundaryJet.sum_of_squares (J : BoundaryJet) (lam : ℝ)
    (hneg : J.value (-1) = 0) (hpos : J.value 1 = 0) :
    boundaryForm lam J.value J.first J.second =
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1,
        normSq (boundarySquare lam J.value J.first J.second x)) +
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (J.first x)) := by
  simpa [hneg, hpos] using J.completion lam

/-- Subtract an affine function without changing the second derivative. -/
def BoundaryJet.subAffine (J : BoundaryJet) (a b : ℂ) : BoundaryJet where
  value x := J.value x - (a + b * (x : ℂ))
  first x := J.first x - b
  second := J.second
  continuous_value := by
    have := J.continuous_value
    fun_prop
  continuous_first := J.continuous_first.sub continuousOn_const
  continuous_second := J.continuous_second
  deriv_value x hx := by
    simpa using! (J.deriv_value x hx).sub
      (((hasDerivAt_id x).ofReal_comp.const_mul b).const_add a)
  deriv_first x hx := by
    simpa using (J.deriv_first x hx).sub_const b

/-- The completed-square expression has zero integral when the value vanishes at
    both endpoints. Its primitive is `w F' + x F - i λ F`. -/
theorem BoundaryJet.integral_square_zero (J : BoundaryJet) (lam : ℝ)
    (hneg : J.value (-1) = 0) (hpos : J.value 1 = 0) :
    (∫ x in (-1 : ℝ)..1, boundarySquare lam J.value J.first J.second x) = 0 := by
  have hle : (-1 : ℝ) ≤ 1 := by linarith
  have hcF := J.continuous_value
  have hcD := J.continuous_first
  have hcE := J.continuous_second
  have hInt : IntervalIntegrable (boundarySquare lam J.value J.first J.second)
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    unfold boundarySquare boundaryWeight
    fun_prop
  have hQ : ∀ x ∈ Icc (-1) 1, HasDerivAt (boundaryPrimitive lam J.value J.first)
      (boundarySquare lam J.value J.first J.second x) x := fun x hx ↦
    hasDerivAt_boundaryPrimitive lam (J.deriv_value x hx) (J.deriv_first x hx)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hQ x (by simpa [uIcc_of_le hle] using hx)) hInt
  simpa [boundaryPrimitive, boundaryWeight, hneg, hpos] using h

/-- A constant shift is orthogonal, under integration, to a zero-mean function. -/
theorem integral_normSq_add_const (A : ℝ → ℂ) (c : ℂ)
    (hA : IntervalIntegrable A volume (-1) 1)
    (hn : IntervalIntegrable (fun x ↦ normSq (A x)) volume (-1) 1)
    (hzero : (∫ x in (-1 : ℝ)..1, A x) = 0) :
    (∫ x in (-1 : ℝ)..1, normSq (A x + c)) =
      (∫ x in (-1 : ℝ)..1, normSq (A x)) + 2 * normSq c := by
  have hr : IntervalIntegrable (fun x ↦ (A x * conj c).re) volume (-1) 1 := by
    rw [intervalIntegrable_iff] at hA ⊢
    simpa [IntegrableOn] using (hA.mul_const (conj c)).re
  have hz : (∫ x in (-1 : ℝ)..1, (A x * conj c).re) = 0 := by
    change (∫ x in (-1 : ℝ)..1, reCLM (A x * conj c)) = 0
    rw [reCLM.intervalIntegral_comp_comm (hA.mul_const (conj c))]
    rw [intervalIntegral.integral_mul_const, hzero]
    simp
  have hid := intervalIntegral.integral_congr (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (fun x _ ↦ show normSq (A x + c) = normSq (A x) + normSq c +
        2 * (A x * conj c).re by
      simp [normSq_apply, mul_re]
      ring)
  rw [intervalIntegral.integral_add (hn.add intervalIntegrable_const) (hr.const_mul 2),
    intervalIntegral.integral_add hn intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hz] at hid
  norm_num at hid
  exact hid

/-- Smooth affine splitting: the mixed terms with the zero-endpoint remainder cancel. -/
theorem BoundaryJet.affine_splitting (J : BoundaryJet) (lam : ℝ) (a b : ℂ)
    (hneg : J.value (-1) = a - b) (hpos : J.value 1 = a + b) :
    boundaryForm lam J.value J.first J.second =
      boundaryForm lam (J.subAffine a b).value (J.subAffine a b).first
        (J.subAffine a b).second + lam ^ 2 * normSq b +
        2 * lam * (b * conj a).im := by
  let J0 := J.subAffine a b
  have hle : (-1 : ℝ) ≤ 1 := by linarith
  have h0neg : J0.value (-1) = 0 := by
    simp [J0, subAffine, hneg, sub_eq_add_neg]
  have h0pos : J0.value 1 = 0 := by
    simp [J0, subAffine, hpos]
  have hcF := J0.continuous_value
  have hcD := J0.continuous_first
  have hcE := J0.continuous_second
  have hcS : ContinuousOn (boundarySquare lam J0.value J0.first J0.second)
      (Icc (-1) 1) := by
    unfold boundarySquare boundaryWeight
    fun_prop
  have hS0 := J0.integral_square_zero lam h0neg h0pos
  have hD0 : (∫ x in (-1 : ℝ)..1, J0.first x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx ↦ J0.deriv_value x (by simpa [uIcc_of_le hle] using hx))
      (J0.continuous_first.intervalIntegrable_of_Icc hle)
    simpa [h0neg, h0pos] using h
  have hS : (∫ x in (-1 : ℝ)..1,
      normSq (boundarySquare lam J.value J.first J.second x)) =
      (∫ x in (-1 : ℝ)..1, normSq (boundarySquare lam J0.value J0.first J0.second x)) +
        2 * normSq (a - I * lam * b) := by
    rw [← integral_normSq_add_const _ (a - I * lam * b)
      (hcS.intervalIntegrable_of_Icc hle)
      (ContinuousOn.intervalIntegrable_of_Icc hle (by fun_prop)) hS0]
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg normSq
    dsimp [boundarySquare, J0, subAffine]
    ring
  have hD : (∫ x in (-1 : ℝ)..1, normSq (J.first x)) =
      (∫ x in (-1 : ℝ)..1, normSq (J0.first x)) + 2 * normSq b := by
    rw [← integral_normSq_add_const _ b (hcD.intervalIntegrable_of_Icc hle)
      (ContinuousOn.intervalIntegrable_of_Icc hle (by fun_prop)) hD0]
    apply intervalIntegral.integral_congr
    intro x _
    simp [J0, subAffine]
  rw [J.completion lam, hS, hD, hpos, hneg]
  change _ = boundaryForm lam J0.value J0.first J0.second + _ + _
  rw [J0.sum_of_squares lam h0neg h0pos]
  simp [normSq_apply, mul_re, mul_im]
  ring

/-- Boundary positivity for the classical domain, including either endpoint parity.
    See `HasWeightedBoundaryH2.boundaryForm_nonneg` for the weighted domain. -/
theorem BoundaryJet.boundaryForm_nonneg (J : BoundaryJet) (lam : ℝ)
    (hends : J.value 1 = J.value (-1) ∨ J.value 1 = -J.value (-1)) :
    0 ≤ boundaryForm lam J.value J.first J.second := by
  let a := (J.value 1 + J.value (-1)) / 2
  let b := (J.value 1 - J.value (-1)) / 2
  have hneg : J.value (-1) = a - b := by dsimp [a, b]; ring
  have hpos : J.value 1 = a + b := by dsimp [a, b]; ring
  let J0 := J.subAffine a b
  have h0neg : J0.value (-1) = 0 := by
    simp [J0, subAffine, hneg, sub_eq_add_neg]
  have h0pos : J0.value 1 = 0 := by
    simp [J0, subAffine, hpos]
  have h0 : 0 ≤ boundaryForm lam J0.value J0.first J0.second := by
    rw [J0.sum_of_squares lam h0neg h0pos]
    have hS := intervalIntegral.integral_nonneg_of_forall
      (μ := volume) (a := (-1 : ℝ)) (b := 1) (by linarith)
      (fun x ↦ normSq_nonneg (boundarySquare lam J0.value J0.first J0.second x))
    have hD := intervalIntegral.integral_nonneg_of_forall
      (μ := volume) (a := (-1 : ℝ)) (b := 1) (by linarith)
      (fun x ↦ normSq_nonneg (J0.first x))
    positivity
  rw [J.affine_splitting lam a b hneg hpos]
  rcases hends with hends | hends
  · have hb : b = 0 := by simp [b, hends]
    simpa [hb, J0] using h0
  · have ha : a = 0 := by simp [a, hends]
    simp only [ha, map_zero, mul_zero, zero_im, add_zero]
    simpa only [J0, ha] using
      add_nonneg h0 (mul_nonneg (sq_nonneg lam) (normSq_nonneg b))

end NoEmbeddedEigenvalues
