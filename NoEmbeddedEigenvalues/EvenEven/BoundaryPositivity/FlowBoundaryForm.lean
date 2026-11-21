import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Function.JacobianOneDim
import NoEmbeddedEigenvalues.Geometry.SeparatrixArcs.SeparatrixArc
import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.WeightedBoundaryForm

/-!
# The boundary form in flow time

Blueprint: `def:boundary-form`, `lem:boundary-form-xi`, `lem:ee-trace-positivity`.

With `P = -i ∂ₛ`, the boundary form of the even–even sector is
`𝓕_λ(z) = ½ ∫ cosh² s |∂ₛ(P - λ)z|² ds - Re ∫ Pz · conj((P - λ)z) ds` over `s ∈ ℝ`.
As for `boundaryForm`, the derivatives `z' = z₁` and `z₁' = z₂` are explicit
arguments. Under `ξ = tanh s`, with `F(ξ) = z(s)`, one has `z₁ = w F'` and
`z₂ = w (w F'' - 2ξ F')` for `w = 1 - ξ²`, and `𝓕_λ(z) = 𝓑_λ(F, F', F'')`.
The substitution is Mathlib's change of variables for the injective map `tanh`,
which needs no integrability; integrability is only used to split the second
integral.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex ComplexConjugate MeasureTheory Set

/-- The boundary form in flow time `s`, with explicit derivatives `z₁ = z'`, `z₂ = z₁'`. -/
def flowBoundaryForm (lam : ℝ) (z z₁ z₂ : ℝ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * (∫ s, Real.cosh s ^ 2 * normSq (-I * z₂ s - lam * z₁ s)) -
    ∫ s, (-I * z₁ s * conj (-I * z₁ s - lam * z s)).re

/-- `z(s) = F(tanh s)`. -/
def flowValue (F : ℝ → ℂ) (s : ℝ) : ℂ := F (Real.tanh s)

/-- `z'(s) = w F'(tanh s)`. -/
def flowFirst (D : ℝ → ℂ) (s : ℝ) : ℂ := (boundaryWeight (Real.tanh s) : ℂ) * D (Real.tanh s)

/-- `z''(s) = w (w F'' - 2ξ F')(tanh s)`. -/
def flowSecond (D E : ℝ → ℂ) (s : ℝ) : ℂ :=
  (boundaryWeight (Real.tanh s) : ℂ) *
    ((boundaryWeight (Real.tanh s) : ℂ) * E (Real.tanh s) - 2 * (Real.tanh s : ℂ) * D (Real.tanh s))

theorem boundaryWeight_tanh (s : ℝ) : boundaryWeight (Real.tanh s) = 1 / Real.cosh s ^ 2 :=
  one_sub_tanh_sq s

/-- The substitution `ξ = tanh s`, `dξ = ds / cosh² s`. -/
theorem integral_tanh_subst {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : ℝ → G) : ∫ s, (1 / Real.cosh s ^ 2) • g (Real.tanh s) = ∫ ξ in Ioo (-1) 1, g ξ := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_tanh x).hasDerivWithinAt) Real.tanh_injective.injOn g
  rw [Real.tanh_bijOn.image_eq, Measure.restrict_univ] at h
  rw [h]
  congr 1
  funext s
  rw [one_sub_tanh_sq, abs_of_pos (by have := Real.cosh_pos s; positivity)]

/-- The chain rule for `z = F ∘ tanh`. -/
theorem hasDerivAt_flowValue {F D : ℝ → ℂ} {s : ℝ}
    (hF : HasDerivAt F (D (Real.tanh s)) (Real.tanh s)) :
    HasDerivAt (flowValue F) (flowFirst D s) s := by
  convert hF.scomp s (hasDerivAt_tanh s) using 1
  · rfl
  · rw [flowFirst, Complex.real_smul]
    rfl

/-- The chain rule for `z' = (w F') ∘ tanh`. -/
theorem hasDerivAt_flowFirst {D E : ℝ → ℂ} {s : ℝ}
    (hD : HasDerivAt D (E (Real.tanh s)) (Real.tanh s)) :
    HasDerivAt (flowFirst D) (flowSecond D E s) s := by
  have hw := ((hasDerivAt_boundaryWeight (Real.tanh s)).comp s (hasDerivAt_tanh s)).ofReal_comp
  convert hw.mul (hD.scomp s (hasDerivAt_tanh s)) using 1
  · rfl
  · simp only [flowSecond, boundaryWeight, Complex.real_smul, Function.comp_apply]
    push_cast
    ring

/-- The boundary form in the variable `ξ = tanh s`. -/
theorem HasWeightedBoundaryH2.flowBoundaryForm_eq {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    flowBoundaryForm lam (flowValue F) (flowFirst D) (flowSecond D E) =
      boundaryForm lam F D E := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  have hio : ∀ g : ℝ → ℝ, ∫ x in (-1 : ℝ)..1, g x = ∫ x in Ioo (-1) 1, g x := fun g ↦ by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have h1 : (∫ s, Real.cosh s ^ 2 * normSq (-I * flowSecond D E s - lam * flowFirst D s)) =
      ∫ x in (-1 : ℝ)..1,
        normSq ((boundaryWeight x : ℂ) * E x - (2 * x : ℂ) * D x - I * lam * D x) := by
    rw [hio, ← integral_tanh_subst]
    congr 1
    funext s
    have hc := (Real.cosh_pos s).ne'
    rw [smul_eq_mul, flowSecond, flowFirst,
      show -I * ((boundaryWeight (Real.tanh s) : ℂ) * ((boundaryWeight (Real.tanh s) : ℂ) *
          E (Real.tanh s) - 2 * (Real.tanh s : ℂ) * D (Real.tanh s))) -
          (lam : ℂ) * ((boundaryWeight (Real.tanh s) : ℂ) * D (Real.tanh s)) =
        ((boundaryWeight (Real.tanh s) : ℂ) * -I) * ((boundaryWeight (Real.tanh s) : ℂ) *
          E (Real.tanh s) - (2 * (Real.tanh s : ℂ)) * D (Real.tanh s) -
            I * lam * D (Real.tanh s)) by ring_nf; rw [I_sq]; ring,
      normSq_mul, normSq_mul, normSq_ofReal, normSq_neg, normSq_I, boundaryWeight_tanh]
    field_simp
  have h2 : (∫ s, (-I * flowFirst D s * conj (-I * flowFirst D s - lam * flowValue F s)).re) =
      ∫ x in (-1 : ℝ)..1, (boundaryWeight x * normSq (D x) - lam * (D x * conj (F x)).im) := by
    rw [hio, ← integral_tanh_subst]
    congr 1
    funext s
    simp only [flowFirst, flowValue, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      normSq_apply]
    rw [← boundaryWeight_tanh]
    ring
  have hB := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 h.integrable_weight_normSq
  have hC := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
    (integrable_im_mul_conj_of_memLp h.h1.memLp_derivative h.h1.memLp_value)
  rw [flowBoundaryForm, boundaryForm, h1, h2, intervalIntegral.integral_sub hB (hC.const_mul lam),
    intervalIntegral.integral_const_mul]
  ring

/-- Positivity of the flow-time boundary form for equal or opposite traces. -/
theorem HasWeightedBoundaryH2.flowBoundaryForm_nonneg {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hends : intervalH1Extension (-1) 1 F D 1 = intervalH1Extension (-1) 1 F D (-1) ∨
      intervalH1Extension (-1) 1 F D 1 = -intervalH1Extension (-1) 1 F D (-1)) :
    0 ≤ flowBoundaryForm lam (flowValue F) (flowFirst D) (flowSecond D E) := by
  rw [h.flowBoundaryForm_eq lam]
  exact h.boundaryForm_nonneg lam hends

end NoEmbeddedEigenvalues
