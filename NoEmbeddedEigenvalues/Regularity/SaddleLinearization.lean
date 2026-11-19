import NoEmbeddedEigenvalues.Regularity.SaddleNormalForm
import NoEmbeddedEigenvalues.DipoleFlow

/-! # The linearized Hamiltonian at a saddle -/

noncomputable section
namespace NoEmbeddedEigenvalues

/-- The Jacobian of the dipole velocity in the orthonormal saddle chart, applied to `q`. -/
def saddleLinearVelocity (P q : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (fun z ↦ fderiv ℝ (saddleOrthoCoord P) P
    (dipoleVelocity (saddleOrthoChart P z))) 0 q

/-- The first-order operator `-i L_s` obtained by retaining the linear part of the flow. -/
def saddleLinearHamiltonian (P : ℝ × ℝ) (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  -Complex.I * ((saddleLinearVelocity P q).1 • coordPartial 0 f q +
    (saddleLinearVelocity P q).2 • coordPartial 1 f q)

/-- The normalized axes diagonalize the saddle Jacobian and give the two eigenvalues
of the linearized Hamiltonian on homogeneous linear polynomials. -/
theorem saddle_linearization {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    let s := Real.cos P.1
    (∀ q, saddleLinearVelocity P q = (-s * q.1, s * q.2)) ∧
    (∀ q, saddleLinearHamiltonian P (fun z ↦ (z.1 : ℂ)) q = Complex.I * s * q.1) ∧
    (∀ q, saddleLinearHamiltonian P (fun z ↦ (z.2 : ℂ)) q = -Complex.I * s * q.2) := by
  sorry

end NoEmbeddedEigenvalues
