import NoEmbeddedEigenvalues.QuotientLocal
import NoEmbeddedEigenvalues.OddOddRegularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Explicit orthonormal saddle charts

The sign in the chart is cos(Pₓ), which is ±1 at a saddle. The factorization is
therefore Ψ = uv m at both torus saddle types, with the same smooth sinc factor.
Orthogonality is expressed using the Euclidean radius, not the maximum product norm.

Taylor bounds for the explicit function include derivatives through order three;
they do not come from formally differentiating a value-only big-O assertion.
The linearized Hamiltonian on linear polynomials is a separate, mixed-sector input.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff

/-- The affine saddle chart, with signs normalized so the leading dipole is uv. -/
def saddleOrthoChart (P q : ℝ × ℝ) : ℝ × ℝ :=
  (P.1 + (q.1 - Real.cos P.1 * q.2) / Real.sqrt 2,
   P.2 + (q.1 + Real.cos P.1 * q.2) / Real.sqrt 2)

/-- Inverse orthonormal coordinates, valid when P is a saddle. -/
def saddleOrthoCoord (P p : ℝ × ℝ) : ℝ × ℝ :=
  (((p.1 - P.1) + (p.2 - P.2)) / Real.sqrt 2,
   Real.cos P.1 * ((p.2 - P.2) - (p.1 - P.1)) / Real.sqrt 2)

/-- Smooth extension of the two sine ratios. -/
def saddleFactor (q : ℝ × ℝ) : ℝ :=
  Real.sinc (q.1 / Real.sqrt 2) * Real.sinc (q.2 / Real.sqrt 2)

/-- Classical derivatives, used only for the explicit smooth dipole remainder. -/
def classicalRealJet : List (Fin 2) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], f => f
  | j :: w, f => coordPartial j (classicalRealJet w f)

/-- The sinc factor is smooth, even, normalized and locally positive. -/
theorem saddleFactor_regular :
    ContDiff ℝ ∞ saddleFactor ∧ saddleFactor 0 = 1 ∧
      (∀ j q, saddleFactor (axisReflect j q) = saddleFactor q) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ localDisk 0 ρ, 0 < saddleFactor q := by
  sorry

/-- Affine inverse and Euclidean orthogonality of the saddle chart. -/
theorem saddleOrthoChart_orthogonal {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    (∀ q, saddleOrthoCoord P (saddleOrthoChart P q) = q) ∧
    (∀ p, saddleOrthoChart P (saddleOrthoCoord P p) = p) ∧
    (∀ q, localRadius P (saddleOrthoChart P q) = localRadius 0 q) := by
  sorry

/-- Exact global identity in each normalized chart (`lem:saddle-normal-form`). -/
theorem saddle_dipole_factorization {P : ℝ × ℝ} (hP : P ∈ saddleSet) (q : ℝ × ℝ) :
    dipoleLift (saddleOrthoChart P q) = q.1 * q.2 * saddleFactor q := by
  sorry

/-- The Cartesian normalization uses exactly the uv coefficient in the chart
(`lem:saddle-quadratic-chart`), with no extra sign or factor of two. -/
theorem saddleQuadratic_comp_chart {P : ℝ × ℝ} (hP : P ∈ saddleSet) (a : ℂ)
    (q : ℝ × ℝ) :
    saddleQuadratic P a (saddleOrthoChart P q) = a * ((q.1 * q.2 : ℝ) : ℂ) := by
  sorry

/-- Value, gradient-square and differentiated Taylor bounds for the explicit dipole
(`lem:saddle-normal-form-derivatives`). The constants do not depend on the point q. -/
theorem saddle_normal_form_derivatives {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ q ∈ localDisk 0 ρ,
      (∀ w : List (Fin 2), w.length ≤ 3 →
        |classicalRealJet w (fun v ↦ dipoleLift (saddleOrthoChart P v) - v.1 * v.2) q| ≤
          C * localRadius 0 q ^ (4 - w.length)) ∧
      |gradSq dipoleLift (saddleOrthoChart P q) - localRadius 0 q ^ 2| ≤
        C * localRadius 0 q ^ 4 := by
  sorry

/-- Odd–odd torus parity becomes oddness in both local chart axes, a.e.
(`lem:saddle-chart-parity`). No pointwise symmetry of an arbitrary L² representative
is asserted. -/
theorem saddle_chart_parity {P : ℝ × ℝ} (hP : P ∈ saddleSet) {f : L2}
    (hf : InSector false false f) :
    ∀ j, ∀ᵐ q, liftL2 f (saddleOrthoChart P (axisReflect j q)) =
      -liftL2 f (saddleOrthoChart P q) := by
  sorry

end NoEmbeddedEigenvalues
