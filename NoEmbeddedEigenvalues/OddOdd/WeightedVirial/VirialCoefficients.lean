module

public import NoEmbeddedEigenvalues.EvenEven.Conclusion.EvenEven
public import NoEmbeddedEigenvalues.OddOdd.Quotient.DipoleOrthogonality
public import NoEmbeddedEigenvalues.OddOdd.BoundaryForm.CorrectedBoundaryForm
public import NoEmbeddedEigenvalues.Regularity.OddOddDomain.OddOddQuotient

/-! # Odd–odd virial weight and coefficient matrix -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- The weight `μ = Ψ²` on the lifted positive cell. -/
def ddWeight (p : ℝ × ℝ) : ℝ := dipoleLift p ^ 2

/-- The potential coefficient `F = s(8-s³)δ²/(3r²)`, with `r = |∇s|²`. -/
def ddF (p : ℝ × ℝ) : ℝ :=
  dipoleLift p * (8 - dipoleLift p ^ 3) * (Real.cos p.1 - Real.cos p.2) ^ 2 /
    (3 * gradSq dipoleLift p ^ 2)

/-- The tangential eigenvalue of `M`. -/
def ddC (p : ℝ × ℝ) : ℝ :=
  dipoleLift p * (8 - dipoleLift p ^ 3) / (3 * gradSq dipoleLift p)

/-- The normal eigenvalue of `M`. -/
def ddA (p : ℝ × ℝ) : ℝ :=
  2 * dipoleLift p ^ 2 / 3 + 32 / (3 * dipoleLift p) - ddC p

/-- The Cartesian entries of the real symmetric Picone matrix. Values at its singular
    points are totalized by real division and do not specify limiting values there. -/
def ddMxx (p : ℝ × ℝ) : ℝ :=
  ddC p + (ddA p - ddC p) * Real.sin p.1 ^ 2 / gradSq dipoleLift p

def ddMxy (p : ℝ × ℝ) : ℝ :=
  (ddA p - ddC p) * Real.sin p.1 * Real.sin p.2 / gradSq dipoleLift p

def ddMyy (p : ℝ × ℝ) : ℝ :=
  ddC p + (ddA p - ddC p) * Real.sin p.2 ^ 2 / gradSq dipoleLift p

/-- `⟨M∇u,∇u⟩` for a complex gradient supplied explicitly. -/
def ddMatrixForm (p : ℝ × ℝ) (vx vy : ℂ) : ℝ :=
  ddA p * ‖normalDeriv (fun _ ↦ vx) (fun _ ↦ vy) p‖ ^ 2 +
    ddC p * ‖tangentDeriv (fun _ ↦ vx) (fun _ ↦ vy) p‖ ^ 2

end NoEmbeddedEigenvalues
