import NoEmbeddedEigenvalues.VirialAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Classical Picone identities for real symmetric planar matrices

Blueprint: `lem:picone`.

The algebraic identity is stated for any finite symmetric real matrix, so it
also covers scalar interval applications. The classical differential and
integrated interfaces below use planar coordinates.

The three real coefficient functions represent `G = [[a,b],[b,c]]`; neither
positive definiteness nor a sign condition on the potential is required.
The pointwise identity requires only first derivatives of the complex function
and positive real comparison function. The divergence form also differentiates
`G∇g`, so it uses C¹ coefficients and C² comparison data on an open set.

The integrated identity takes the divergence formula for the actual current as
an explicit hypothesis, together with absolute integrability of all densities.
The boundary measure and outward normal are supplied by the application. This
is not a divergence theorem for arbitrary domains, a Sobolev approximation
result, or a justification for removing singular points. In particular the
current uses values of the function, not boundary values of its gradient.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- A finite real matrix's Hermitian quadratic form, written without coordinates. -/
def piconeQuadratic {ι : Type*} [Fintype ι] (G : ι → ι → ℝ) (v : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, G i j * (v i * (starRingEnd ℂ) (v j)).re

/-- Algebraic Picone identity for specified values and gradients in any finite
    dimension. The last factor is the quotient-rule gradient of `|z|²/g`. -/
theorem picone_algebra {ι : Type*} [Fintype ι] (G : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) {g : ℝ} (hpos : 0 < g)
    (dg : ι → ℝ) (z : ℂ) (dz : ι → ℂ) :
    piconeQuadratic G dz =
      g ^ 2 * piconeQuadratic G (fun j ↦ dz j / (g : ℂ) - z * (dg j : ℂ) / (g : ℂ) ^ 2) +
        ∑ i, ∑ j, G i j * dg i *
          (2 * (dz j * (starRingEnd ℂ) z).re / g - ‖z‖ ^ 2 * dg j / g ^ 2) := by
  sorry

/-- The real Hermitian quadratic form of the symmetric matrix `[[a,b],[b,c]]`. -/
def piconeMatrixForm (a b c : ℝ) (vx vy : ℂ) : ℝ :=
  a * ‖vx‖ ^ 2 + 2 * b * (vx * (starRingEnd ℂ) vy).re + c * ‖vy‖ ^ 2

/-- Classical gradient energy for three specified real symmetric coefficients. -/
def piconeEnergy (a b c : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeMatrixForm (a p) (b p) (c p) (partialX z p) (partialY z p)

/-- The first component of `G∇g`. -/
def piconeGroundFlux₁ (a b : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p * partialX g p + b p * partialY g p

/-- The second component of `G∇g`. -/
def piconeGroundFlux₂ (b c : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  b p * partialX g p + c p * partialY g p

/-- The residual `-div(G∇g) - Vg` of a real comparison function. -/
def piconeResidual (a b c V g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -divergence (piconeGroundFlux₁ a b g) (piconeGroundFlux₂ b c g) p - V p * g p

/-- The first component of the current `J = |z|² G∇g/g`. -/
def piconeCurrent₁ (a b g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₁ a b g p / g p * ‖z p‖ ^ 2

/-- The second component of the same current. -/
def piconeCurrent₂ (b c g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₂ b c g p / g p * ‖z p‖ ^ 2

/-- Pointwise Picone identity, for a complex function and a positive real divisor.
    Symmetry is built into the three coefficient representation. -/
theorem picone_identity (a b c : ℝ × ℝ → ℝ) {g : ℝ × ℝ → ℝ}
    {z : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (hg : DifferentiableAt ℝ g p)
    (hz : DifferentiableAt ℝ z p) (hpos : 0 < g p) :
    piconeEnergy a b c z p =
      g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p +
        piconeGroundFlux₁ a b g p * partialX (fun q ↦ ‖z q‖ ^ 2 / g q) p +
        piconeGroundFlux₂ b c g p * partialY (fun q ↦ ‖z q‖ ^ 2 / g q) p := by
  sorry

/-- Classical divergence form, with the potential and actual current explicit. -/
theorem picone_divergence {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b c V g : ℝ × ℝ → ℝ} {z : ℝ × ℝ → ℂ}
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U)
    (hc : ContDiffOn ℝ 1 c U) (hg : ContDiffOn ℝ 2 g U)
    (hz : ContDiffOn ℝ 1 z U) (hpos : ∀ p ∈ U, 0 < g p)
    {p : ℝ × ℝ} (hp : p ∈ U) :
    piconeEnergy a b c z p - V p * ‖z p‖ ^ 2 =
      g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p +
        piconeResidual a b c V g p / g p * ‖z p‖ ^ 2 +
        divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p := by
  sorry

/-- Integrated Picone identity after a supplied integration-by-parts formula for
    `J`. The boundary measure `σ` and outward normal components `n₁,n₂` enter
    only through that formula. No regularity of the boundary is asserted here. -/
theorem picone_integral {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b c V g : ℝ × ℝ → ℝ} {z : ℝ × ℝ → ℂ}
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U)
    (hc : ContDiffOn ℝ 1 c U) (hg : ContDiffOn ℝ 2 g U)
    (hz : ContDiffOn ℝ 1 z U) (hpos : ∀ p ∈ U, 0 < g p)
    (hraw : IntegrableOn (fun p ↦ piconeEnergy a b c z p - V p * ‖z p‖ ^ 2) U)
    (hgrad : IntegrableOn (fun p ↦ g p ^ 2 *
      piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p) U)
    (hpot : IntegrableOn (fun p ↦ piconeResidual a b c V g p / g p * ‖z p‖ ^ 2) U)
    (hdiv : IntegrableOn
      (divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z)) U)
    {σ : Measure (ℝ × ℝ)} {n₁ n₂ : ℝ × ℝ → ℝ}
    (hboundary : Integrable (fun p ↦ n₁ p * piconeCurrent₁ a b g z p +
      n₂ p * piconeCurrent₂ b c g z p) σ)
    (hibp : (∫ p in U, divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p) =
      ∫ p, n₁ p * piconeCurrent₁ a b g z p + n₂ p * piconeCurrent₂ b c g z p ∂σ) :
    (∫ p in U, piconeEnergy a b c z p - V p * ‖z p‖ ^ 2) =
      (∫ p in U, g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p) +
        (∫ p in U, piconeResidual a b c V g p / g p * ‖z p‖ ^ 2) +
        ∫ p, n₁ p * piconeCurrent₁ a b g z p + n₂ p * piconeCurrent₂ b c g z p ∂σ := by
  sorry

end NoEmbeddedEigenvalues
