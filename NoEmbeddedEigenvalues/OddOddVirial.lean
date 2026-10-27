import NoEmbeddedEigenvalues.OddOdd

/-!
# Weighted odd–odd virial interfaces

Classical differential expressions are used only for smooth functions. The quotient
Poisson equation is instead tested weakly, with specified Fourier first derivatives.
The annular and truncated virials use the original eigenfunction quotients on the
open cell and arbitrary weak derivative witnesses there: global quotient existence
is not a hypothesis. Level parameters here are `s = ε`, so orbit integrals use `ε/2`.

The existing `normalDeriv` points out of the positive superlevel cell. Here the
weighted virial uses the inward normal `∇Ψ/|∇Ψ|`, so its linear normal term must
use the opposite sign; the quadratic energies are unaffected.

The gradient limits allow a common null set of exceptional levels. In contrast, the
renormalized bulk has a full positive-level limit; no all-level vorticity pairing
limit is asserted. These interfaces do not change the Picone/exclusion assembly.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- The original stream quotient on the open positive cell. Values elsewhere are
    totalized, not continuous separatrix traces. -/
def ddStreamQuotient (ω : L2) (p : ℝ × ℝ) : ℂ :=
  contStream ω p / (dipoleLift p : ℂ)

/-- The original vorticity quotient, used only on the open positive cell. -/
def ddVorticityQuotient (ω : L2) (p : ℝ × ℝ) : ℂ :=
  liftL2 ω p / (dipoleLift p : ℂ)

/-- Weighted area on the positive cell, with `μ = Ψ²`. -/
def ddCellMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict cellSquare).withDensity (fun p ↦ ENNReal.ofReal (ddWeight p))

/-- Classical weighted Laplacian `μ⁻¹ div(μ∇)`. -/
def ddWeightedLaplacian (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (partialX (fun q ↦ (ddWeight q : ℂ) * partialX u q) p +
    partialY (fun q ↦ (ddWeight q : ℂ) * partialY u q) p) / (ddWeight p : ℂ)

/-- Classical `E = 1 - μ⁻¹ div(μ∇)`; not an operator on raw Sobolev representatives. -/
def ddOperator (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  u p - ddWeightedLaplacian u p

/-- Weak realization of `Eu = e`, recording the specified first derivatives.
    All tests are supported inside the open cell, away from `Ψ = 0`. -/
def HasDDOperator (u e ux uy : ℝ × ℝ → ℂ) : Prop :=
  HasWeakPartialOn cellSquare 0 u ux ∧ HasWeakPartialOn cellSquare 1 u uy ∧
    LocallyIntegrableOn e cellSquare ∧
    ∀ η, IsTestFunctionOn cellSquare η →
      (∫ p in cellSquare, (ddWeight p : ℂ) * (e p - u p) * η p) =
        ∫ p in cellSquare, (ddWeight p : ℂ) *
          (ux p * partialX η p + uy p * partialY η p)

/-- Multiplication by `s` is unitary from weighted to ordinary cell L². The
    representative identity is asserted only a.e. on the positive cell. -/
theorem dd_cell_unitary :
    ∃ U : Lp ℂ 2 ddCellMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict cellSquare),
      ∀ u, ∀ᵐ p ∂(volume.restrict cellSquare),
        U u p = (dipoleLift p : ℂ) * u p := by
  sorry

/-- Smooth conjugation on the open cell, where division by `s` is smooth. -/
theorem dd_operator_conjugation {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u cellSquare) {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    (dipoleLift p : ℂ) * ddOperator (fun q ↦ u q / (dipoleLift q : ℂ)) p =
      -laplacian u p := by
  sorry

/-- The original quotients satisfy the weak Poisson equation on the open cell,
    without any assumption about their global divided regularity. -/
theorem dd_quotient_equations {lam : ℝ} {ω : L2} (hω : IsEigenSolution lam ω) :
    ∃ ux uy, HasDDOperator (ddStreamQuotient ω)
      (fun p ↦ -ddVorticityQuotient ω p) ux uy := by
  sorry

/-- The quotient Poisson equation for supplied data, without a classical derivative
    of the chosen L² representative or any global transport-domain claim. -/
theorem DDQuotientData.operator_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hω : IsEigenSolution lam ω) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    HasDDOperator (liftL2 q.phi) (fun p ↦ -liftL2 q.nu p) (liftL2 dx) (liftL2 dy) := by
  sorry

/-- Scalar coefficient `q(s)` of the weighted virial field. -/
def ddVirialQ (s : ℝ) : ℝ := (s ^ 3 - 8) / (3 * s ^ 2)

def ddVirialField₁ (p : ℝ × ℝ) : ℝ :=
  ddVirialQ (dipoleLift p) * partialX dipoleLift p / gradSq dipoleLift p

def ddVirialField₂ (p : ℝ × ℝ) : ℝ :=
  ddVirialQ (dipoleLift p) * partialY dipoleLift p / gradSq dipoleLift p

/-- Adapted coefficient `f = F/μ`. -/
def ddVirialCoeff (p : ℝ × ℝ) : ℝ := ddF p / ddWeight p

/-- Classical Picone operator `P = -div(M∇) - F`, on the punctured cell. -/
def ddPiconeOperator (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -(partialX (fun q ↦ (ddMxx q : ℂ) * partialX u q +
      (ddMxy q : ℂ) * partialY u q) p +
    partialY (fun q ↦ (ddMxy q : ℂ) * partialX u q +
      (ddMyy q : ℂ) * partialY u q) p) - (ddF p : ℂ) * u p

/-- Weighted divergence of a smooth real vector field. -/
def ddWeightedDiv (W₁ W₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  divergence (fun q ↦ ddWeight q * W₁ q) (fun q ↦ ddWeight q * W₂ q) p / ddWeight p

/-- Weighted half-density generator evaluated on specified first derivatives. -/
def ddWeightedGenerator (W₁ W₂ : ℝ × ℝ → ℝ) (u ux uy : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  (W₁ p : ℂ) * ux p + (W₂ p : ℂ) * uy p +
    ((ddWeightedDiv W₁ W₂ p / 2 : ℝ) : ℂ) * u p

/-- The cell with the elliptic center removed; all virial coefficients are smooth here. -/
def ddRegularCell : Set (ℝ × ℝ) := {p | p ∈ cellSquare ∧ gradSq dipoleLift p ≠ 0}

/-- Adaptedness, constant weighted defect, and all three entries of
    `μ(2 sym DW - f I) = M`. -/
theorem dd_virial_algebra :
    IsAdaptedOn ddVirialField₁ ddVirialField₂ ddVirialCoeff ddRegularCell ∧
      ∀ p ∈ ddRegularCell,
        ddVirialCoeff p - ddWeightedDiv ddVirialField₁ ddVirialField₂ p = -1 ∧
        ddWeight p * (2 * partialX ddVirialField₁ p - ddVirialCoeff p) = ddMxx p ∧
        ddWeight p * (partialY ddVirialField₁ p + partialX ddVirialField₂ p) = ddMxy p ∧
        ddWeight p * (2 * partialY ddVirialField₂ p - ddVirialCoeff p) = ddMyy p := by
  sorry

/-- Function-level virial density, with the value of `Eu` supplied separately. -/
def ddVirialDensity (u e ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddF p * (‖e p‖ ^ 2 - ‖u p‖ ^ 2) + ddMatrixForm p (ux p) (uy p)

/-- The weighted virial's inward derivative `∇u · ∇Ψ/|∇Ψ|`. The shared
    `normalDeriv` has the opposite, outward orientation. -/
def ddInwardNormal (ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -normalDeriv ux uy p

/-- The boundary term in flow time. The last term includes `dℓ = √r dt`.
    No pointwise gradient trace on every level is claimed. -/
def ddVirialLevel (u e ux uy : ℝ × ℝ → ℂ) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦
    (8 - ε ^ 3) / 3 * (‖ddInwardNormal ux uy p‖ ^ 2 - ‖tangentDeriv ux uy p‖ ^ 2 -
      ‖u p‖ ^ 2 + (e p * (starRingEnd ℂ) (u p)).re) -
    ε ^ 2 * gradNorm p * ((starRingEnd ℂ) (u p) * ddInwardNormal ux uy p).re)

/-- First component of the classical Green flux. -/
def ddGreenFlux₁ (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * partialX u p).re -
    2 * (((ddVirialField₁ p : ℂ) * partialX u p +
      (ddVirialField₂ p : ℂ) * partialY u p) * (starRingEnd ℂ) (partialX u p)).re +
    ddVirialField₁ p * (‖partialX u p‖ ^ 2 + ‖partialY u p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Second component of the classical Green flux. -/
def ddGreenFlux₂ (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * partialY u p).re -
    2 * (((ddVirialField₁ p : ℂ) * partialX u p +
      (ddVirialField₂ p : ℂ) * partialY u p) * (starRingEnd ℂ) (partialY u p)).re +
    ddVirialField₂ p * (‖partialX u p‖ ^ 2 + ‖partialY u p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Local classical Green identity, separate from its weak annular justification. -/
theorem dd_green {u : ℝ × ℝ → ℂ} (hu : ContDiffOn ℝ 3 u ddRegularCell)
    {p : ℝ × ℝ} (hp : p ∈ ddRegularCell) :
    ddWeight p * ddVirialCoeff p *
        (‖ddOperator u p‖ ^ 2 - (ddOperator u p * (starRingEnd ℂ) (u p)).re) +
      2 * ddWeight p * (ddWeightedGenerator ddVirialField₁ ddVirialField₂
        u (partialX u) (partialY u) p * (starRingEnd ℂ) (ddOperator u p)).re =
      ddVirialDensity u (ddOperator u) (partialX u) (partialY u) p +
        divergence (ddGreenFlux₁ u) (ddGreenFlux₂ u) p := by
  sorry

/-- Weighted first identity with annular cutoff, on the original eigenfunction domain.
    Only local weak derivatives of the raw stream quotient are supplied. -/
theorem dd_weighted_first {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
      (ddVorticityQuotient ω p * (starRingEnd ℂ)
        (ddVorticityQuotient ω p + ddStreamQuotient ω p)).re) =
    2 * ∫ p in cellSquare, ddWeight p *
      (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
        (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
        (ddStreamQuotient ω) ux uy p * (starRingEnd ℂ) (ddVorticityQuotient ω p)).re := by
  sorry

/-- Annular virial with one common exceptional set for both endpoints. Neither a
    derivative of the vorticity nor global quotient data are hypotheses. -/
theorem dd_annular_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy) :
    (∀ a b : ℝ, 0 < a → a < b → b < 2 →
      IntegrableOn (ddVirialDensity (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy)
        {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b}) ∧
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ a b : ℝ, 0 < a → a < b → b < 2 →
      a ∉ N → b ∉ N →
      (∫ p in {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b},
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy a -
        ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy b := by
  sorry

/-- Truncated virial including the center, at almost every positive stream level. -/
theorem dd_truncated_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy) :
    ∀ᵐ ε ∂(volume.restrict (Ioo (0 : ℝ) 2)),
      IntegrableOn (ddVirialDensity (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy) (ddTruncatedCell ε) ∧
      (∫ p in ddTruncatedCell ε,
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy ε := by
  sorry

/-- Even H² gradient limits, using specified Fourier derivatives and continuous values.
    All three limits share one exceptional null set in the `ε = Ψ` variable. -/
theorem dd_quotient_gradient_traces {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) :
    (∀ k : Fin 4, Integrable (fun t ↦ Real.cosh t ^ 2 / 2 *
      ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 (∑ k : Fin 4,
          ∫ t, Real.cosh t ^ 2 / 2 * ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦ gradNorm p *
        ((starRingEnd ℂ) (continuousRep u (torusProj p)) *
          ddInwardNormal (liftL2 dx) (liftL2 dy) p).re))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  sorry

/-- Exact truncated coefficient integral and its scalar finite part. -/
theorem dd_finite_part :
    (∀ ε ∈ Ioo (0 : ℝ) 2,
      (∫ p in ddTruncatedCell ε, ddF p) =
        (8 - ε ^ 3) / 3 * orbitPeriod (ε / 2) -
          ∫ p in ddTruncatedCell ε, ddWeight p) ∧
    Tendsto (fun ε ↦ (∫ p in ddTruncatedCell ε, ddF p) -
      (32 / 3 : ℝ) * Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 ((32 / 3 : ℝ) * Real.log 8 - 2 * Real.pi ^ 2)) := by
  sorry

/-- Full renormalized bulk limit. The squared operator value can be any supplied
    function `e` with `e/d ∈ L²`; no equation for `e` is needed for this estimate. -/
theorem dd_renormalized_bulk {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) {e : ℝ × ℝ → ℂ}
    (he : MemLp (fun p ↦ e p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare)) :
    IntegrableOn (fun p ↦ ddF p * ‖e p‖ ^ 2) cellSquare ∧
      IntegrableOn (fun p ↦ ddMatrixForm p (liftL2 dx p) (liftL2 dy p)) cellSquare ∧
      ∃ J : ℝ, Tendsto (fun ε ↦
        (∫ p in ddTruncatedCell ε, ddVirialDensity (liftL2 u) e (liftL2 dx) (liftL2 dy) p) +
          ddLogCounterterm u ε) (𝓝[>] 0) (𝓝 J) := by
  sorry

end NoEmbeddedEigenvalues
