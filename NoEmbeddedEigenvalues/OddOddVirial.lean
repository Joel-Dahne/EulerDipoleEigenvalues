import NoEmbeddedEigenvalues.OddOddForms

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
limit is asserted. Supplied-data bridges identify the raw local quotients a.e.,
rescale exceptional levels by `ε = 2h`, and split the boundary integral using coarea.
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

/-- On the positive cell the raw stream quotient is exactly the continuous supplied
    quotient. No assertion is made on the separatrix. -/
theorem DDQuotientData.raw_stream_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    ddStreamQuotient ω p = continuousRep q.phi (torusProj p) := by
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  rw [ddStreamQuotient, q.contStream_eq]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The raw vorticity quotient agrees with supplied data a.e. on the open cell. -/
theorem DDQuotientData.raw_vorticity_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) :
    ∀ᵐ p ∂(volume.restrict cellSquare), ddVorticityQuotient ω p = liftL2 q.nu p := by
  have hm : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  filter_upwards [ae_restrict_of_ae (ae_torusProj q.vorticity_eq),
    ae_restrict_mem hm] with p hp hpc
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hpc
  unfold ddVorticityQuotient liftL2
  rw [hp, Ψ_torusProj]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- Change the raw local quotients to supplied data in the truncated virial. The
    conclusion is in the orbit parameter, so the stream level is explicitly `2*h`. -/
theorem DDQuotientData.ae_truncated_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (q : DDQuotientData lam ω) (hω : IsEigenSolution lam ω)
    (hs : InSector false false ω) {dx dy : L2}
    (hx : HasFourierPartial 0 q.phi dx) (hy : HasFourierPartial 1 q.phi dy) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ddRawBulk q.phi q.nu dx dy (2 * h) =
        ddVirialLevel (fun p ↦ continuousRep q.phi (torusProj p))
          (fun p ↦ -liftL2 q.nu p) (liftL2 dx) (liftL2 dy) (2 * h) := by
  have hm : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hrep := ae_torusProj (coeFn_eq_continuousRep q.regular)
  have hu : ∀ᵐ p, p ∈ cellSquare →
      liftL2 q.phi p = ddStreamQuotient ω p := by
    filter_upwards [hrep] with p hp hpc
    exact hp.trans (q.raw_stream_eq hpc).symm
  have hd (j : Fin 2) (d : L2) (hd : HasFourierPartial j q.phi d) :
      HasWeakPartialOn cellSquare j (ddStreamQuotient ω) (liftL2 d) :=
    (hasWeakPartialOn_liftL2 hd cellSquare).congr_ae_on hm hu
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hv := dd_truncated_virial hlam hω hs (hd 0 dx hx) (hd 1 dy hy)
  have hv' := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (by norm_num : (2 : ℝ) ≠ 0)).ae ((ae_restrict_iff' measurableSet_Ioo).mp hv)
  simp only [smul_eq_mul] at hv'
  have mν : Measurable (liftL2 q.nu) := (Lp.stronglyMeasurable q.nu).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  have mv : Measurable (ddVorticityQuotient ω) := by
    unfold ddVorticityQuotient dipoleLift liftL2
    have := (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    fun_prop
  have hlevels := ae_level_of_ae_cellSquare (measurableSet_eq_fun mv mν) q.raw_vorticity_eq
  filter_upwards [ae_restrict_of_ae hv', hlevels, ae_restrict_mem measurableSet_Ioo]
    with h hvh hlevel hh
  have hε : 2 * h ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hvir := (hvh hε).2
  have hb : ddRawBulk q.phi q.nu dx dy (2 * h) =
      ∫ p in ddTruncatedCell (2 * h),
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p)
          (liftL2 dx) (liftL2 dy) p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_of_ae ((ae_restrict_iff' hm).mp q.raw_vorticity_eq),
      ae_restrict_mem (show MeasurableSet (ddTruncatedCell (2 * h)) from
        hm.inter (measurableSet_lt measurable_const
          (show Measurable dipoleLift by unfold dipoleLift; fun_prop)))]
      with p hp hvp hpc
    rw [ddVirialDensity, q.raw_stream_eq hpc.1, hvp hpc.1, norm_neg, ← hp]
    dsimp only [ddVorticityDensity, ddRawEnergy, liftL2]
    ring
  rw [hb, hvir, ddVirialLevel, ddVirialLevel]
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [levelIntegral_eq_integral_orbitWindow hh.1 hh.2,
    levelIntegral_eq_integral_orbitWindow hh.1 hh.2]
  apply integral_congr_ae
  filter_upwards [hlevel] with t ht
  rw [q.raw_stream_eq (dipoleOrbit_mem_cellSquare hh.1 hh.2 t), ht]

/-- Splitting the boundary integral is justified on almost every level by coarea
    applied separately to the five integrable densities. -/
theorem dd_virial_level_split {φ : L2} (hφ : MemSobolev 2 φ) (ν dx dy : L2) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ddVirialLevel (fun p ↦ continuousRep φ (torusProj p))
        (fun p ↦ -liftL2 ν p) (liftL2 dx) (liftL2 dy) (2 * h) =
      (8 - (2 * h) ^ 3) / 3 *
        (levelIntegral h (fun p ↦ ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
          levelIntegral h (fun p ↦ ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
          ddLevelMass φ (2 * h) -
          levelIntegral h (fun p ↦
            (liftL2 ν p * (starRingEnd ℂ) (continuousRep φ (torusProj p))).re)) -
        (2 * h) ^ 2 * levelIntegral h (fun p ↦ gradNorm p *
          ((starRingEnd ℂ) (continuousRep φ (torusProj p)) *
            ddInwardNormal (liftL2 dx) (liftL2 dy) p).re) := by
  let u := fun p ↦ continuousRep φ (torusProj p)
  let n := ddInwardNormal (liftL2 dx) (liftL2 dy)
  let τ := tangentDeriv (liftL2 dx) (liftL2 dy)
  have ml (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have mu : Measurable u := ((continuousRep φ).continuous.comp
    isOpenQuotientMap_torusProj.continuous).measurable
  have mn : Measurable n := by
    change Measurable (fun p ↦ -normalDeriv (liftL2 dx) (liftL2 dy) p)
    simp only [normalDeriv, gradNorm]
    fun_prop
  have mt : Measurable τ := by
    change Measurable (fun p ↦ tangentDeriv (liftL2 dx) (liftL2 dy) p)
    simp only [tangentDeriv, gradNorm]
    fun_prop
  have mr : Measurable gradNorm := by unfold gradNorm; fun_prop
  have hsub : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hsub
  have iu : IntegrableOn (fun p ↦ ‖u p‖ ^ 2) cellSquare := by
    apply (hsq φ).congr
    filter_upwards [ae_restrict_of_ae (ae_torusProj (coeFn_eq_continuousRep hφ))]
      with p hp
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hp
  let F := fun p ↦ ‖u p‖ ^ 2 + ‖liftL2 dx p‖ ^ 2 +
    ‖liftL2 dy p‖ ^ 2 + ‖liftL2 ν p‖ ^ 2
  have iF : IntegrableOn F cellSquare := ((iu.add (hsq dx)).add (hsq dy)).add (hsq ν)
  have hn (p) : ‖n p‖ ^ 2 ≤ 2 * F p := by
    have hb := norm_normalDeriv_le (liftL2 dx) (liftL2 dy) p
    have he : ‖n p‖ = ‖normalDeriv (liftL2 dx) (liftL2 dy) p‖ := norm_neg _
    dsimp only [F]
    rw [← he] at hb
    nlinarith [sq_nonneg (‖liftL2 dx p‖ - ‖liftL2 dy p‖),
      norm_nonneg (n p), norm_nonneg (liftL2 dx p), norm_nonneg (liftL2 dy p),
      sq_nonneg ‖u p‖, sq_nonneg ‖liftL2 ν p‖]
  have ht (p) : ‖τ p‖ ^ 2 ≤ 2 * F p := by
    have hb := norm_tangentDeriv_le (liftL2 dx) (liftL2 dy) p
    dsimp only [F]
    nlinarith [sq_nonneg (‖liftL2 dx p‖ - ‖liftL2 dy p‖),
      norm_nonneg (τ p), norm_nonneg (liftL2 dx p), norm_nonneg (liftL2 dy p),
      sq_nonneg ‖u p‖, sq_nonneg ‖liftL2 ν p‖]
  have hre (a b : ℂ) : |(a * (starRingEnd ℂ) b).re| ≤ ‖a‖ * ‖b‖ := by
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hp (p) : |(liftL2 ν p * (starRingEnd ℂ) (u p)).re| ≤ F p := by
    refine (hre _ _).trans ?_
    dsimp only [F]
    nlinarith [sq_nonneg (‖liftL2 ν p‖ - ‖u p‖),
      sq_nonneg ‖liftL2 dx p‖, sq_nonneg ‖liftL2 dy p‖]
  have hr (p) : gradNorm p ≤ 2 := by
    have h0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have h2 : gradNorm p ^ 2 ≤ 2 := by
      rw [gradNorm, Real.sq_sqrt (by positivity)]
      nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
    nlinarith
  have hm (p) : |gradNorm p * ((starRingEnd ℂ) (u p) * n p).re| ≤ 3 * F p := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ gradNorm p from Real.sqrt_nonneg _)]
    have hu : ‖u p‖ ^ 2 ≤ F p := by
      dsimp only [F]
      nlinarith [sq_nonneg (‖liftL2 dx p‖), sq_nonneg (‖liftL2 dy p‖),
        sq_nonneg (‖liftL2 ν p‖)]
    have hb : |((starRingEnd ℂ) (u p) * n p).re| ≤ ‖u p‖ * ‖n p‖ := by
      simpa [mul_comm] using hre (n p) (u p)
    nlinarith [mul_le_mul (hr p) hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      hn p, sq_nonneg (‖u p‖ - ‖n p‖)]
  have iN : IntegrableOn (fun p ↦ ‖n p‖ ^ 2) cellSquare :=
    (iF.const_mul 2).mono' (mn.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hn p)
  have iT : IntegrableOn (fun p ↦ ‖τ p‖ ^ 2) cellSquare :=
    (iF.const_mul 2).mono' (mt.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact ht p)
  have iP : IntegrableOn (fun p ↦ (liftL2 ν p * (starRingEnd ℂ) (u p)).re) cellSquare :=
    iF.mono' (by fun_prop) (Eventually.of_forall fun p ↦ hp p)
  have iM : IntegrableOn (fun p ↦ gradNorm p * ((starRingEnd ℂ) (u p) * n p).re)
      cellSquare :=
    (iF.const_mul 3).mono' (by fun_prop) (Eventually.of_forall fun p ↦ hm p)
  filter_upwards [(integral_cellSquare_eq iN).1, (integral_cellSquare_eq iT).1,
    (integral_cellSquare_eq iu).1, (integral_cellSquare_eq iP).1,
    (integral_cellSquare_eq iM).1, ae_restrict_mem measurableSet_Ioo]
    with h jN jT jU jP jM hh
  simp only [ddVirialLevel, ddLevelMass, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    levelIntegral_eq_integral_orbitWindow hh.1 hh.2]
  change (∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
    (8 - (2 * h) ^ 3) / 3 * (‖n (dipoleOrbit h t)‖ ^ 2 - ‖τ (dipoleOrbit h t)‖ ^ 2 -
      ‖u (dipoleOrbit h t)‖ ^ 2 + (-liftL2 ν (dipoleOrbit h t) *
        (starRingEnd ℂ) (u (dipoleOrbit h t))).re) -
      (2 * h) ^ 2 * gradNorm (dipoleOrbit h t) *
        ((starRingEnd ℂ) (u (dipoleOrbit h t)) * n (dipoleOrbit h t)).re) = _
  simp only [neg_mul, Complex.neg_re, ← sub_eq_add_neg]
  simp_rw [mul_assoc ((2 * h) ^ 2)]
  simp only [neg_mul] at jN jT jU jP jM
  have hsplit := integral_sub
    ((((jN.sub jT).sub jU).sub jP).const_mul ((8 - (2 * h) ^ 3) / 3))
    (jM.const_mul ((2 * h) ^ 2))
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_const_mul, integral_const_mul]
  have h1 := integral_sub ((jN.sub jT).sub jU) jP
  have h2 := integral_sub (jN.sub jT) jU
  have h3 := integral_sub jN jT
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3]

end NoEmbeddedEigenvalues