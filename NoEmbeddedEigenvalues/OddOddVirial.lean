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

Positive truncations need only smooth local division of the original stream, not
existence of global quotient data. Weak-derivative uniqueness gives square integrability
for arbitrary witnesses. Bounded bulk coefficients and a Cauchy–Schwarz center-flux
estimate allow the annular identity to include the center by dominated convergence.
Measurable versions and null hulls transfer these estimates to the given witnesses.

The weighted differential algebra is pointwise on the regular cell. The annular
extraction takes a weak cutoff identity as input, then obtains one exceptional set
for both endpoints by coarea and du Bois–Reymond. The planar boundary density
identifies each level term directly, without splitting its summands.
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

theorem ddVirialField₁_eq :
    ddVirialField₁ = fun p ↦ ddVirialQ (dipoleLift p) * -Real.sin p.1 / gradSq dipoleLift p := by
  funext p
  rw [ddVirialField₁, partialX_dipoleLift]

theorem ddVirialField₂_eq :
    ddVirialField₂ = fun p ↦ ddVirialQ (dipoleLift p) * -Real.sin p.2 / gradSq dipoleLift p := by
  funext p
  rw [ddVirialField₂, partialY_dipoleLift]

/-- The radial coefficient has a particularly simple derivative away from zero. -/
theorem hasDerivAt_ddVirialQ {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt ddVirialQ (1 / 3 + 16 / (3 * s ^ 3)) s := by
  have h := (((hasDerivAt_id s).pow 3).sub_const 8).div
    (((hasDerivAt_id s).pow 2).const_mul 3) (by positivity : 3 * s ^ 2 ≠ 0)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

theorem contDiffAt_ddVirialField {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ddVirialField₁ p ∧
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ddVirialField₂ p := by
  have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q ↦ ddVirialQ (dipoleLift q)) p := by
    unfold ddVirialQ
    have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift := by
      unfold dipoleLift
      fun_prop
    exact ((hΨ.contDiffAt.pow 3).sub
      contDiffAt_const).div
      (contDiffAt_const.mul ((by unfold dipoleLift; fun_prop :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift).contDiffAt.pow 2)) (by positivity)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gradSq dipoleLift) := by
    simp only [gradSq_dipoleLift]
    fun_prop
  constructor
  · unfold ddVirialField₁
    exact (hq.mul (by rw [partialX_dipoleLift]; fun_prop)).div hg.contDiffAt hr
  · unfold ddVirialField₂
    exact (hq.mul (by rw [partialY_dipoleLift]; fun_prop)).div hg.contDiffAt hr

theorem partialX_ddVirialField₁ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddVirialField₁ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 ^ 2 / gradSq dipoleLift p -
      ddVirialQ (dipoleLift p) * Real.cos p.1 / gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 ^ 2 * Real.cos p.1 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.1
    ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos t + Real.cos p.2) *
      -Real.sin t / (Real.sin t ^ 2 + Real.sin p.2 ^ 2)) _ p.1 :=
    (hq.mul (Real.hasDerivAt_sin p.1).neg).div
    (((Real.hasDerivAt_sin p.1).pow 2).add_const (Real.sin p.2 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₁_eq]
  simp only [partialX, dipoleLift, gradSq_dipoleLift]
  simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialY_ddVirialField₁ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddVirialField₁ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 * Real.sin p.2 /
        gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 * Real.sin p.2 * Real.cos p.2 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.2
    ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos p.1 + Real.cos t) *
      -Real.sin p.1 / (Real.sin p.1 ^ 2 + Real.sin t ^ 2)) _ p.2 :=
    (hq.mul_const (-Real.sin p.1)).div
    (((Real.hasDerivAt_sin p.2).pow 2).const_add (Real.sin p.1 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₁_eq]
  simp only [partialY, dipoleLift, gradSq_dipoleLift]
  simp only [Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialX_ddVirialField₂ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddVirialField₂ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 * Real.sin p.2 /
        gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 * Real.sin p.2 * Real.cos p.1 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.1
    ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos t + Real.cos p.2) *
      -Real.sin p.2 / (Real.sin t ^ 2 + Real.sin p.2 ^ 2)) _ p.1 :=
    (hq.mul_const (-Real.sin p.2)).div
    (((Real.hasDerivAt_sin p.1).pow 2).add_const (Real.sin p.2 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₂_eq]
  simp only [partialX, dipoleLift, gradSq_dipoleLift]
  simp only [Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialY_ddVirialField₂ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddVirialField₂ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.2 ^ 2 / gradSq dipoleLift p -
      ddVirialQ (dipoleLift p) * Real.cos p.2 / gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.2 ^ 2 * Real.cos p.2 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.2
    ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos p.1 + Real.cos t) *
      -Real.sin t / (Real.sin p.1 ^ 2 + Real.sin t ^ 2)) _ p.2 :=
    (hq.mul (Real.hasDerivAt_sin p.2).neg).div
    (((Real.hasDerivAt_sin p.2).pow 2).const_add (Real.sin p.1 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₂_eq]
  simp only [partialY, dipoleLift, gradSq_dipoleLift]
  simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

/-- Weighted divergence differs from ordinary divergence by `2q(s)/s`. -/
theorem ddWeightedDiv_virial {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddWeightedDiv ddVirialField₁ ddVirialField₂ p =
      partialX ddVirialField₁ p + partialY ddVirialField₂ p +
        2 * ddVirialQ (dipoleLift p) / dipoleLift p := by
  have hd := contDiffAt_ddVirialField hs hr
  have hm : DifferentiableAt ℝ ddWeight p := by unfold ddWeight dipoleLift; fun_prop
  have hx : partialX ddWeight p = -2 * dipoleLift p * Real.sin p.1 := by
    exact (((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2)).pow 2).deriv.trans
      (by unfold dipoleLift; ring)
  have hy : partialY ddWeight p = -2 * dipoleLift p * Real.sin p.2 := by
    exact (((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1)).pow 2).deriv.trans
      (by unfold dipoleLift; ring)
  unfold ddWeightedDiv divergence
  rw [show (fun q ↦ ddWeight q * ddVirialField₁ q) =
      (fun q ↦ ddWeight q • ddVirialField₁ q) from rfl,
    show (fun q ↦ ddWeight q * ddVirialField₂ q) =
      (fun q ↦ ddWeight q • ddVirialField₂ q) from rfl,
    partialX_smul hm (hd.1.differentiableAt (by simp)),
    partialY_smul hm (hd.2.differentiableAt (by simp)), hx, hy]
  simp only [smul_eq_mul, ddWeight, ddVirialField₁, ddVirialField₂,
    partialX_dipoleLift, partialY_dipoleLift]
  field_simp
  rw [gradSq_dipoleLift] at *
  ring

/-- Pointwise differential algebra; only the two explicit denominators need be nonzero. -/
theorem dd_virial_algebra_at {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    (classicalL0 ddVirialField₁ p - Real.cos p.2 * ddVirialField₂ p =
      ddVirialCoeff p * Real.sin p.2 ∧
      classicalL0 ddVirialField₂ p + Real.cos p.1 * ddVirialField₁ p =
        -(ddVirialCoeff p * Real.sin p.1)) ∧
    ddVirialCoeff p - ddWeightedDiv ddVirialField₁ ddVirialField₂ p = -1 ∧
    ddWeight p * (2 * partialX ddVirialField₁ p - ddVirialCoeff p) = ddMxx p ∧
    ddWeight p * (partialY ddVirialField₁ p + partialX ddVirialField₂ p) = ddMxy p ∧
    ddWeight p * (2 * partialY ddVirialField₂ p - ddVirialCoeff p) = ddMyy p := by
  have hx : Real.sin p.1 ^ 2 = 1 - Real.cos p.1 ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq p.1]
  have hy : Real.sin p.2 ^ 2 = 1 - Real.cos p.2 ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq p.2]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [classicalL0, smul_eq_mul, ddWeightedDiv_virial hs hr,
      partialX_ddVirialField₁ hs hr, partialY_ddVirialField₁ hs hr,
      partialX_ddVirialField₂ hs hr, partialY_ddVirialField₂ hs hr]
    simp only [ddVirialField₁, ddVirialField₂, partialX_dipoleLift, partialY_dipoleLift,
      ddVirialCoeff, ddWeight, ddF, ddMxx, ddMxy, ddMyy, ddA, ddC, ddVirialQ]
    simp only [gradSq_dipoleLift, dipoleLift] at hs hr ⊢
    field_simp
    simp only [hx, hy]
    ring

/-- Adaptedness, constant weighted defect, and all three entries of
    `μ(2 sym DW - f I) = M`. -/
theorem dd_virial_algebra :
    IsAdaptedOn ddVirialField₁ ddVirialField₂ ddVirialCoeff ddRegularCell ∧
      ∀ p ∈ ddRegularCell,
        ddVirialCoeff p - ddWeightedDiv ddVirialField₁ ddVirialField₂ p = -1 ∧
        ddWeight p * (2 * partialX ddVirialField₁ p - ddVirialCoeff p) = ddMxx p ∧
        ddWeight p * (partialY ddVirialField₁ p + partialX ddVirialField₂ p) = ddMxy p ∧
        ddWeight p * (2 * partialY ddVirialField₂ p - ddVirialCoeff p) = ddMyy p := by
  have hlocal (p) (hp : p ∈ ddRegularCell) := dd_virial_algebra_at
    (show dipoleLift p ≠ 0 from ne_of_gt (by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)) hp.2
  exact ⟨fun p hp ↦ (hlocal p hp).1, fun p hp ↦ (hlocal p hp).2⟩

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

/-- Planar boundary density whose restriction to Ψ = ε is the level integrand. -/
def ddBoundaryDensity (u e ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  (8 - dipoleLift p ^ 3) / 3 *
    (‖ddInwardNormal ux uy p‖ ^ 2 - ‖tangentDeriv ux uy p‖ ^ 2 -
      ‖u p‖ ^ 2 + (e p * (starRingEnd ℂ) (u p)).re) -
    dipoleLift p ^ 2 * gradNorm p *
      ((starRingEnd ℂ) (u p) * ddInwardNormal ux uy p).re

/-- The boundary density identifies the level term without choosing gradient traces
    or splitting possibly nonintegrable level integrals. -/
theorem levelIntegral_ddBoundaryDensity (u e ux uy : ℝ × ℝ → ℂ)
    {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    levelIntegral h (ddBoundaryDensity u e ux uy) = ddVirialLevel u e ux uy (2 * h) := by
  unfold ddVirialLevel
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  unfold levelIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [ddBoundaryDensity, dipoleLift_dipoleOrbit h0 h1]

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

/-- A compact-level cutoff identity determines the virial on every annulus outside
    one common null set. The bulk and boundary densities need only be integrable
    on closed level bands; no positivity or smooth representatives are required. -/
theorem annular_virial_of_cutoff_identity {J B : ℝ × ℝ → ℝ}
    (hJ : ∀ a b : ℝ, 0 < a → b < 1 →
      IntegrableOn J {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b})
    (hB : ∀ a b : ℝ, 0 < a → b < 1 →
      IntegrableOn B {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b})
    (hcut : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        (∫ p in cellSquare, φ (dipoleLift p / 2) * J p) =
          ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * B p) :
    ∃ N : Set ℝ, volume N = 0 ∧
      ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
        (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'}, J p) =
          levelIntegral h B - levelIntegral h' B := by
  have hΨ : Measurable dipoleLift := by unfold dipoleLift; fun_prop
  have hderiv_supp {φ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∀ s, deriv φ s ≠ 0 → a ≤ s ∧ s ≤ b := by
    intro s hs
    by_contra hns
    apply hs
    have hev : φ =ᶠ[𝓝 s] fun _ ↦ 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds (show s ∉ Icc a b from hns)] with t ht
      by_contra hne
      exact ht (hsupp t hne)
    rw [hev.deriv_eq, deriv_const]
  have hbound {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
      (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∃ C, ∀ s, |g s| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hg.continuousOn (s := Icc a b))
    refine ⟨max C 0, fun s ↦ ?_⟩
    by_cases hs : g s = 0
    · simp [hs]
    · exact (show |g s| ≤ C by simpa using hC s (hsupp s hs)).trans (le_max_left _ _)
  have hcompl {g F : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∫ s, g s * F s = ∫ s in Icc a b, g s * F s := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_).symm
    have : g s = 0 := by
      by_contra hne
      exact hs (hsupp s hne)
    simp [this]
  have hid : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        ∫ s, φ s * (2 * levelIntegral s J) =
          ∫ s, deriv φ s * levelIntegral s B := by
    intro φ hφ a b ha hb hsupp
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    obtain ⟨C, hC⟩ := hbound hφ.continuous hsupp
    obtain ⟨C', hC'⟩ := hbound hdc (hderiv_supp hsupp)
    have hsupp' : ∀ s, deriv φ s / 2 ≠ 0 → a ≤ s ∧ s ≤ b := fun s hs ↦
      hderiv_supp hsupp s fun h ↦ hs (by simp [h])
    have hC'' : ∀ s, |deriv φ s / 2| ≤ C' / 2 := fun s ↦ by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right (hC' s) (by norm_num)
    have c1 := integral_cellSquare_level_mul hφ.continuous.measurable hC ha hb hsupp
      (hJ a b ha hb)
    have c2 := integral_cellSquare_level_mul (hdc.measurable.div_const 2) hC'' ha hb hsupp'
      (hB a b ha hb)
    rw [hcompl hsupp, hcompl (hderiv_supp hsupp)]
    calc
      _ = 2 * ∫ s in Icc a b, φ s * levelIntegral s J := by
        rw [← integral_const_mul]; congr 1; funext s; ring
      _ = ∫ p in cellSquare, φ (dipoleLift p / 2) * J p := c1.symm
      _ = ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * B p :=
        hcut φ hφ a b ha hb hsupp
      _ = 2 * ∫ s in Icc a b, deriv φ s / 2 * levelIntegral s B := c2
      _ = _ := by rw [← integral_const_mul]; congr 1; funext s; ring
  obtain ⟨N, hN, hdbr⟩ := exists_null_sub_eq_intervalIntegral (α := 0) (β := 1)
    (m := fun h ↦ 2 * levelIntegral h J) (G := fun h ↦ levelIntegral h B)
    (fun a b ha hb ↦ (integrableOn_levelIntegral ha hb (hJ a b ha hb)).const_mul 2)
    (fun a b ha hb ↦ integrableOn_levelIntegral ha hb (hB a b ha hb)) hid
  refine ⟨N, hN, fun h h' h0 hh' h'1 hNh hNh' ↦ ?_⟩
  rw [← hdbr h h' h0 hh' h'1 hNh hNh']
  let S := {p | 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hΨ).inter (measurableSet_lt hΨ measurable_const)
  have hind := integral_cellSquare_level_mul
    (φ := (Ioo h h').indicator fun _ ↦ (1 : ℝ)) (measurable_const.indicator measurableSet_Ioo)
    (C := 1) (fun s ↦ by by_cases hs : s ∈ Ioo h h' <;> simp [hs]) h0 h'1
    (fun s hs ↦ ⟨(Set.mem_of_indicator_ne_zero hs).1.le,
      (Set.mem_of_indicator_ne_zero hs).2.le⟩) (hJ h h' h0 h'1)
  have hpt (p) : (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) (dipoleLift p / 2) * J p =
      S.indicator J p := by
    by_cases hp : p ∈ S
    · rw [indicator_of_mem (show dipoleLift p / 2 ∈ Ioo h h' from
        ⟨by linarith [hp.1], by linarith [hp.2]⟩), indicator_of_mem hp, one_mul]
    · rw [indicator_of_notMem (show dipoleLift p / 2 ∉ Ioo h h' from
        fun hm ↦ hp ⟨by linarith [hm.1], by linarith [hm.2]⟩), indicator_of_notMem hp, zero_mul]
  have hst (s) : (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) s * levelIntegral s J =
      (Ioo h h').indicator (fun s ↦ levelIntegral s J) s := by
    by_cases hs : s ∈ Ioo h h' <;> simp [hs]
  simp_rw [hpt, hst] at hind
  rw [integral_indicator hS, Measure.restrict_restrict hS, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Icc_self] at hind
  have hset : {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'} =
      S ∩ cellSquare := by ext p; simp only [S, mem_ofPred_eq, mem_inter_iff]; tauto
  rw [hset, hind, intervalIntegral.integral_of_le hh'.le, integral_Ioc_eq_integral_Ioo,
    integral_const_mul]

/-! ### Positive-level regularity and bulk integrability -/

/-- Positive truncations are open. -/
theorem isOpen_ddTruncatedCell (a : ℝ) : IsOpen (ddTruncatedCell a) := by
  have hc : IsOpen cellSquare := by
    exact (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|)
      by unfold diagCoord; fun_prop) continuous_const).inter
      (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|)
        by unfold diagCoord; fun_prop) continuous_const)
  exact hc.inter (isOpen_lt continuous_const
    (show Continuous dipoleLift by unfold dipoleLift; fun_prop))

/-- Smooth division preserves both available stream derivatives on a positive
    truncation, including its elliptic center, without a global divided domain. -/
theorem ddStreamQuotient_memSobolevOn_of_le (ω : L2) {k : ℕ} (hk : k ≤ 2)
    {a : ℝ} (ha : 0 < a) : MemSobolevOn k (ddTruncatedCell a) (ddStreamQuotient ω) := by
  have hs : MemSobolev (k : ℝ) (invLap ω) :=
    (memSobolev_two_invLap ω).mono (by exact_mod_cast hk)
  have hb : Bornology.IsBounded cellNeighbourhood := isBounded_cellNeighbourhood
  have hh : MemSobolevOn k cellNeighbourhood (liftL2 (invLap ω)) := by
    exact memSobolevOn_liftL2 (k := k) (g := invLap ω) (U := cellNeighbourhood)
      (by simpa using hs) hb
  have hc : MemSobolevOn k cellNeighbourhood (contStream ω) :=
    MemSobolevOn.congr_ae (k := k) (U := cellNeighbourhood)
      (g := liftL2 (invLap ω)) (g' := contStream ω) hh (streamLift_ae_eq_contStream ω)
  let U := cellNeighbourhood ∩ {p | 0 < dipoleLift p}
  have hU : IsOpen U := isOrbitUnion_cellNeighbourhood.1.inter
    (isOpen_lt continuous_const
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop))
  have hloc : MemSobolevLocOn k U (contStream ω) :=
    (MemSobolevOn.memSobolevLocOn (k := k) hc).mono inter_subset_left
  have hd : MemSobolevLocOn k U (ddStreamQuotient ω) :=
    hloc.div_smooth hU (by unfold dipoleLift; fun_prop) (fun _ hp ↦ hp.2.ne')
  have hbound : Bornology.IsBounded cellSquare :=
    hb.subset (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  have hclosure : closure (ddTruncatedCell a) ⊆ U := by
    intro p hp
    refine ⟨closure_cellSquare_subset_cellNeighbourhood
      (closure_mono (fun _ h ↦ h.1) hp), ?_⟩
    have hle : a ≤ dipoleLift p :=
      closure_minimal (fun _ h ↦ h.2.le)
        (isClosed_le continuous_const
          (show Continuous dipoleLift by unfold dipoleLift; fun_prop)) hp
    exact ha.trans_le hle
  exact hd _ (isOpen_ddTruncatedCell a)
    (hbound.subset (fun _ hp ↦ hp.1)).isCompact_closure hclosure

/-- H¹ regularity on positive truncations. -/
theorem ddStreamQuotient_memSobolevOn (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemSobolevOn 1 (ddTruncatedCell a) (ddStreamQuotient ω) :=
  ddStreamQuotient_memSobolevOn_of_le ω (by norm_num) ha

/-- H² regularity on positive truncations. -/
theorem ddStreamQuotient_memSobolevOn_two (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemSobolevOn 2 (ddTruncatedCell a) (ddStreamQuotient ω) :=
  ddStreamQuotient_memSobolevOn_of_le ω (by norm_num) ha

/-- Arbitrary weak-derivative witnesses inherit H¹ regularity from the H² quotient. -/
theorem ddStreamQuotient_memSobolevOn_derivative {ω : L2} {j : Fin 2}
    {d : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn cellSquare j (ddStreamQuotient ω) d)
    {a : ℝ} (ha : 0 < a) : MemSobolevOn 1 (ddTruncatedCell a) d := by
  obtain ⟨d', hd', hi⟩ := (ddStreamQuotient_memSobolevOn_two ω ha).2 j
  exact MemSobolevOn.congr_ae_on (k := 1) hi (isOpen_ddTruncatedCell a).measurableSet
    (hd'.ae_eq (isOpen_ddTruncatedCell a) (hd.mono (fun _ hp ↦ hp.1)))

/-- Arbitrary weak-derivative witnesses are square integrable above positive levels. -/
theorem ddStreamQuotient_memLp_derivative {ω : L2} {j : Fin 2}
    {d : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn cellSquare j (ddStreamQuotient ω) d)
    {a : ℝ} (ha : 0 < a) :
    MemLp d 2 (volume.restrict (ddTruncatedCell a)) :=
  (ddStreamQuotient_memSobolevOn_derivative hd ha).1

/-- The apparent center singularities of the bulk coefficients are bounded on
    every positive truncation. Values at `Ψ = 2` are the totalized expressions. -/
theorem dd_coefficients_bound {p : ℝ × ℝ} {a : ℝ} (ha : 0 < a)
    (hp : a < dipoleLift p) :
    |ddF p| ≤ 8 / a ∧ |ddA p| ≤ 8 + 16 / a ∧ |ddC p| ≤ 4 := by
  let s := dipoleLift p
  have hs0 : 0 < s := ha.trans hp
  have hs2 : s ≤ 2 := by
    dsimp only [s, dipoleLift]
    linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
  have hβ0 : 0 ≤ (s ^ 2 + 2 * s + 4) / 3 := by positivity
  have hβ : (s ^ 2 + 2 * s + 4) / 3 ≤ 4 := by nlinarith
  have hF : ddF p = (s ^ 2 + 2 * s + 4) / 3 * normalCoeff p := by
    unfold ddF normalCoeff
    dsimp only [s]
    ring
  have hC : ddC p = (s ^ 2 + 2 * s + 4) / 3 * normalC p := by
    unfold ddC normalC
    dsimp only [s]
    ring
  have hf : 0 ≤ ddF p ∧ ddF p ≤ 8 / a := by
    rcases lt_or_eq_of_le hs2 with hs | hs
    · have hn := normalCoeff_nonneg hs0 hs
      have hb : normalCoeff p ≤ 2 / a := by
        refine (normalCoeff_le hs0 hs).trans ?_
        apply (div_le_div_iff₀ hs0 ha).mpr
        nlinarith [hp]
      rw [hF]
      refine ⟨mul_nonneg hβ0 hn, ?_⟩
      calc _ ≤ 4 * (2 / a) := mul_le_mul hβ hb hn (by norm_num)
        _ = _ := by ring
    · have hz : ddF p = 0 := by unfold ddF; change s * (8 - s ^ 3) * _ / _ = 0; rw [hs]; norm_num
      rw [hz]
      exact ⟨le_rfl, by positivity⟩
  have hc : 0 ≤ ddC p ∧ ddC p ≤ 4 := by
    rcases lt_or_eq_of_le hs2 with hs | hs
    · obtain ⟨hn, hb⟩ := normalC_pos_le_one hs0 hs
      rw [hC]
      exact ⟨mul_nonneg hβ0 hn.le, (mul_le_mul hβ hb hn.le (by norm_num)).trans_eq (by ring)⟩
    · have hz : ddC p = 0 := by unfold ddC; change s * (8 - s ^ 3) / _ = 0; rw [hs]; norm_num
      rw [hz]
      exact ⟨le_rfl, by norm_num⟩
  have hi : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha hp.le
  have hs : 0 ≤ 2 * s ^ 2 / 3 := by positivity
  have ht : 0 ≤ 32 / (3 * s) := by positivity
  have hA : |ddA p| ≤ 8 + 16 / a := by
    unfold ddA
    change |2 * s ^ 2 / 3 + 32 / (3 * s) - ddC p| ≤ _
    calc
      _ ≤ (2 * s ^ 2 / 3 + 32 / (3 * s)) + ddC p := by
        have hab := abs_sub (2 * s ^ 2 / 3 + 32 / (3 * s)) (ddC p)
        rw [abs_of_nonneg (add_nonneg hs ht), abs_of_nonneg hc.1] at hab
        exact hab
      _ ≤ _ := by
        have hpow : s ^ 2 ≤ 4 := by nlinarith
        have hb : 32 / (3 * s) ≤ (32 / 3 : ℝ) * (1 / a) := by
          calc _ = (32 / 3 : ℝ) * (1 / s) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)
        have hia : 0 ≤ 1 / a := by positivity
        simp only [div_eq_mul_inv] at hb hia ⊢
        nlinarith [hc.2]
  exact ⟨by rw [abs_of_nonneg hf.1]; exact hf.2,
    hA, by rw [abs_of_nonneg hc.1]; exact hc.2⟩

theorem measurable_ddStreamQuotient (ω : L2) : Measurable (ddStreamQuotient ω) := by
  unfold ddStreamQuotient dipoleLift
  have hc := (continuous_contStream ω).measurable
  fun_prop

theorem measurable_ddVorticityQuotient (ω : L2) : Measurable (ddVorticityQuotient ω) := by
  unfold ddVorticityQuotient dipoleLift
  have hm : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  fun_prop

/-- The undivided vorticity's L² norm controls division above a positive level. -/
theorem ddVorticityQuotient_memLp (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemLp (ddVorticityQuotient ω) 2 (volume.restrict (ddTruncatedCell a)) := by
  have hb : Bornology.IsBounded (ddTruncatedCell a) :=
    isBounded_cellNeighbourhood.subset (fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1))
  apply ((memLp_liftL2 ω hb).norm.const_mul (1 / a)).mono'
    (measurable_ddVorticityQuotient ω).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
  have hs : 0 < dipoleLift p := ha.trans hp.2
  rw [ddVorticityQuotient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hs.le]
  have hn := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ha hp.2.le)
    (norm_nonneg (liftL2 ω p))
  convert hn using 1
  ring

/-- The normal component of an L² gradient is L² for any measure, including
    totalized values at critical points. -/
theorem memLp_normalDeriv {μ : Measure (ℝ × ℝ)} {ux uy : ℝ × ℝ → ℂ}
    (hx : MemLp ux 2 μ) (hy : MemLp uy 2 μ) : MemLp (normalDeriv ux uy) 2 μ := by
  have msx : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have msy : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have mi : Measurable (fun p : ℝ × ℝ ↦ (gradNorm p : ℂ)⁻¹) := by
    unfold gradNorm
    fun_prop
  apply (hx.norm.add hy.norm).mono'
    (((msx.aestronglyMeasurable.mul hx.aestronglyMeasurable).add
      (msy.aestronglyMeasurable.mul hy.aestronglyMeasurable)).mul
        mi.aestronglyMeasurable)
  exact Eventually.of_forall (norm_normalDeriv_le ux uy)

/-- The tangential component obeys the same L² estimate. -/
theorem memLp_tangentDeriv {μ : Measure (ℝ × ℝ)} {ux uy : ℝ × ℝ → ℂ}
    (hx : MemLp ux 2 μ) (hy : MemLp uy 2 μ) : MemLp (tangentDeriv ux uy) 2 μ := by
  have msx : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have msy : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have mi : Measurable (fun p : ℝ × ℝ ↦ (gradNorm p : ℂ)⁻¹) := by
    unfold gradNorm
    fun_prop
  apply (hx.norm.add hy.norm).mono'
    (((msy.aestronglyMeasurable.mul hx.aestronglyMeasurable).sub
      (msx.aestronglyMeasurable.mul hy.aestronglyMeasurable)).mul
        mi.aestronglyMeasurable)
  exact Eventually.of_forall (norm_tangentDeriv_le ux uy)

/-- L² values and first derivatives suffice for absolute integrability of the
    weighted virial bulk on a positive truncation. -/
theorem ddVirialDensity_integrable {u e ux uy : ℝ × ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hu : MemLp u 2 (volume.restrict (ddTruncatedCell a)))
    (he : MemLp e 2 (volume.restrict (ddTruncatedCell a)))
    (hx : MemLp ux 2 (volume.restrict (ddTruncatedCell a)))
    (hy : MemLp uy 2 (volume.restrict (ddTruncatedCell a))) :
    IntegrableOn (ddVirialDensity u e ux uy) (ddTruncatedCell a) := by
  have isq (v : ℝ × ℝ → ℂ) (hv : MemLp v 2 (volume.restrict (ddTruncatedCell a))) :
      IntegrableOn (fun p ↦ ‖v p‖ ^ 2) (ddTruncatedCell a) :=
    (memLp_two_iff_integrable_sq hv.norm.aestronglyMeasurable).mp hv.norm
  have iU := isq u hu
  have iE := isq e he
  have iX := isq ux hx
  have iY := isq uy hy
  have mn := (memLp_normalDeriv hx hy).aestronglyMeasurable
  have mt := (memLp_tangentDeriv hx hy).aestronglyMeasurable
  have mf : Measurable ddF := by
    change Measurable (fun p ↦ ddF p)
    simp only [ddF, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have ma : Measurable ddA := by
    change Measurable (fun p ↦ ddA p)
    simp only [ddA, ddC, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have mc : Measurable ddC := by
    change Measurable (fun p ↦ ddC p)
    simp only [ddC, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have md : AEStronglyMeasurable (ddVirialDensity u e ux uy)
      (volume.restrict (ddTruncatedCell a)) :=
    (mf.aestronglyMeasurable.mul (he.aestronglyMeasurable.norm.pow 2 |>.sub
      (hu.aestronglyMeasurable.norm.pow 2))).add
      ((ma.aestronglyMeasurable.mul (mn.norm.pow 2)).add
        (mc.aestronglyMeasurable.mul (mt.norm.pow 2)))
  apply (((iE.add iU).const_mul (8 / a)).add
    ((iX.add iY).const_mul (24 + 32 / a))).mono' md
  filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
  rw [Real.norm_eq_abs]
  obtain ⟨hf, hA, hC⟩ := dd_coefficients_bound ha hp.2
  have hn : ‖normalDeriv ux uy p‖ ^ 2 ≤ 2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2) := by
    have hb := norm_normalDeriv_le ux uy p
    nlinarith [norm_nonneg (normalDeriv ux uy p), norm_nonneg (ux p),
      norm_nonneg (uy p), sq_nonneg (‖ux p‖ - ‖uy p‖)]
  have ht : ‖tangentDeriv ux uy p‖ ^ 2 ≤ 2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2) := by
    have hb := norm_tangentDeriv_le ux uy p
    nlinarith [norm_nonneg (tangentDeriv ux uy p), norm_nonneg (ux p),
      norm_nonneg (uy p), sq_nonneg (‖ux p‖ - ‖uy p‖)]
  have hv : |‖e p‖ ^ 2 - ‖u p‖ ^ 2| ≤ ‖e p‖ ^ 2 + ‖u p‖ ^ 2 := by
    have hb := abs_sub (‖e p‖ ^ 2) (‖u p‖ ^ 2)
    rw [abs_of_nonneg (sq_nonneg (‖e p‖)), abs_of_nonneg (sq_nonneg (‖u p‖))] at hb
    exact hb
  dsimp only [ddVirialDensity, ddMatrixForm]
  calc
    _ ≤ |ddF p * (‖e p‖ ^ 2 - ‖u p‖ ^ 2)| +
        (|ddA p * ‖normalDeriv (fun _ ↦ ux p) (fun _ ↦ uy p) p‖ ^ 2| +
          |ddC p * ‖tangentDeriv (fun _ ↦ ux p) (fun _ ↦ uy p) p‖ ^ 2|) :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (8 / a) * (‖e p‖ ^ 2 + ‖u p‖ ^ 2) +
        ((8 + 16 / a) * (2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2)) +
          4 * (2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2))) := by
      simp only [abs_mul, abs_pow, abs_norm]
      gcongr
      · exact hn
      · exact ht
    _ = _ := by dsimp only [Pi.add_apply]; ring

/-- The boundary density is absolutely integrable above each positive level.
    Thus coarea produces locally integrable level terms for arbitrary weak witnesses. -/
theorem ddBoundaryDensity_integrable {u e ux uy : ℝ × ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hu : MemLp u 2 (volume.restrict (ddTruncatedCell a)))
    (he : MemLp e 2 (volume.restrict (ddTruncatedCell a)))
    (hx : MemLp ux 2 (volume.restrict (ddTruncatedCell a)))
    (hy : MemLp uy 2 (volume.restrict (ddTruncatedCell a))) :
    IntegrableOn (ddBoundaryDensity u e ux uy) (ddTruncatedCell a) := by
  have hn : MemLp (ddInwardNormal ux uy) 2 (volume.restrict (ddTruncatedCell a)) :=
    (memLp_normalDeriv hx hy).neg
  have ht := memLp_tangentDeriv hx hy
  have isq (v : ℝ × ℝ → ℂ) (hv : MemLp v 2 (volume.restrict (ddTruncatedCell a))) :
      IntegrableOn (fun p ↦ ‖v p‖ ^ 2) (ddTruncatedCell a) :=
    (memLp_two_iff_integrable_sq hv.norm.aestronglyMeasurable).mp hv.norm
  have ic : IntegrableOn (fun p ↦ ‖ddInwardNormal ux uy p‖ ^ 2 -
      ‖tangentDeriv ux uy p‖ ^ 2 - ‖u p‖ ^ 2 +
      (e p * (starRingEnd ℂ) (u p)).re) (ddTruncatedCell a) :=
    (((isq _ hn).sub (isq _ ht)).sub (isq _ hu)).add (he.integrable_mul hu.star).re
  have il : IntegrableOn (fun p ↦ ((starRingEnd ℂ) (u p) *
      ddInwardNormal ux uy p).re) (ddTruncatedCell a) := (hu.star.integrable_mul hn).re
  have mb : Measurable (fun p ↦ (8 - dipoleLift p ^ 3) / 3) := by
    unfold dipoleLift
    fun_prop
  have ml : Measurable (fun p ↦ dipoleLift p ^ 2 * gradNorm p) := by
    unfold dipoleLift gradNorm
    fun_prop
  have hb : ∀ᵐ p ∂(volume.restrict (ddTruncatedCell a)),
      ‖(8 - dipoleLift p ^ 3) / 3‖ ≤ 8 ∧ ‖dipoleLift p ^ 2 * gradNorm p‖ ≤ 8 := by
    filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
    have hs0 : 0 < dipoleLift p := ha.trans hp.2
    have hs2 : dipoleLift p ≤ 2 := by
      unfold dipoleLift
      linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
    have hg0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have hg2 : gradNorm p ≤ 2 := by
      have hsq : gradNorm p ^ 2 ≤ 2 := by
        rw [gradNorm, Real.sq_sqrt (by positivity)]
        linarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
      nlinarith
    have hs3 : dipoleLift p ^ 3 ≤ 8 := by
      calc _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hs0.le hs2 3
        _ = 8 := by norm_num
    constructor
    · rw [Real.norm_of_nonneg (by linarith : 0 ≤ (8 - dipoleLift p ^ 3) / 3)]
      have hs3pos : 0 ≤ dipoleLift p ^ 3 := by positivity
      linarith
    · rw [Real.norm_of_nonneg (by positivity)]
      have hpow : dipoleLift p ^ 2 ≤ 4 := by nlinarith
      nlinarith
  exact (ic.bdd_mul mb.aestronglyMeasurable (hb.mono fun _ h ↦ h.1)).sub
    (il.bdd_mul ml.aestronglyMeasurable (hb.mono fun _ h ↦ h.2))

/-- Once the weak cutoff identity is known, all integrability, coarea, level
    normalization and common-exceptional-set conclusions of the annular virial follow. -/
theorem dd_annular_virial_of_cutoff_identity (ω : L2) {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    (hcut : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        (∫ p in cellSquare, φ (dipoleLift p / 2) *
          ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
        ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 *
          ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) :
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
  have iJ (a : ℝ) (ha : 0 < a) := ddVirialDensity_integrable ha
    (ddStreamQuotient_memSobolevOn ω ha).1 (ddVorticityQuotient_memLp ω ha).neg
    (ddStreamQuotient_memLp_derivative hx ha) (ddStreamQuotient_memLp_derivative hy ha)
  have iB (a : ℝ) (ha : 0 < a) := ddBoundaryDensity_integrable ha
    (ddStreamQuotient_memSobolevOn ω ha).1 (ddVorticityQuotient_memLp ω ha).neg
    (ddStreamQuotient_memLp_derivative hx ha) (ddStreamQuotient_memLp_derivative hy ha)
  refine ⟨fun a b ha _ _ ↦ (iJ a ha).mono_set (fun _ hp ↦ ⟨hp.1, hp.2.1⟩), ?_⟩
  obtain ⟨N, hN, hann⟩ := annular_virial_of_cutoff_identity
    (J := ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy)
    (B := ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy)
    (fun a _ ha _ ↦ (iJ a ha).mono_set fun _ hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩)
    (fun a _ ha _ ↦ (iB a ha).mono_set fun _ hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩) hcut
  refine ⟨(fun ε : ℝ ↦ ε / 2) ⁻¹' N, ?_, fun a b ha hab hb haN hbN ↦ ?_⟩
  · rw [show (fun ε : ℝ ↦ ε / 2) = (fun ε ↦ (1 / 2 : ℝ) * ε) by funext ε; ring,
      Real.volume_preimage_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0), hN, mul_zero]
  · have h := hann (a / 2) (b / 2) (by linarith) (by linarith) (by linarith) haN hbN
    rw [levelIntegral_ddBoundaryDensity _ _ _ _ (by linarith) (by linarith),
      levelIntegral_ddBoundaryDensity _ _ _ _ (by linarith) (by linarith)] at h
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

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
  apply dd_annular_virial_of_cutoff_identity ω hx hy
  intro φ hφ a b ha hb hsupp
  sorry

/-! ### Center flux and removal -/

/-- A quantitative center bound for arbitrary measurable values and first derivatives.
    It uses only a bounded value and square-integrable orbit energy, not an equation. -/
theorem abs_ddVirialLevel_le {u e ux uy : ℝ × ℝ → ℂ}
    (mu : Measurable u) (me : Measurable e) (mx : Measurable ux) (my : Measurable uy)
    {M h : ℝ} (hM0 : 0 ≤ M) (hh : 1 / 2 < h) (h1 : h < 1)
    (hF : IntegrableOn (fun t ↦ ‖u (dipoleOrbit h t)‖ ^ 2 +
      ‖ux (dipoleOrbit h t)‖ ^ 2 + ‖uy (dipoleOrbit h t)‖ ^ 2 +
      ‖e (dipoleOrbit h t)‖ ^ 2) (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖u (dipoleOrbit h t)‖ ≤ M) :
    |ddVirialLevel u e ux uy (2 * h)| ≤
      4 * M * √(128 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2))) +
      96 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2)) := by
  have h0 : 0 < h := by linarith
  have hL := eighthPeriod_pos h0 h1
  have hL2 : eighthPeriod h ≤ 2 :=
    (eighthPeriod_le_inv h0 h1).trans (by rw [div_le_iff₀ h0]; linarith)
  let I := Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
  let γ := fun t ↦ dipoleOrbit h t
  let n := ddInwardNormal ux uy
  let τ := tangentDeriv ux uy
  let F := fun t ↦ ‖u (γ t)‖ ^ 2 + ‖ux (γ t)‖ ^ 2 +
    ‖uy (γ t)‖ ^ 2 + ‖e (γ t)‖ ^ 2
  let B := fun t ↦ ‖n (γ t)‖ ^ 2 - ‖τ (γ t)‖ ^ 2 - ‖u (γ t)‖ ^ 2 +
    (e (γ t) * (starRingEnd ℂ) (u (γ t))).re
  let A := fun t ↦ gradNorm (γ t) * ((starRingEnd ℂ) (u (γ t)) * n (γ t)).re
  have mγ : Measurable γ :=
    (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have mn : Measurable (fun t ↦ n (γ t)) := by
    dsimp [n, ddInwardNormal, normalDeriv, gradNorm]
    fun_prop
  have mt : Measurable (fun t ↦ τ (γ t)) := by
    dsimp [τ, tangentDeriv, gradNorm]
    fun_prop
  have mρ : Measurable (fun t ↦ gradNorm (γ t)) := by unfold gradNorm; fun_prop
  have hρ0 (t) : 0 ≤ gradNorm (γ t) := Real.sqrt_nonneg _
  have hρ2 (t) : gradNorm (γ t) ^ 2 ≤ 4 * (1 - h) := by
    have hΨ := dipoleLift_dipoleOrbit h0 h1 t
    change dipoleLift (γ t) = 2 * h at hΨ
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    simp only [dipoleLift] at hΨ
    nlinarith [Real.sin_sq_add_cos_sq (γ t).1, Real.sin_sq_add_cos_sq (γ t).2,
      sq_nonneg (1 - Real.cos (γ t).1), sq_nonneg (1 - Real.cos (γ t).2)]
  have hn (t) : ‖n (γ t)‖ ^ 2 ≤ 2 * F t := by
    have hb := norm_normalDeriv_le ux uy (γ t)
    have he : ‖n (γ t)‖ = ‖normalDeriv ux uy (γ t)‖ := norm_neg _
    rw [← he] at hb
    dsimp only [F]
    nlinarith [norm_nonneg (n (γ t)), norm_nonneg (ux (γ t)), norm_nonneg (uy (γ t)),
      sq_nonneg (‖ux (γ t)‖ - ‖uy (γ t)‖), sq_nonneg (‖u (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have ht (t) : ‖τ (γ t)‖ ^ 2 ≤ 2 * F t := by
    have hb := norm_tangentDeriv_le ux uy (γ t)
    dsimp only [F]
    nlinarith [norm_nonneg (τ (γ t)), norm_nonneg (ux (γ t)), norm_nonneg (uy (γ t)),
      sq_nonneg (‖ux (γ t)‖ - ‖uy (γ t)‖), sq_nonneg (‖u (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have hu (t) : ‖u (γ t)‖ ^ 2 ≤ F t := by
    dsimp only [F]
    nlinarith [sq_nonneg (‖ux (γ t)‖), sq_nonneg (‖uy (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have hre (a b : ℂ) : |(a * (starRingEnd ℂ) b).re| ≤ ‖a‖ * ‖b‖ :=
    (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hp (t) : |(e (γ t) * (starRingEnd ℂ) (u (γ t))).re| ≤ F t := by
    refine (hre _ _).trans ?_
    dsimp only [F]
    nlinarith [sq_nonneg (‖e (γ t)‖ - ‖u (γ t)‖),
      sq_nonneg (‖ux (γ t)‖), sq_nonneg (‖uy (γ t)‖)]
  have hb (t) : |B t| ≤ 6 * F t := by
    have hp' := abs_le.mp (hp t)
    dsimp only [B]
    apply abs_le.mpr
    constructor <;> nlinarith [hn t, ht t, hu t,
      sq_nonneg (‖n (γ t)‖), sq_nonneg (‖τ (γ t)‖), sq_nonneg (‖u (γ t)‖)]
  have ha (t) : |A t| ≤ 3 * F t := by
    dsimp only [A]
    rw [abs_mul, abs_of_nonneg (hρ0 t)]
    have hr : gradNorm (γ t) ≤ 2 := by nlinarith [hρ2 t, hρ0 t]
    have hrp : |((starRingEnd ℂ) (u (γ t)) * n (γ t)).re| ≤ ‖u (γ t)‖ * ‖n (γ t)‖ := by
      simpa [mul_comm] using hre (n (γ t)) (u (γ t))
    nlinarith [mul_le_mul hr hrp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      hn t, hu t, sq_nonneg (‖u (γ t)‖ - ‖n (γ t)‖)]
  have iF : Integrable F (volume.restrict I) := hF
  have iN : Integrable (fun t ↦ ‖n (γ t)‖ ^ 2) (volume.restrict I) :=
    (iF.const_mul 2).mono' (mn.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hn t)
  have iB : Integrable B (volume.restrict I) :=
    (iF.const_mul 6).mono'
      (((mn.norm.pow_const 2).sub (mt.norm.pow_const 2)).sub
        ((mu.comp mγ).norm.pow_const 2) |>.add
        (Complex.measurable_re.comp ((me.comp mγ).mul
          (Complex.continuous_conj.measurable.comp (mu.comp mγ))))).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ hb t)
  have iA : Integrable A (volume.restrict I) :=
    (iF.const_mul 3).mono'
      (mρ.mul (Complex.measurable_re.comp
        ((Complex.continuous_conj.measurable.comp (mu.comp mγ)).mul mn))).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ha t)
  have iρ : Integrable (fun t ↦ gradNorm (γ t) ^ 2) (volume.restrict I) :=
    (integrable_const (4 * (1 - h))).mono' (mρ.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hρ2 t)
  have iρn : Integrable (fun t ↦ gradNorm (γ t) * ‖n (γ t)‖) (volume.restrict I) :=
    (iρ.add iN).mono' (mρ.mul mn.norm).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (norm_nonneg _)), Pi.add_apply]
        nlinarith [sq_nonneg (gradNorm (γ t) - ‖n (γ t)‖)])
  let g := ∫ t in I, F t
  have hg0 : 0 ≤ g := integral_nonneg fun t ↦ by dsimp only [F]; positivity
  have hNI : (∫ t in I, ‖n (γ t)‖ ^ 2) ≤ 2 * g := by
    rw [← integral_const_mul]
    exact integral_mono iN (iF.const_mul 2) hn
  have hBI : |∫ t in I, B t| ≤ 6 * g := by
    rw [← integral_const_mul]
    exact abs_integral_le_integral_abs.trans (integral_mono iB.abs (iF.const_mul 6) hb)
  have hρI : ∫ t in I, gradNorm (γ t) ^ 2 ≤ 64 * (1 - h) := by
    calc _ ≤ ∫ t in I, 4 * (1 - h) := integral_mono iρ (integrable_const _) hρ2
      _ = 8 * eighthPeriod h * (4 * (1 - h)) := by
        rw [setIntegral_const, Real.volume_real_Ico_of_le (by linarith),
          smul_eq_mul]
        ring
      _ ≤ _ := by nlinarith
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict I)
    Real.HolderConjugate.two_two (Eventually.of_forall hρ0)
    (Eventually.of_forall fun t ↦ norm_nonneg (n (γ t)))
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq mρ.aestronglyMeasurable).2 iρ)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq mn.norm.aestronglyMeasurable).2 iN)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hAI : |∫ t in I, A t| ≤ M * √(128 * ((1 - h) * g)) := by
    calc _ ≤ ∫ t in I, |A t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in I, M * (gradNorm (γ t) * ‖n (γ t)‖) := by
        apply integral_mono_ae iA.abs (iρn.const_mul M)
        filter_upwards [hM] with t hMt
        dsimp only [A]
        rw [abs_mul, abs_of_nonneg (hρ0 t)]
        have hrp : |((starRingEnd ℂ) (u (γ t)) * n (γ t)).re| ≤
            ‖u (γ t)‖ * ‖n (γ t)‖ := by
          simpa [mul_comm] using hre (n (γ t)) (u (γ t))
        calc _ ≤ gradNorm (γ t) * (‖u (γ t)‖ * ‖n (γ t)‖) :=
            mul_le_mul_of_nonneg_left hrp (hρ0 t)
          _ ≤ gradNorm (γ t) * (M * ‖n (γ t)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hMt (norm_nonneg _)) (hρ0 t)
          _ = _ := by ring
      _ = M * ∫ t in I, gradNorm (γ t) * ‖n (γ t)‖ := integral_const_mul _ _
      _ ≤ M * (√(∫ t in I, gradNorm (γ t) ^ 2) *
          √(∫ t in I, ‖n (γ t)‖ ^ 2)) := by gcongr
      _ ≤ M * (√(64 * (1 - h)) * √(2 * g)) := by gcongr
      _ = _ := by
        rw [← Real.sqrt_mul (by linarith)]
        congr 2
        ring
  have hc0 : 0 ≤ (8 - (2 * h) ^ 3) / 3 := by
    have hp := pow_le_pow_left₀ h0.le h1.le 3
    norm_num at hp
    nlinarith
  have hc : (8 - (2 * h) ^ 3) / 3 ≤ 16 * (1 - h) := by
    have h2 : h ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - h) (by nlinarith : 0 ≤ 5 - h - h ^ 2)]
  have hG : ddVirialLevel u e ux uy (2 * h) =
      (8 - (2 * h) ^ 3) / 3 * (∫ t in I, B t) - (2 * h) ^ 2 * ∫ t in I, A t := by
    unfold ddVirialLevel
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      levelIntegral_eq_integral_orbitWindow h0 h1]
    simp_rw [mul_assoc ((2 * h) ^ 2)]
    exact (integral_sub (iB.const_mul _) (iA.const_mul _)).trans
      (by rw [integral_const_mul, integral_const_mul])
  rw [hG]
  calc _ ≤ (8 - (2 * h) ^ 3) / 3 * |∫ t in I, B t| +
        (2 * h) ^ 2 * |∫ t in I, A t| := by
          have hb := abs_sub ((8 - (2 * h) ^ 3) / 3 * ∫ t in I, B t)
            ((2 * h) ^ 2 * ∫ t in I, A t)
          rw [abs_mul, abs_mul, abs_of_nonneg hc0,
            abs_of_nonneg (sq_nonneg (2 * h))] at hb
          exact hb
    _ ≤ 16 * (1 - h) * (6 * g) + 4 * (M * √(128 * ((1 - h) * g))) := by
      gcongr
      nlinarith
    _ = _ := by ring

/-- The weighted boundary term vanishes along center levels avoiding any prescribed
    null set. Energy is required only on the fixed inner truncation `Ψ > 1`. -/
theorem dd_center_limit {u e ux uy : ℝ × ℝ → ℂ}
    (mu : Measurable u) (me : Measurable e) (mx : Measurable ux) (my : Measurable uy)
    (hi : IntegrableOn (fun p ↦ ‖u p‖ ^ 2 + ‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖e p‖ ^ 2)
      (ddTruncatedCell 1))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ ddTruncatedCell 1, ‖u p‖ ≤ M)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ seq : ℕ → ℝ, (∀ j, seq j ∈ Ioo 0 1 ∧ seq j ∉ N) ∧
      Tendsto seq atTop (𝓝 1) ∧
      Tendsto (fun j ↦ ddVirialLevel u e ux uy (2 * seq j)) atTop (𝓝 0) := by
  let F := (ddTruncatedCell 1).indicator
    (fun p ↦ ‖u p‖ ^ 2 + ‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖e p‖ ^ 2)
  have mF : Measurable F := by
    apply Measurable.indicator _ (isOpen_ddTruncatedCell 1).measurableSet
    fun_prop
  have iF : IntegrableOn F cellSquare :=
    hi.integrable_indicator (isOpen_ddTruncatedCell 1).measurableSet |>.integrableOn
  have hF0 (p) : 0 ≤ F p := by
    apply Set.indicator_nonneg
    intro p _
    positivity
  have hg : ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      ENNReal.ofReal (F (dipoleOrbit h t)) ≠ ⊤ := by
    intro htop
    have hc := lintegral_cellSquare_eq (ENNReal.measurable_ofReal.comp mF)
    have hlt := iF.lintegral_lt_top
    simp only [Function.comp_apply] at hc
    rw [hc, htop, ENNReal.mul_top (by norm_num)] at hlt
    exact lt_irrefl _ hlt
  have hgood : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), 1 / 2 < h → h < 1 →
      |ddVirialLevel u e ux uy (2 * h)| ≤
        4 * M * √(128 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h)
          (6 * eighthPeriod h), ENNReal.ofReal (F (dipoleOrbit h t))).toReal)) +
        96 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h)
          (6 * eighthPeriod h), ENNReal.ofReal (F (dipoleOrbit h t))).toReal) := by
    filter_upwards [(integral_cellSquare_eq iF).1] with h hFh hh h1
    have horbit (t) : dipoleOrbit h t ∈ ddTruncatedCell 1 :=
      ⟨dipoleOrbit_mem_cellSquare (by linarith) h1 t,
        by rw [dipoleLift_dipoleOrbit (by linarith) h1]; linarith⟩
    have hFeq (t) : F (dipoleOrbit h t) =
        ‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2 :=
      indicator_of_mem (horbit t) _
    have hb := abs_ddVirialLevel_le mu me mx my hM0 hh h1
      (hFh.congr_fun (fun t _ ↦ hFeq t) measurableSet_Ico)
      (ae_restrict_of_forall_mem measurableSet_Ico (fun t _ ↦ hM _ (horbit t)))
    have hint : (∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), F (dipoleOrbit h t)) =
        (∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
          ENNReal.ofReal (F (dipoleOrbit h t))).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t ↦ hF0 _)
        hFh.aestronglyMeasurable
    rw [← hint]
    simpa only [hFeq] using hb
  rw [ae_restrict_iff' measurableSet_Ioo] at hgood
  obtain ⟨seq, hmem, hlim, hprod⟩ := exists_seq_one_sub_mul_tendsto_zero hg
    (N := N ∪ {h | ¬(h ∈ Ioo 0 1 → 1 / 2 < h → h < 1 → _)})
    (measure_union_null hN (ae_iff.1 hgood))
  refine ⟨seq, fun j ↦ ⟨(hmem j).1, fun h ↦ (hmem j).2 (Or.inl h)⟩, hlim, ?_⟩
  have hpr : Tendsto (fun j ↦ (1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
      (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod
    simp only [ENNReal.toReal_zero] at h
    exact h.congr fun j ↦ by
      simp only [Function.comp_apply, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by linarith [(hmem j).1.2] : 0 ≤ 1 - seq j)]
  have hup : Tendsto (fun j ↦
      4 * M * √(128 * ((1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
        (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal)) +
      96 * ((1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
        (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal))
      atTop (𝓝 0) := by
    simpa using ((hpr.const_mul 128).sqrt.const_mul (4 * M)).add (hpr.const_mul 96)
  refine squeeze_zero_norm' ?_ hup
  filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
    with j hj
  have hgj := (hmem j).2
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hgj
  exact hgj.2 (hmem j).1 hj (hmem j).1.2

/-- Coarea transfers even nonmeasurable a.e. properties: cover the bad planar set
    by a measurable null set before applying the measurable coarea interface. -/
theorem ae_level_of_ae_cellSquare' {P : ℝ × ℝ → Prop}
    (hP : ∀ᵐ p ∂(volume.restrict cellSquare), P p) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
        P (dipoleOrbit h t) := by
  have hc : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  let B := {p | p ∈ cellSquare ∧ ¬P p}
  have hB : volume B = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' hc).mp hP
  let M := toMeasurable volume B
  have hM : volume M = 0 := by rw [measure_toMeasurable, hB]
  have hlevels := ae_level_of_ae_cellSquare
    (measurableSet_toMeasurable volume B).compl
    (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hM))
  filter_upwards [hlevels, ae_restrict_mem measurableSet_Ioo] with h hh hi
  filter_upwards [hh] with t ht
  by_contra hbad
  exact ht (subset_toMeasurable volume B
    ⟨dipoleOrbit_mem_cellSquare hi.1 hi.2 t, hbad⟩)

/-- Center removal for the original eigenfunction quotients and arbitrary weak
    derivative witnesses; no global divided-domain theorem is invoked. -/
theorem dd_raw_center_limit (ω : L2) {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ seq : ℕ → ℝ, (∀ j, seq j ∈ Ioo 0 2 ∧ seq j ∉ N) ∧
      Tendsto seq atTop (𝓝 2) ∧
      Tendsto (fun j ↦ ddVirialLevel (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy (seq j)) atTop (𝓝 0) := by
  have hxl := ddStreamQuotient_memLp_derivative hx (by norm_num : (0 : ℝ) < 1)
  have hyl := ddStreamQuotient_memLp_derivative hy (by norm_num : (0 : ℝ) < 1)
  let X := hxl.aestronglyMeasurable.mk ux
  let Y := hyl.aestronglyMeasurable.mk uy
  have mX : Measurable X := hxl.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have mY : Measurable Y := hyl.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hX : ux =ᵐ[volume.restrict (ddTruncatedCell 1)] X := hxl.aestronglyMeasurable.ae_eq_mk
  have hY : uy =ᵐ[volume.restrict (ddTruncatedCell 1)] Y := hyl.aestronglyMeasurable.ae_eq_mk
  have iU : IntegrableOn (fun p ↦ ‖ddStreamQuotient ω p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq
      (measurable_ddStreamQuotient ω).norm.aestronglyMeasurable).mp
      (ddStreamQuotient_memSobolevOn ω (by norm_num : (0 : ℝ) < 1)).1.norm
  have iE : IntegrableOn (fun p ↦ ‖-ddVorticityQuotient ω p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq
      (measurable_ddVorticityQuotient ω).neg.norm.aestronglyMeasurable).mp
      (ddVorticityQuotient_memLp ω (by norm_num : (0 : ℝ) < 1)).neg.norm
  have iX : IntegrableOn (fun p ↦ ‖X p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq mX.norm.aestronglyMeasurable).mp
      ((memLp_congr_ae hX).mp hxl).norm
  have iY : IntegrableOn (fun p ↦ ‖Y p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq mY.norm.aestronglyMeasurable).mp
      ((memLp_congr_ae hY).mp hyl).norm
  have hbound (p) (hp : p ∈ ddTruncatedCell 1) :
      ‖ddStreamQuotient ω p‖ ≤ ‖continuousRep (invLap ω)‖ := by
    have hs : 0 < dipoleLift p := lt_trans (by norm_num) hp.2
    rw [ddStreamQuotient, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    calc _ ≤ ‖contStream ω p‖ := div_le_self (norm_nonneg _) hp.2.le
      _ ≤ _ := (continuousRep (invLap ω)).norm_coe_le_norm _
  have hrep : ∀ᵐ p ∂(volume.restrict cellSquare),
      p ∈ ddTruncatedCell 1 → ux p = X p ∧ uy p = Y p := by
    filter_upwards [ae_restrict_of_ae
      ((ae_restrict_iff' (isOpen_ddTruncatedCell 1).measurableSet).mp hX),
      ae_restrict_of_ae
        ((ae_restrict_iff' (isOpen_ddTruncatedCell 1).measurableSet).mp hY)]
      with p hp hq hpc
    exact ⟨hp hpc, hq hpc⟩
  let P : ℝ → Prop := fun h ↦ 1 / 2 < h →
    ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy (2 * h) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) X Y (2 * h)
  have hP : ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)), P h := by
    filter_upwards [ae_level_of_ae_cellSquare' hrep, ae_restrict_mem measurableSet_Ioo]
      with h hh hi hhalf
    unfold ddVirialLevel
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      levelIntegral_eq_integral_orbitWindow hi.1 hi.2,
      levelIntegral_eq_integral_orbitWindow hi.1 hi.2]
    apply integral_congr_ae
    filter_upwards [hh] with t ht
    have hp : dipoleOrbit h t ∈ ddTruncatedCell 1 :=
      ⟨dipoleOrbit_mem_cellSquare hi.1 hi.2 t,
        by rw [dipoleLift_dipoleOrbit hi.1 hi.2]; linarith⟩
    obtain ⟨hx, hy⟩ := ht hp
    simp only [ddInwardNormal, normalDeriv, tangentDeriv, hx, hy]
  let B := {h | h ∈ Ioo 0 1 ∧ ¬P h}
  have hB : volume B = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' measurableSet_Ioo).mp hP
  have hNr : volume ((fun h : ℝ ↦ 2 * h) ⁻¹' N) = 0 := by
    rw [Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0), hN, mul_zero]
  obtain ⟨seq, hseq, hlim, hG⟩ := dd_center_limit
    (measurable_ddStreamQuotient ω) (measurable_ddVorticityQuotient ω).neg mX mY
    (((iU.add iX).add iY).add iE) (norm_nonneg _) hbound
    (measure_union_null hNr hB)
  refine ⟨fun j ↦ 2 * seq j, fun j ↦ ⟨⟨by linarith [(hseq j).1.1],
    by linarith [(hseq j).1.2]⟩, fun hj ↦ (hseq j).2 (Or.inl hj)⟩, ?_, ?_⟩
  · simpa using hlim.const_mul (2 : ℝ)
  · apply hG.congr'
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with j hj
    have hp : P (seq j) := by
      by_contra hbad
      exact (hseq j).2 (Or.inr ⟨(hseq j).1, hbad⟩)
    exact (hp hj).symm

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
  obtain ⟨-, N, hN, hann⟩ := dd_annular_virial hlam hω hs hx hy
  have hlt2 : ∀ᵐ p : ℝ × ℝ, dipoleLift p < 2 := by
    filter_upwards [ae_cos_fst_ne_cos_snd] with p hp
    by_contra hge
    exact hp (by
      have h1 := Real.cos_le_one p.1
      have h2 := Real.cos_le_one p.2
      unfold dipoleLift at hge
      linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hN)] with a ha haN
  have hi := ddVirialDensity_integrable ha.1
    (ddStreamQuotient_memSobolevOn ω ha.1).1
    (ddVorticityQuotient_memLp ω ha.1).neg
    (ddStreamQuotient_memLp_derivative hx ha.1)
    (ddStreamQuotient_memLp_derivative hy ha.1)
  refine ⟨hi, ?_⟩
  obtain ⟨seq, hseq, hlim, hG⟩ := dd_raw_center_limit ω hx hy hN
  let D := ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy
  let A := ddTruncatedCell a
  have hm (b : ℝ) : MeasurableSet {p | dipoleLift p < b} :=
    measurableSet_lt (show Measurable dipoleLift by unfold dipoleLift; fun_prop) measurable_const
  have hset (j : ℕ) : {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < seq j} =
      A ∩ {p | dipoleLift p < seq j} := by
    ext p
    simp only [A, ddTruncatedCell, mem_ofPred_eq, mem_inter_iff, and_assoc]
  have hev : ∀ᶠ j in atTop, a < seq j := hlim.eventually (lt_mem_nhds ha.2)
  have hlim1 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < seq j}, D p)
      atTop (𝓝 (ddVirialLevel (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy a)) := by
    have hd := (tendsto_const_nhds (x := ddVirialLevel (ddStreamQuotient ω)
      (fun p ↦ -ddVorticityQuotient ω p) ux uy a)).sub hG
    rw [sub_zero] at hd
    apply hd.congr'
    filter_upwards [hev] with j hj
    rw [← hset]
    exact (hann a (seq j) ha.1 hj (hseq j).1.2 haN (hseq j).2).symm
  have hlim2 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < seq j}, D p)
      atTop (𝓝 (∫ p in A, D p)) := by
    have hind (j : ℕ) : (∫ p in A ∩ {p | dipoleLift p < seq j}, D p) =
        ∫ p in A, {p | dipoleLift p < seq j}.indicator D p := by
      rw [Set.inter_comm A, ← Measure.restrict_restrict (hm _), integral_indicator (hm _)]
    simp_rw [hind]
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖D p‖)
    · exact fun j ↦ hi.aestronglyMeasurable.indicator (hm _)
    · exact hi.norm
    · intro j
      filter_upwards with p
      by_cases hp : p ∈ {p | dipoleLift p < seq j}
      · simp [indicator_of_mem hp]
      · simp [indicator_of_notMem hp]
    · filter_upwards [ae_restrict_of_ae hlt2] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (lt_mem_nhds hp)] with j hj
      exact (indicator_of_mem (show p ∈ {q | dipoleLift q < seq j} from hj) D).symm
  exact tendsto_nhds_unique hlim2 hlim1

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