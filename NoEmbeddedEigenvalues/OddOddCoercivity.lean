import NoEmbeddedEigenvalues.OddOddVirial

/-!
# The weighted form domain for odd–odd bulk coercivity

The measure is `ddCellMeasure = Ψ² dx` on the open positive cell. Its maximal
weak H¹ form domain records value and specified first derivatives in weighted
L², with distributional derivatives on the open cell. It imposes no boundary
trace, boundedness, or smooth-density hypothesis. In particular it is not the
zero-trace closure of an unweighted Sobolev space.

The Poincaré constant is for Cartesian derivatives. Diagonal coordinates give
one half of the sum of the two one-dimensional eigenvalues `n(n+2)`; simultaneous
central parity removes odd total degree, leaving first nonconstant eigenvalue 3.
The spectral argument must apply to the whole weak form domain, not just smooth
functions or finite polynomial sums.

For the actual Picone quotient, the matrix lower bound and the supplied Picone
energy give precisely this weighted domain. Kantorovich and the constraint
`∫ w z = 0` control the mean of `z = φ/w`; they do not assert its mean is zero.
Coefficient inequalities are asserted off the elliptic center (or a.e.), because
real division assigns artificial values to the singular matrix formulas there.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

private theorem measurable_ground : Measurable ddGround := by
  unfold ddGround
  simp only [gradSq_dipoleLift, dipoleLift]
  fun_prop

private theorem measurable_weight : Measurable ddWeight := by
  unfold ddWeight dipoleLift
  fun_prop

private theorem ae_regular :
    ∀ᵐ p ∂volume.restrict cellSquare, p ∈ cellSquare ∧ gradSq dipoleLift p ≠ 0 := by
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet,
    ae_restrict_of_ae ae_cos_fst_ne_cos_snd] with p hp hn
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have ht : dipoleLift p < 2 := by
    by_contra hge
    apply hn
    unfold dipoleLift at hge
    linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
  exact ⟨hp, (gradSq_dipoleLift_pos hs ht).ne'⟩

private theorem integral_ddCellMeasure (f : ℝ × ℝ → ℝ) :
    ∫ p, f p ∂ddCellMeasure = ∫ p in cellSquare, ddWeight p * f p := by
  rw [ddCellMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_weight.ennreal_ofReal) (by simp)]
  simp only [ddWeight, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-- Maximal weighted first-order form domain on the open positive cell, with
    specified distributional Cartesian derivatives. There is no boundary condition. -/
structure DDWeightedH1 (z zx zy : ℝ × ℝ → ℂ) : Prop where
  weak_x : HasWeakPartialOn cellSquare 0 z zx
  weak_y : HasWeakPartialOn cellSquare 1 z zy
  value_l2 : MemLp z 2 ddCellMeasure
  x_l2 : MemLp zx 2 ddCellMeasure
  y_l2 : MemLp zy 2 ddCellMeasure

/-- Mean for the probability normalization of `Ψ² dx` on the cell. -/
def ddWeightedMean (z : ℝ × ℝ → ℂ) : ℂ :=
  (∫ p, z p ∂ddCellMeasure) / (ddCellMeasure.real univ : ℂ)

/-- Unnormalized squared weighted L² norm. Integrability is a separate property. -/
def ddWeightedNormSq (z : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p, ‖z p‖ ^ 2 ∂ddCellMeasure

/-- Unnormalized weighted energy for specified Cartesian derivatives. -/
def ddWeightedEnergy (zx zy : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p, ‖zx p‖ ^ 2 + ‖zy p‖ ^ 2 ∂ddCellMeasure

/-- Unnormalized variance; only the mean uses the probability normalization. -/
def ddWeightedVariance (z : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p, ‖z p - ddWeightedMean z‖ ^ 2 ∂ddCellMeasure

/-- The total weighted cell mass is finite and has its physical normalization. -/
theorem ddCellMeasure_mass : ddCellMeasure univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  sorry

/-- All integrals used in the weighted form and its variance are genuine finite
    integrals on the stated weak domain. -/
theorem DDWeightedH1.integrable {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy) :
    Integrable z ddCellMeasure ∧
      Integrable (fun p ↦ ‖z p‖ ^ 2) ddCellMeasure ∧
      Integrable (fun p ↦ ‖zx p‖ ^ 2 + ‖zy p‖ ^ 2) ddCellMeasure ∧
      Integrable (fun p ↦ ‖z p - ddWeightedMean z‖ ^ 2) ddCellMeasure := by
  sorry

/-- Weighted Poincaré on the maximal weak form domain, with central parity a.e.
    No endpoint traces or extra reflection parities are assumed. -/
theorem zonal_poincare {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy)
    (hc : ∀ᵐ p ∂(volume.restrict cellSquare), z (-p.1, -p.2) = z p) :
    3 * ddWeightedVariance z ≤ ddWeightedEnergy zx zy := by
  sorry

/-- The elementary Kantorovich bound, for a real weight on an arbitrary probability
    space. Boundedness and a.e. measurability suffice; no differentiability is used. -/
theorem kantorovich_bound {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {w : α → ℝ} (hw : AEStronglyMeasurable w ρ)
    (hb : ∀ᵐ p ∂ρ, 1 ≤ w p ∧ w p ≤ 5 / 4) :
    0 < (∫ p, w p ∂ρ) ∧
      (∫ p, (w p - ∫ q, w q ∂ρ) ^ 2 ∂ρ) / (∫ p, w p ∂ρ) ^ 2 ≤ (1 / 80 : ℝ) := by
  sorry

/-- The weighted orthogonality constraint controls the nonzero mean of `z`.
    The norms and variance here use unnormalized weighted area. -/
theorem dd_weighted_constraint {z : ℝ × ℝ → ℂ} (hz : MemLp z 2 ddCellMeasure)
    {w : ℝ × ℝ → ℝ} (hw : AEStronglyMeasurable w ddCellMeasure)
    (hb : ∀ᵐ p ∂ddCellMeasure, 1 ≤ w p ∧ w p ≤ 5 / 4)
    (hmean : (∫ p, (w p : ℂ) * z p ∂ddCellMeasure) = 0) :
    ddWeightedNormSq z ≤ (81 / 80 : ℝ) * ddWeightedVariance z := by
  sorry

/-- Constrained Poincaré in the exact constants consumed by the Picone gradient:
    `z` is centrally even and `w z`, not `z`, has weighted mean zero. -/
theorem dd_constrained_poincare {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy)
    (hc : ∀ᵐ p ∂(volume.restrict cellSquare), z (-p.1, -p.2) = z p)
    {w : ℝ × ℝ → ℝ} (hw : AEStronglyMeasurable w ddCellMeasure)
    (hb : ∀ᵐ p ∂ddCellMeasure, 1 ≤ w p ∧ w p ≤ 5 / 4)
    (hmean : (∫ p, (w p : ℂ) * z p ∂ddCellMeasure) = 0) :
    (80 / 27 : ℝ) * ddWeightedNormSq (fun p ↦ (w p : ℂ) * z p) ≤
      (25 / 16 : ℝ) * ddWeightedEnergy zx zy := by
  sorry

/-- Elementary ground-state range and matrix lower bound, excluding the artificial
    value of the singular matrix expression at the elliptic center. -/
theorem dd_ground_matrix_bounds {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) :
    (1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4) ∧
      ∀ vx vy : ℂ, (25 / 16 : ℝ) * ddWeight p * (‖vx‖ ^ 2 + ‖vy‖ ^ 2) ≤
        ddGround p ^ 2 * ddMatrixForm p vx vy := by
  sorry

/-- The three bulk coefficient bounds on the regular positive cell. The residual
    inequality is a separate sign-certificate obligation, not a Poincaré consequence. -/
theorem dd_bulk_coefficients {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) :
    (1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4) ∧
      (∀ vx vy : ℂ, (25 / 16 : ℝ) * ddWeight p * (‖vx‖ ^ 2 + ‖vy‖ ^ 2) ≤
        ddGround p ^ 2 * ddMatrixForm p vx vy) ∧
      -(5 / 2 : ℝ) * ddWeight p * ddGround p ≤ ddGroundResidual p := by
  sorry

/-- The data actually supplied to weighted Poincaré by the bulk Picone hypotheses.
    The derivative witnesses are the existing quotient-rule Fourier derivatives.
    No global H¹ representative or boundary trace of the divided function is assumed. -/
theorem dd_bulk_form_domain {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    (hc : centralInversion φ = φ)
    (hmean : (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 φ p) = 0)
    (hgrad : IntegrableOn (ddPiconeGradient φ dx dy) cellSquare) :
    let z : ℝ × ℝ → ℂ := fun p ↦ liftL2 φ p / (ddGround p : ℂ)
    DDWeightedH1 z (ddDividedPartial φ dx 0) (ddDividedPartial φ dy 1) ∧
      (∀ᵐ p ∂(volume.restrict cellSquare), z (-p.1, -p.2) = z p) ∧
      (∫ p, (ddGround p : ℂ) * z p ∂ddCellMeasure) = 0 ∧
      ddWeightedNormSq (fun p ↦ (ddGround p : ℂ) * z p) =
        ∫ p in cellSquare, ddMassDensity φ p := by
  sorry

/-- Gradient coercivity on the precise domain used by `dd_bulk_picone`. -/
theorem dd_bulk_gradient_bound {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    (hc : centralInversion φ = φ)
    (hmean : (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 φ p) = 0)
    (hgrad : IntegrableOn (ddPiconeGradient φ dx dy) cellSquare) :
    (80 / 27 : ℝ) * (∫ p in cellSquare, ddMassDensity φ p) ≤
      ∫ p in cellSquare, ddPiconeGradient φ dx dy p := by
  obtain ⟨hz, hc, hm, hmass⟩ := dd_bulk_form_domain hφ hdx hdy hc hmean hgrad
  have hb : ∀ᵐ p ∂volume.restrict cellSquare, 1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4 := by
    filter_upwards [ae_regular] with p hp
    exact (dd_ground_matrix_bounds hp.1 hp.2).1
  have hbρ : ∀ᵐ p ∂ddCellMeasure, 1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4 :=
    (withDensity_absolutelyContinuous _ _).ae_le hb
  have hP := dd_constrained_poincare hz hc
    (measurable_ground.aestronglyMeasurable) hbρ hm
  rw [hmass] at hP
  apply hP.trans
  rw [ddWeightedEnergy, integral_ddCellMeasure, ← integral_const_mul]
  have hi : IntegrableOn (fun p ↦ (25 / 16 : ℝ) * (ddWeight p *
      (‖ddDividedPartial φ dx 0 p‖ ^ 2 + ‖ddDividedPartial φ dy 1 p‖ ^ 2))) cellSquare := by
    have he := hz.integrable.2.2.1
    have hi := (integrable_withDensity_iff_integrable_smul'
      measurable_weight.ennreal_ofReal (by simp)).mp he
    simpa only [IntegrableOn, ddWeight, ENNReal.toReal_ofReal (sq_nonneg _),
      smul_eq_mul] using hi.const_mul (25 / 16 : ℝ)
  apply integral_mono_ae hi hgrad
  filter_upwards [ae_regular] with p hp
  simpa only [ddPiconeGradient, mul_assoc] using
    (dd_ground_matrix_bounds hp.1 hp.2).2
      (ddDividedPartial φ dx 0 p) (ddDividedPartial φ dy 1 p)

/-- The residual certificate bounds the integrable potential term from below. -/
theorem dd_bulk_potential_bound (φ : L2)
    (hpot : IntegrableOn (ddPiconePotential φ) cellSquare) :
    -(5 / 2 : ℝ) * (∫ p in cellSquare, ddMassDensity φ p) ≤
      ∫ p in cellSquare, ddPiconePotential φ p := by
  rw [← integral_const_mul]
  apply integral_mono_ae ((integrableOn_ddMassDensity φ).const_mul _) hpot
  filter_upwards [ae_regular] with p hp
  have hb := dd_bulk_coefficients hp.1 hp.2
  have hw : 0 < ddGround p := lt_of_lt_of_le zero_lt_one hb.1.1
  have h := (le_div_iff₀ hw).mpr hb.2.2
  simpa only [ddPiconePotential, ddMassDensity, mul_assoc] using
    mul_le_mul_of_nonneg_right h (sq_nonneg ‖liftL2 φ p‖)

end NoEmbeddedEigenvalues
