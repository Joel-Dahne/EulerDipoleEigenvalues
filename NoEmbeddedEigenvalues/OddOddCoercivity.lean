import NoEmbeddedEigenvalues.OddOddVirial
import NoEmbeddedEigenvalues.PolynomialInequalities

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
energy give precisely this weighted domain. A midpoint completed-square estimate
and the constraint `∫ w z = 0` control the mean of `z = φ/w`; they do not assert
its mean is zero.
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
  have hi : IntegrableOn ddWeight cellSquare := by
    have hb : Bornology.IsBounded cellSquare :=
      isBounded_cellNeighbourhood.subset fun _ hp ↦
        closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
    have hc : Continuous ddWeight := by unfold ddWeight dipoleLift; fun_prop
    exact (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hcos : (∫ x in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos x ^ 2) = Real.pi / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_cos_sq]
    simp only [neg_div, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, sub_zero]
    ring
  have hd : (∫ p in cellSquare, ddWeight p) = 2 * Real.pi ^ 2 := by
    rw [← integral_indicator isOpen_cellSquare.measurableSet,
      integral_eq_two_smul_integral_diagInv]
    have heq : (fun q ↦ cellSquare.indicator ddWeight (diagInv q)) =
        (Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2)).indicator
          (fun q ↦ 4 * (Real.cos q.1 ^ 2 * Real.cos q.2 ^ 2)) := by
      funext q
      have hq : diagInv q ∈ cellSquare ↔
          q ∈ Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2) := by
        simp only [cellSquare, mem_ofPred_eq, diagCoord_diagInv, abs_lt, mem_prod,
          mem_Ioo, neg_div]
      by_cases hp : diagInv q ∈ cellSquare
      · rw [indicator_of_mem hp, indicator_of_mem (hq.mp hp), ddWeight,
          dipoleLift_eq_diag, diagCoord_diagInv]
        ring
      · rw [indicator_of_notMem hp, indicator_of_notMem (mt hq.mpr hp)]
    rw [heq, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
      integral_const_mul, Measure.volume_eq_prod,
      setIntegral_prod_mul (fun x : ℝ ↦ Real.cos x ^ 2) (fun x : ℝ ↦ Real.cos x ^ 2), hcos]
    simp only [smul_eq_mul]
    ring
  rw [ddCellMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun p ↦ sq_nonneg _), hd]

/-- All integrals used in the weighted form and its variance are genuine finite
    integrals on the stated weak domain. -/
theorem DDWeightedH1.integrable {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy) :
    Integrable z ddCellMeasure ∧
      Integrable (fun p ↦ ‖z p‖ ^ 2) ddCellMeasure ∧
      Integrable (fun p ↦ ‖zx p‖ ^ 2 + ‖zy p‖ ^ 2) ddCellMeasure ∧
      Integrable (fun p ↦ ‖z p - ddWeightedMean z‖ ^ 2) ddCellMeasure := by
  let : IsFiniteMeasure ddCellMeasure := ⟨by rw [ddCellMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  exact ⟨h.value_l2.integrable (by norm_num),
    h.value_l2.integrable_norm_pow (by norm_num),
    (h.x_l2.integrable_norm_pow (by norm_num)).add
      (h.y_l2.integrable_norm_pow (by norm_num)),
    (h.value_l2.sub (memLp_const _)).integrable_norm_pow (by norm_num)⟩

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

private theorem midpoint_square_bound {w : ℝ} (hw : 1 ≤ w ∧ w ≤ 5 / 4)
    (a b : ℝ) : (80 / 81 : ℝ) * a ^ 2 ≤ (a - b) ^ 2 + (16 / 9 : ℝ) * w * a * b := by
  have ht : 0 ≤ 1 - (8 * w - 9) ^ 2 := by nlinarith [hw.1, hw.2]
  nlinarith [sq_nonneg (a / 9 + (8 * w - 9) * b), mul_nonneg ht (sq_nonneg b)]

private theorem midpoint_norm_bound {w : ℝ} (hw : 1 ≤ w ∧ w ≤ 5 / 4)
    (a b : ℂ) : (80 / 81 : ℝ) * ‖a‖ ^ 2 ≤ ‖a - b‖ ^ 2 +
      (16 / 9 : ℝ) * (((w : ℂ) * a) * starRingEnd ℂ b).re := by
  have hr := midpoint_square_bound hw a.re b.re
  have hi := midpoint_square_bound hw a.im b.im
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero] at *
  nlinarith

/-- The weighted orthogonality constraint controls the nonzero mean of `z`.
    The norms and variance here use unnormalized weighted area. -/
theorem dd_weighted_constraint {z : ℝ × ℝ → ℂ} (hz : MemLp z 2 ddCellMeasure)
    {w : ℝ × ℝ → ℝ} (hw : AEStronglyMeasurable w ddCellMeasure)
    (hb : ∀ᵐ p ∂ddCellMeasure, 1 ≤ w p ∧ w p ≤ 5 / 4)
    (hmean : (∫ p, (w p : ℂ) * z p ∂ddCellMeasure) = 0) :
    ddWeightedNormSq z ≤ (81 / 80 : ℝ) * ddWeightedVariance z := by
  let : IsFiniteMeasure ddCellMeasure := ⟨by rw [ddCellMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  let m := ddWeightedMean z
  have hi := hz.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hv : Integrable (fun p ↦ ‖z p - m‖ ^ 2) ddCellMeasure :=
    (hz.sub (memLp_const m)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hwz : Integrable (fun p ↦ (w p : ℂ) * z p) ddCellMeasure := by
    apply (hz.integrable (by norm_num)).bdd_mul (c := (5 / 4 : ℝ))
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw)
    filter_upwards [hb] with p hp
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ w p)]
      using hp.2
  have hc : Integrable (fun p ↦ (((w p : ℂ) * z p) * starRingEnd ℂ m).re) ddCellMeasure :=
    (hwz.mul_const (starRingEnd ℂ m)).re
  have hzero : (∫ p, (((w p : ℂ) * z p) * starRingEnd ℂ m).re ∂ddCellMeasure) = 0 := by
    change (∫ p, RCLike.re (((w p : ℂ) * z p) * starRingEnd ℂ m) ∂ddCellMeasure) = 0
    rw [integral_re (hwz.mul_const _), integral_mul_const, hmean, zero_mul]
    rfl
  have hineq : (80 / 81 : ℝ) * ddWeightedNormSq z ≤ ddWeightedVariance z := by
    have h := integral_mono_ae (hi.const_mul (80 / 81 : ℝ))
      (hv.add (hc.const_mul (16 / 9 : ℝ))) (by
        filter_upwards [hb] with p hp
        exact midpoint_norm_bound hp (z p) m)
    change (∫ p, (80 / 81 : ℝ) * ‖z p‖ ^ 2 ∂ddCellMeasure) ≤
      ∫ p, ‖z p - m‖ ^ 2 + (16 / 9 : ℝ) *
        (((w p : ℂ) * z p) * starRingEnd ℂ m).re ∂ddCellMeasure at h
    rw [integral_add hv (hc.const_mul (16 / 9 : ℝ)), integral_const_mul, integral_const_mul, hzero,
      mul_zero, add_zero] at h
    exact h
  linarith

/-- Constrained Poincaré in the exact constants consumed by the Picone gradient:
    `z` is centrally even and `w z`, not `z`, has weighted mean zero. -/
theorem dd_constrained_poincare {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy)
    (hc : ∀ᵐ p ∂(volume.restrict cellSquare), z (-p.1, -p.2) = z p)
    {w : ℝ × ℝ → ℝ} (hw : AEStronglyMeasurable w ddCellMeasure)
    (hb : ∀ᵐ p ∂ddCellMeasure, 1 ≤ w p ∧ w p ≤ 5 / 4)
    (hmean : (∫ p, (w p : ℂ) * z p ∂ddCellMeasure) = 0) :
    (80 / 27 : ℝ) * ddWeightedNormSq (fun p ↦ (w p : ℂ) * z p) ≤
      (25 / 16 : ℝ) * ddWeightedEnergy zx zy := by
  have hn := dd_weighted_constraint h.value_l2 hw hb hmean
  have hp := zonal_poincare h hc
  have hi := h.integrable.2.1
  have hb2 : ∀ᵐ p ∂ddCellMeasure, w p ^ 2 ≤ (25 / 16 : ℝ) := by
    filter_upwards [hb] with p hp
    nlinarith [hp.1, hp.2]
  have hiw : Integrable (fun p ↦ ‖(w p : ℂ) * z p‖ ^ 2) ddCellMeasure := by
    apply (hi.const_mul (25 / 16 : ℝ)).mono'
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable hw).mul
        h.value_l2.aestronglyMeasurable).norm.pow 2)
    filter_upwards [hb2] with p hp
    change ‖‖(w p : ℂ) * z p‖ ^ 2‖ ≤ (25 / 16 : ℝ) * ‖z p‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_right hp (sq_nonneg ‖z p‖)
  have hN : ddWeightedNormSq (fun p ↦ (w p : ℂ) * z p) ≤
      (25 / 16 : ℝ) * ddWeightedNormSq z := by
    rw [ddWeightedNormSq, ddWeightedNormSq, ← integral_const_mul]
    apply integral_mono_ae hiw (hi.const_mul _)
    filter_upwards [hb2] with p hp
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_right hp (sq_nonneg ‖z p‖)
  linarith

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
  obtain ⟨hw, hM⟩ := dd_ground_matrix_bounds hp hr
  refine ⟨hw, hM, ?_⟩
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hrpos : 0 < gradSq dipoleLift p := lt_of_le_of_ne
    (by rw [gradSq_dipoleLift]; positivity) hr.symm
  have hrhi : gradSq dipoleLift p ≤ 2 - dipoleLift p ^ 2 / 2 := by
    nlinarith [sq_cos_sub_cos p, sq_nonneg (Real.cos p.1 - Real.cos p.2)]
  have hs2 : dipoleLift p < 2 := by nlinarith
  have hR := dd_residual_nonneg hs hs2 (dipoleLift_mul_le_gradSq p) hrhi
  rw [← dd_residual_identity hp hr] at hR
  linarith

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
