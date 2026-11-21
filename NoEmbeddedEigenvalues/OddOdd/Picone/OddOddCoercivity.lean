import NoEmbeddedEigenvalues.OddOdd.WeightedVirial.OddOddVirial
import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddBulkIntegrability
import NoEmbeddedEigenvalues.Certificates.Inequalities.OddOdd
import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddPiconeIntegrability
import NoEmbeddedEigenvalues.Analysis.TorusSobolev.FourierC1Multiplier
import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalTransport
import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalSpectral

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

For the actual Picone quotient, the globally C¹ reciprocal ground state sends
Fourier H¹ data into ordinary H¹ on the bounded cell. Boundedness of the weight
then gives the weighted domain without a Picone-energy assumption. The matrix
lower bound is used by gradient coercivity, not domain membership. A midpoint
completed-square estimate and `∫ w z = 0` control the mean of `z = φ/w`;
they do not assert its mean is zero.
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
  rw [ddCellMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun p ↦ sq_nonneg _), integral_cellSquare_ddWeight]

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

/-- The physical maximal weak domain supplies both diagonal weak derivatives
and their weighted L² membership. No boundary traces or parity are needed. -/
theorem DDWeightedH1.zonal_diagonal_domain {z zx zy : ℝ × ℝ → ℂ}
    (h : DDWeightedH1 z zx zy) :
    HasWeakPartialOn zonalSquare 0 (z ∘ diagInv) ((fun p ↦ zx p + zy p) ∘ diagInv) ∧
      HasWeakPartialOn zonalSquare 1 (z ∘ diagInv) ((fun p ↦ zx p - zy p) ∘ diagInv) ∧
      MemLp (z ∘ diagInv) 2 zonalMeasure ∧
      MemLp ((fun p ↦ zx p + zy p) ∘ diagInv) 2 zonalMeasure ∧
      MemLp ((fun p ↦ zx p - zy p) ∘ diagInv) 2 zonalMeasure := by
  have ha := h.weak_x.comp_diagInv_fst isOpen_cellSquare h.weak_y
  have hb := h.weak_x.comp_diagInv_snd isOpen_cellSquare h.weak_y
  rw [preimage_cellSquare_diagInv] at ha hb
  exact ⟨ha, hb, memLp_zonalMeasure_comp_diagInv h.value_l2,
    memLp_zonalMeasure_comp_diagInv (h.x_l2.add h.y_l2),
    memLp_zonalMeasure_comp_diagInv (h.x_l2.sub h.y_l2)⟩

/-- Weak pairing with every product zonal mode, on the original maximal weak
weighted H¹ domain (`lem:zonal-weak-pairing`), including absolute integrability. -/
theorem DDWeightedH1.zonal_weak_pairing {z zx zy : ℝ × ℝ → ℂ}
    (h : DDWeightedH1 z zx zy) (k : ℕ × ℕ) :
    Integrable (fun q ↦ (zx (diagInv q) + zy (diagInv q)) *
      (zonalProductPartial k 0 q : ℂ)) zonalMeasure ∧
      Integrable (fun q ↦ (zx (diagInv q) - zy (diagInv q)) *
        (zonalProductPartial k 1 q : ℂ)) zonalMeasure ∧
      Integrable (fun q ↦ z (diagInv q) * (zonalProduct k q : ℂ)) zonalMeasure ∧
      (∫ q, (zx (diagInv q) + zy (diagInv q)) * (zonalProductPartial k 0 q : ℂ) +
        (zx (diagInv q) - zy (diagInv q)) * (zonalProductPartial k 1 q : ℂ) ∂zonalMeasure) =
        (2 * zonalEigenvalue k.1 k.2 : ℝ) *
          (∫ q, z (diagInv q) * (zonalProduct k q : ℂ) ∂zonalMeasure) := by
  obtain ⟨ha, hb, hz, hza, hzb⟩ := h.zonal_diagonal_domain
  exact zonal_weak_pairing_square ha hb hz hza hzb k

/-- Weighted Poincaré on the maximal weak form domain, with central parity a.e.
    No endpoint traces or extra reflection parities are assumed. -/
theorem zonal_poincare {z zx zy : ℝ × ℝ → ℂ} (h : DDWeightedH1 z zx zy)
    (hc : ∀ᵐ p ∂(volume.restrict cellSquare), z (-p.1, -p.2) = z p) :
    3 * ddWeightedVariance z ≤ ddWeightedEnergy zx zy := by
  obtain ⟨ha, hb, hz, hza, hzb⟩ := h.zonal_diagonal_domain
  have hcν : ∀ᵐ q ∂zonalMeasure, (z ∘ diagInv) (-q) = (z ∘ diagInv) q := by
    filter_upwards [ae_zonalMeasure_comp_diagInv hc] with q hq
    change z (diagInv (-q)) = z (diagInv q)
    rw [map_neg]
    exact (congrArg z (show -(diagInv q) = (-(diagInv q).1, -(diagInv q).2) from
      Prod.ext rfl rfl)).trans hq
  have hspec := zonal_poincare_square ha hb hz hza hzb hcν
  dsimp only [Function.comp_apply] at hspec
  let r : ℝ := 1 / (2 * Real.pi ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hmass : ddCellMeasure.real univ = 2 * Real.pi ^ 2 := by
    change (ddCellMeasure univ).toReal = _
    rw [ddCellMeasure_mass, ENNReal.toReal_ofReal (by positivity)]
  have hmean : (∫ q, z (diagInv q) ∂zonalMeasure) = ddWeightedMean z := by
    rw [integral_comp_diagInv_zonalMeasure, ddWeightedMean, hmass]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hvar : (∫ q, ‖z (diagInv q) - ∫ t, z (diagInv t) ∂zonalMeasure‖ ^ 2 ∂zonalMeasure) =
      r * ddWeightedVariance z := by
    simp_rw [hmean]
    exact integral_comp_diagInv_zonalMeasure (fun p ↦ ‖z p - ddWeightedMean z‖ ^ 2)
  have henergy : (∫ q, ‖zx (diagInv q) + zy (diagInv q)‖ ^ 2 ∂zonalMeasure) +
      (∫ q, ‖zx (diagInv q) - zy (diagInv q)‖ ^ 2 ∂zonalMeasure) =
        (2 * r) * ddWeightedEnergy zx zy := by
    rw [integral_comp_diagInv_zonalMeasure (fun p ↦ ‖zx p + zy p‖ ^ 2),
      integral_comp_diagInv_zonalMeasure (fun p ↦ ‖zx p - zy p‖ ^ 2)]
    change r * (∫ p, ‖zx p + zy p‖ ^ 2 ∂ddCellMeasure) +
      r * (∫ p, ‖zx p - zy p‖ ^ 2 ∂ddCellMeasure) = _
    have ia : Integrable (fun p ↦ ‖zx p + zy p‖ ^ 2) ddCellMeasure :=
      (h.x_l2.add h.y_l2).integrable_norm_pow (by norm_num)
    have ib : Integrable (fun p ↦ ‖zx p - zy p‖ ^ 2) ddCellMeasure :=
      (h.x_l2.sub h.y_l2).integrable_norm_pow (by norm_num)
    rw [← mul_add, ← integral_add ia ib]
    have heq : (fun p ↦ ‖zx p + zy p‖ ^ 2 + ‖zx p - zy p‖ ^ 2) =
        fun p ↦ 2 * (‖zx p‖ ^ 2 + ‖zy p‖ ^ 2) := by
      funext p
      exact parallelogram_law_with_norm ℂ (zx p) (zy p)
    rw [heq, integral_const_mul]
    change r * (2 * ddWeightedEnergy zx zy) = _
    ring
  rw [hvar, henergy] at hspec
  exact (mul_le_mul_iff_right₀ (mul_pos zero_lt_two hr)).mp (by nlinarith only [hspec])

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

/-- Scalar matrix comparison on the geometric range; no residual sign is used. -/
private theorem ground_scalar_matrix {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hlo : s * (2 - s) ≤ r) (hhi : r ≤ 2 - s ^ 2 / 2) :
    let w := 1 + (r + s ^ 2) / 16 - r ^ 2 / 256 * Real.log (r / 2)
    (1 ≤ w ∧ w ≤ 5 / 4) ∧
      (25 / 16 : ℝ) * s ^ 2 ≤ s * (8 - s ^ 3) / (3 * r) * w ^ 2 ∧
      s * (8 - s ^ 3) / (3 * r) ≤
        2 * s ^ 2 / 3 + 32 / (3 * s) - s * (8 - s ^ 3) / (3 * r) := by
  dsimp only
  let w := 1 + (r + s ^ 2) / 16 - r ^ 2 / 256 * Real.log (r / 2)
  have hs2 : s < 2 := by nlinarith
  have hr2 : r ≤ 2 := by nlinarith [sq_nonneg s]
  have hlog : Real.log (r / 2) ≤ 0 :=
    Real.log_nonpos (by positivity) (by linarith)
  have hlower : (16 + s ^ 2 + r) / 16 ≤ w := by
    dsimp [w]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hlog]
  have hw1 : 1 ≤ w := by nlinarith [sq_nonneg s]
  have habs := (Real.abs_log_mul_self_lt (r / 2) (by positivity) (by linarith)).le
  have hlogbound : -(r * Real.log (r / 2)) ≤ 2 := by
    have := (abs_le.mp habs).1
    nlinarith
  have hw2 : w ≤ 5 / 4 := by
    have := mul_le_mul_of_nonneg_left hlogbound hr.le
    dsimp [w]
    nlinarith
  refine ⟨⟨hw1, hw2⟩, ?_, ?_⟩
  · let R := 2 - s ^ 2 / 2
    let a := 16 + s ^ 2
    have hR : 0 < R := hr.trans_le hhi
    have hR2 : R ≤ 2 := by dsimp [R]; nlinarith [sq_nonneg s]
    have ha : 16 ≤ a := by dsimp [a]; nlinarith [sq_nonneg s]
    have hrR : r ≤ R := hhi
    have hfac : 0 ≤ a ^ 2 - r * R := by
      have := mul_le_mul hr2 hR2 (by positivity : 0 ≤ R) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    have hmon : r * (a + R) ^ 2 ≤ R * (a + r) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hrR) hfac]
    have hpoly : 0 ≤ 2 * (s ^ 2 + 2 * s + 4) * (s ^ 2 + 36) ^ 2 -
        4800 * s * (s + 2) := by
      let t := 2 - s
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have ht2 : t ≤ 2 := by dsimp [t]; linarith
      have h1 : 0 ≤ 4544 - 1984 * t := by linarith
      have h2 : 0 ≤ 312 - 28 * t := by linarith
      calc
        _ = t * (1920 + t * (4544 - 1984 * t) +
            t ^ 3 * (312 - 28 * t) + 2 * t ^ 5) := by dsimp [t]; ring
        _ ≥ 0 := by positivity
    have hbase : 1200 * s * R ≤ (8 - s ^ 3) * (a + R) ^ 2 := by
      have := mul_nonneg (sub_nonneg.mpr hs2.le) hpoly
      dsimp [a, R]
      nlinarith only [this]
    have h8 : 0 ≤ 8 - s ^ 3 := by
      have := mul_nonneg (sub_nonneg.mpr hs2.le)
        (by nlinarith [sq_nonneg s] : 0 ≤ s ^ 2 + 2 * s + 4)
      nlinarith only [this]
    have hnum : 1200 * s * r ≤ (8 - s ^ 3) * (a + r) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hR).mp
      have h1 := mul_le_mul_of_nonneg_left hmon h8
      have h2 := mul_le_mul_of_nonneg_right hbase hr.le
      nlinarith only [h1, h2]
    have hwsq : (a + r) ^ 2 ≤ 256 * w ^ 2 := by
      dsimp [a]
      nlinarith [sq_nonneg (16 * w - (16 + s ^ 2 + r))]
    have h1 := mul_le_mul_of_nonneg_left hwsq (mul_nonneg hs.le h8)
    have h2 := mul_le_mul_of_nonneg_left hnum hs.le
    change (25 / 16 : ℝ) * s ^ 2 ≤ s * (8 - s ^ 3) / (3 * r) * w ^ 2
    rw [show s * (8 - s ^ 3) / (3 * r) * w ^ 2 =
      (s * (8 - s ^ 3) * w ^ 2) / (3 * r) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith only [h1, h2]
  · have heq : (2 * s ^ 2 / 3 + 32 / (3 * s) -
        2 * (s * (8 - s ^ 3) / (3 * r))) * (3 * s * r) =
        (2 * s ^ 3 + 32) * r - 2 * s ^ 2 * (8 - s ^ 3) := by
      field_simp
    have h1 := mul_le_mul_of_nonneg_left hlo
      (by positivity : 0 ≤ 2 * s ^ 3 + 32)
    have h2 : 0 ≤ 4 * s * (s - 2) ^ 2 * (s + 4) := by positivity
    have hn : 0 ≤ 2 * s ^ 2 / 3 + 32 / (3 * s) -
        2 * (s * (8 - s ^ 3) / (3 * r)) := by
      apply nonneg_of_mul_nonneg_right _ (by positivity : 0 < 3 * s * r)
      rw [mul_comm, heq]
      nlinarith only [h1, h2]
    linarith

/-- Elementary ground-state range and matrix lower bound, excluding the artificial
    value of the singular matrix expression at the elliptic center. -/
theorem dd_ground_matrix_bounds {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) :
    (1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4) ∧
      ∀ vx vy : ℂ, (25 / 16 : ℝ) * ddWeight p * (‖vx‖ ^ 2 + ‖vy‖ ^ 2) ≤
        ddGround p ^ 2 * ddMatrixForm p vx vy := by
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hrpos : 0 < gradSq dipoleLift p :=
    lt_of_le_of_ne (by rw [gradSq_dipoleLift]; positivity) hr.symm
  have hrhi : gradSq dipoleLift p ≤ 2 - dipoleLift p ^ 2 / 2 := by
    nlinarith [sq_cos_sub_cos p, sq_nonneg (Real.cos p.1 - Real.cos p.2)]
  obtain ⟨hw, hC, hA⟩ := ground_scalar_matrix hs hrpos (dipoleLift_mul_le_gradSq p) hrhi
  change (1 ≤ ddGround p ∧ ddGround p ≤ 5 / 4) at hw
  change (25 / 16 : ℝ) * ddWeight p ≤ ddC p * ddGround p ^ 2 at hC
  change ddC p ≤ ddA p at hA
  refine ⟨hw, fun vx vy ↦ ?_⟩
  have hf := norm_normalDeriv_sq_add_norm_tangentDeriv_sq
    (fun _ ↦ vx) (fun _ ↦ vy) (by
      apply Real.sqrt_ne_zero'.mpr
      simpa only [gradSq_dipoleLift] using hrpos)
  have hn := mul_le_mul_of_nonneg_right hA
    (sq_nonneg ‖normalDeriv (fun _ ↦ vx) (fun _ ↦ vy) p‖)
  have hc := mul_le_mul_of_nonneg_right hC
    (add_nonneg (sq_nonneg ‖vx‖) (sq_nonneg ‖vy‖))
  have hw0 := mul_le_mul_of_nonneg_left hn (sq_nonneg (ddGround p))
  conv_rhs at hc => rw [← hf]
  dsimp only [ddMatrixForm]
  nlinarith only [hc, hw0]

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

private theorem contDiff_sq_mul_log : ContDiff ℝ 1 (fun x : ℝ ↦ x ^ 2 * Real.log x) := by
  let D := fun x : ℝ ↦ 2 * (x * Real.log x) + x
  have hD : Continuous D := (Real.continuous_mul_log.const_mul 2).add continuous_id
  have hF : Continuous (fun x : ℝ ↦ x ^ 2 * Real.log x) := by
    convert continuous_id.mul Real.continuous_mul_log using 1
    funext x
    change x ^ 2 * Real.log x = x * (x * Real.log x)
    ring
  have hdne (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun x : ℝ ↦ x ^ 2 * Real.log x) (D x) x := by
    convert ((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_log hx) using 1
    · rfl
    · dsimp [D]
      field_simp
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2 * Real.log x) (D x) x :=
    hasDerivAt_of_hasDerivAt_of_ne' hdne (hF.continuousAt (x := 0))
      (hD.continuousAt (x := 0)) x
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  have heq : deriv (fun x : ℝ ↦ x ^ 2 * Real.log x) = D := funext fun x ↦ (hd x).deriv
  rw [heq]
  exact hD

/-- The logarithmic ground state is C¹ even at the elliptic center. -/
theorem contDiff_one_ddGround : ContDiff ℝ 1 ddGround := by
  have hr : ContDiff ℝ 1 (gradSq dipoleLift) := by rw [gradSq_dipoleLift]; fun_prop
  have hs : ContDiff ℝ 1 dipoleLift := by unfold dipoleLift; fun_prop
  have h := ((contDiff_const (c := (1 : ℝ))).add ((hr.add (hs.pow 2)).div_const 16)).sub
    (((contDiff_const (c := (4 : ℝ))).mul
      (contDiff_sq_mul_log.comp (hr.div_const 2))).div_const 256)
  convert h using 1
  funext p
  dsimp [ddGround]
  ring

private theorem memLp_continuous_mul_cell {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict cellSquare)) {c : ℝ × ℝ → ℂ} (hc : Continuous c) :
    MemLp (fun p ↦ c p * f p) 2 (volume.restrict cellSquare) := by
  have hb : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hc.continuousOn
  apply hf.of_le_mul (c := C) (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet] with p hp
  change ‖c p * f p‖ ≤ C * ‖f p‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC p (subset_closure hp)) (norm_nonneg _)

private theorem memLp_ddCellMeasure {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict cellSquare)) : MemLp f 2 ddCellMeasure := by
  have hw : ∀ p, 0 ≤ ddWeight p ∧ ddWeight p ≤ 4 := by
    intro p
    refine ⟨sq_nonneg _, ?_⟩
    unfold ddWeight dipoleLift
    nlinarith [Real.cos_le_one p.1, Real.cos_le_one p.2,
      Real.neg_one_le_cos p.1, Real.neg_one_le_cos p.2]
  have hac : ddCellMeasure ≪ volume.restrict cellSquare := withDensity_absolutelyContinuous _ _
  apply (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable.mono_ac hac)).mpr
  rw [ddCellMeasure, integrable_withDensity_iff_integrable_smul'
    measurable_weight.ennreal_ofReal (by simp)]
  have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).bdd_mul
    measurable_weight.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ by
      simpa only [Real.norm_of_nonneg (hw p).1] using (hw p).2)
  simpa only [ddWeight, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul] using hi

private theorem coordPartial_ground_inv (j : Fin 2) (p : ℝ × ℝ) :
    coordPartial j (fun q ↦ (ddGround q : ℂ)⁻¹) p =
      -(coordPartial (E := ℝ) j ddGround p : ℂ) / (ddGround p : ℂ) ^ 2 := by
  have hg := contDiff_one_ddGround.differentiable (by simp)
  have hn : (ddGround p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (one_le_ddGround p)).ne'
  unfold coordPartial
  split_ifs
  · exact ((hasDerivAt_partialX (hg p)).ofReal_comp.inv hn).deriv
  · exact ((hasDerivAt_partialY (hg p)).ofReal_comp.inv hn).deriv

set_option linter.unusedVariables false in
/-- The data actually supplied to weighted Poincaré by the bulk Picone hypotheses.
    C¹ division gives ordinary H¹ on the cell, so no Picone energy is needed here.
    The stronger hypotheses are retained for the common bulk interface. -/
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
  -- C¹ division already gives the domain; the stronger energy hypotheses are not needed.
  clear hφ hgrad
  let χ : ℝ × ℝ → ℂ := fun p ↦ (ddGround p : ℂ)⁻¹
  let z : ℝ × ℝ → ℂ := fun p ↦ liftL2 φ p / (ddGround p : ℂ)
  have hn (p) : (ddGround p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (one_le_ddGround p)).ne'
  have hχ : ContDiff ℝ 1 χ :=
    (Complex.ofRealCLM.contDiff.comp contDiff_one_ddGround).inv hn
  have heq : (fun p ↦ χ p * liftL2 φ p) = z := by
    funext p
    simp only [χ, z, div_eq_mul_inv, mul_comm]
  have hD (j : Fin 2) (d : L2) :
      (fun p ↦ coordPartial j χ p * liftL2 φ p + χ p * liftL2 d p) =
        ddDividedPartial φ d j := by
    funext p
    rw [show coordPartial j χ p =
      -(coordPartial (E := ℝ) j ddGround p : ℂ) / (ddGround p : ℂ) ^ 2 from
        coordPartial_ground_inv j p]
    dsimp only [χ, ddDividedPartial]
    field_simp [hn p]
    ring
  have hweak {j : Fin 2} {d : L2} (hd : HasFourierPartial j φ d) :
      HasWeakPartialOn cellSquare j z (ddDividedPartial φ d j) := by
    simpa only [heq, hD] using hd.weak_mul_contDiff hχ cellSquare
  have hb : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  have hvalue := memLp_continuous_mul_cell (memLp_liftL2 φ hb) hχ.continuous
  rw [heq] at hvalue
  have hderiv (j : Fin 2) (d : L2) :
      MemLp (ddDividedPartial φ d j) 2 ddCellMeasure := by
    rw [← hD]
    exact memLp_ddCellMeasure
      ((memLp_continuous_mul_cell (memLp_liftL2 φ hb)
        (contDiff_coordPartial (n := 0) j hχ).continuous).add
          (memLp_continuous_mul_cell (memLp_liftL2 d hb) hχ.continuous))
  refine ⟨⟨hweak hdx, hweak hdy, memLp_ddCellMeasure hvalue, hderiv 0 dx, hderiv 1 dy⟩,
    ?_, ?_, ?_⟩
  · have hs := ae_torusProj (ae_comp_of_pullback_eq
      (show pullback Ic measurePreserving_Ic φ = φ from hc))
    filter_upwards [ae_restrict_of_ae hs] with p hp
    have hv : liftL2 φ (-p.1, -p.2) = liftL2 φ p := by
      simpa only [liftL2, Ic, torusProj, Real.Angle.coe_neg] using hp
    have hw : ddGround (-p.1, -p.2) = ddGround p := by
      simp [ddGround, gradSq_dipoleLift, dipoleLift, Real.sin_neg, Real.cos_neg]
    change liftL2 φ (-p.1, -p.2) / (ddGround (-p.1, -p.2) : ℂ) =
      liftL2 φ p / (ddGround p : ℂ)
    rw [hv, hw]
  · have hz (p) : (ddGround p : ℂ) * z p = liftL2 φ p := by
      dsimp only [z]
      field_simp [hn p]
    change (∫ p, (ddGround p : ℂ) * z p ∂ddCellMeasure) = 0
    simp_rw [hz]
    rw [ddCellMeasure, integral_withDensity_eq_integral_toReal_smul
      measurable_weight.ennreal_ofReal (by simp)]
    simpa only [ddWeight, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul] using hmean
  · have hz (p) : (ddGround p : ℂ) * z p = liftL2 φ p := by
      dsimp only [z]
      field_simp [hn p]
    change ddWeightedNormSq (fun p ↦ (ddGround p : ℂ) * z p) = _
    unfold ddWeightedNormSq
    simp_rw [hz]
    rw [integral_ddCellMeasure]
    rfl

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
