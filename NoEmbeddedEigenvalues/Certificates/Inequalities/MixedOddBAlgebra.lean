module

public import NoEmbeddedEigenvalues.Certificates.Tools.Bernstein
public import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedComparison
public import Mathlib.Data.Fin.VecNotation

/-!
# Polynomial reduction of the odd-in-b residual

The logarithm is treated as an independent parameter in the cleared
numerator. Derivatives before clearing use the logarithm's actual jet.
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- Auxiliary A_F in the odd-in-b differential reduction, in `(h,k)` variables. -/
def mixedOddBFluxA (p : ℝ × ℝ) : ℝ :=
  -mixedD p * partialX mixedOddBMultiplier p + mixedC p *
    (p.2 * mixedOddBMultiplier p - (1 - p.2 ^ 2) * partialY mixedOddBMultiplier p)

/-- Auxiliary B_F in the same reduction. -/
def mixedOddBFluxB (p : ℝ × ℝ) : ℝ :=
  -mixedC p * (1 - p.1 ^ 2) * (1 - p.2 ^ 2) * partialX mixedOddBMultiplier p +
    mixedD p * (p.2 * mixedOddBMultiplier p -
      (1 - p.2 ^ 2) * partialY mixedOddBMultiplier p)

/-- Normalized odd-in-b residual after subtracting `h² F_v/100`. -/
def mixedOddBResidual (p : ℝ × ℝ) : ℝ :=
  -p.1 * mixedOddBFluxA p + (1 - p.1 ^ 2) * partialX mixedOddBFluxA p +
    partialY mixedOddBFluxB p + mixedV p * mixedOddBMultiplier p -
    p.1 ^ 2 * mixedOddBMultiplier p / 100

private theorem deriv_comp_pow {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a) (n : ℕ) :
    deriv (fun x ↦ f x ^ n) a = n * f a ^ (n - 1) * deriv f a :=
  (hf.hasDerivAt.pow n).deriv

private def dNum (h s : ℝ) : ℝ := h ^ 2 * s + 2 * h * (1 - h ^ 2)
private def cNum (h : ℝ) : ℝ := 2 * h ^ 2
private def dxNum (h s : ℝ) : ℝ :=
  s * (2 * h * s + h ^ 2 + 2 - 6 * h ^ 2) - dNum h s
private def dyNum (h s : ℝ) : ℝ := s * h ^ 2 - dNum h s
private def cxNum (h s : ℝ) : ℝ := s * (4 * h) - 2 * cNum h
private def cyNum (h : ℝ) : ℝ := -2 * cNum h

private theorem matrix_partials (h k : ℝ) (hs : h + k ≠ 0) :
    partialX mixedD (h, k) = dxNum h (h + k) / (h + k) ^ 2 ∧
    partialY mixedD (h, k) = dyNum h (h + k) / (h + k) ^ 2 ∧
    partialX mixedC (h, k) = cxNum h (h + k) / (h + k) ^ 3 ∧
    partialY mixedC (h, k) = cyNum h / (h + k) ^ 3 := by
  have hx : deriv (fun x : ℝ ↦ x + k) h = 1 := ((hasDerivAt_id h).add_const k).deriv
  have hy : deriv (fun y : ℝ ↦ h + y) k = 1 := ((hasDerivAt_id k).const_add h).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [partialX, partialY, mixedD, mixedC, dxNum, dyNum, cxNum, cyNum, dNum, cNum]
    simp (disch := first | positivity | assumption | fun_prop)
      only [deriv_fun_div, deriv_fun_add, deriv_fun_mul, deriv_fun_sub, deriv_const,
        deriv_const_mul_id, deriv_pow_field, deriv_comp_pow, hx, hy]
    field_simp [hs]
    ring

private def bP (h k : ℝ) : ℝ :=
  10000 + 4132 * k ^ 2 + 2167 * k ^ 3 - 2011 * h * k - 7640 * h * k ^ 2 -
    226 * h ^ 2 + 3795 * h ^ 2 * k - 834 * h ^ 3
private def bT (k : ℝ) : ℝ := 808 * k + 2505 * k ^ 2
private def bT' (k : ℝ) : ℝ := 808 + 5010 * k
private def bF (h k l : ℝ) : ℝ := bP h k + h * bT k * l
private def bFx (h k l : ℝ) : ℝ :=
  -2011 * k - 7640 * k ^ 2 - 452 * h + 7590 * h * k - 2502 * h ^ 2 + bT k * (1 + l)
private def bFy (h k l : ℝ) : ℝ :=
  8264 * k + 6501 * k ^ 2 - 2011 * h - 15280 * h * k + 3795 * h ^ 2 + h * bT' k * l
private def bFxx (h k : ℝ) : ℝ := -452 + 7590 * k - 5004 * h + bT k / h
private def bFxy (h k l : ℝ) : ℝ := -2011 - 15280 * k + 7590 * h + bT' k * (1 + l)
private def bFyy (h k l : ℝ) : ℝ := 8264 + 13002 * k - 15280 * h + 5010 * h * l

private theorem multiplier_value (h k : ℝ) :
    mixedOddBMultiplier (h, k) = bF h k (Real.log h) / 10000 := by
  unfold mixedOddBMultiplier mixedOddBPolynomial bF bP bT
  dsimp only
  ring

private theorem multiplier_x (h k : ℝ) (hh : 0 < h) :
    partialX mixedOddBMultiplier (h, k) = bFx h k (Real.log h) / 10000 := by
  change deriv (fun x ↦ mixedOddBMultiplier (x, k)) h = _
  simp_rw [multiplier_value]
  unfold bF bFx bP bT
  simp (disch := fun_prop (disch := exact hh.ne'))
    only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const,
      deriv_pow_field, deriv_id'', deriv_const_mul_id, Real.deriv_log]
  field_simp [hh.ne']
  ring

private theorem multiplier_y (h k : ℝ) :
    partialY mixedOddBMultiplier (h, k) = bFy h k (Real.log h) / 10000 := by
  change deriv (fun y ↦ mixedOddBMultiplier (h, y)) k = _
  simp_rw [multiplier_value]
  unfold bF bFy bP bT bT'
  simp (disch := fun_prop) only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub,
    deriv_const, deriv_pow_field, deriv_const_mul_id]
  ring

private theorem multiplier_xx (h k : ℝ) (hh : 0 < h) :
    partialX (partialX mixedOddBMultiplier) (h, k) = bFxx h k / 10000 := by
  change deriv (fun x ↦ partialX mixedOddBMultiplier (x, k)) h = _
  have he : (fun x ↦ partialX mixedOddBMultiplier (x, k)) =ᶠ[𝓝 h]
      fun x ↦ bFx x k (Real.log x) / 10000 := by
    filter_upwards [lt_mem_nhds hh] with x hx
    exact multiplier_x x k hx
  rw [he.deriv_eq]
  unfold bFx bFxx bT
  simp (disch := fun_prop (disch := exact hh.ne'))
    only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const,
      deriv_pow_field, deriv_const_mul_id, Real.deriv_log]
  ring

private theorem multiplier_xy (h k : ℝ) (hh : 0 < h) :
    partialX (partialY mixedOddBMultiplier) (h, k) =
        bFxy h k (Real.log h) / 10000 ∧
    partialY (partialX mixedOddBMultiplier) (h, k) =
        bFxy h k (Real.log h) / 10000 := by
  constructor
  · change deriv (fun x ↦ partialY mixedOddBMultiplier (x, k)) h = _
    simp_rw [multiplier_y]
    unfold bFy bFxy bT'
    simp (disch := fun_prop (disch := exact hh.ne'))
      only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const,
        deriv_pow_field, deriv_id'', deriv_const_mul_id, Real.deriv_log]
    field_simp [hh.ne']
    ring
  · change deriv (fun y ↦ partialX mixedOddBMultiplier (h, y)) k = _
    simp_rw [multiplier_x h _ hh]
    unfold bFx bFxy bT bT'
    simp (disch := fun_prop) only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub,
      deriv_const, deriv_pow_field, deriv_const_mul_id]
    ring

private theorem multiplier_yy (h k : ℝ) :
    partialY (partialY mixedOddBMultiplier) (h, k) = bFyy h k (Real.log h) / 10000 := by
  change deriv (fun y ↦ partialY mixedOddBMultiplier (h, y)) k = _
  simp_rw [multiplier_y]
  unfold bFy bFyy bT'
  simp (disch := fun_prop) only [deriv_div_const, deriv_fun_mul, deriv_fun_add, deriv_fun_sub,
    deriv_const, deriv_pow_field, deriv_const_mul_id]
  ring

/-- The first-coordinate partial depends only on the local germ. -/
theorem partialX_congr_nhds {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : f =ᶠ[𝓝 p] g) : partialX f p = partialX g p :=
  EventuallyEq.deriv_eq
    (((continuous_id.prodMk continuous_const).tendsto' p.1 p Prod.mk.eta).eventually h)

/-- The second-coordinate partial depends only on the local germ. -/
theorem partialY_congr_nhds {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : f =ᶠ[𝓝 p] g) : partialY f p = partialY g p :=
  EventuallyEq.deriv_eq
    (((continuous_const.prodMk continuous_id).tendsto' p.2 p Prod.mk.eta).eventually h)

private theorem partialX_eq_fderiv_nhds {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p) :
    partialX f =ᶠ[𝓝 p] fun q ↦ fderiv ℝ f q (1, 0) := by
  obtain ⟨U, hU, h⟩ := hf.contDiffOn (m := 2) le_rfl (by norm_num)
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)] with q hq
  exact partialX_eq_fderiv ((h.contDiffAt (mem_interior_iff_mem_nhds.mp hq)).differentiableAt
    (by norm_num))

private theorem partialY_eq_fderiv_nhds {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p) :
    partialY f =ᶠ[𝓝 p] fun q ↦ fderiv ℝ f q (0, 1) := by
  obtain ⟨U, hU, h⟩ := hf.contDiffOn (m := 2) le_rfl (by norm_num)
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)] with q hq
  exact partialY_eq_fderiv ((h.contDiffAt (mem_interior_iff_mem_nhds.mp hq)).differentiableAt
    (by norm_num))

/-- First partials of a locally C² function are differentiable, with equal cross partials. -/
theorem mixed_partial_data {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (partialX f) p ∧ DifferentiableAt ℝ (partialY f) p ∧
      partialX (partialY f) p = partialY (partialX f) p := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hX := hd.clm_apply (differentiableAt_const (c := ((1, 0) : ℝ × ℝ)))
  have hY := hd.clm_apply (differentiableAt_const (c := ((0, 1) : ℝ × ℝ)))
  have hx := partialX_eq_fderiv_nhds hf
  have hy := partialY_eq_fderiv_nhds hf
  refine ⟨hX.congr_of_eventuallyEq hx, hY.congr_of_eventuallyEq hy, ?_⟩
  rw [partialX_congr_nhds hy, partialY_congr_nhds hx, partialX_eq_fderiv hY,
    partialY_eq_fderiv hX, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.isSymmSndFDerivAt (by norm_num) (1, 0) (0, 1)

-- Take products before clearing denominators; this identity also applies
-- at the center, where the potential is totalized.
private theorem residual_expanded (h k : ℝ) (hh : 0 < h) (hs : h + k ≠ 0) :
    let p := (h, k)
    let u := 1 - h ^ 2
    let v := 1 - k ^ 2
    let f := mixedOddBMultiplier p
    let fx := partialX mixedOddBMultiplier p
    let fy := partialY mixedOddBMultiplier p
    let G := k * f - v * fy
    mixedOddBResidual p =
      -h * (-mixedD p * fx + mixedC p * G) +
      u * (-(partialX mixedD p * fx + mixedD p * partialX (partialX mixedOddBMultiplier) p) +
        partialX mixedC p * G +
        mixedC p * (k * fx - v * partialX (partialY mixedOddBMultiplier) p)) -
      (partialY mixedC p * u * v - 2 * k * mixedC p * u) * fx -
      mixedC p * u * v * partialY (partialX mixedOddBMultiplier) p +
      partialY mixedD p * G + mixedD p *
        (f + 3 * k * fy - v * partialY (partialY mixedOddBMultiplier) p) +
      mixedV p * f - h ^ 2 * f / 100 := by
  dsimp only
  have hD : DifferentiableAt ℝ mixedD (h, k) := by
    unfold mixedD
    fun_prop (disch := exact hs)
  have hC : DifferentiableAt ℝ mixedC (h, k) := by
    unfold mixedC
    fun_prop (disch := first | exact hs | positivity)
  have hF : ContDiffAt ℝ 2 mixedOddBMultiplier (h, k) :=
    mixedOddBMultiplier_contDiffAt hh
  have hdF := hF.differentiableAt (by norm_num)
  obtain ⟨hxF, hyF, _⟩ := mixed_partial_data hF
  have hAx : partialX mixedOddBFluxA (h, k) =
      -(partialX mixedD (h, k) * partialX mixedOddBMultiplier (h, k) +
        mixedD (h, k) * partialX (partialX mixedOddBMultiplier) (h, k)) +
      partialX mixedC (h, k) *
        (k * mixedOddBMultiplier (h, k) - (1 - k ^ 2) * partialY mixedOddBMultiplier (h, k)) +
      mixedC (h, k) *
        (k * partialX mixedOddBMultiplier (h, k) -
          (1 - k ^ 2) * partialX (partialY mixedOddBMultiplier) (h, k)) := by
    unfold partialX mixedOddBFluxA
    dsimp only
    have hn : deriv (fun x ↦ -mixedD (x, k)) h = -deriv (fun x ↦ mixedD (x, k)) h :=
      deriv.neg
    simp (disch := fun_prop) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const, hn]
    simp only [partialX]
    ring
  have hBy : partialY mixedOddBFluxB (h, k) =
      -(partialY mixedC (h, k) * (1 - h ^ 2) * (1 - k ^ 2) -
        2 * k * mixedC (h, k) * (1 - h ^ 2)) * partialX mixedOddBMultiplier (h, k) -
      mixedC (h, k) * (1 - h ^ 2) * (1 - k ^ 2) *
        partialY (partialX mixedOddBMultiplier) (h, k) +
      partialY mixedD (h, k) *
        (k * mixedOddBMultiplier (h, k) - (1 - k ^ 2) * partialY mixedOddBMultiplier (h, k)) +
      mixedD (h, k) * (mixedOddBMultiplier (h, k) + 3 * k * partialY mixedOddBMultiplier (h, k) -
        (1 - k ^ 2) * partialY (partialY mixedOddBMultiplier) (h, k)) := by
    unfold partialY mixedOddBFluxB
    dsimp only
    have hn : deriv (fun y ↦ -mixedC (h, y)) k = -deriv (fun y ↦ mixedC (h, y)) k :=
      deriv.neg
    simp (disch := fun_prop) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul, hn,
      deriv_const, deriv_pow_field, deriv_id'']
    simp only [partialY]
    ring
  unfold mixedOddBResidual
  rw [hAx, hBy, mixedOddBFluxA]
  dsimp only
  ring

/-- The residual at the one point where the potential denominator vanishes. -/
theorem mixed_odd_b_residual_center : mixedOddBResidual (1, 1) = 670267 / 1000000 := by
  rw [residual_expanded 1 1 (by norm_num) (by norm_num)]
  obtain ⟨hdx, hdy, hcx, hcy⟩ :=
    matrix_partials (1 : ℝ) (1 : ℝ) (by norm_num)
  rw [hdx, hdy, hcx, hcy, multiplier_value, multiplier_x 1 1 (by norm_num), multiplier_y]
  norm_num [mixedD, mixedC, mixedV, dNum, cNum, dxNum, dyNum, cxNum, cyNum,
    bF, bFx, bFy, bP, bT, bT']

/-- Integer-scaled cleared residual with an independent logarithm parameter `l`.
The factor `h` in the diagonal numerator cancels the sole `1 / h` jet term. -/
@[no_expose] def mixedOddBCleared (h k l : ℝ) : ℝ :=
  let s := h + k
  let r := 2 - h ^ 2 - k ^ 2
  let u := 1 - h ^ 2
  let v := 1 - k ^ 2
  let f := bF h k l
  let fx := bFx h k l
  let fy := bFy h k l
  let g := k * f - v * fy
  let d := dNum h s
  let c := cNum h
  let fxxNum := h * (-452 + 7590 * k - 5004 * h) + bT k
  let dFactor := h * s + 2 * u
  let potentialNum := -h ^ 2 * r ^ 2 + 2 * h * u * s * r - 2 * u ^ 2 * s ^ 2
  100 * (r * (-h * (-d * s ^ 2 * fx + c * s * g) +
    u * (-dxNum h s * s * fx - dFactor * s ^ 2 * fxxNum +
      cxNum h s * g + c * s * (k * fx - v * bFxy h k l)) -
    (cyNum h * u * v - 2 * k * c * s * u) * fx -
    c * s * u * v * bFxy h k l + dyNum h s * s * g +
    d * s ^ 2 * (f + 3 * k * fy - v * bFyy h k l)) +
    s * potentialNum * f) - h ^ 2 * s ^ 3 * r * f

theorem mixed_odd_b_clear (h k : ℝ) (hh : 0 < h) (hs : h + k ≠ 0)
    (hr : 2 - h ^ 2 - k ^ 2 ≠ 0) :
    mixedOddBCleared h k (Real.log h) =
      1000000 * (h + k) ^ 3 * (2 - h ^ 2 - k ^ 2) * mixedOddBResidual (h, k) := by
  have hd : mixedD (h, k) = dNum h (h + k) / (h + k) := by
    simp only [mixedD, dNum]
    field_simp [hs]
  have hc : mixedC (h, k) = cNum h / (h + k) ^ 2 := rfl
  obtain ⟨hdx, hdy, hcx, hcy⟩ := matrix_partials h k hs
  obtain ⟨hxy, hyx⟩ := multiplier_xy h k hh
  rw [residual_expanded h k hh hs, hd, hc, hdx, hdy, hcx, hcy, hxy, hyx,
    multiplier_value, multiplier_x h k hh, multiplier_y, multiplier_xx h k hh, multiplier_yy]
  simp only [mixedOddBCleared, bFxx, mixedV]
  generalize h + k = s at hs ⊢
  generalize 2 - h ^ 2 - k ^ 2 = r at hr ⊢
  unfold dNum
  field_simp [hs, hr, hh.ne']
  ring

/-- Polynomial terms independent of, and multiplying, the logarithm. -/
def mixedOddBA (h k : ℝ) : ℝ := mixedOddBCleared h k 0

def mixedOddBB (h k : ℝ) : ℝ := mixedOddBCleared h k 1 - mixedOddBA h k

theorem mixed_odd_b_cleared_affine (h k l : ℝ) :
    mixedOddBCleared h k l = mixedOddBA h k + mixedOddBB h k * l := by
  simp only [mixedOddBA, mixedOddBB, mixedOddBCleared, bF, bFx, bFy, bFxy, bFyy,
    mul_zero, add_zero]
  generalize h + k = s
  generalize 2 - h ^ 2 - k ^ 2 = r
  generalize 1 - h ^ 2 = u
  generalize 1 - k ^ 2 = v
  ring

/-- Integer power coefficients of the odd-in-b polynomial A. -/
def mixedOddBAInt : Fin 11 → Fin 9 → ℤ := ![
  ![0, 0, 0, -1842000,
    1052000, -905400, -959400, 0,
    0],
  ![0, 0, -414800, -13823200,
    16936400, 26895200, -10903000, -9877900,
    0],
  ![0, -282000, 1423200, 21002600,
    -34335000, -675464, 26041366, -4127868,
    -3681733],
  ![-1328400, 9577200, 10622200, -18024800,
    -13263970, -17530522, 2948785, 9145561,
    0],
  ![1558000, -4111600, 1048200, -10239474,
    28881448, -1451531, -12871957, 0,
    0],
  ![18200, -7662400, -7618642, 25618904,
    1779406, 724359, 0, 0,
    0],
  ![-932200, 3661778, -12313186, 354248,
    -443681, 0, 0, 0,
    0],
  ![207652, -872386, 1197195, -5260009,
    0, 0, 0, 0,
    0],
  ![2663668, -1383289, 4121109, 0,
    0, 0, 0, 0,
    0],
  ![-181026, 1089993, 0, 0,
    0, 0, 0, 0,
    0],
  ![-1251834, 0, 0, 0,
    0, 0, 0, 0,
    0]]

def mixedOddBAPower (i : Fin 11) (j : Fin 9) : ℚ :=
  mixedOddBAInt i j

theorem mixed_odd_b_a_table (h k : ℝ) :
    mixedOddBA h k = certificatePolynomial mixedOddBAPower h k := by
  simp [certificatePolynomial, Fin.sum_univ_succ, mixedOddBAPower, mixedOddBAInt,
    mixedOddBA, mixedOddBCleared, bF, bFx, bFy, bFxy, bFyy, bP, bT, bT',
    dNum, cNum, dxNum, dyNum, cxNum, cyNum]
  ring

/-- Integer power coefficients of the odd-in-b polynomial B. -/
def mixedOddBBInt : Fin 9 → Fin 8 → ℤ := ![
  ![0, 0, 0, -323200,
    -1002000, 161600, 501000, 0],
  ![0, 0, -323200, -1002000,
    -323200, -1002000, 161600, 501000],
  ![0, -323200, -6012000, 3716800,
    22044000, -1939200, -10020000, 0],
  ![-323200, -6012000, 5332800, 29058000,
    -971216, -5516010, -645592, -3253995],
  ![-2004000, 2585600, 19539000, -3883248,
    -21558030, 810424, 3264015, 0],
  ![808000, 8016000, -5660848, -28572030,
    972832, 4018020, 0, 0],
  ![2004000, -2264016, -14033010, 972832,
    5020020, 0, 0, 0],
  ![-323200, -2505000, 1295224, 6270015,
    0, 0, 0, 0],
  ![-501000, 485608, 2758005, 0,
    0, 0, 0, 0]]

def mixedOddBBPower (i : Fin 9) (j : Fin 8) : ℚ :=
  mixedOddBBInt i j

theorem mixed_odd_b_b_table (h k : ℝ) :
    mixedOddBB h k = certificatePolynomial mixedOddBBPower h k := by
  simp [certificatePolynomial, Fin.sum_univ_succ, mixedOddBBPower, mixedOddBBInt,
    mixedOddBB, mixedOddBA, mixedOddBCleared, bF, bFx, bFy, bFxy, bFyy, bP, bT, bT',
    dNum, cNum, dxNum, dyNum, cxNum, cyNum]
  ring

end

end NoEmbeddedEigenvalues
