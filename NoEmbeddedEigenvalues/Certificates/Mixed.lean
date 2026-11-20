import NoEmbeddedEigenvalues.Certificates.Bernstein
import NoEmbeddedEigenvalues.Certificates.MixedOddA
import NoEmbeddedEigenvalues.Certificates.MixedOddBLog
import NoEmbeddedEigenvalues.MixedComparison
import Mathlib.Data.Fin.VecNotation

/-!
# Mixed comparison differential reductions and certificates

The interior identities first factor the two flux components locally in cosine
coordinates, then differentiate them. No polynomial positivity is used in these
reductions. The Robin polynomial at zero extends the regular-edge expression;
it is not computed from raw corner derivatives.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set Filter
open scoped ContDiff Topology

private def cosPair (p : ℝ × ℝ) : ℝ × ℝ := (Real.cos p.1, Real.cos p.2)

private theorem cosPair_eventually {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    ∀ᶠ q in 𝓝 p, 0 < (cosPair q).1 ∧ 0 < (cosPair q).2 := by
  have h (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  exact Filter.Eventually.and
    ((isOpen_lt continuous_const (Real.continuous_cos.comp continuous_fst)).mem_nhds
    (h _ hp.1))
    ((isOpen_lt continuous_const (Real.continuous_cos.comp continuous_snd)).mem_nhds (h _ hp.2))

private theorem cosPair_hasDerivX {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f (cosPair p)) :
    HasDerivAt (fun x ↦ f (cosPair (x, p.2)))
      (partialX f (cosPair p) * -Real.sin p.1) p.1 := by
  simpa only [Function.comp_def, cosPair] using
    (hasDerivAt_partialX hf).comp p.1 (Real.hasDerivAt_cos p.1)

private theorem cosPair_hasDerivY {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f (cosPair p)) :
    HasDerivAt (fun y ↦ f (cosPair (p.1, y)))
      (partialY f (cosPair p) * -Real.sin p.2) p.2 := by
  simpa only [Function.comp_def, cosPair] using
    (hasDerivAt_partialY hf).comp p.2 (Real.hasDerivAt_cos p.2)

private theorem mixedD_diff {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    DifferentiableAt ℝ mixedD p := by
  unfold mixedD
  fun_prop (disch := exact hp.ne')

private theorem mixedC_diff {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    DifferentiableAt ℝ mixedC p := by
  unfold mixedC
  fun_prop (disch := first | exact hp.ne' | positivity)

theorem mixed_odd_b_identity {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    mixedComparisonOperator mixedOddBComparison p -
        (1 / 100 : ℝ) * Real.cos p.1 ^ 2 * mixedOddBComparison p =
      Real.sin p.2 * mixedOddBResidual (Real.cos p.1, Real.cos p.2) := by
  have hpos := cosPair_eventually hp
  obtain ⟨hh, hk⟩ := hpos.self_of_nhds
  let F := mixedOddBMultiplier
  have hF (q : ℝ × ℝ) (hq : 0 < q.1) : DifferentiableAt ℝ F q :=
    (mixedOddBMultiplier_contDiffAt (n := 2) hq).differentiableAt (by norm_num)
  have hs (q : ℝ × ℝ) : Real.sin q.1 ^ 2 = 1 - (cosPair q).1 ^ 2 ∧
      Real.sin q.2 ^ 2 = 1 - (cosPair q).2 ^ 2 := by
    exact ⟨by simpa [cosPair] using Real.sin_sq q.1, by simpa [cosPair] using Real.sin_sq q.2⟩
  have hflux : ∀ᶠ q in 𝓝 p,
      mixedComparisonDiagonal q * partialX mixedOddBComparison q +
        mixedComparisonOffDiagonal q * partialY mixedOddBComparison q =
          Real.sin q.1 * Real.sin q.2 * mixedOddBFluxA (cosPair q) ∧
      mixedComparisonOffDiagonal q * partialX mixedOddBComparison q +
        mixedComparisonDiagonal q * partialY mixedOddBComparison q =
          mixedOddBFluxB (cosPair q) := by
    filter_upwards [hpos] with q hq
    have hx := (cosPair_hasDerivX (hF _ hq.1)).const_mul (Real.sin q.2)
    have hy := (Real.hasDerivAt_sin q.2).mul (cosPair_hasDerivY (hF _ hq.1))
    have hx' : partialX mixedOddBComparison q = _ := hx.deriv
    have hy' : partialY mixedOddBComparison q = _ := hy.deriv
    rw [hx', hy']
    simp only [mixedComparisonDiagonal, mixedComparisonOffDiagonal, mixedOddBFluxA,
      mixedOddBFluxB, ← (hs q).1, ← (hs q).2]
    dsimp only [cosPair, F]
    exact ⟨by ring, by ring⟩
  have hA : DifferentiableAt ℝ mixedOddBFluxA (cosPair p) := by
    unfold mixedOddBFluxA
    have hD := mixedD_diff (add_pos hh hk)
    have hC := mixedC_diff (add_pos hh hk)
    obtain ⟨hx, hy, _⟩ := mixed_partial_data (mixedOddBMultiplier_contDiffAt hh)
    have hF' : DifferentiableAt ℝ mixedOddBMultiplier (cosPair p) := hF _ hh
    fun_prop
  have hB : DifferentiableAt ℝ mixedOddBFluxB (cosPair p) := by
    unfold mixedOddBFluxB
    have hD := mixedD_diff (add_pos hh hk)
    have hC := mixedC_diff (add_pos hh hk)
    obtain ⟨hx, hy, _⟩ := mixed_partial_data (mixedOddBMultiplier_contDiffAt hh)
    have hF' : DifferentiableAt ℝ mixedOddBMultiplier (cosPair p) := hF _ hh
    fun_prop
  unfold mixedComparisonOperator
  rw [partialX_congr_nhds (hflux.mono fun _ h ↦ h.1),
    partialY_congr_nhds (hflux.mono fun _ h ↦ h.2)]
  have hx := ((Real.hasDerivAt_sin p.1).mul_const (Real.sin p.2)).mul (cosPair_hasDerivX hA)
  have hx' : partialX (fun q ↦ Real.sin q.1 * Real.sin q.2 * mixedOddBFluxA (cosPair q)) p = _ :=
    hx.deriv
  have hy' : partialY (fun q ↦ mixedOddBFluxB (cosPair q)) p = _ := (cosPair_hasDerivY hB).deriv
  rw [hx', hy']
  simp only [mixedOddBResidual]
  dsimp only [mixedOddBComparison, mixedComparisonPotential, cosPair]
  ring_nf
  rw [Real.sin_sq]
  ring

/-- The normalized residual includes the one-sided boundary values in the rectangle.
    At `(1,1)` the potential uses its specified continuous value. -/
theorem mixed_odd_b_residual_nonneg {h k : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1)
    (hk : k ∈ Icc (0 : ℝ) 1) : 0 ≤ mixedOddBResidual (h, k) :=
  mixed_odd_b_residual_nonneg_of_strips mixed_odd_b_strip_signs hh hk

private theorem cos_mem_unit {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    Real.cos t ∈ Ioo 0 1 := by
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩, ?_⟩
  have h := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show t ∈ Icc 0 Real.pi from ⟨ht.1.le, ht.2.le.trans (half_le_self Real.pi_pos.le)⟩) ht.1
  simpa only [Real.cos_zero] using h

private theorem sin_pos_quarter {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans (half_lt_self Real.pi_pos))

theorem mixed_odd_b_interior {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    (1 / 100 : ℝ) * Real.cos p.1 ^ 2 * mixedOddBComparison p ≤
      mixedComparisonOperator mixedOddBComparison p := by
  rw [← sub_nonneg, mixed_odd_b_identity hp]
  have hh := cos_mem_unit hp.1
  have hk := cos_mem_unit hp.2
  exact mul_nonneg (sin_pos_quarter hp.2).le
    (mixed_odd_b_residual_nonneg ⟨hh.1, hh.2.le⟩ ⟨hk.1.le, hk.2.le⟩)

theorem mixed_odd_a_identity {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    mixedComparisonOperator mixedOddAComparison p -
        (1 / 200 : ℝ) * Real.cos p.1 ^ 2 * mixedOddAComparison p =
      mixedOddAComparison p * mixedOddAResidual (Real.cos p.1, Real.cos p.2) := by
  have hpos := cosPair_eventually hp
  obtain ⟨hh, hk⟩ := hpos.self_of_nhds
  let q := cosPair p
  let F := mixedOddAExponent
  let A := fun r : ℝ × ℝ ↦ mixedD r * (r.1 - (1 - r.1 ^ 2) * partialX F r) -
    mixedC r * (1 - r.1 ^ 2) * (1 - r.2 ^ 2) * partialY F r
  let B := fun r : ℝ × ℝ ↦ mixedC r * (r.1 - (1 - r.1 ^ 2) * partialX F r) -
    mixedD r * partialY F r
  have hF (r : ℝ × ℝ) (hr : 0 < r.1 + r.2) : DifferentiableAt ℝ F r :=
    (mixedOddAExponent_contDiffAt (n := 2) hr).differentiableAt (by norm_num)
  have hflux : ∀ᶠ t in 𝓝 p,
      mixedComparisonDiagonal t * partialX mixedOddAComparison t +
        mixedComparisonOffDiagonal t * partialY mixedOddAComparison t =
          Real.exp (F (cosPair t)) * A (cosPair t) ∧
      mixedComparisonOffDiagonal t * partialX mixedOddAComparison t +
        mixedComparisonDiagonal t * partialY mixedOddAComparison t =
          Real.sin t.1 * Real.sin t.2 * Real.exp (F (cosPair t)) * B (cosPair t) := by
    filter_upwards [hpos] with t ht
    have hx := (Real.hasDerivAt_sin t.1).mul (cosPair_hasDerivX (hF _ (add_pos ht.1 ht.2))).exp
    have hy := ((cosPair_hasDerivY (hF _ (add_pos ht.1 ht.2))).exp).const_mul (Real.sin t.1)
    have hx' : partialX mixedOddAComparison t = _ := hx.deriv
    have hy' : partialY mixedOddAComparison t = _ := hy.deriv
    rw [hx', hy']
    simp only [mixedComparisonDiagonal, mixedComparisonOffDiagonal, A, B]
    dsimp only [cosPair]
    constructor
    · ring_nf
      rw [Real.sin_sq t.1, Real.sin_sq t.2]
      ring
    · ring_nf
      rw [show Real.sin t.1 ^ 3 = Real.sin t.1 * (1 - Real.cos t.1 ^ 2) by
        rw [pow_succ, Real.sin_sq, mul_comm]]
      ring
  have hD := mixedD_diff (add_pos hh hk)
  have hC := mixedC_diff (add_pos hh hk)
  have hdf : DifferentiableAt ℝ F q := hF _ (add_pos hh hk)
  obtain ⟨hFx, hFy, hxy⟩ :=
    mixed_partial_data (f := F) (mixedOddAExponent_contDiffAt (add_pos hh hk))
  have hA : DifferentiableAt ℝ A q := by unfold A; fun_prop
  have hB : DifferentiableAt ℝ B q := by unfold B; fun_prop
  have hx := (cosPair_hasDerivX hdf).exp.mul (cosPair_hasDerivX hA)
  have hy := (((Real.hasDerivAt_sin p.2).const_mul (Real.sin p.1)).mul
    (cosPair_hasDerivY hdf).exp).mul (cosPair_hasDerivY hB)
  have hx' : partialX (fun t ↦ Real.exp (F (cosPair t)) * A (cosPair t)) p = _ := hx.deriv
  have hy' : partialY (fun t ↦ Real.sin t.1 * Real.sin t.2 *
      Real.exp (F (cosPair t)) * B (cosPair t)) p = _ := hy.deriv
  unfold mixedComparisonOperator
  rw [partialX_congr_nhds (hflux.mono fun _ h ↦ h.1),
    partialY_congr_nhds (hflux.mono fun _ h ↦ h.2), hx', hy']
  have hAx : partialX A q =
      partialX mixedD q * (q.1 - (1 - q.1 ^ 2) * partialX F q) +
      mixedD q * (1 + 2 * q.1 * partialX F q - (1 - q.1 ^ 2) * partialX (partialX F) q) -
      (partialX mixedC q * (1 - q.1 ^ 2) * (1 - q.2 ^ 2) * partialY F q -
        mixedC q * (2 * q.1) * (1 - q.2 ^ 2) * partialY F q +
        mixedC q * (1 - q.1 ^ 2) * (1 - q.2 ^ 2) * partialX (partialY F) q) := by
    let t := hasDerivAt_id q.1
    have u := (hasDerivAt_const q.1 (1 : ℝ)).sub (t.pow 2)
    have v := hasDerivAt_const q.1 (1 - q.2 ^ 2)
    have e := ((hasDerivAt_partialX hD).mul
      (t.sub (u.mul (hasDerivAt_partialX hFx)))).sub
        ((((hasDerivAt_partialX hC).mul u).mul v).mul (hasDerivAt_partialX hFy))
    have he : partialX A q = _ := e.deriv
    rw [he]
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  have hBy : partialY B q =
      partialY mixedC q * (q.1 - (1 - q.1 ^ 2) * partialX F q) -
      mixedC q * (1 - q.1 ^ 2) * partialY (partialX F) q -
      (partialY mixedD q * partialY F q + mixedD q * partialY (partialY F) q) := by
    have e := ((hasDerivAt_partialY hC).mul
      ((hasDerivAt_const q.2 q.1).sub ((hasDerivAt_partialY hFx).const_mul (1 - q.1 ^ 2)))).sub
        ((hasDerivAt_partialY hD).mul (hasDerivAt_partialY hFy))
    have he : partialY B q = _ := e.deriv
    rw [he]
    simp only [Pi.sub_apply]
    ring
  rw [hAx, hBy, hxy]
  change _ = mixedOddAComparison p * mixedOddAResidual q
  simp only [mixedOddAResidual, mixedOddACoeffZero, mixedOddACoeffH, mixedOddACoeffK,
    mixedOddAComparison, mixedComparisonPotential, A, B]
  simp only [Pi.mul_apply, q, cosPair, F]
  ring_nf
  rw [Real.sin_sq p.2]
  ring

theorem mixed_odd_a_interior {p : ℝ × ℝ} (hp : p ∈ mixedQuarterCell) :
    (1 / 200 : ℝ) * Real.cos p.1 ^ 2 * mixedOddAComparison p ≤
      mixedComparisonOperator mixedOddAComparison p := by
  rw [← sub_nonneg, mixed_odd_a_identity hp]
  have hw : 0 ≤ mixedOddAComparison p :=
    mul_nonneg (sin_pos_quarter hp.1).le (Real.exp_pos _).le
  exact mul_nonneg hw (mixed_odd_a_residual_nonneg (cos_mem_unit hp.1) (cos_mem_unit hp.2))

/-- The exact Robin margin polynomial, including its continuous endpoint value. -/
def mixedRobinPolynomial (h : ℝ) : ℝ :=
  (673 * h ^ 7 - 1953 * h ^ 6 - 3213 * h ^ 5 + 7317 * h ^ 4 +
    109 * h ^ 3 - 4647 * h ^ 2 + 1718 * h + 1) / 1000 - h / 250

/-- The differential identity excludes the corner, where raw partial derivatives
    of the rational exponent do not equal their limits along `k=0`. -/
theorem mixed_robin_identity {h : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) :
    3 * h - 2 * (1 - h ^ 2) * partialX mixedOddAExponent (h, 0) -
        (2 - h ^ 2) * partialY mixedOddAExponent (h, 0) - h / 250 =
      mixedRobinPolynomial h := by
  have hn : h ≠ 0 := hh.1.ne'
  have hx : partialX mixedOddAExponent (h, 0) =
      (-98 * 2 * h + 781 * 3 * h ^ 2 - 240 * 4 * h ^ 3 - 263 * 5 * h ^ 4 +
        53 * 6 * h ^ 5 - 1 / 2 - 4 - 2744 * 2 * h + 1033 * 2 * h +
        224 * 3 * h ^ 2 + 235 * 3 * h ^ 2) / 1000 := by
    unfold partialX
    have he : (fun x : ℝ ↦ mixedOddAExponent (x, (0 : ℝ))) =ᶠ[𝓝 h]
        fun x ↦ (-98 * x ^ 2 + 781 * x ^ 3 - 240 * x ^ 4 - 263 * x ^ 5 +
          53 * x ^ 6 - x / 2 - 4 * x - 2744 * x ^ 2 + 1033 * x ^ 2 +
          224 * x ^ 3 + 235 * x ^ 3) / 1000 := by
      filter_upwards [isOpen_ne.mem_nhds (show h ∈ {x : ℝ | x ≠ 0} from hn)] with x hx
      change x ≠ 0 at hx
      simp only [mixedOddAExponent, mixedOddAPolynomial]
      field_simp [hx]
      ring
    change deriv (fun x : ℝ ↦ mixedOddAExponent (x, 0)) h = _
    rw [he.deriv_eq]
    simp (disch := fun_prop) only [deriv_div_const, deriv_fun_add, deriv_fun_sub,
      deriv_const_mul_field, deriv_pow_field, deriv_id'', deriv_const_mul_id]
    ring
  have hy : partialY mixedOddAExponent (h, 0) =
      (-519 * h - 583 * h ^ 3 + 677 * h ^ 4 + 37 * h ^ 5 - 4 +
        8 + 10976 * h - 6198 * h - 224 * h ^ 2 - 1175 * h ^ 2) / 1000 := by
    change deriv (fun y : ℝ ↦ mixedOddAExponent (h, y)) 0 = _
    have hquot (c : ℝ) (n : ℕ) :
        deriv (fun y : ℝ ↦ c / (h + y) ^ n) 0 =
          (-(c * (n * h ^ (n - 1)))) / (h ^ n) ^ 2 := by
      have hd := ((hasDerivAt_const (0 : ℝ) h).add (hasDerivAt_id 0)).pow n
      have he := ((hasDerivAt_const (0 : ℝ) c).div hd
        (by simpa only [Pi.pow_apply, Pi.add_apply, id_eq, add_zero] using pow_ne_zero n hn)).deriv
      change deriv ((fun _ : ℝ ↦ c) / ((fun _ : ℝ ↦ h) + id) ^ n) 0 = _
      simpa only [Pi.pow_apply, Pi.add_apply, zero_mul, zero_sub, zero_add, id_eq,
        add_zero, mul_one] using he
    have hquot₁ (c : ℝ) : deriv (fun y : ℝ ↦ c / (h + y)) 0 = -c / h ^ 2 := by
      simpa using hquot c 1
    simp (disch := first | fun_prop (disch := first | simpa using hn | positivity)) only
      [mixedOddAExponent, mixedOddAPolynomial, deriv_div_const, deriv_fun_add, deriv_fun_sub,
        deriv_const_mul_field, deriv_pow_field, deriv_const, deriv_const_mul_id, hquot, hquot₁]
    field_simp [hn]
    ring
  rw [hx, hy]
  unfold mixedRobinPolynomial
  ring

-- Use degree zero in the second variable to reuse the box criterion.
private def mixedRobinPower (i : Fin 8) (_ : Fin 1) : ℚ :=
  (![1, 1714, -4647, 109, 7317, -3213, -1953, 673] : Fin 8 → ℚ) i

private theorem mixedRobinPower_identity (h : ℝ) :
    certificatePolynomial mixedRobinPower h 0 = 1000 * mixedRobinPolynomial h := by
  simp [certificatePolynomial, mixedRobinPower, mixedRobinPolynomial, Fin.sum_univ_succ]
  ring

private theorem mixedRobinPower_box {a b : ℚ} (hab : a < b)
    (hc : ∀ i j, 0 ≤ certificateBoxCoeff mixedRobinPower a b 0 1 i j)
    {h : ℝ} (hh : h ∈ Icc (a : ℝ) (b : ℝ)) : 0 ≤ mixedRobinPolynomial h := by
  have hp := certificate_bernstein_nonneg mixedRobinPower hab (by norm_num) hc hh
    (y := 0) (by norm_num)
  rw [mixedRobinPower_identity] at hp
  linarith

theorem mixed_robin_nonneg {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedRobinPolynomial h := by
  rcases le_or_gt h (1 / 2) with h₁ | h₁
  · exact mixedRobinPower_box (a := 0) (b := 1 / 2) (by norm_num)
      (by decide +kernel) (by norm_num; exact ⟨hh.1, h₁⟩)
  rcases le_or_gt h (5 / 8) with h₂ | h₂
  · exact mixedRobinPower_box (a := 1 / 2) (b := 5 / 8) (by norm_num)
      (by decide +kernel) (by norm_num; exact ⟨h₁.le, h₂⟩)
  rcases le_or_gt h (11 / 16) with h₃ | h₃
  · exact mixedRobinPower_box (a := 5 / 8) (b := 11 / 16) (by norm_num)
      (by decide +kernel) (by norm_num; exact ⟨h₂.le, h₃⟩)
  rcases le_or_gt h (3 / 4) with h₄ | h₄
  · exact mixedRobinPower_box (a := 11 / 16) (b := 3 / 4) (by norm_num)
      (by decide +kernel) (by norm_num; exact ⟨h₃.le, h₄⟩)
  · exact mixedRobinPower_box (a := 3 / 4) (b := 1) (by norm_num)
      (by decide +kernel) (by norm_num; exact ⟨h₄.le, hh.2⟩)

/-- The exponent version of the odd-in-a Robin bound. Only the regular
edge is used; the closed-interval sign is a separate certificate. -/
theorem mixed_odd_a_robin :
    ∀ h ∈ Ioc (0 : ℝ) 1,
      h / 250 ≤ 3 * h - 2 * (1 - h ^ 2) * partialX mixedOddAExponent (h, 0) -
        (2 - h ^ 2) * partialY mixedOddAExponent (h, 0) := by
  intro h hh
  rw [← sub_nonneg, mixed_robin_identity hh]
  exact mixed_robin_nonneg ⟨hh.1.le, hh.2⟩

end NoEmbeddedEigenvalues
