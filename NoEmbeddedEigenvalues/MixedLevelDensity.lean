import NoEmbeddedEigenvalues.Regularity.MixedDividedEquation
import NoEmbeddedEigenvalues.OrbitCoordinates

/-! # Signed geometric densities in diagonal coordinates -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Real
open scoped ComplexConjugate

local notation "Plane" => (ℝ × ℝ)

/-- Components of the unnormalized outward conormal, in diagonal coordinates. -/
def mixedLevelS (q : Plane) : ℝ := cos q.2 * sin q.1
def mixedLevelR (q : Plane) : ℝ := cos q.1 * sin q.2

/-- Sign-reversed normal-minus-tangent coefficient in the first coordinate. -/
def mixedLevelSign (q : Plane) : ℝ :=
  (mixedLevelR q ^ 2 - mixedLevelS q ^ 2) / (mixedLevelR q ^ 2 + mixedLevelS q ^ 2)

/-- Cross coefficient of the signed level energy. -/
def mixedLevelCross (q : Plane) : ℝ :=
  4 * mixedLevelS q * mixedLevelR q / (mixedLevelR q ^ 2 + mixedLevelS q ^ 2)

/-- The cross coefficient stays bounded even as both conormal
components approach zero. -/
theorem mixed_level_cross_norm_le (q : Plane) : ‖mixedLevelCross q‖ ≤ 2 := by
  unfold mixedLevelCross
  let R := mixedLevelR q
  let S := mixedLevelS q
  change ‖4 * S * R / (R ^ 2 + S ^ 2)‖ ≤ 2
  by_cases hz : R ^ 2 + S ^ 2 = 0
  · simp [hz]
  have hp : 0 < R ^ 2 + S ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith only [sq_nonneg (R + S), sq_nonneg (R - S)]

private theorem mixed_level_sin_add (q : Plane) :
    sin (diagInv q).1 + sin (diagInv q).2 = 2 * mixedLevelS q := by
  simp only [diagInv_apply, sin_add, sin_sub, mixedLevelS]
  ring

private theorem mixed_level_sin_sub (q : Plane) :
    sin (diagInv q).1 - sin (diagInv q).2 = 2 * mixedLevelR q := by
  simp only [diagInv_apply, sin_add, sin_sub, mixedLevelR]
  ring

theorem mixed_level_gradNorm_sq (q : Plane) :
    gradNorm (diagInv q) ^ 2 = 2 * (mixedLevelR q ^ 2 + mixedLevelS q ^ 2) := by
  rw [gradNorm, sq_sqrt (by positivity)]
  nlinarith only [mixed_level_sin_add q, mixed_level_sin_sub q,
    congrArg (· ^ 2) (mixed_level_sin_add q), congrArg (· ^ 2) (mixed_level_sin_sub q)]

/-- At a critical point the first-order level density is zero on both sides
of this identity; no division by the gradient is needed there. -/
theorem MixedQuotientData.level_first_order_ae {ω : L2} (d : MixedQuotientData ω) :
    ∀ᵐ q ∂volume.restrict mixedOpenCell,
      gradNorm (diagInv q) * (streamLift ω (diagInv q) * conj (streamNormal ω (diagInv q))).re =
        (((cos q.1 : ℂ) * d.phi q) * conj
          ((mixedLevelS q : ℂ) * d.streamA q + (mixedLevelR q : ℂ) * d.streamB q)).re := by
  filter_upwards [d.stream_eq, d.stream_partials_ae] with q hs hq
  let p := diagInv q
  let X := streamLiftX ω p
  let Y := streamLiftY ω p
  have hn : sin p.1 * X + sin p.2 * Y =
      (mixedLevelS q : ℂ) * d.streamA q + (mixedLevelR q : ℂ) * d.streamB q := by
    rw [hq.1, hq.2]
    have ha := congrArg Complex.ofReal (mixed_level_sin_add q)
    have hb := congrArg Complex.ofReal (mixed_level_sin_sub q)
    push_cast at ha hb
    simp only [← Complex.ofReal_sin] at ha hb
    change (sin p.1 : ℂ) + sin p.2 = _ at ha
    change (sin p.1 : ℂ) - sin p.2 = _ at hb
    linear_combination X / 2 * (ha + hb) + Y / 2 * (ha - hb)
  change gradNorm p * (liftL2 (invLap ω) p * conj (streamNormal ω p)).re = _
  by_cases hz : gradNorm p = 0
  · have he := mixed_level_gradNorm_sq q
    change gradNorm p ^ 2 = _ at he
    rw [hz] at he
    have hr : mixedLevelR q = 0 := by nlinarith only [he, sq_nonneg (mixedLevelS q)]
    have hS : mixedLevelS q = 0 := by nlinarith only [he, sq_nonneg (mixedLevelR q)]
    simp [hz, hr, hS]
  · rw [show liftL2 (invLap ω) p = _ from hs, streamNormal, normalDeriv]
    change gradNorm p * (_ * conj ((sin p.1 * X + sin p.2 * Y) / (gradNorm p : ℂ))).re = _
    rw [hn, map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.div_ofReal_re]
    field_simp

private theorem mixed_level_norm_diff (R S : ℝ) (A B : ℂ) :
    ‖(S : ℂ) * A + (R : ℂ) * B‖ ^ 2 - ‖-(R : ℂ) * A + (S : ℂ) * B‖ ^ 2 =
      (S ^ 2 - R ^ 2) * (‖A‖ ^ 2 - ‖B‖ ^ 2) + 4 * S * R * (A * conj B).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Signed gradient density with the normalization for the coefficient
`2 - 2s` in the geometric level integral. -/
theorem MixedQuotientData.level_signed_gradient_ae {ω : L2} (d : MixedQuotientData ω) :
    ∀ᵐ q ∂volume.restrict mixedOpenCell, gradNorm (diagInv q) ≠ 0 →
      2 * (‖streamNormal ω (diagInv q)‖ ^ 2 - ‖streamTangent ω (diagInv q)‖ ^ 2) =
        -(mixedLevelSign q) * (‖d.streamA q‖ ^ 2 - ‖d.streamB q‖ ^ 2) +
          mixedLevelCross q * (d.streamA q * conj (d.streamB q)).re := by
  filter_upwards [d.stream_partials_ae] with q hq hρ
  let p := diagInv q
  let X := streamLiftX ω p
  let Y := streamLiftY ω p
  have ha := congrArg Complex.ofReal (mixed_level_sin_add q)
  have hb := congrArg Complex.ofReal (mixed_level_sin_sub q)
  push_cast at ha hb
  simp only [← Complex.ofReal_sin] at ha hb
  change (sin p.1 : ℂ) + sin p.2 = _ at ha
  change (sin p.1 : ℂ) - sin p.2 = _ at hb
  have hn : sin p.1 * X + sin p.2 * Y =
      (mixedLevelS q : ℂ) * d.streamA q + (mixedLevelR q : ℂ) * d.streamB q := by
    rw [hq.1, hq.2]
    linear_combination X / 2 * (ha + hb) + Y / 2 * (ha - hb)
  have ht : sin p.2 * X - sin p.1 * Y =
      -(mixedLevelR q : ℂ) * d.streamA q + (mixedLevelS q : ℂ) * d.streamB q := by
    rw [hq.1, hq.2]
    linear_combination X / 2 * (ha - hb) - Y / 2 * (ha + hb)
  have hD : mixedLevelR q ^ 2 + mixedLevelS q ^ 2 ≠ 0 := by
    intro hz
    have hh := mixed_level_gradNorm_sq q
    rw [hz, mul_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)] at hh
    exact hρ hh
  change 2 * (‖(sin p.1 * X + sin p.2 * Y) / (gradNorm p : ℂ)‖ ^ 2 -
    ‖(sin p.2 * X - sin p.1 * Y) / (gradNorm p : ℂ)‖ ^ 2) = _
  rw [hn, ht]
  have hp0 : 0 ≤ gradNorm p := sqrt_nonneg _
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hp0, div_pow, ← sub_div]
  change 2 * ((_ - _) / gradNorm p ^ 2) = _
  rw [mixed_level_norm_diff, mixed_level_gradNorm_sq, mixedLevelSign, mixedLevelCross]
  field_simp; ring

/-- All non-model terms in the signed gradient density have one factor
of the Dirichlet cosine. This is the factor that absorbs the quarter
time weight on either side of a corner. -/
theorem MixedQuotientData.level_gradient_split {ω : L2} (d : MixedQuotientData ω) (q : Plane) :
    -mixedLevelSign q * (‖d.streamA q‖ ^ 2 - ‖d.streamB q‖ ^ 2) +
        mixedLevelCross q * (d.streamA q * conj (d.streamB q)).re =
      -mixedLevelSign q * ‖d.phi q‖ ^ 2 + cos q.1 *
        (mixedLevelSign q * (cos q.1 * (‖d.phi q‖ ^ 2 - ‖d.jet [0] q‖ ^ 2 +
            ‖d.jet [1] q‖ ^ 2) + 2 * sin q.1 * (d.jet [0] q * conj (d.phi q)).re) +
          mixedLevelCross q * (d.streamA q * conj (d.jet [1] q)).re) := by
  have hh : sin q.1 ^ 2 = 1 - cos q.1 ^ 2 := by linarith only [sin_sq_add_cos_sq q.1]
  generalize hC : mixedLevelSign q = C
  generalize hX : mixedLevelCross q = K
  simp only [MixedQuotientData.streamA, MixedQuotientData.streamB, Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (-C * ((d.phi q).re ^ 2 + (d.phi q).im ^ 2)) * hh

end NoEmbeddedEigenvalues
