import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Distribution.Sobolev

/-!
# The critical Hardy inequality for odd functions

Blueprint: `def:gagliardo`, `lem:odd-hardy`; `lem:sobolev-fractional-gagliardo` (stated).

For an odd function `a` on `ℝ`, `∫₀^∞ |a(u)|² du/u ≤ 2 [a]²`, where
`[a]² = ∫∫ |a(u) - a(w)|² / (u - w)² du dw` is the Gagliardo seminorm of `H^{1/2}`.

The proof is pointwise. For `u > 0` and `|w| ≤ u`, oddness gives `a(u) - a(-w) = a(u) + a(w)`,
and the parallelogram law gives
`|a(u) - a(w)|² + |a(u) + a(w)|² ≥ 2|a(u)|²`. Both denominators `(u ∓ w)²` are at most
`4u²`, so `A(u, w) + A(u, -w) ≥ |a(u)|² / (2u²)` with `A(u, w) = |a(u) - a(w)|² / (u - w)²`.
Integrating over `w ∈ [-u, u]` gives `|a(u)|²/u ≤ 2 ∫ A(u, w) dw`. Everything is
nonnegative, so no integrability assumption is needed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ENNReal

/-- The squared Gagliardo seminorm `[a]² = ∫∫ |a(u) - a(w)|² / (u - w)² du dw` of
    `H^{1/2}(ℝ)`. -/
def gagliardoSq (a : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ u, ∫⁻ w, ENNReal.ofReal (‖a u - a w‖ ^ 2 / (u - w) ^ 2)

/-- `‖x‖² / (4u²) ≤ ‖x‖² / d` for `0 ≤ d ≤ 4u²`, provided `x = 0` when `d = 0`. -/
theorem div_four_sq_le {x : ℂ} {u d : ℝ} (hd : 0 ≤ d) (hdu : d ≤ 4 * u ^ 2)
    (h0 : d = 0 → x = 0) : ‖x‖ ^ 2 / (4 * u ^ 2) ≤ ‖x‖ ^ 2 / d := by
  rcases hd.eq_or_lt with h | h
  · simp [h0 h.symm]
  · exact div_le_div_of_nonneg_left (sq_nonneg _) h hdu

/-- The pointwise inequality: `|a(u)|² / (2u²) ≤ A(u, w) + A(u, -w)` for `|w| ≤ u`. -/
theorem sq_div_le_of_odd {a : ℝ → ℂ} (hodd : ∀ u, a (-u) = -a u) {u w : ℝ} (hu : 0 < u)
    (hw : w ∈ Icc (-u) u) :
    ‖a u‖ ^ 2 / (2 * u ^ 2) ≤
      ‖a u - a w‖ ^ 2 / (u - w) ^ 2 + ‖a u - a (-w)‖ ^ 2 / (u - -w) ^ 2 := by
  have h1 := div_four_sq_le (x := a u - a w) (u := u) (sq_nonneg (u - w))
    (by nlinarith [hw.1, hw.2])
    (fun h ↦ by
      have : w = u := by nlinarith
      simp [this])
  have h2 := div_four_sq_le (x := a u - a (-w)) (u := u) (sq_nonneg (u - -w))
    (by nlinarith [hw.1, hw.2])
    (fun h ↦ by
      have : -w = u := by nlinarith
      simp [this])
  have hpar := parallelogram_law_with_norm ℝ (a u) (a w)
  rw [hodd, sub_neg_eq_add] at h2 ⊢
  have hu2 : 0 < u ^ 2 := by positivity
  have : ‖a u‖ ^ 2 / (2 * u ^ 2) ≤
      ‖a u - a w‖ ^ 2 / (4 * u ^ 2) + ‖a u + a w‖ ^ 2 / (4 * u ^ 2) := by
    rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity), add_comm, hpar]
    nlinarith [sq_nonneg ‖a w‖, sq_nonneg ‖a u‖, mul_nonneg (sq_nonneg ‖a w‖) hu2.le]
  linarith

/-- The critical Hardy inequality for odd functions: `∫₀^∞ |a(u)|² du/u ≤ 2 [a]²`. -/
theorem lintegral_sq_div_le_gagliardoSq {a : ℝ → ℂ} (ha : AEMeasurable a)
    (hodd : ∀ u, a (-u) = -a u) :
    ∫⁻ u in Ioi 0, ENNReal.ofReal (‖a u‖ ^ 2 / u) ≤ 2 * gagliardoSq a := by
  rw [gagliardoSq, ← lintegral_const_mul' _ _ (by norm_num)]
  refine (setLIntegral_mono' measurableSet_Ioi fun u hu ↦ ?_).trans
    (setLIntegral_le_lintegral _ _)
  have hu : (0 : ℝ) < u := hu
  set A : ℝ → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (‖a u - a w‖ ^ 2 / (u - w) ^ 2) with hA_def
  have hA : AEMeasurable A := by
    rw [hA_def]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((aemeasurable_const.sub ha).norm.pow_const 2).div (by fun_prop))
  calc ENNReal.ofReal (‖a u‖ ^ 2 / u)
      = ∫⁻ _ in Icc (-u) u, ENNReal.ofReal (‖a u‖ ^ 2 / (2 * u ^ 2)) := by
        rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ ≤ ∫⁻ w in Icc (-u) u, (A w + A (-w)) := by
        refine setLIntegral_mono' measurableSet_Icc fun w hw ↦ ?_
        rw [hA_def, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (sq_div_le_of_odd hodd hu hw)
    _ ≤ ∫⁻ w, (A w + A (-w)) := setLIntegral_le_lintegral _ _
    _ = (∫⁻ w, A w) + ∫⁻ w, A (-w) := lintegral_add_left' hA _
    _ = 2 * ∫⁻ w, A w := by rw [lintegral_neg_eq_self, two_mul]

/-- `H^{1/2}(ℝ)` in Gagliardo form (`lem:sobolev-fractional-gagliardo`, stated): an `L²`
    function lies in Mathlib's Bessel potential space `H^{1/2, 2}` iff `[a] < ∞`. -/
theorem memSobolev_half_iff_gagliardoSq_lt_top {a : ℝ → ℂ} (ha : MemLp a 2) :
    (MeasureTheory.Lp.toTemperedDistribution (ha.toLp a)).MemSobolev (1 / 2) 2 ↔
      gagliardoSq a < ⊤ := by
  sorry

end NoEmbeddedEigenvalues
