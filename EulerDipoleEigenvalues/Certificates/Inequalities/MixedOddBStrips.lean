module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBLog
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBReplay.Strip0
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBStripPower
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip1Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip2Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip3Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip4Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip5Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip6Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip7Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip8Full
import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Strip9
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Dyadic
import Mathlib.Tactic.IntervalCases

/-!
# The mixed odd-in-b endpoint signs

For strip 9, direct endpoint inequalities enclose the logarithm on each
leaf. The generated Horner traces in `MixedOddBTrace.Strip9` prove the
polynomial signs on those leaves; this file checks their coverage.
Strips 1 through 8 use plain Horner and two-axis centered bounds, checked on
covering trees. The strip-zero Bernstein proof is retained only for the
standalone endpoint theorem.
-/

@[expose] public section

namespace EulerDipoleEigenvalues

open Set
open Finset hiding Icc
open Inclusion.IntervalDyadicReal

private theorem logTaylor_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    certificateLogTaylor y ≤ certificateLogTaylor x := by
  unfold certificateLogTaylor
  apply neg_le_neg
  gcongr

private theorem logTail_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x ^ 15 / (15 * (1 - x)) ≤ y ^ 15 / (15 * (1 - y)) := by
  have hxp : 0 ≤ x ^ 15 := pow_nonneg hx _
  have hn : x ^ 15 ≤ y ^ 15 := by gcongr
  exact div_le_div₀ (hxp.trans hn) hn (by linarith) (by linarith)

-- The two endpoint expressions already used in the strip theorem.
private def logHi {R : Type} [Field R] (c x : R) : R :=
  -9 * c - ∑ i ∈ Finset.range 14, x ^ (i + 1) / (i + 1 : ℕ)

private def logLo {R : Type} [Field R] (c x : R) : R :=
  logHi c x - x ^ 15 / (15 * (1 - x))

private def stripX {R : Type} [Ring R] (h : R) : R := 1 - 512 * h

private theorem logHi_eq (c x : ℝ) : logHi c x = -9 * c + certificateLogTaylor x := by
  simp only [logHi, certificateLogTaylor, Nat.cast_add, Nat.cast_one, sub_eq_add_neg]

-- The box certifies the entire interval between the two log endpoints.
private def boxSign (a b c d : Dyadic) : Prop :=
    ∀ {h k l : ℝ}, h ∈ Icc a.toReal b.toReal → k ∈ Icc c.toReal d.toReal →
      logLo (certificateLogTwoUpper : ℝ) (stripX h) ≤ l →
      l ≤ logHi (certificateLogTwoLower : ℝ) (stripX h) →
      0 ≤ mixedOddBCleared h k l

private def dy (n : ℤ) : Dyadic := Dyadic.ofIntWithPrec n 20

private theorem boxSplitH {a b c d m : Dyadic}
    (left : boxSign a m c d) (right : boxSign m b c d) : boxSign a b c d := by
  intro h k l hh hk hlo hhi
  rcases le_or_gt h m.toReal with hm | hm
  · exact left ⟨hh.1, hm⟩ hk hlo hhi
  · exact right ⟨hm.le, hh.2⟩ hk hlo hhi

private theorem boxSplitK {a b c d m : Dyadic}
    (left : boxSign a b c m) (right : boxSign a b m d) : boxSign a b c d := by
  intro h k l hh hk hlo hhi
  rcases le_or_gt k m.toReal with hm | hm
  · exact left hh ⟨hk.1, hm⟩ hlo hhi
  · exact right hh ⟨hm.le, hk.2⟩ hlo hhi

-- Outward-rounded endpoints in units of 2^-20. Only the horizontal endpoints
-- occurring in the strip-9 boxes are used; each bound is checked below.
private def stripNineLogLower : ℤ → ℤ
  | 1024 => -7268176
  | 1152 => -7144671
  | 1280 => -7034193
  | 1408 => -6934253
  | 1536 => -6843014
  | 1664 => -6759084
  | 1792 => -6681376
  | _ => 0

private def stripNineLogUpper : ℤ → ℤ
  | 1152 => -7144670
  | 1280 => -7034191
  | 1408 => -6934252
  | 1536 => -6843013
  | 1664 => -6759083
  | 1792 => -6681375
  | 2048 => -6541357
  | _ => 0

-- Freeze rational log-two bounds once, before evaluating the endpoint series.
private theorem stripNineLogTwoLower :
    (6931471805599453 / 10 ^ 16 : ℝ) ≤ (certificateLogTwoLower : ℝ) := by
  have h : (6931471805599453 / 10 ^ 16 : ℚ) ≤ certificateLogTwoLower := by
    norm_num [certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

private theorem stripNineLogTwoUpper :
    (certificateLogTwoUpper : ℝ) ≤ (6931471805599454 / 10 ^ 16 : ℝ) := by
  have h : certificateLogTwoUpper ≤ (6931471805599454 / 10 ^ 16 : ℚ) := by
    norm_num [certificateLogTwoUpper, certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

private theorem logLo_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    logLo (certificateLogTwoUpper : ℝ) y ≤ logLo (certificateLogTwoUpper : ℝ) x := by
  unfold logLo
  rw [logHi_eq, logHi_eq]
  exact sub_le_sub ((add_le_add_iff_left _).2 (logTaylor_anti hx hxy))
    (logTail_mono hx hxy hy)

private theorem stripNineLeaf {a b c d : ℤ}
    (hpoly : ∀ {h k l : ℝ}, h ∈ Icc (dy a).toReal (dy b).toReal →
      k ∈ Icc (dy c).toReal (dy d).toReal →
      l ∈ Icc (dy (stripNineLogLower a)).toReal (dy (stripNineLogUpper b)).toReal →
      0 ≤ mixedOddBCleared h k l)
    (hrange : 0 < dy a ∧ dy b ≤ dy 2048)
    (hlo : (dy (stripNineLogLower a)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy a).toReal))
    (hhi : logHi (certificateLogTwoLower : ℝ) (stripX (dy b).toReal) ≤
      (dy (stripNineLogUpper b)).toReal) :
    boxSign (dy a) (dy b) (dy c) (dy d) := by
  intro h k l hh hk hl hu
  rcases hrange with ⟨ha, hb'⟩
  have ha₀ : 0 < (dy a).toReal := by
    have hp : (0 : Dyadic).toReal < (dy a).toReal :=
      Dyadic.toRealOrderEmbedding.strictMono ha
    simpa only [Dyadic.toReal, Dyadic.toRat_zero, Rat.cast_zero] using hp
  have hb₁ : (dy b).toReal ≤ 1 / 512 := by
    have he : (dy 2048).toReal = (1 / 512 : ℝ) := by
      norm_num [dy, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
    exact he ▸ Dyadic.toRealOrderEmbedding.monotone hb'
  have hbh : stripX (dy b).toReal ≤ stripX h := by
    dsimp [stripX]; linarith only [hh.2]
  have hha : stripX h ≤ stripX (dy a).toReal := by
    dsimp [stripX]; linarith only [hh.1]
  have hb₀ : 0 ≤ stripX (dy b).toReal := by dsimp [stripX]; linarith only [hb₁]
  have ha₁ : stripX (dy a).toReal < 1 := by dsimp [stripX]; linarith only [ha₀]
  have hupper : logHi (certificateLogTwoLower : ℝ) (stripX h) ≤
      logHi (certificateLogTwoLower : ℝ) (stripX (dy b).toReal) := by
    rw [logHi_eq, logHi_eq]
    exact add_le_add_right (logTaylor_anti hb₀ hbh) _
  exact hpoly hh hk
    ⟨hlo.trans ((logLo_anti (hb₀.trans hbh) hha ha₁).trans hl), hu.trans (hupper.trans hhi)⟩

private theorem stripNineLower1024 :
    (dy (stripNineLogLower 1024)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1024).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1024).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1152 :
    (dy (stripNineLogLower 1152)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1152).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1152).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1280 :
    (dy (stripNineLogLower 1280)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1280).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1280).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1408 :
    (dy (stripNineLogLower 1408)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1408).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1408).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1536 :
    (dy (stripNineLogLower 1536)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1536).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1536).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1664 :
    (dy (stripNineLogLower 1664)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1664).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1664).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineLower1792 :
    (dy (stripNineLogLower 1792)).toReal ≤
      logLo (certificateLogTwoUpper : ℝ) (stripX (dy 1792).toReal) := by
  apply le_trans (b := logLo (6931471805599454 / 10 ^ 16 : ℝ) (stripX (dy 1792).toReal))
  · norm_num [logLo, logHi, stripNineLogLower, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]
  · unfold logLo logHi
    linarith only [stripNineLogTwoUpper]

private theorem stripNineUpper1152 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1152).toReal) ≤
      (dy (stripNineLogUpper 1152)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1152).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper1280 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1280).toReal) ≤
      (dy (stripNineLogUpper 1280)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1280).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper1408 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1408).toReal) ≤
      (dy (stripNineLogUpper 1408)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1408).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper1536 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1536).toReal) ≤
      (dy (stripNineLogUpper 1536)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1536).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper1664 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1664).toReal) ≤
      (dy (stripNineLogUpper 1664)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1664).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper1792 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 1792).toReal) ≤
      (dy (stripNineLogUpper 1792)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 1792).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

private theorem stripNineUpper2048 :
    logHi (certificateLogTwoLower : ℝ) (stripX (dy 2048).toReal) ≤
      (dy (stripNineLogUpper 2048)).toReal := by
  apply le_trans (b := logHi (6931471805599453 / 10 ^ 16 : ℝ) (stripX (dy 2048).toReal))
  · unfold logHi
    linarith only [stripNineLogTwoLower]
  · norm_num [logHi, stripNineLogUpper, stripX, dy, Dyadic.toReal,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Finset.sum_range_succ]

-- Reconcile the dyadic endpoints in the coverage tree with the explicit
-- real rationals in the generated theorem. Only the six constants are reduced.
local macro "stripNineTrace " leaf:term : tactic =>
  `(tactic| (intro h k l hh hk hl;
             apply $leaf <;>
               (norm_num [dy, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
                   stripNineLogLower, stripNineLogUpper] at hh hk hl ⊢; assumption)))

private theorem stripNineBox : boxSign (dy 1024) (dy 2048) (dy 0) (dy 1048576) := by
  apply boxSplitK (m := dy 524288)
  · apply boxSplitK (m := dy 262144)
    · apply boxSplitK (m := dy 131072)
      · apply boxSplitK (m := dy 65536)
        · apply boxSplitK (m := dy 32768)
          · apply boxSplitK (m := dy 16384)
            · apply boxSplitK (m := dy 8192)
              · apply boxSplitK (m := dy 4096)
                · apply boxSplitH (m := dy 1536)
                  · apply boxSplitK (m := dy 2048)
                    · apply boxSplitK (m := dy 1024)
                      · apply boxSplitH (m := dy 1280)
                        · apply boxSplitH (m := dy 1152)
                          · exact stripNineLeaf
                              (by stripNineTrace MixedOddBTrace.Strip9.leaf00) (by decide)
                              stripNineLower1024 stripNineUpper1152
                          · exact stripNineLeaf
                              (by stripNineTrace MixedOddBTrace.Strip9.leaf01) (by decide)
                              stripNineLower1152 stripNineUpper1280
                        · apply boxSplitH (m := dy 1408)
                          · exact stripNineLeaf
                              (by stripNineTrace MixedOddBTrace.Strip9.leaf02) (by decide)
                              stripNineLower1280 stripNineUpper1408
                          · exact stripNineLeaf
                              (by stripNineTrace MixedOddBTrace.Strip9.leaf03) (by decide)
                              stripNineLower1408 stripNineUpper1536
                      · exact stripNineLeaf
                          (by stripNineTrace MixedOddBTrace.Strip9.leaf04) (by decide)
                          stripNineLower1024 stripNineUpper1536
                    · exact stripNineLeaf
                        (by stripNineTrace MixedOddBTrace.Strip9.leaf05) (by decide)
                        stripNineLower1024 stripNineUpper1536
                  · apply boxSplitH (m := dy 1792)
                    · apply boxSplitH (m := dy 1664)
                      · exact stripNineLeaf
                          (by stripNineTrace MixedOddBTrace.Strip9.leaf06) (by decide)
                          stripNineLower1536 stripNineUpper1664
                      · exact stripNineLeaf
                          (by stripNineTrace MixedOddBTrace.Strip9.leaf07) (by decide)
                          stripNineLower1664 stripNineUpper1792
                    · exact stripNineLeaf
                        (by stripNineTrace MixedOddBTrace.Strip9.leaf08) (by decide)
                        stripNineLower1792 stripNineUpper2048
                · exact stripNineLeaf
                    (by stripNineTrace MixedOddBTrace.Strip9.leaf09) (by decide)
                    stripNineLower1024 stripNineUpper2048
              · exact stripNineLeaf
                  (by stripNineTrace MixedOddBTrace.Strip9.leaf10) (by decide)
                  stripNineLower1024 stripNineUpper2048
            · exact stripNineLeaf
                (by stripNineTrace MixedOddBTrace.Strip9.leaf11) (by decide)
                stripNineLower1024 stripNineUpper2048
          · exact stripNineLeaf
              (by stripNineTrace MixedOddBTrace.Strip9.leaf12) (by decide)
              stripNineLower1024 stripNineUpper2048
        · exact stripNineLeaf
            (by stripNineTrace MixedOddBTrace.Strip9.leaf13) (by decide)
            stripNineLower1024 stripNineUpper2048
      · exact stripNineLeaf
          (by stripNineTrace MixedOddBTrace.Strip9.leaf14) (by decide)
          stripNineLower1024 stripNineUpper2048
    · exact stripNineLeaf
        (by stripNineTrace MixedOddBTrace.Strip9.leaf15) (by decide)
        stripNineLower1024 stripNineUpper2048
  · exact stripNineLeaf
      (by stripNineTrace MixedOddBTrace.Strip9.leaf16) (by decide)
      stripNineLower1024 stripNineUpper2048

private theorem mixed_odd_b_strip_nine_signs {z k : ℝ} (hz : z ∈ Set.Icc 0 1)
    (hk : k ∈ Set.Icc 0 1) :
    0 ≤ mixedOddBStripLower 9 z k ∧ 0 ≤ mixedOddBStripUpper 9 z k := by
  let h := mixedOddBStripH 9 z
  have hx : stripX h = z / 2 := by
    dsimp [stripX, h, mixedOddBStripH]
    ring
  have hs : h = (1 / 512 : ℝ) * (1 - z / 2) := by
    norm_num [h, mixedOddBStripH]
  have hdz : 0 < 1 - z / 2 := by linarith [hz.2]
  have hh : h ∈ Icc (dy 1024).toReal (dy 2048).toReal := by
    rw [hs]
    constructor <;> simp [dy, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow] <;>
      norm_num <;> linarith [hz.1, hz.2]
  have hk' : k ∈ Icc (dy 0).toReal (dy 1048576).toReal := by
    have he : (dy 1048576).toReal = (1 : ℝ) := by
      norm_num [dy, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
    rw [he]
    simpa [dy, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow] using hk
  have hpos : 0 ≤ h := hs ▸ mul_nonneg (by norm_num) hdz.le
  let lo : ℝ := logLo (certificateLogTwoUpper : ℝ) (stripX h)
  let hi : ℝ := logHi (certificateLogTwoLower : ℝ) (stripX h)
  have hle : lo ≤ hi := by
    simp only [lo, hi, logLo, logHi_eq, hx]
    have h₂ := certificate_log_two_bounds.1.trans certificate_log_two_bounds.2
    have htail : 0 ≤ (z / 2) ^ 15 / (15 * (1 - z / 2)) :=
      div_nonneg (pow_nonneg (div_nonneg hz.1 (by norm_num)) _) (by positivity)
    linarith only [h₂, htail]
  have hlo := stripNineBox hh hk' (le_refl lo) hle
  have hhi := stripNineBox hh hk' hle (le_refl hi)
  refine ⟨?_, ?_⟩
  · have he : mixedOddBStripLower 9 z k = h * mixedOddBCleared h k lo := by
      change h * mixedOddBCleared h k _ - _ = _
      simp only [lo, logLo, logHi_eq, hx, mixed_odd_b_cleared_affine, Nat.cast_ofNat]
      generalize mixedOddBA h k = a
      generalize mixedOddBB h k = b
      rw [hs]
      generalize 1 - z / 2 = w at hdz ⊢
      field_simp [hdz.ne']
      ring
    rw [he]
    exact mul_nonneg hpos hlo
  · simpa only [hi, hx, logHi_eq, mixedOddBStripUpper, h, Nat.cast_ofNat] using hhi

/-- The Taylor endpoint signs on strips 1 through 9. -/
theorem mixed_odd_b_positive_strip_signs (j : ℕ) (hj : j < 10) (hj₀ : 0 < j) (z k : ℝ)
    (hz : z ∈ Icc 0 1) (hk : k ∈ Icc 0 1) :
    0 ≤ mixedOddBStripLower j z k ∧ 0 ≤ mixedOddBStripUpper j z k := by
  interval_cases j
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip1.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip2.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip3.root hz hk
  · exact MixedOddBTrace.Strip4.endpoints MixedOddBTrace.Strip4.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip5.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip6.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip7.root hz hk
  · exact MixedOddBTrace.Scaled.endpoints (by norm_num) (by norm_num)
      MixedOddBTrace.Strip8.root hz hk
  · exact mixed_odd_b_strip_nine_signs hz hk

private theorem endpoint_nonneg {n m : ℕ} (p : BernsteinIntTable n m)
    (t : BernsteinMidTree) (hc : t.check (bernsteinIntFromPower p) = true)
    {D z k v : ℝ} (hD : 0 < D) (he : bernsteinIntPowerEval p z k = D * v)
    (hz : z ∈ Icc (0 : ℝ) 1) (hk : k ∈ Icc (0 : ℝ) 1) : 0 ≤ v := by
  have h := t.power_nonneg p hc hz hk
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h hD

/-- The twenty polynomial signs on the rescaled unit squares.
The residual certificate uses the separate short-log proof on strip zero. -/
theorem mixed_odd_b_strip_signs (j : ℕ) (hj : j < 10) (z k : ℝ)
    (hz : z ∈ Icc 0 1) (hk : k ∈ Icc 0 1) :
    0 ≤ mixedOddBStripLower j z k ∧ 0 ≤ mixedOddBStripUpper j z k := by
  by_cases hj₀ : j = 0
  · subst j
    exact ⟨endpoint_nonneg _ _ oddBLower0_check (by norm_num [oddBLower0Scale])
        (oddBLower0_power z k) hz hk,
        endpoint_nonneg _ _ oddBUpper0_check (by norm_num [oddBUpper0Scale])
          (oddBUpper0_power z k) hz hk⟩
  · exact mixed_odd_b_positive_strip_signs j hj (Nat.pos_of_ne_zero hj₀) z k hz hk

end EulerDipoleEigenvalues
