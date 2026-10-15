import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Complex H¹ functions on a bounded interval

Blueprint: `def:h1-interval`, `lem:h1-interval-endpoints`, and `def:h1-zero-interval`.

`HasIntervalH1 a b F D` records a locally absolutely continuous representative on
`(a,b)` with explicit a.e. derivative `D`, and square integrability of both. No
condition is imposed on the arbitrary values of `F` at the endpoints or outside
the interval. `intervalH1Extension` constructs the canonical endpoint values;
uniqueness means equality on `[a,b]`, not outside it.

This is an unbundled first-order API, not yet a normed Sobolev space or a
weighted second-order domain. Interval H² and periodic H¹ are deferred.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Interval Topology

/-- An interval H¹ representative with a specified a.e. derivative. All regularity
    conditions concern the open interval; the raw endpoint values are irrelevant. -/
structure HasIntervalH1 (a b : ℝ) (F D : ℝ → ℂ) : Prop where
  memLp_value : MemLp F 2 (volume.restrict (Ioo a b))
  memLp_derivative : MemLp D 2 (volume.restrict (Ioo a b))
  locally_absolutelyContinuous : ∀ c d, a < c → c ≤ d → d < b →
    AbsolutelyContinuousOnInterval F c d
  hasDerivAt_ae : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt F (D x) x

/-- Constant functions belong to the interval H¹ domain. -/
theorem hasIntervalH1_const (a b : ℝ) (c : ℂ) :
    HasIntervalH1 a b (fun _ ↦ c) (fun _ ↦ 0) where
  memLp_value := memLp_const c
  memLp_derivative := MemLp.zero
  locally_absolutelyContinuous _ _ _ _ _ :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  hasDerivAt_ae := Eventually.of_forall (fun x _ ↦ hasDerivAt_const x c)

/-- Membership in interval H¹, without choosing the derivative as part of the data. -/
def MemIntervalH1 (a b : ℝ) (F : ℝ → ℂ) : Prop :=
  ∃ D, HasIntervalH1 a b F D

/-- H¹ data are closed under addition. -/
theorem HasIntervalH1.add {a b : ℝ} {F D G E : ℝ → ℂ}
    (hF : HasIntervalH1 a b F D) (hG : HasIntervalH1 a b G E) :
    HasIntervalH1 a b (F + G) (D + E) where
  memLp_value := hF.memLp_value.add hG.memLp_value
  memLp_derivative := hF.memLp_derivative.add hG.memLp_derivative
  locally_absolutelyContinuous c d hac hcd hdb :=
    (hF.locally_absolutelyContinuous c d hac hcd hdb).add
      (hG.locally_absolutelyContinuous c d hac hcd hdb)
  hasDerivAt_ae := by
    filter_upwards [hF.hasDerivAt_ae, hG.hasDerivAt_ae] with x hxF hxG hx
    exact (hxF hx).add (hxG hx)

/-- H¹ data are closed under complex scalar multiplication. -/
theorem HasIntervalH1.smul {a b : ℝ} {F D : ℝ → ℂ}
    (hF : HasIntervalH1 a b F D) (c : ℂ) : HasIntervalH1 a b (c • F) (c • D) where
  memLp_value := hF.memLp_value.const_smul c
  memLp_derivative := hF.memLp_derivative.const_smul c
  locally_absolutelyContinuous u v hau huv hvb :=
    AbsolutelyContinuousOnInterval.const_smul c
      (hF.locally_absolutelyContinuous u v hau huv hvb)
  hasDerivAt_ae := by
    filter_upwards [hF.hasDerivAt_ae] with x hx hxI
    exact (hx hxI).const_smul c

/-- The canonical continuous extension, anchored at the midpoint. Its values are
    only used on the closed interval; the integral is total outside it. -/
def intervalH1Extension (a b : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℂ :=
  F ((a + b) / 2) + ∫ t in ((a + b) / 2)..x, D t

/-- On a finite interval an H¹ derivative is integrable, including across the endpoints. -/
theorem HasIntervalH1.integrableOn_derivative {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) : IntegrableOn D (Icc a b) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact h.memLp_derivative.integrable (by norm_num)

/-- Local absolute continuity on an unoriented compact subinterval. -/
theorem HasIntervalH1.absolutelyContinuous {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval F c d := by
  rcases le_total c d with hcd | hdc
  · exact h.locally_absolutelyContinuous c d hc.1 hcd hd.2
  · exact (h.locally_absolutelyContinuous d c hd.1 hdc hc.2).symm

/-- FTC for an absolutely continuous complex-valued function with a specified a.e.
    derivative. Mathlib's real-valued FTC is applied to its two components. -/
theorem complex_integral_eq_sub_of_ac {F D : ℝ → ℂ} {c d : ℝ}
    (hF : AbsolutelyContinuousOnInterval F c d)
    (hD : IntervalIntegrable D volume c d)
    (hderiv : ∀ᵐ x, x ∈ uIcc c d → HasDerivAt F (D x) x) :
    (∫ x in c..d, D x) = F d - F c := by
  have hFr : AbsolutelyContinuousOnInterval (fun x ↦ (F x).re) c d := by
    simpa using! reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hF
  have hFi : AbsolutelyContinuousOnInterval (fun x ↦ (F x).im) c d := by
    simpa using! imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hF
  have hr : (∫ x in c..d, (D x).re) = (F d).re - (F c).re := by
    rw [← hFr.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx hxcd
    have hproj : HasDerivAt (fun y ↦ (F y).re) (D x).re x := by
      simpa using! reCLM.hasFDerivAt.comp_hasDerivAt x (hx (uIoc_subset_uIcc hxcd))
    exact hproj.deriv.symm
  have hi : (∫ x in c..d, (D x).im) = (F d).im - (F c).im := by
    rw [← hFi.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx hxcd
    have hproj : HasDerivAt (fun y ↦ (F y).im) (D x).im x := by
      simpa using! imCLM.hasFDerivAt.comp_hasDerivAt x (hx (uIoc_subset_uIcc hxcd))
    exact hproj.deriv.symm
  apply Complex.ext
  · exact (reCLM.intervalIntegral_comp_comm hD).symm.trans hr
  · exact (imCLM.intervalIntegral_comp_comm hD).symm.trans hi

/-- The first-order fundamental theorem on compact subintervals of the open interval. -/
theorem HasIntervalH1.integral_eq_sub {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) :
    (∫ x in c..d, D x) = F d - F c := by
  have hsub : uIcc c d ⊆ Ioo a b := by
    intro x hx
    rcases mem_uIcc.mp hx with hx | hx
    · exact ⟨hc.1.trans_le hx.1, hx.2.trans_lt hd.2⟩
    · exact ⟨hd.1.trans_le hx.1, hx.2.trans_lt hc.2⟩
  apply complex_integral_eq_sub_of_ac (h.absolutelyContinuous hc hd)
  · exact (h.integrableOn_derivative.mono_set
      (fun x hx ↦ Ioo_subset_Icc_self (hsub hx))).intervalIntegrable
  · filter_upwards [h.hasDerivAt_ae] with x hx hxcd
    exact hx (hsub hxcd)

/-- The canonical extension agrees with the original representative in the interior. -/
theorem HasIntervalH1.extension_eq {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) :
    EqOn (intervalH1Extension a b F D) F (Ioo a b) := by
  intro x hx
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rw [intervalH1Extension, h.integral_eq_sub hm hx]
  abel

/-- The canonical extension is continuous on the closed interval. -/
theorem HasIntervalH1.continuousOn_extension {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) :
    ContinuousOn (intervalH1Extension a b F D) (Icc a b) := by
  have hD : IntegrableOn D (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using h.integrableOn_derivative
  have hm : (a + b) / 2 ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    constructor <;> linarith
  have hp := intervalIntegral.continuousOn_primitive_interval' hD.intervalIntegrable hm
  change ContinuousOn (fun x ↦ F ((a + b) / 2) + ∫ t in ((a + b) / 2)..x, D t) (Icc a b)
  apply continuousOn_const.add
  simpa only [uIcc_of_le hab.le] using hp

/-- The extension is unique on the closed interval, regardless of how another
    extension is defined outside it or of the chosen a.e. derivative. -/
theorem HasIntervalH1.extension_unique {a b : ℝ} {F D G : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (hG : ContinuousOn G (Icc a b)) (heq : EqOn G F (Ioo a b)) :
    EqOn G (intervalH1Extension a b F D) (Icc a b) := by
  have hext : EqOn G (intervalH1Extension a b F D) (Ioo a b) := by
    intro x hx
    exact (heq hx).trans (h.extension_eq hab hx).symm
  exact hext.of_subset_closure hG (h.continuousOn_extension hab)
    Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- FTC up to the endpoints, using traces rather than the raw endpoint values. -/
theorem HasIntervalH1.integral_eq_extension_sub {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    (∫ x in c..d, D x) = intervalH1Extension a b F D d - intervalH1Extension a b F D c := by
  have hm : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hmc := (h.integrableOn_derivative.mono_set (uIcc_subset_Icc hm hc)).intervalIntegrable
  have hmd := (h.integrableOn_derivative.mono_set (uIcc_subset_Icc hm hd)).intervalIntegrable
  dsimp only [intervalH1Extension]
  rw [show (F ((a + b) / 2) + ∫ x in ((a + b) / 2)..d, D x) -
      (F ((a + b) / 2) + ∫ x in ((a + b) / 2)..c, D x) =
      (∫ x in ((a + b) / 2)..d, D x) - ∫ x in ((a + b) / 2)..c, D x by abel]
  exact (intervalIntegral.integral_interval_sub_left hmd hmc).symm

/-- Choosing another a.e. derivative does not change the extension or its traces. -/
theorem HasIntervalH1.extension_independent {a b : ℝ} {F D E : ℝ → ℂ}
    (hD : HasIntervalH1 a b F D) (hE : HasIntervalH1 a b F E) (hab : a < b) :
    EqOn (intervalH1Extension a b F E) (intervalH1Extension a b F D) (Icc a b) :=
  hD.extension_unique hab (hE.continuousOn_extension hab) (hE.extension_eq hab)

/-- A membership statement supplies a continuous extension, unique on the closed interval. -/
theorem MemIntervalH1.exists_extension {a b : ℝ} {F : ℝ → ℂ}
    (h : MemIntervalH1 a b F) (hab : a < b) :
    ∃ G : ℝ → ℂ, ContinuousOn G (Icc a b) ∧ EqOn G F (Ioo a b) ∧
      ∀ H : ℝ → ℂ, ContinuousOn H (Icc a b) → EqOn H F (Ioo a b) → EqOn H G (Icc a b) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨intervalH1Extension a b F D, hD.continuousOn_extension hab, hD.extension_eq hab,
    fun _ hH heq ↦ hD.extension_unique hab hH heq⟩

/-- Interval H¹ with zero endpoint traces. This imposes no condition on the raw
    values `F a` and `F b`, only on the canonical continuous extension. -/
def MemIntervalH10 (a b : ℝ) (F : ℝ → ℂ) : Prop :=
  ∃ D, HasIntervalH1 a b F D ∧ intervalH1Extension a b F D a = 0 ∧
    intervalH1Extension a b F D b = 0

/-- Zero-trace H¹ membership includes ordinary H¹ membership. -/
theorem MemIntervalH10.mem {a b : ℝ} {F : ℝ → ℂ} (h : MemIntervalH10 a b F) :
    MemIntervalH1 a b F := by
  obtain ⟨D, hD, _⟩ := h
  exact ⟨D, hD⟩

/-- Zero-trace membership can be tested using any specified H¹ derivative. -/
theorem HasIntervalH1.memH10_iff {a b : ℝ} {F D : ℝ → ℂ}
    (hD : HasIntervalH1 a b F D) (hab : a < b) :
    MemIntervalH10 a b F ↔ intervalH1Extension a b F D a = 0 ∧
      intervalH1Extension a b F D b = 0 := by
  constructor
  · rintro ⟨E, hE, ha, hb⟩
    have heq := hD.extension_independent hE hab
    exact ⟨(heq ⟨le_rfl, hab.le⟩).symm.trans ha, (heq ⟨hab.le, le_rfl⟩).symm.trans hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨D, hD, ha, hb⟩

end NoEmbeddedEigenvalues
