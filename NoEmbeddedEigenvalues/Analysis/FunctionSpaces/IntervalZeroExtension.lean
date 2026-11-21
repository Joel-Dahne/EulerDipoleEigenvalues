module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Zero extension of interval H¹ data

Blueprint: `def:interval-zero-extension`, `lem:interval-zero-extension-l2`,
`lem:h1-zero-extension`.

Zero traces allow the interval representative to be extended by zero without
introducing endpoint jumps. The extension is an integral primitive of the
zero-extended derivative, hence absolutely continuous on every bounded interval.
This is first-order infrastructure; no second-order extension or mollification
is asserted here.

The complex primitive and elementary zero-extension helpers are also used by
`TraceH2.lean`. A square-integrable increment identity recovers local absolute
continuity and the specified a.e. derivative.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Interval Topology

/-- Extend the interior values by zero, ignoring the raw endpoint values. -/
def intervalZeroExtension (a b : ℝ) (F : ℝ → ℂ) : ℝ → ℂ :=
  (Ioo a b).indicator F

/-- Zero extension turns interval L² data into global L² data. -/
theorem memLp_intervalZeroExtension {a b : ℝ} {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b))) :
    MemLp (intervalZeroExtension a b F) 2 volume :=
  (memLp_indicator_iff_restrict (measurableSet_Ioo.nullMeasurableSet (μ := volume))).mpr hF

/-- On a bounded interval, zero-extended L² data are globally integrable too. -/
theorem integrable_intervalZeroExtension {a b : ℝ} {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b))) :
    Integrable (intervalZeroExtension a b F) := by
  have hi : IntegrableOn F (Ioo a b) := hF.integrable (by norm_num)
  exact hi.integrable_indicator measurableSet_Ioo

/-- The topological support of the zero extension lies in the closed interval. -/
theorem tsupport_intervalZeroExtension_subset (a b : ℝ) (F : ℝ → ℂ) :
    tsupport (intervalZeroExtension a b F) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  apply hx
  exact indicator_of_notMem (s := Ioo a b) (fun hi ↦ hn (Ioo_subset_Icc_self hi)) F

/-- The zero extension has compact support, even without regularity assumptions. -/
theorem hasCompactSupport_intervalZeroExtension (a b : ℝ) (F : ℝ → ℂ) :
    HasCompactSupport (intervalZeroExtension a b F) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (tsupport_intervalZeroExtension_subset a b F)

/-- Zero extension preserves the squared L² integral on an ordered interval. -/
theorem integral_sq_intervalZeroExtension {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℂ) :
    (∫ x : ℝ, ‖intervalZeroExtension a b F x‖ ^ 2) = ∫ x in a..b, ‖F x‖ ^ 2 := by
  have heq : (fun x ↦ ‖intervalZeroExtension a b F x‖ ^ 2) =
      (Ioo a b).indicator (fun x ↦ ‖F x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioo a b <;> simp [intervalZeroExtension, hx]
  rw [heq, integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]

/-- On interior subintervals including their endpoints, extension changes no integral. -/
theorem intervalIntegral_intervalZeroExtension {a b c d : ℝ} (F : ℝ → ℂ)
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    (∫ x in c..d, intervalZeroExtension a b F x) = ∫ x in c..d, F x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a, volume.ae_ne b] with x hxa hxb hx
  have hi : x ∈ Icc a b := uIcc_subset_Icc hc hd (uIoc_subset_uIcc hx)
  exact indicator_of_mem (s := Ioo a b)
    ⟨lt_of_le_of_ne hi.1 hxa.symm, lt_of_le_of_ne hi.2 hxb⟩ F

/-- Absolute continuity of a complex integral primitive on any bounded interval.
    The real-valued Mathlib theorem is applied to its real and imaginary parts. -/
theorem absolutelyContinuous_complex_primitive {D : ℝ → ℂ} (hD : Integrable D)
    (a c d : ℝ) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in a..x, D t) c d := by
  have hr := hD.re.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : c ∈ uIcc c d)
  have hi := hD.im.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : c ∈ uIcc c d)
  have hbase : AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in c..x, D t) c d := by
    apply ((ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hr).add
      ((ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hi).const_smul I)).congr
    intro x _
    simp only [Pi.add_apply, Function.comp_apply, smul_eq_mul, ofRealCLM_apply,
      RCLike.re_eq_complex_re, RCLike.im_eq_complex_im]
    have hrEq : (∫ t in c..x, (D t).re) = (∫ t in c..x, D t).re :=
      reCLM.intervalIntegral_comp_comm hD.intervalIntegrable
    have hiEq : (∫ t in c..x, (D t).im) = (∫ t in c..x, D t).im :=
      imCLM.intervalIntegral_comp_comm hD.intervalIntegrable
    rw [hrEq, hiEq]
    simpa only [mul_comm] using Complex.re_add_im (∫ t in c..x, D t)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ ∫ t in a..c, D t) c d :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (hconst.add hbase).congr (fun x _ ↦
    intervalIntegral.integral_add_adjacent_intervals hD.intervalIntegrable hD.intervalIntegrable)

/-- The extended derivative is globally integrable as well as square integrable. -/
theorem HasIntervalH1.integrable_zeroExtension_derivative {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) : Integrable (intervalZeroExtension a b D) :=
  integrable_intervalZeroExtension h.memLp_derivative

/-- Zero traces identify the zero extension with an integral primitive globally. -/
theorem HasIntervalH1.zeroExtension_eq_integral {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0)
    (hb : intervalH1Extension a b F D b = 0) (x : ℝ) :
    intervalZeroExtension a b F x = ∫ t in a..x, intervalZeroExtension a b D t := by
  have hDi := h.integrable_zeroExtension_derivative
  by_cases hxa : x ≤ a
  · have hz : (∫ t in a..x, intervalZeroExtension a b D t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      refine Eventually.of_forall (fun t ht ↦ ?_)
      have ht' : t ∈ Icc x a := by simpa only [uIcc_of_ge hxa] using uIoc_subset_uIcc ht
      exact indicator_of_notMem (s := Ioo a b) (fun hi ↦ (not_lt_of_ge ht'.2) hi.1) D
    rw [hz]
    exact indicator_of_notMem (s := Ioo a b) (fun hi ↦ (not_lt_of_ge hxa) hi.1) F
  · have hax : a < x := lt_of_not_ge hxa
    by_cases hxb : x < b
    · rw [show intervalZeroExtension a b F x = F x from
          indicator_of_mem (s := Ioo a b) ⟨hax, hxb⟩ F,
        intervalIntegral_intervalZeroExtension D ⟨le_rfl, hab.le⟩ ⟨hax.le, hxb.le⟩,
        h.integral_eq_extension_sub hab ⟨le_rfl, hab.le⟩ ⟨hax.le, hxb.le⟩,
        ha, sub_zero, h.extension_eq hab ⟨hax, hxb⟩]
    · have hbx : b ≤ x := le_of_not_gt hxb
      have hz : (∫ t in b..x, intervalZeroExtension a b D t) = 0 := by
        apply intervalIntegral.integral_zero_ae
        refine Eventually.of_forall (fun t ht ↦ ?_)
        have ht' : t ∈ Ioc b x := by simpa only [uIoc_of_le hbx] using ht
        exact indicator_of_notMem (s := Ioo a b) (fun hi ↦ (not_lt_of_ge ht'.1.le) hi.2) D
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hDi.intervalIntegrable (a := a) (b := b)) (hDi.intervalIntegrable (a := b) (b := x)),
        hz, add_zero, intervalIntegral_intervalZeroExtension D ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩,
        h.integral_eq_extension_sub hab ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩, ha, hb, sub_self]
      exact indicator_of_notMem (s := Ioo a b) (fun hi ↦ (not_lt_of_ge hbx) hi.2) F

/-- Zero traces prevent jumps: the extension is absolutely continuous on every
    bounded interval, including intervals crossing the original endpoints. -/
theorem HasIntervalH1.absolutelyContinuous_zeroExtension {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0)
    (hb : intervalH1Extension a b F D b = 0) (c d : ℝ) :
    AbsolutelyContinuousOnInterval (intervalZeroExtension a b F) c d :=
  (absolutelyContinuous_complex_primitive h.integrable_zeroExtension_derivative a c d).congr
    (fun x _ ↦ (h.zeroExtension_eq_integral hab ha hb x).symm)

/-- Zero traces also give continuity of the extension on the whole real line. -/
theorem HasIntervalH1.continuous_zeroExtension {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0)
    (hb : intervalH1Extension a b F D b = 0) :
    Continuous (intervalZeroExtension a b F) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (h.absolutelyContinuous_zeroExtension hab ha hb (x - 1) (x + 1)).continuousOn.continuousAt
  rw [uIcc_of_le (by linarith : x - 1 ≤ x + 1)]
  exact Icc_mem_nhds (by linarith) (by linarith)

/-- Away from the two measure-zero endpoints, zero extension commutes with the
    a.e. derivative. This statement alone does not require zero traces. -/
theorem HasIntervalH1.hasDerivAt_zeroExtension_ae {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) :
    ∀ᵐ x, HasDerivAt (intervalZeroExtension a b F) (intervalZeroExtension a b D x) x := by
  filter_upwards [h.hasDerivAt_ae, volume.ae_ne a, volume.ae_ne b] with x hx hxa hxb
  by_cases hi : x ∈ Ioo a b
  · have heq : intervalZeroExtension a b F =ᶠ[𝓝 x] F := by
      filter_upwards [isOpen_Ioo.mem_nhds hi] with y hy
      exact indicator_of_mem hy F
    simpa only [intervalZeroExtension, indicator_of_mem hi] using
      (hx hi).congr_of_eventuallyEq heq
  · have ho : x ∈ (Icc a b)ᶜ := by
      intro hcc
      exact hi ⟨lt_of_le_of_ne hcc.1 hxa.symm, lt_of_le_of_ne hcc.2 hxb⟩
    have heq : intervalZeroExtension a b F =ᶠ[𝓝 x] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ho] with y hy
      exact indicator_of_notMem (s := Ioo a b) (fun hm ↦ hy (Ioo_subset_Icc_self hm)) F
    rw [show intervalZeroExtension a b D x = 0 from indicator_of_notMem hi D]
    exact (hasDerivAt_const x 0).congr_of_eventuallyEq heq

/-- The zero extension of zero-trace H¹ data gives H¹ data on every bounded interval. -/
theorem HasIntervalH1.zeroExtension {a b : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b)
    (ha : intervalH1Extension a b F D a = 0)
    (hb : intervalH1Extension a b F D b = 0) (c d : ℝ) :
    HasIntervalH1 c d (intervalZeroExtension a b F) (intervalZeroExtension a b D) where
  memLp_value := (memLp_intervalZeroExtension h.memLp_value).mono_measure Measure.restrict_le_self
  memLp_derivative :=
    (memLp_intervalZeroExtension h.memLp_derivative).mono_measure Measure.restrict_le_self
  locally_absolutelyContinuous u v _ _ _ := h.absolutelyContinuous_zeroExtension hab ha hb u v
  hasDerivAt_ae := h.hasDerivAt_zeroExtension_ae.mono (fun _ hx _ ↦ hx)

/-- An integral increment identity with an L² right side gives local absolute
continuity and the specified a.e. derivative, without smooth approximation. -/
theorem locally_ac_of_integral_eq {a₀ a₁ : ℝ} {F D : ℝ → ℂ} (ha : a₀ < a₁)
    (hD : MemLp D 2 (volume.restrict (Ioo a₀ a₁)))
    (hFTC : ∀ c ∈ Ioo a₀ a₁, ∀ d ∈ Ioo a₀ a₁, (∫ a in c..d, D a) = F d - F c) :
    (∀ c d, a₀ < c → c ≤ d → d < a₁ → AbsolutelyContinuousOnInterval F c d) ∧
      ∀ᵐ a ∂(volume.restrict (Ioo a₀ a₁)), HasDerivAt F (D a) a := by
  let m := (a₀ + a₁) / 2
  have hm : m ∈ Ioo a₀ a₁ := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hi : IntervalIntegrable D volume a₀ a₁ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).2 (hD.integrable (by norm_num))
  let P := fun x ↦ F m + ∫ a in m..x, D a
  have hPF : EqOn P F (Ioo a₀ a₁) := by
    intro x hx
    dsimp [P]
    rw [hFTC m hm x hx]
    abel
  have hmcc : m ∈ uIcc a₀ a₁ := by
    simpa only [uIcc_of_le ha.le] using Ioo_subset_Icc_self hm
  have hprim : AbsolutelyContinuousOnInterval (fun x ↦ ∫ a in m..x, D a) a₀ a₁ := by
    apply (absolutelyContinuous_complex_primitive (integrable_intervalZeroExtension hD)
      m a₀ a₁).congr
    intro x hx
    rw [uIcc_of_le ha.le] at hx hmcc
    exact intervalIntegral_intervalZeroExtension D hmcc hx
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ F m) a₀ a₁ :=
    (LipschitzWith.const (F m)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hPac : AbsolutelyContinuousOnInterval P a₀ a₁ := hconst.add hprim
  refine ⟨?_, ?_⟩
  · intro c d hc hcd hd
    have hsub : uIcc c d ⊆ Ioo a₀ a₁ := by
      rw [uIcc_of_le hcd]
      exact Icc_subset_Ioo hc hd
    exact (hPac.mono (by
      rw [uIcc_of_le ha.le]
      exact hsub.trans Ioo_subset_Icc_self)).congr (fun x hx ↦ hPF (hsub hx))
  · filter_upwards [ae_restrict_of_ae hi.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hp := (hx (by simpa only [uIcc_of_le ha.le] using Ioo_subset_Icc_self hxI)
      m hmcc).const_add (F m)
    apply hp.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
    exact (hPF hy).symm

end NoEmbeddedEigenvalues
