module

public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.IntervalZeroExtension
public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.IntervalH1WeakLift

/-!
# Integration by parts with canonical interval traces

Blueprint: `lem:interval-trace-integration`.

The closed-interval extension is an absolutely continuous integral primitive.
Its endpoint values, rather than the raw endpoint assignments, are the boundary
terms used to glue transverse weak derivatives.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Integration by parts for H¹ data, with canonical traces at both endpoints. -/
theorem HasIntervalH1.integral_mul_deriv {a b : ℝ} {F D β : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hβ : ContDiff ℝ 1 β) :
    (∫ x in Ioo a b, F x * deriv β x) =
      intervalH1Extension a b F D b * β b -
      intervalH1Extension a b F D a * β a - ∫ x in Ioo a b, D x * β x := by
  let E := intervalH1Extension a b F D
  have hAC : AbsolutelyContinuousOnInterval E a b := by
    have hP := absolutelyContinuous_complex_primitive h.integrable_zeroExtension_derivative
      ((a + b) / 2) a b
    have hC : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ F ((a + b) / 2)) a b :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    apply (hC.add hP).congr
    intro x hx
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hx
    have hm : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
    simp only [Pi.add_apply, E, intervalH1Extension]
    rw [intervalIntegral_intervalZeroExtension D hm hx']
  have hder : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt E (D x) x := by
    filter_upwards [h.hasDerivAt_ae, volume.ae_ne a, volume.ae_ne b] with x hx hxa hxb hxI
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hxI
    have hxo : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx'.1 hxa.symm, lt_of_le_of_ne hx'.2 hxb⟩
    apply (hx hxo).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hy
    exact h.extension_eq hab hy
  have hDi : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 h.integrableOn_derivative
  have hi := integral_mul_deriv_of_ac hab.le hAC hDi hder hβ
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [show E x = F x from h.extension_eq hab hx]

end EulerDipoleEigenvalues
