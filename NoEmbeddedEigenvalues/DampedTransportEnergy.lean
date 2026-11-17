import NoEmbeddedEigenvalues.TransportODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Dissipative energy for complex transport

Blueprint: `lem:damped-transport-energy`, `lem:transport-weighted-endpoint-energy`.

A positive real damping controls the interval L² energy independently of the
real oscillation frequency. Absolute continuity supplies genuine integrability
of the unknown before the energy identity is used. Boundary values are those
of the specified absolutely continuous function.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- A damped complex transport equation has an L² energy bound independent of
its real frequency. No zero initial value is required. -/
theorem damped_transport_energy {a b c lam : ℝ} {W G : ℝ → ℂ}
    (hab : a ≤ b) (hc : 0 < c)
    (hW : AbsolutelyContinuousOnInterval W a b)
    (hG : MemLp G 2 (volume.restrict (Icc a b)))
    (hd : ∀ᵐ t, t ∈ Icc a b →
      HasDerivAt W (Complex.I * (lam : ℂ) * W t - (c : ℂ) * W t + G t) t) :
    IntegrableOn (fun t ↦ ‖W t‖ ^ 2) (Icc a b) ∧
      (∫ t in Icc a b, ‖W t‖ ^ 2) ≤
        ‖W a‖ ^ 2 / c + (∫ t in Icc a b, ‖G t‖ ^ 2) / c ^ 2 := by
  let E : ℝ → ℝ := fun t ↦ (W t).re ^ 2 + (W t).im ^ 2
  have hre : AbsolutelyContinuousOnInterval (fun t ↦ (W t).re) a b :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hW
  have him : AbsolutelyContinuousOnInterval (fun t ↦ (W t).im) a b :=
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hW
  have hE : AbsolutelyContinuousOnInterval E a b := by
    apply ((hre.fun_mul hre).add (him.fun_mul him)).congr
    intro t _
    simp [E, pow_two]
  have hEn (t : ℝ) : E t = ‖W t‖ ^ 2 := by
    simpa [E, Complex.normSq_apply, pow_two] using (Complex.sq_norm (W t)).symm
  have hWi : IntegrableOn (fun t ↦ ‖W t‖ ^ 2) (Icc a b) := by
    simpa only [← hEn] using
      (hE.continuousOn.mono (by rw [uIcc_of_le hab])).integrableOn_Icc
  have hGi := hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hder : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      deriv E t ≤ ‖G t‖ ^ 2 / c - c * ‖W t‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc] with t ht htI
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht htI)
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht htI)
    have he := (hr.pow 2).add (hi.pow 2)
    have he' : deriv E t =
        2 * (W t).re * (-lam * (W t).im - c * (W t).re + (G t).re) +
        2 * (W t).im * (lam * (W t).re - c * (W t).im + (G t).im) := by
      convert he.deriv using 1
      · congr 1
      · simp [Complex.mul_re, Complex.mul_im]
    rw [he', ← hEn, Complex.sq_norm, Complex.normSq_apply]
    apply (le_sub_iff_add_le).2
    apply (le_div_iff₀ hc).2
    dsimp [E]
    nlinarith [sq_nonneg (c * (W t).re - (G t).re),
      sq_nonneg (c * (W t).im - (G t).im)]
  have hDi : IntegrableOn (deriv E) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hE.intervalIntegrable_deriv
  have hFTC : (∫ t in Icc a b, deriv E t) = E b - E a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact hE.integral_deriv_eq_sub
  have hbound := integral_mono_ae hDi ((hGi.div_const c).sub (hWi.const_mul c)) hder
  dsimp only [Pi.sub_apply] at hbound
  rw [hFTC, integral_sub (hGi.div_const c) (hWi.const_mul c), integral_div,
    integral_const_mul, hEn, hEn] at hbound
  refine ⟨hWi, ?_⟩
  calc
    _ ≤ (‖W a‖ ^ 2 + (∫ t in Icc a b, ‖G t‖ ^ 2) / c) / c := by
      apply (le_div_iff₀ hc).2
      nlinarith [sq_nonneg ‖W b‖]
    _ = _ := by field_simp

/-- Exponential-weighted canonical transport energy from the left endpoint.
The forcing is controlled in weighted L², not by a pointwise envelope. -/
theorem transport_left_weighted_energy {a b c lam : ℝ} {W F : ℝ → ℂ}
    (hab : a ≤ b) (hc : 0 < c)
    (hW : AbsolutelyContinuousOnInterval W a b)
    (hF : MemLp (fun t ↦ (exp (-c * t) : ℂ) * F t) 2
      (volume.restrict (Icc a b)))
    (hd : ∀ᵐ t, t ∈ Icc a b →
      HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t) :
    IntegrableOn (fun t ↦ exp (-(2 * c) * t) * ‖W t‖ ^ 2) (Icc a b) ∧
      (∫ t in Icc a b, exp (-(2 * c) * t) * ‖W t‖ ^ 2) ≤
        exp (-(2 * c) * a) * ‖W a‖ ^ 2 / c +
        (∫ t in Icc a b, exp (-(2 * c) * t) * ‖F t‖ ^ 2) / c ^ 2 := by
  let e : ℝ → ℂ := fun t ↦ (exp (-c * t) : ℂ)
  have he : ContDiff ℝ 1 e :=
    Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ 1 (fun t : ℝ ↦ exp (-c * t)) from by fun_prop)
  have he' (t : ℝ) : HasDerivAt e (-(c : ℂ) * e t) t := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).const_mul (-c)).exp) using 1 <;>
      simp [e, Function.comp_def, mul_comm]
  have hn (H : ℝ → ℂ) (t : ℝ) :
      ‖e t * H t‖ ^ 2 = exp (-(2 * c) * t) * ‖H t‖ ^ 2 := by
    simp only [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _), mul_pow]
    rw [← exp_nat_mul]
    congr 2
    ring
  have hY : AbsolutelyContinuousOnInterval (fun t ↦ e t * W t) a b :=
    he.contDiffOn.absolutelyContinuousOnInterval.fun_smul hW
  have hG : MemLp (fun t ↦ Complex.I * (e t * F t)) 2
      (volume.restrict (Icc a b)) := hF.const_mul Complex.I
  have hder : ∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t ↦ e t * W t)
      (Complex.I * (lam : ℂ) * (e t * W t) - (c : ℂ) * (e t * W t) +
        Complex.I * (e t * F t)) t := by
    filter_upwards [hd] with t ht htI
    convert (he' t).mul (ht htI) using 1
    ring
  obtain ⟨hi, hb⟩ := damped_transport_energy hab hc hY hG hder
  have hgn (t : ℝ) : ‖Complex.I * (e t * F t)‖ ^ 2 =
      exp (-(2 * c) * t) * ‖F t‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, hn]
  simp_rw [hn, hgn] at hi hb
  exact ⟨hi, hb⟩

/-- The right-endpoint counterpart uses the growing exponential weight.
Reflection reverses the frequency and forcing, but introduces no sign restriction. -/
theorem transport_right_weighted_energy {a b c lam : ℝ} {W F : ℝ → ℂ}
    (hab : a ≤ b) (hc : 0 < c)
    (hW : AbsolutelyContinuousOnInterval W a b)
    (hF : MemLp (fun t ↦ (exp (c * t) : ℂ) * F t) 2
      (volume.restrict (Icc a b)))
    (hd : ∀ᵐ t, t ∈ Icc a b →
      HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t) :
    IntegrableOn (fun t ↦ exp ((2 * c) * t) * ‖W t‖ ^ 2) (Icc a b) ∧
      (∫ t in Icc a b, exp ((2 * c) * t) * ‖W t‖ ^ 2) ≤
        exp ((2 * c) * b) * ‖W b‖ ^ 2 / c +
        (∫ t in Icc a b, exp ((2 * c) * t) * ‖F t‖ ^ 2) / c ^ 2 := by
  have hpre : (fun t : ℝ ↦ -t) ⁻¹' Icc a b = Icc (-b) (-a) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hneg : MeasurePreserving (fun t : ℝ ↦ -t)
      (volume.restrict (Icc (-b) (-a))) (volume.restrict (Icc a b)) := by
    rw [← hpre]
    exact (Measure.measurePreserving_neg volume).restrict_preimage measurableSet_Icc
  have hWF : AbsolutelyContinuousOnInterval (fun t ↦ W (-t)) (-b) (-a) := by
    apply AbsolutelyContinuousOnInterval.comp_antitoneOn hW (K := 1)
      LipschitzWith.id.neg.lipschitzOnWith
      (fun x _ y _ h ↦ neg_le_neg h)
    intro t ht
    rw [uIcc_of_le (neg_le_neg hab)] at ht
    rw [uIcc_of_le hab]
    change a ≤ -t ∧ -t ≤ b
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hFF : MemLp (fun t ↦ (exp (-c * t) : ℂ) * (-F (-t))) 2
      (volume.restrict (Icc (-b) (-a))) := by
    convert (hF.comp_measurePreserving hneg).neg using 1
    funext t
    simp [Function.comp_def, mul_neg, neg_mul]
  have hDF : ∀ᵐ t, t ∈ Icc (-b) (-a) → HasDerivAt (fun t ↦ W (-t))
      (Complex.I * (((-lam : ℝ) : ℂ) * W (-t) + (-F (-t)))) t := by
    have hd' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hd
    filter_upwards [hd'] with t ht htI
    have ht' : -t ∈ Icc a b := ⟨by linarith [htI.2], by linarith [htI.1]⟩
    convert (ht ht').scomp t (hasDerivAt_neg t) using 1
    · simp [Function.comp_def]
    · simp
      ring
  obtain ⟨_, hbound⟩ := transport_left_weighted_energy (neg_le_neg hab) hc hWF hFF hDF
  have hInt (H : ℝ → ℝ) : (∫ t in Icc (-b) (-a), H (-t)) = ∫ t in Icc a b, H t := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (neg_le_neg hab), intervalIntegral.integral_comp_neg]
    simp only [neg_neg]
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have hJ (H : ℝ → ℂ) :
      (∫ t in Icc (-b) (-a), exp (-(2 * c) * t) * ‖H (-t)‖ ^ 2) =
        ∫ t in Icc a b, exp ((2 * c) * t) * ‖H t‖ ^ 2 := by
    convert hInt (fun t ↦ exp ((2 * c) * t) * ‖H t‖ ^ 2) using 1
    congr 1
    funext t
    rw [mul_neg, neg_mul]
  simp only [norm_neg] at hbound
  rw [hJ W, hJ F] at hbound
  refine ⟨?_, by simpa only [neg_mul_neg, neg_neg] using hbound⟩
  exact ((show Continuous (fun t : ℝ ↦ exp ((2 * c) * t)) from by fun_prop).continuousOn.mul
    ((hW.continuousOn.mono (by rw [uIcc_of_le hab])).norm.pow 2)).integrableOn_Icc

/-- Two canonical endpoint norms and the forcing's genuine exponential L²
mass control the unknown's exponential L² mass. No pointwise forcing decay
is assumed, and the estimate is uniform in the real transport frequency. -/
theorem transport_weighted_endpoint_energy {L c lam A : ℝ} {W F : ℝ → ℂ}
    (hL : 0 ≤ L) (hc : 0 < c)
    (hW : ∀ a b, AbsolutelyContinuousOnInterval W a b)
    (hF : MemLp (fun t ↦ (exp (c * |t|) : ℂ) * F t) 2
      (volume.restrict (Icc (-L) L)))
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t)
    (hleft : ‖W (-L)‖ ≤ A) (hright : ‖W L‖ ≤ A) :
    IntegrableOn (fun t ↦ exp ((2 * c) * |t|) * ‖W t‖ ^ 2) (Icc (-L) L) ∧
      (∫ t in Icc (-L) L, exp ((2 * c) * |t|) * ‖W t‖ ^ 2) ≤
        2 * exp ((2 * c) * L) * A ^ 2 / c +
        (∫ t in Icc (-L) L, exp ((2 * c) * |t|) * ‖F t‖ ^ 2) / c ^ 2 := by
  have hn : Icc (-L) 0 ⊆ Icc (-L) L := Icc_subset_Icc le_rfl hL
  have hp : Icc 0 L ⊆ Icc (-L) L := Icc_subset_Icc (by linarith) le_rfl
  have hFn : MemLp (fun t ↦ (exp (-c * t) : ℂ) * F t) 2
      (volume.restrict (Icc (-L) 0)) := by
    apply (hF.mono_measure (Measure.restrict_mono_set _ hn)).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [abs_of_nonpos ht.2]
  have hFp : MemLp (fun t ↦ (exp (c * t) : ℂ) * F t) 2
      (volume.restrict (Icc 0 L)) := by
    apply (hF.mono_measure (Measure.restrict_mono_set _ hp)).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [abs_of_nonneg ht.1]
  obtain ⟨hiN, heN⟩ := transport_left_weighted_energy (by linarith : -L ≤ 0) hc
    (hW (-L) 0) hFn (hd.mono fun _ ht _ ↦ ht)
  obtain ⟨hiP, heP⟩ := transport_right_weighted_energy hL hc
    (hW 0 L) hFp (hd.mono fun _ ht _ ↦ ht)
  let E (H : ℝ → ℂ) : ℝ → ℝ := fun t ↦ exp ((2 * c) * |t|) * ‖H t‖ ^ 2
  have hEn (H : ℝ → ℂ) : E H =ᵐ[volume.restrict (Icc (-L) 0)]
      (fun t ↦ exp (-(2 * c) * t) * ‖H t‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [E, abs_of_nonpos ht.2]
  have hEp (H : ℝ → ℂ) : E H =ᵐ[volume.restrict (Icc 0 L)]
      (fun t ↦ exp ((2 * c) * t) * ‖H t‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [E, abs_of_nonneg ht.1]
  have hiN' : IntegrableOn (E W) (Icc (-L) 0) := hiN.congr (hEn W).symm
  have hiP' : IntegrableOn (E W) (Icc 0 L) := hiP.congr (hEp W).symm
  have hsplit (H : ℝ → ℝ) (hN : IntegrableOn H (Icc (-L) 0))
      (hP : IntegrableOn H (Icc 0 L)) :
      (∫ t in Icc (-L) L, H t) =
        (∫ t in Icc (-L) 0, H t) + ∫ t in Icc 0 L, H t := by
    simp only [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -L ≤ L),
      ← intervalIntegral.integral_of_le (by linarith : -L ≤ 0),
      ← intervalIntegral.integral_of_le hL]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -L ≤ 0)).2 hN)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hL).2 hP)).symm
  have hFi : IntegrableOn (E F) (Icc (-L) L) := by
    apply (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    apply Eventually.of_forall
    intro t
    simp only [E, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _), mul_pow]
    rw [← exp_nat_mul]
    congr 2
    ring
  refine ⟨(hiN'.union hiP').mono_set ?_, ?_⟩
  · intro t ht
    rcases le_total t 0 with ht0 | ht0
    · exact Or.inl ⟨ht.1, ht0⟩
    · exact Or.inr ⟨ht0, ht.2⟩
  · change (∫ t in Icc (-L) L, E W t) ≤ _
    rw [hsplit (E W) hiN' hiP', hsplit (E F) (hFi.mono_set hn) (hFi.mono_set hp),
      integral_congr_ae (hEn W), integral_congr_ae (hEp W),
      integral_congr_ae (hEn F), integral_congr_ae (hEp F)]
    have hA : 0 ≤ A := (norm_nonneg _).trans hleft
    have hsN := (sq_le_sq₀ (norm_nonneg _) hA).2 hleft
    have hsP := (sq_le_sq₀ (norm_nonneg _) hA).2 hright
    simp only [neg_mul_neg] at heN
    have hends : exp ((2 * c) * L) * (‖W (-L)‖ ^ 2 + ‖W L‖ ^ 2) ≤
        2 * exp ((2 * c) * L) * A ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hsN hsP) (exp_pos ((2 * c) * L)).le]
    have hsum := add_le_add heN heP
    have hend := div_le_div_of_nonneg_right hends hc.le
    simp only [mul_add, add_div] at hend ⊢
    linarith

end NoEmbeddedEigenvalues
