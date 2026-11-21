import NoEmbeddedEigenvalues.Transport.PeriodicComparison.TransportODE

/-!
# Exponential tails and canonical endpoint reconstruction

Blueprint: `lem:exponential-forcing-tails`,
`lem:transport-endpoint-exponential-decay`.

Every positive exponential rate is preserved by integration from the nearer
time endpoint, with the exact factor 1/a. The real oscillation frequency has
no sign or nonvanishing restriction. All endpoints belong to the specified
absolutely continuous function, not to a raw spatial representative.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- A continuous exponential envelope gives an integrable oscillatory product
and its exact exponential antiderivative bound. -/
theorem oscillatory_integral_exp_bound {a b C k : ℝ} {F : ℝ → ℂ}
    (hab : a ≤ b) (hk : k ≠ 0) (hF : ContinuousOn F (Icc a b))
    (hbound : ∀ s ∈ Icc a b, ‖F s‖ ≤ C * exp (k * s)) (lam : ℝ) :
    IntervalIntegrable (fun s ↦ F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)))
      volume a b ∧
    ‖∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
      C / k * (exp (k * b) - exp (k * a)) := by
  have hc : ContinuousOn (fun s ↦ F s *
      Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))) (Icc a b) := hF.mul (by fun_prop)
  have hd (s : ℝ) : HasDerivAt (fun x ↦ C / k * exp (k * x)) (C * exp (k * s)) s := by
    convert! (((hasDerivAt_id s).const_mul k).exp.const_mul (C / k)) using 1
    dsimp
    field_simp
  have hei : IntervalIntegrable (fun s ↦ C * exp (k * s)) volume a b :=
    (show Continuous (fun s ↦ C * exp (k * s)) from by fun_prop).intervalIntegrable _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) hei
  refine ⟨hc.intervalIntegrable_of_Icc hab, ?_⟩
  have hn : ‖∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
      ∫ s in a..b, C * exp (k * s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hei
    exact Eventually.of_forall fun s hs ↦ by
      have hn : ‖Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [norm_mul, hn, mul_one]
      exact hbound s ⟨hs.1.le, hs.2⟩
  rw [hi] at hn
  convert hn using 1
  ring

/-- The integrating factor controls a canonical endpoint by the other
endpoint and the actual oscillatory forcing integral, in either orientation. -/
theorem norm_transport_le_endpoint {lam a b : ℝ} {W F : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval W a b) (hF : IntervalIntegrable F volume a b)
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t) :
    ‖W b‖ ≤ ‖W a‖ +
      ‖∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ := by
  have hi := transport_integratingFactor hac hF (hd.mono fun _ ht _ ↦ ht)
  have hint : (∫ s in a..b, Complex.exp (-(Complex.I * (lam : ℂ) * (s : ℂ))) * F s) =
      ∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show -(Complex.I * (lam : ℂ) * (s : ℂ)) =
      -Complex.I * ((lam * s : ℝ) : ℂ) by push_cast; ring, mul_comm]
  rw [hint] at hi
  calc ‖W b‖ = ‖Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b‖ := by
        rw [norm_mul, norm_exp_neg_I_mul, one_mul]
       _ = ‖(Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b -
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a) +
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ := by
        rw [sub_add_cancel]
       _ ≤ ‖Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b -
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ +
          ‖Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ := norm_add_le _ _
       _ = _ := by
        rw [hi, norm_mul, Complex.norm_I, one_mul, norm_mul, norm_exp_neg_I_mul, one_mul]
        ring

/-- Oscillatory tails preserve any positive exponential decay rate. Actual
integrability and constants independent of the real frequency are explicit. -/
theorem forcing_exp_decay_tail_bounds {L C a : ℝ} {F : ℝ → ℂ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (ha : 0 < a)
    (hF : ContinuousOn F (Icc (-L) L))
    (hbound : ∀ t, |t| ≤ L → ‖F t‖ ≤ C * exp (-a * |t|)) (lam : ℝ) :
    (∀ t ∈ Icc (-L) 0,
      IntervalIntegrable (fun s ↦ F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)))
        volume (-L) t ∧
      ‖∫ s in (-L)..t, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
        (C / a) * exp (a * t)) ∧
    (∀ t ∈ Icc 0 L,
      IntervalIntegrable (fun s ↦ F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)))
        volume t L ∧
      ‖∫ s in t..L, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
        (C / a) * exp (-a * t)) := by
  constructor
  · intro t ht
    obtain ⟨hi, hb⟩ := oscillatory_integral_exp_bound ht.1 ha.ne'
      (hF.mono (Icc_subset_Icc le_rfl (ht.2.trans hL)))
      (fun s hs ↦ by
        have hb := hbound s (abs_le.2 ⟨hs.1, hs.2.trans (ht.2.trans hL)⟩)
        simpa only [abs_of_nonpos (hs.2.trans ht.2), neg_mul_neg] using hb) lam
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (exp_pos _).le) (div_nonneg hC ha.le))⟩
  · intro t ht
    obtain ⟨hi, hb⟩ := oscillatory_integral_exp_bound (k := -a) ht.2 (neg_ne_zero.mpr ha.ne')
      (hF.mono (Icc_subset_Icc (by linarith [ht.1]) le_rfl))
      (fun s hs ↦ by
        simpa only [abs_of_nonneg (ht.1.trans hs.1)] using
          hbound s (abs_le.2 ⟨by linarith [ht.1, hs.1], hs.2⟩)) lam
    have he : C / (-a) * (exp (-a * L) - exp (-a * t)) =
        (C / a) * (exp (-a * t) - exp (-a * L)) := by rw [div_neg]; ring
    rw [he] at hb
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (exp_pos _).le) (div_nonneg hC ha.le))⟩

/-- Canonical ACL transport reconstruction retains any positive exponential
forcing rate by integrating from the nearer canonical endpoint. -/
theorem norm_transport_le_endpoints_of_exp_decay {lam L C A a : ℝ} {W F : ℝ → ℂ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (ha : 0 < a)
    (hF : ContinuousOn F (Icc (-L) L))
    (hdecay : ∀ t, |t| ≤ L → ‖F t‖ ≤ C * exp (-a * |t|))
    (hac : ∀ x y, AbsolutelyContinuousOnInterval W x y)
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t)
    (hleft : ‖W (-L)‖ ≤ A) (hright : ‖W L‖ ≤ A) :
    ∀ t, |t| ≤ L → ‖W t‖ ≤ A + (C / a) * exp (-a * |t|) := by
  obtain ⟨hneg, hpos⟩ := forcing_exp_decay_tail_bounds hL hC ha hF hdecay lam
  intro t ht
  have htI := abs_le.1 ht
  rcases le_total t 0 with ht0 | ht0
  · have hiF : IntervalIntegrable F volume (-L) t :=
      (hF.mono (Icc_subset_Icc le_rfl htI.2)).intervalIntegrable_of_Icc htI.1
    have hn := norm_transport_le_endpoint (hac (-L) t) hiF hd
    have hb := hn.trans (add_le_add hleft (hneg t ⟨htI.1, ht0⟩).2)
    simpa only [abs_of_nonpos ht0, neg_mul_neg] using hb
  · have hiF : IntervalIntegrable F volume L t :=
      ((hF.mono (Icc_subset_Icc htI.1 le_rfl)).intervalIntegrable_of_Icc htI.2).symm
    have hn := norm_transport_le_endpoint (hac L t) hiF hd
    rw [intervalIntegral.integral_symm, norm_neg] at hn
    have hb := hn.trans (add_le_add hright (hpos t ⟨ht0, htI.2⟩).2)
    simpa only [abs_of_nonneg ht0] using hb

end NoEmbeddedEigenvalues
