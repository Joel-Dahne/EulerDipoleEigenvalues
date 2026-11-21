module

public import NoEmbeddedEigenvalues.Transport.PeriodicComparison.PairingLimit
public import NoEmbeddedEigenvalues.Transport.WeightedGains.TransportRotations
public import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix.MixedQuotient
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedVirialBulk

/-! # Recombining the two imaginary rotation characters -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate

local notation "Plane" => ℝ × ℝ

private def pair (v f : ℂ) : ℝ := (v * conj f).re

private theorem pair_add (v w f g : ℂ) :
    pair (v + w) (f + g) = pair v f + pair w g + (pair v g + pair w f) := by
  simp only [pair, map_add, mul_add, add_mul, Complex.add_re]
  ring

private theorem pair_char_add (v w f g : ℂ) :
    pair (I * v) (-I * g) + pair (-I * w) (I * f) =
      -(pair v g + pair w f) := by
  simp only [pair, map_mul, map_neg, Complex.conj_I]
  have e (z y : ℂ) : I * z * (- -I * conj y) = -(z * conj y) := by
    linear_combination z * conj y * Complex.I_sq
  have e' (z y : ℂ) : -I * z * (-I * conj y) = -(z * conj y) := by
    linear_combination z * conj y * Complex.I_sq
  rw [e, e', Complex.neg_re, Complex.neg_re]
  ring

private theorem intervalIntegral_eq_zero_of_add_eq_neg {C : ℝ → ℝ} {T : ℝ}
    (hc : Continuous C) (hodd : ∀ t, C (t + T) = -C t) :
    (∫ t in (0 : ℝ)..4 * T, C t) = 0 := by
  have hp : Function.Periodic C (2 * T) := fun t ↦ by
    rw [show t + 2 * T = t + T + T by ring, hodd, hodd, neg_neg]
  have h0 : (∫ t in (0 : ℝ)..2 * T, C t) = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 T) (hc.intervalIntegrable T (2 * T))]
    have h := intervalIntegral.integral_comp_add_right C T (a := 0) (b := T)
    simp_rw [hodd] at h
    rw [intervalIntegral.integral_neg, zero_add, ← two_mul] at h
    rw [← h, add_neg_cancel]
  have h := hp.intervalIntegral_add_zsmul_eq 2 0 (fun a b ↦ hc.intervalIntegrable a b)
  convert h.trans (show (2 : ℤ) • (∫ t in (0 : ℝ)..0 + 2 * T, C t) = 0 by
    rw [zero_add, h0, smul_zero]) using 2
  norm_num
  ring

private theorem period_pair_sum {T : ℝ} {v w f g : ℝ → ℂ}
    (hv : Continuous v) (hw : Continuous w) (hf : Continuous f) (hg : Continuous g)
    (hvR : ∀ t, v (t + T) = I * v t) (hwR : ∀ t, w (t + T) = -I * w t)
    (hfR : ∀ t, f (t + T) = I * f t) (hgR : ∀ t, g (t + T) = -I * g t) :
    (∫ t in (0 : ℝ)..4 * T, pair (v t + w t) (f t + g t)) =
      (∫ t in (0 : ℝ)..4 * T, pair (v t) (f t)) +
      (∫ t in (0 : ℝ)..4 * T, pair (w t) (g t)) := by
  let C : ℝ → ℝ := fun t ↦ pair (v t) (g t) + pair (w t) (f t)
  have hc : Continuous C := by dsimp [C, pair]; fun_prop
  have hodd (t : ℝ) : C (t + T) = -C t := by
    simp only [C, hvR, hwR, hfR, hgR]
    exact pair_char_add _ _ _ _
  have hj : Continuous (fun t ↦ pair (v t) (f t) + pair (w t) (g t)) := by
    unfold pair
    fun_prop
  have h1 : Continuous (fun t ↦ pair (v t) (f t)) := by unfold pair; fun_prop
  have h2 : Continuous (fun t ↦ pair (w t) (g t)) := by unfold pair; fun_prop
  simp_rw [pair_add]
  change (∫ t in (0 : ℝ)..4 * T, (pair (v t) (f t) + pair (w t) (g t)) + C t) = _
  rw [intervalIntegral.integral_add (hj.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral_eq_zero_of_add_eq_neg hc hodd, add_zero,
    intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]

private theorem canonical_add {lam : ℝ} {f g : ℝ → ℂ}
    (hf : Integrable (deriv f)) (hg : Integrable (deriv g))
    (hfd : ∀ᵐ t, DifferentiableAt ℝ f t) (hgd : ∀ᵐ t, DifferentiableAt ℝ g t) (s : ℝ) :
    canonicalProfile lam (fun t ↦ f t + g t) s =
      canonicalProfile lam f s + canonicalProfile lam g s := by
  have he : profileIntegrand lam (fun t ↦ f t + g t) =ᵐ[volume.restrict (Ioi s)]
      fun t ↦ profileIntegrand lam f t + profileIntegrand lam g t := by
    apply ae_restrict_of_ae
    filter_upwards [hfd, hgd] with t ht hu
    rw [profileIntegrand, deriv_fun_add ht hu, add_mul]
    rfl
  unfold canonicalProfile
  rw [integral_congr_ae he, integral_add (integrable_profileIntegrand hf).integrableOn
    (integrable_profileIntegrand hg).integrableOn, mul_add]

private theorem canonical_mul (lam : ℝ) (c : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    canonicalProfile lam (fun s ↦ c * g s) t = c * canonicalProfile lam g t := by
  simp only [canonicalProfile, profileIntegrand, deriv_const_mul_field', mul_assoc,
    integral_const_mul]
  ring

private theorem integrable_arc_cross {lam : ℝ} {U : Set Plane} {κ : ℂ}
    {v : Plane → ℂ} {f g : Plane → ℂ} (hp : IsTransportPair lam U v f)
    (hU : closure cellSquare ⊆ U) (hroot : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I)
    (hκ : ∀ p ∈ U, f (rotLift p) = κ * f p)
    (hUR : ∀ p ∈ U, rotLift p ∈ U) (hfc : ContinuousOn f U) (hgc : ContinuousOn g U) :
    Integrable (fun t ↦ pair (canonicalProfile lam (f ∘ separatrixArc) t)
      (g (separatrixArc t))) := by
  have hK := arcSegment_subset_closure_cellSquare.trans hU
  obtain ⟨hac, _, hdi⟩ := arcTrace_regularity hp.isOrbitUnion.1 hK hfc hp.memSobolevOn
  have hMel := (melnikov_character hp hU hroot hUR hκ hfc).2
  obtain ⟨_, _, _, _, _, _, _, _, hp', hm', _⟩ :=
    exists_forcing_comparison hp.isOrbitUnion.1 hU hfc hp.memSobolevOn
  obtain ⟨B, hB⟩ := norm_canonicalProfile_le_exp hac hdi hMel (by norm_num : (0 : ℝ) < 1 / 2)
    hp' hm'
  obtain ⟨M, hM⟩ := isCompact_arcSegment.exists_bound_of_continuousOn (hgc.mono hK)
  have h1 := continuous_of_absolutelyContinuous
    (absolutelyContinuousOnInterval_canonicalProfile (lam := lam) hdi)
  have hm : Continuous separatrixArc := by
    unfold separatrixArc
    exact lipschitzWith_arcAngle.continuous.prodMk
      (lipschitzWith_arcAngle.continuous.sub continuous_const)
  have h2 := hgc.comp_continuous hm (fun t ↦ hK (separatrixArc_mem_arcSegment t))
  have hc : Continuous (fun t ↦ pair (canonicalProfile lam (f ∘ separatrixArc) t)
      (g (separatrixArc t))) :=
    Complex.continuous_re.comp (h1.mul (Complex.continuous_conj.comp h2))
  refine (integrable_exp_neg_half_abs.const_mul (B * M)).mono' hc.aestronglyMeasurable
    (.of_forall fun t ↦ ?_)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (by simpa using hB 0)
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖canonicalProfile lam (f ∘ separatrixArc) t * conj (g (separatrixArc t))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (B * Real.exp (-(1 / 2) * |t|)) * M := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hB t) (hM _ (separatrixArc_mem_arcSegment t)) (norm_nonneg _)
        (mul_nonneg hB0 (Real.exp_pos _).le)
    _ = _ := by ring

private theorem arc_sum {lam : ℝ} {U : Set Plane} {v w f g : Plane → ℂ}
    (hp : IsTransportPair lam U v f) (hq : IsTransportPair lam U w g)
    (hU : closure cellSquare ⊆ U) (hUR : ∀ p ∈ U, rotLift p ∈ U)
    (hfc : ContinuousOn f U) (hgc : ContinuousOn g U)
    (hfR : ∀ p ∈ U, f (rotLift p) = I * f p)
    (hgR : ∀ p ∈ U, g (rotLift p) = -I * g p) :
    (∑ k ∈ Finset.range 4, ∫ t, pair (canonicalProfile lam
      ((fun p ↦ f p + g p) ∘ cellArc k) t) (f (cellArc k t) + g (cellArc k t))) =
    (∑ k ∈ Finset.range 4, ∫ t,
      pair (canonicalProfile lam (f ∘ cellArc k) t) (f (cellArc k t))) +
    (∑ k ∈ Finset.range 4, ∫ t,
      pair (canonicalProfile lam (g ∘ cellArc k) t) (g (cellArc k t))) := by
  let F := f ∘ separatrixArc
  let G := g ∘ separatrixArc
  have hf (k : ℕ) : f ∘ cellArc k = fun t ↦ I ^ k * F t := by
    funext t
    exact apply_rotLift_iterate hUR hfR
      (hU (arcSegment_subset_closure_cellSquare (separatrixArc_mem_arcSegment t))) k
  have hg (k : ℕ) : g ∘ cellArc k = fun t ↦ (-I) ^ k * G t := by
    funext t
    exact apply_rotLift_iterate hUR hgR
      (hU (arcSegment_subset_closure_cellSquare (separatrixArc_mem_arcSegment t))) k
  have hK := arcSegment_subset_closure_cellSquare.trans hU
  obtain ⟨_, hFd, hFi⟩ := arcTrace_regularity hp.isOrbitUnion.1 hK hfc hp.memSobolevOn
  obtain ⟨_, hGd, hGi⟩ := arcTrace_regularity hq.isOrbitUnion.1 hK hgc hq.memSobolevOn
  change ∀ᵐ t, DifferentiableAt ℝ F t at hFd
  change ∀ᵐ t, DifferentiableAt ℝ G t at hGd
  let X (t : ℝ) := pair (canonicalProfile lam F t) (G t) + pair (canonicalProfile lam G t) (F t)
  have hX : Integrable X :=
    (integrable_arc_cross hp hU (Or.inr (Or.inr (Or.inl rfl))) hfR hUR hfc hgc).add
      (integrable_arc_cross hq hU (Or.inr (Or.inr (Or.inr rfl))) hgR hUR hgc hfc)
  have hD₁ := integrable_arc_cross hp hU (Or.inr (Or.inr (Or.inl rfl))) hfR hUR hfc hfc
  have hD₂ := integrable_arc_cross hq hU (Or.inr (Or.inr (Or.inr rfl))) hgR hUR hgc hgc
  have diag (a b z : ℂ) (h : a * conj a = 1) : pair (a * b) (a * z) = pair b z := by
    unfold pair
    rw [map_mul, show a * b * (conj a * conj z) = (a * conj a) * (b * conj z) by ring,
      h, one_mul]
  have hunit (k : ℕ) : I ^ k * conj (I ^ k) = 1 ∧ (-I) ^ k * conj ((-I) ^ k) = 1 := by
    simp only [map_pow, ← mul_pow, Complex.conj_I, map_neg, neg_neg,
      mul_neg, neg_mul, Complex.I_mul_I, neg_neg, one_pow, and_self]
  have hc (k : ℕ) : (fun t ↦
      pair (I ^ k * canonicalProfile lam F t) ((-I) ^ k * G t) +
      pair ((-I) ^ k * canonicalProfile lam G t) (I ^ k * F t)) =
        fun t ↦ (-1 : ℝ) ^ k * X t := by
    funext t
    have e (a b z y : ℂ) : pair (a ^ k * z) (b ^ k * y) =
        ((a * conj b) ^ k * (z * conj y)).re := by
      unfold pair
      rw [map_mul, map_pow, mul_pow]
      congr 1
      ring
    rw [e, e]
    have hi : I * conj (-I) = (-1 : ℂ) := by
      rw [map_neg, Complex.conj_I, neg_neg, Complex.I_mul_I]
    have hj : -I * conj I = (-1 : ℂ) := by
      rw [Complex.conj_I, neg_mul_neg, Complex.I_mul_I]
    rw [hi, hj]
    have hr : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
    simp only [hr, Complex.re_ofReal_mul, X, pair, mul_add]
  let D (t : ℝ) := pair (canonicalProfile lam F t) (F t)
  let E (t : ℝ) := pair (canonicalProfile lam G t) (G t)
  change Integrable D at hD₁
  change Integrable E at hD₂
  have he (k : ℕ) : (∫ t, pair (canonicalProfile lam
      ((fun p ↦ f p + g p) ∘ cellArc k) t) (f (cellArc k t) + g (cellArc k t))) =
      (∫ t, D t) + (∫ t, E t) + (-1 : ℝ)^k * ∫ t, X t := by
    have hi₁ : Integrable (deriv (fun t ↦ I ^ k * F t)) := by
      simp only [deriv_const_mul_field']
      exact hFi.const_mul _
    have hi₂ : Integrable (deriv (fun t ↦ (-I) ^ k * G t)) := by
      simp only [deriv_const_mul_field']
      exact hGi.const_mul _
    have hh₁ := hFd.mono fun _ ht ↦ ht.const_mul (I ^ k)
    have hh₂ := hGd.mono fun _ ht ↦ ht.const_mul ((-I) ^ k)
    calc
      _ = ∫ t, D t + E t + (-1 : ℝ)^k * X t := by
        apply integral_congr_ae
        filter_upwards with t
        change pair (canonicalProfile lam (fun s ↦ (f ∘ cellArc k) s +
          (g ∘ cellArc k) s) t) ((f ∘ cellArc k) t + (g ∘ cellArc k) t) = _
        rw [hf, hg, canonical_add hi₁ hi₂ hh₁ hh₂, canonical_mul, canonical_mul, pair_add,
          diag _ _ _ (hunit k).1, diag _ _ _ (hunit k).2, congrFun (hc k)]
      _ = _ := by
        change (∫ t, (D + E) t + (-1 : ℝ)^k * X t) = _
        rw [integral_add (hD₁.add hD₂) (hX.const_mul _), integral_const_mul]
        simp only [Pi.add_apply, integral_add hD₁ hD₂]
  have h₁ (k : ℕ) :
      (∫ t, pair (canonicalProfile lam (f ∘ cellArc k) t) (f (cellArc k t))) = ∫ t, D t := by
    apply integral_congr_ae
    filter_upwards with t
    change pair (canonicalProfile lam (f ∘ cellArc k) t) ((f ∘ cellArc k) t) = _
    rw [hf, canonical_mul, diag _ _ _ (hunit k).1]
  have h₂ (k : ℕ) :
      (∫ t, pair (canonicalProfile lam (g ∘ cellArc k) t) (g (cellArc k t))) = ∫ t, E t := by
    apply integral_congr_ae
    filter_upwards with t
    change pair (canonicalProfile lam (g ∘ cellArc k) t) ((g ∘ cellArc k) t) = _
    rw [hg, canonical_mul, diag _ _ _ (hunit k).2]
  simp_rw [he, h₁, h₂, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hzero : (∑ k ∈ Finset.range 4, (-1 : ℝ)^k) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hzero, zero_mul, add_zero]

private theorem period_repr {lam h : ℝ} {U : Set Plane} {f : Plane → ℂ} {κ : ℂ}
    (hU : cellSquare ⊆ U)
    (hfR : ∀ p ∈ U, f (rotLift p) = κ * f p) (hh : h ∈ Ioo 0 1)
    (hgood : ∃ m : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3)
    {Z : ℝ → ℂ}
    (hper : Function.Periodic Z (orbitPeriod h))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval Z a b)
    (hd : ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t) :
    ∀ t, Z (t + 2 * eighthPeriod h) = κ * Z t := by
  obtain ⟨m, hm⟩ := hgood
  apply transport_character_of_periodic (orbitPeriod_pos hh.1 hh.2)
    (exp_orbitPeriod_ne_one_of_goodWindow hm) hper hac hd
  intro t
  rw [dipoleOrbit_add_quarter hh.1 hh.2]
  exact hfR _ (hU (dipoleOrbit_mem_cellSquare hh.1 hh.2 t))

private theorem level_pair_sum {lam h : ℝ} {v w f g : Plane → ℂ}
    (hf : Continuous fun t ↦ f (dipoleOrbit h t)) (hg : Continuous fun t ↦ g (dipoleOrbit h t))
    (hfR : ∀ t, f (dipoleOrbit h (t + 2 * eighthPeriod h)) = I * f (dipoleOrbit h t))
    (hgR : ∀ t, g (dipoleOrbit h (t + 2 * eighthPeriod h)) = -I * g (dipoleOrbit h t))
    {Z W : ℝ → ℂ} (hZ : Continuous Z) (hW : Continuous W)
    (hZv : ∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t))
    (hWw : ∀ᵐ t, W t = transportUnknown lam w g (dipoleOrbit h t))
    (hZR : ∀ t, Z (t + 2 * eighthPeriod h) = I * Z t)
    (hWR : ∀ t, W (t + 2 * eighthPeriod h) = -I * W t)
    (hlam : lam ≠ 0) :
    levelIntegral h (fun p ↦ pair (v p + w p) (f p + g p)) =
      levelIntegral h (fun p ↦ pair (v p) (f p)) + levelIntegral h (fun p ↦ pair (w p) (g p)) := by
  let F t := f (dipoleOrbit h t)
  let G t := g (dipoleOrbit h t)
  let V t := -(lam : ℂ) * Z t - F t
  let U t := -(lam : ℂ) * W t - G t
  have hV : Continuous V := (continuous_const.mul hZ).sub hf
  have hU : Continuous U := (continuous_const.mul hW).sub hg
  have hVR (t : ℝ) : V (t + 2 * eighthPeriod h) = I * V t := by
    dsimp only [V, F]
    rw [hZR, hfR]
    ring
  have hUR (t : ℝ) : U (t + 2 * eighthPeriod h) = -I * U t := by
    dsimp only [U, G]
    rw [hWR, hgR]
    ring
  have hv : V =ᵐ[volume] fun t ↦ v (dipoleOrbit h t) := by
    filter_upwards [hZv] with t ht
    dsimp only [V, F]
    rw [ht, transportUnknown]
    field_simp [Complex.ofReal_ne_zero.2 hlam]
    ring
  have hw : U =ᵐ[volume] fun t ↦ w (dipoleOrbit h t) := by
    filter_upwards [hWw] with t ht
    dsimp only [U, G]
    rw [ht, transportUnknown]
    field_simp [Complex.ofReal_ne_zero.2 hlam]
    ring
  have h₁ := intervalIntegral.integral_congr_ae (a := (0 : ℝ)) (b := orbitPeriod h)
    (hv.mono (fun t ht _ ↦ congrArg (fun z ↦ pair z (F t)) ht))
  have h₂ := intervalIntegral.integral_congr_ae (a := (0 : ℝ)) (b := orbitPeriod h)
    (hw.mono (fun t ht _ ↦ congrArg (fun z ↦ pair z (G t)) ht))
  have h₃ := intervalIntegral.integral_congr_ae (a := (0 : ℝ)) (b := orbitPeriod h)
    ((hv.and hw).mono (fun t ht _ ↦ congrArg (fun z ↦ pair z (F t + G t))
      (congrArg₂ (· + ·) ht.1 ht.2)))
  unfold levelIntegral
  rw [← h₁, ← h₂, ← h₃, orbitPeriod, show 8 * eighthPeriod h = 4 * (2 * eighthPeriod h) by ring]
  exact period_pair_sum hV hU hf hg hVR hUR hfR hgR

set_option maxHeartbeats 400000 in
-- Assemble two ACL transports, their limits and cancellation of their cross terms.
/-- The vorticity pairing for forcing odd under the half turn. The two imaginary
characters share the same good levels; their cross terms cancel over a period
and over the four canonical arcs. Any additional a.e. level requirement can
be imposed when selecting the sequence. -/
theorem pairing_limit_half_turn_odd {lam : ℝ} {U : Set Plane} {v f : Plane → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U)
    (hUR : rotLift ⁻¹' U = U) (hfc : ContinuousOn f U)
    (hodd : ∀ p ∈ U, f (rotLift (rotLift p)) = -f p) {P : ℝ → Prop}
    (hP : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), P h) :
    ∃ hs : ℕ → ℝ, (∀ n, hs n ∈ Ioo 0 1 ∧ P (hs n)) ∧ Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun n ↦ levelIntegral (hs n) (fun p ↦ (v p * conj (f p)).re)) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ t,
          (canonicalProfile lam (f ∘ cellArc k) t * conj (f (cellArc k t))).re)) := by
  let plus (s : Plane → ℂ) (p : Plane) := (1 / 2 : ℂ) * (s p + (-I) * s (rotLift p))
  let minus (s : Plane → ℂ) (p : Plane) := (1 / 2 : ℂ) * (s p + I * s (rotLift p))
  have hs (s : Plane → ℂ) : (fun p ↦ plus s p + minus s p) = s := by
    funext p
    dsimp only [plus, minus]
    ring
  have hrot : ∀ p ∈ U, rotLift p ∈ U := fun p h ↦ show p ∈ rotLift ⁻¹' U by rwa [hUR]
  have hpr := hp.comp_rotLift
  rw [hUR] at hpr
  have hp₁ : IsTransportPair lam U (plus v) (plus f) := by
    exact ((hp.add (hpr.const_mul (-I))).const_mul (1 / 2))
  have hp₂ : IsTransportPair lam U (minus v) (minus f) := by
    exact ((hp.add (hpr.const_mul I)).const_mul (1 / 2))
  have h₁ (p : Plane) (h : p ∈ U) : plus f (rotLift p) = I * plus f p := by
    dsimp only [plus]
    rw [hodd p h]
    linear_combination (f (rotLift p) / 2) * Complex.I_sq
  have h₂ (p : Plane) (h : p ∈ U) : minus f (rotLift p) = -I * minus f p := by
    dsimp only [minus]
    rw [hodd p h]
    linear_combination (f (rotLift p) / 2) * Complex.I_sq
  have hfcR : ContinuousOn (f ∘ rotLift) U := hfc.comp
    (show Continuous rotLift by unfold rotLift; fun_prop).continuousOn hrot
  have hc₁ : ContinuousOn (plus f) U :=
    continuousOn_const.mul (hfc.add (continuousOn_const.mul hfcR))
  have hc₂ : ContinuousOn (minus f) U :=
    continuousOn_const.mul (hfc.add (continuousOn_const.mul hfcR))
  have hcell : cellSquare ⊆ U := subset_closure.trans hU
  obtain ⟨seq, hseq, hlim⟩ := exists_goodLevels_avoiding hp.ne_zero
    ((hP.and (hp₁.ae_orbit_transport_cell hcell)).and (hp₂.ae_orbit_transport_cell hcell))
    (N := ∅) (by simp)
  have hreg (n : ℕ) := (hseq n).1
  have hgood (n : ℕ) := (hseq n).2.2.2.2
  have ha₁ (n : ℕ) := (hseq n).2.2.2.1.1.2
  have ha₂ (n : ℕ) := (hseq n).2.2.2.1.2
  choose Z hZ hZp hZa hZd using ha₁
  choose W hW hWp hWa hWd using ha₂
  have hZr (n : ℕ) := period_repr hcell h₁ (hreg n) (hgood n) (hZp n) (hZa n) (hZd n)
  have hWr (n : ℕ) := period_repr hcell h₂ (hreg n) (hgood n) (hWp n) (hWa n) (hWd n)
  have hb₁ := pairing_limit_character_of_goodLevels hp₁ hU (Or.inr (Or.inr (Or.inl rfl)))
    hrot h₁ hc₁ (fun n ↦ ⟨hreg n, hgood n⟩) hlim
    (fun n ↦ ⟨hZ n, hZa n, hZd n, hZr n⟩)
  have hb₂ := pairing_limit_character_of_goodLevels hp₂ hU (Or.inr (Or.inr (Or.inr rfl)))
    hrot h₂ hc₂ (fun n ↦ ⟨hreg n, hgood n⟩) hlim
    (fun n ↦ ⟨hW n, hWa n, hWd n, hWr n⟩)
  refine ⟨seq, fun n ↦ ⟨hreg n, (hseq n).2.2.2.1.1.1⟩, hlim, ?_⟩
  have hArc := arc_sum hp₁ hp₂ hU hrot hc₁ hc₂ h₁ h₂
  rw [hs f] at hArc
  simp only [congrFun (hs f)] at hArc
  change Tendsto (fun n ↦ levelIntegral (seq n) (fun p ↦ pair (v p) (f p))) atTop
    (𝓝 (∑ k ∈ Finset.range 4, ∫ t,
      pair (canonicalProfile lam (f ∘ cellArc k) t) (f (cellArc k t))))
  rw [hArc]
  apply (hb₁.add hb₂).congr
  intro n
  have hc (F : Plane → ℂ) (hF : ContinuousOn F U) :
      Continuous (fun t ↦ F (dipoleOrbit (seq n) t)) :=
    hF.comp_continuous (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id))
      (fun t ↦ hcell (dipoleOrbit_mem_cellSquare (hreg n).1 (hreg n).2 t))
  have hr (F : Plane → ℂ) (c : ℂ) (hF : ∀ p ∈ U, F (rotLift p) = c * F p) (t : ℝ) :
      F (dipoleOrbit (seq n) (t + 2 * eighthPeriod (seq n))) = c * F (dipoleOrbit (seq n) t) := by
    rw [dipoleOrbit_add_quarter (hreg n).1 (hreg n).2]
    exact hF _ (hcell (dipoleOrbit_mem_cellSquare (hreg n).1 (hreg n).2 t))
  have he := level_pair_sum (hc _ hc₁) (hc _ hc₂) (hr _ I h₁) (hr _ (-I) h₂)
    (continuous_of_absolutelyContinuous (hZa n)) (continuous_of_absolutelyContinuous (hWa n))
    (hZ n) (hW n) (hZr n) (hWr n) hp.ne_zero
  simp only [congrFun (hs v), congrFun (hs f)] at he
  exact he.symm

/-- Common levels for the mixed normal virial and canonical vorticity
pairing. The additional a.e. requirement can carry the geometric trace
properties needed for the signed gradient contribution. -/
theorem mixed_normal_and_pairing_levels {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    {P : ℝ → Prop} (hP : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), P h) :
    ∃ seq : ℕ → ℝ, (∀ n, seq n ∈ Ioo 0 1 ∧ P (seq n)) ∧ Tendsto seq atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eeLevelTerm ω (seq n)) atTop
        (𝓝 (∫ q in mixedOpenCell, mixedNormalVirialDensity d q)) ∧
      Tendsto (fun n ↦ levelIntegral (seq n) (fun p ↦
        (liftL2 ω p * conj (streamLift ω p)).re)) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ t,
          (canonicalProfile lam (contStream ω ∘ cellArc k) t *
            conj (contStream ω (cellArc k t))).re)) := by
  have hp := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hUR : rotLift ⁻¹' cellNeighbourhood = cellNeighbourhood := by
    ext p
    constructor
    · intro h
      change rotLift p ∈ cellNeighbourhood at h
      have h' := rotLift_mem_cellNeighbourhood
        (rotLift_mem_cellNeighbourhood (rotLift_mem_cellNeighbourhood h))
      simpa only [rotLift, neg_neg, Prod.eta] using h'
    · exact rotLift_mem_cellNeighbourhood
  have hodd (p : Plane) (_ : p ∈ cellNeighbourhood) :
      contStream ω (rotLift (rotLift p)) = -contStream ω p := by
    have e : rotLift (rotLift p) = diagInv (-(diagCoord p)) := by
      ext <;> simp only [rotLift, diagInv_apply, Prod.fst_neg, Prod.snd_neg, diagCoord] <;> ring
    rw [e, contStream_diagInv_neg hs, diagInv_diagCoord]
  have hvm : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  have hfm : Measurable (streamLift ω) := (Lp.stronglyMeasurable (invLap ω)).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  have hcm := (continuous_contStream ω).measurable
  have hraw : Measurable (fun p ↦ (liftL2 ω p * conj (streamLift ω p)).re) := by fun_prop
  have hcont : Measurable (fun p ↦ (liftL2 ω p * conj (contStream ω p)).re) := by fun_prop
  have he : (fun p ↦ (liftL2 ω p * conj (streamLift ω p)).re) =ᵐ[volume]
      (fun p ↦ (liftL2 ω p * conj (contStream ω p)).re) :=
    (streamLift_ae_eq_contStream ω).mono (fun p h ↦ by
      change (liftL2 ω p * conj (streamLift ω p)).re = _
      rw [h])
  obtain ⟨seq, hseq, hlim, hpair⟩ := pairing_limit_half_turn_odd hp
    closure_cellSquare_subset_cellNeighbourhood hUR (continuous_contStream ω).continuousOn hodd
    (hP.and ((ee_truncated_virial hlam hω).and (ae_levelIntegral_congr hraw hcont he)))
  exact ⟨seq, fun n ↦ ⟨(hseq n).1, (hseq n).2.1⟩, hlim,
    mixed_normal_level_limit d hlim (fun n ↦ (hseq n).2.2.1.2),
    hpair.congr fun n ↦ (hseq n).2.2.2.symm⟩

end NoEmbeddedEigenvalues
