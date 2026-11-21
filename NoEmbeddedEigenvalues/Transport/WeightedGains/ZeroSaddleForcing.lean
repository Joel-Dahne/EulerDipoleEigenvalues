import NoEmbeddedEigenvalues.Transport.CanonicalProfile.Melnikov
import NoEmbeddedEigenvalues.Transport.WeightedGains.ExponentialTransportDecay

/-!
# Pointwise forcing estimates from zero saddle values

Blueprint: `lem:zero-saddle-forcing-decay`, `lem:zero-saddle-forcing-tails`.

Local H² gives one-half Hölder continuity near the base separatrix segment.
The corner selected by the sign of orbit time has distance O(exp(-|t|));
at a moving endpoint its distance is O(sqrt(h)). Comparing with its zero
forcing value yields the exponential and fourth-root bounds.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set MeasureTheory Filter Real
open scoped Topology

/-- A continuous H² forcing vanishing at the ends of the base arc decays along
both half-quarter orbits, with a uniform fourth-root bound at moving endpoints. -/
theorem zero_saddle_forcing_decay {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hK : arcSegment ⊆ U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgs : MemSobolevOn 2 U g) (hneg : g (π, 0) = 0) (hpos : g (0, -π) = 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| ≤ eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ C * exp (-|t| / 2)) ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| = eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ C * h ^ (1 / 4 : ℝ)) := by
  obtain ⟨ρ, hρ, H, hH, hholder⟩ := exists_holder_near_arcSegment hU hK hg hgs
    (α := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
  obtain ⟨A, r, hr, hclose⟩ := orbit_close_arc
  have hlim : Tendsto (fun h : ℝ ↦ A * √h) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ ↦ A * √h) := by fun_prop
    simpa only [sqrt_zero, mul_zero] using hc.tendsto (0 : ℝ)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1
    (hlim.eventually (eventually_lt_nhds hρ))
  let h₀ := min ε (min r (1 / 2)) / 2
  have hh₀ : 0 < h₀ := half_pos (lt_min hε (lt_min hr (by norm_num)))
  have hh₀ε : h₀ < ε := by have := min_le_left ε (min r (1 / 2)); dsimp [h₀]; linarith
  have hh₀r : h₀ < r := by
    have := (min_le_right ε (min r (1 / 2))).trans (min_le_left r (1 / 2))
    dsimp [h₀]; linarith
  have hh₀h : h₀ < 1 / 2 := by
    have := (min_le_right ε (min r (1 / 2))).trans (min_le_right r (1 / 2))
    dsimp [h₀]; linarith
  have horbit (h : ℝ) (hh : h ∈ Ioo 0 h₀) (t : ℝ) (ht : |t| ≤ eighthPeriod h) :
      dipoleOrbit h t ∈ Metric.thickening ρ arcSegment := by
    apply Metric.mem_thickening_iff.2
    refine ⟨separatrixArc t, separatrixArc_mem_arcSegment t, ?_⟩
    rw [dist_eq_norm]
    exact (hclose h ⟨hh.1, hh.2.trans hh₀r⟩ t ht).trans_lt
      (hεb (by rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]; exact hh.2.trans hh₀ε))
  have hvalue (h : ℝ) (hh : h ∈ Ioo 0 h₀) (t : ℝ) (ht : |t| ≤ eighthPeriod h) :
      ‖g (dipoleOrbit h t)‖ ≤ H * √(dist (dipoleOrbit h t)
        (if t < 0 then (π, 0) else (0, -π))) := by
    let P : ℝ × ℝ := if t < 0 then (π, 0) else (0, -π)
    have hP : P ∈ arcSegment := by
      dsimp only [P]; split_ifs
      · exact saddle_neg_mem_arcSegment
      · exact saddle_pos_mem_arcSegment
    have hz : g P = 0 := by dsimp only [P]; split_ifs <;> assumption
    have h := hholder _ (horbit h hh t ht) P (Metric.self_subset_thickening hρ _ hP)
    simpa only [hz, sub_zero, ← sqrt_eq_rpow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, P] using h
  let C := H * √(π * exp 2) + H * √π + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₁ : H * √(π * exp 2) ≤ C := by
    dsimp [C]; nlinarith [mul_nonneg hH (sqrt_nonneg π)]
  have hC₂ : H * √π ≤ C := by
    dsimp [C]; nlinarith [mul_nonneg hH (sqrt_nonneg (π * exp 2))]
  refine ⟨C, h₀, hC, hh₀, hh₀h, ?_, ?_⟩
  · intro h hh t ht
    calc ‖g (dipoleOrbit h t)‖ ≤ H * √(dist (dipoleOrbit h t)
          (if t < 0 then (π, 0) else (0, -π))) := hvalue h hh t ht
         _ ≤ H * √((π * exp 2) * exp (-|t|)) :=
           mul_le_mul_of_nonneg_left (sqrt_le_sqrt
             (dist_dipoleOrbit_saddle_le hh.1 (hh.2.trans hh₀h) ht)) hH
         _ = (H * √(π * exp 2)) * exp (-|t| / 2) := by
           rw [sqrt_mul (by positivity), ← exp_half]; ring
         _ ≤ C * exp (-|t| / 2) := mul_le_mul_of_nonneg_right hC₁ (exp_pos _).le
  · intro h hh t ht
    calc ‖g (dipoleOrbit h t)‖ ≤ H * √(dist (dipoleOrbit h t)
          (if t < 0 then (π, 0) else (0, -π))) := hvalue h hh t ht.le
         _ ≤ H * √(π * √h) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt
           (dist_dipoleOrbit_saddle_endpoints_le hh.1
             (by linarith [hh.2, hh₀h]) ht)) hH
         _ = (H * √π) * h ^ (1 / 4 : ℝ) := by
           rw [sqrt_mul pi_pos.le]
           simp_rw [sqrt_eq_rpow]
           rw [← rpow_mul hh.1.le]
           norm_num [mul_assoc]
         _ ≤ C * h ^ (1 / 4 : ℝ) :=
           mul_le_mul_of_nonneg_right hC₂ (rpow_nonneg hh.1.le _)

/-- The pointwise decay estimate applies to the original continuous forcing
representative of a zero-saddle transport pair, without a character assumption. -/
theorem IsTransportPair.zero_saddle_forcing_decay {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| ≤ eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ C * exp (-|t| / 2)) ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| = eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ C * h ^ (1 / 4 : ℝ)) := by
  have hU := hp.isOrbitUnion.1
  have hgs : MemSobolevOn 2 U g := MemSobolevOn.congr_ae_on hp.memSobolevOn hU.measurableSet
    ((ae_restrict_iff' hU.measurableSet).1 hfg)
  apply NoEmbeddedEigenvalues.zero_saddle_forcing_decay hU
    (arcSegment_subset_closure_cellSquare.trans hcell) hg hgs
  · exact hz (π, 0) ⟨1, 0, by decide, by simp⟩
      (arcSegment_subset_closure_cellSquare saddle_neg_mem_arcSegment)
  · exact hz (0, -π) ⟨0, -1, by decide, by simp⟩
      (arcSegment_subset_closure_cellSquare saddle_pos_mem_arcSegment)

/-- Oscillatory forcing tails are bounded by the same exponential profile,
with factor two, uniformly in the real oscillation frequency. Integrability
is supplied explicitly along with each bound. -/
theorem forcing_decay_tail_bounds {L C : ℝ} {F : ℝ → ℂ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hF : ContinuousOn F (Icc (-L) L))
    (hbound : ∀ t, |t| ≤ L → ‖F t‖ ≤ C * exp (-|t| / 2)) (lam : ℝ) :
    (∀ t ∈ Icc (-L) 0,
      IntervalIntegrable (fun s ↦ F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)))
        volume (-L) t ∧
      ‖∫ s in (-L)..t, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
        2 * C * exp (t / 2)) ∧
    (∀ t ∈ Icc 0 L,
      IntervalIntegrable (fun s ↦ F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)))
        volume t L ∧
      ‖∫ s in t..L, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ ≤
        2 * C * exp (-t / 2)) := by
  constructor
  · intro t ht
    obtain ⟨hi, hb⟩ := oscillatory_integral_exp_bound (C := C) (k := 1 / 2) ht.1
      (by norm_num) (hF.mono (Icc_subset_Icc le_rfl (ht.2.trans hL)))
      (fun s hs ↦ by
        have hb := hbound s (abs_le.2 ⟨hs.1, hs.2.trans (ht.2.trans hL)⟩)
        simpa only [abs_of_nonpos (hs.2.trans ht.2), neg_neg, div_eq_mul_inv,
          one_mul, mul_comm] using hb) lam
    refine ⟨hi, hb.trans ?_⟩
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring,
      show (1 / 2 : ℝ) * (-L) = -L / 2 by ring]
    norm_num
    nlinarith [mul_nonneg hC (exp_pos (-L / 2)).le]
  · intro t ht
    obtain ⟨hi, hb⟩ := oscillatory_integral_exp_bound (C := C) (k := -(1 / 2)) ht.2
      (by norm_num) (hF.mono (Icc_subset_Icc (by linarith [ht.1]) le_rfl))
      (fun s hs ↦ by
        have hb := hbound s (abs_le.2 ⟨by linarith [ht.1, hs.1], hs.2⟩)
        rw [show -(1 / 2 : ℝ) * s = -s / 2 by ring]
        simpa only [abs_of_nonneg (ht.1.trans hs.1)] using hb) lam
    refine ⟨hi, hb.trans ?_⟩
    rw [show -(1 / 2 : ℝ) * L = -L / 2 by ring,
      show -(1 / 2 : ℝ) * t = -t / 2 by ring]
    norm_num
    nlinarith [mul_nonneg hC (exp_pos (-L / 2)).le]

/-- The actual zero-saddle forcing of a transport pair has both integrable
oscillatory tails, with a common collar and constant for all real frequencies. -/
theorem IsTransportPair.zero_saddle_forcing_tails {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ h ∈ Ioo 0 h₀, ∀ μ : ℝ,
      (∀ t ∈ Icc (-eighthPeriod h) 0,
        IntervalIntegrable (fun s ↦ g (dipoleOrbit h s) *
          Complex.exp (-Complex.I * ((μ * s : ℝ) : ℂ))) volume (-eighthPeriod h) t ∧
        ‖∫ s in (-eighthPeriod h)..t, g (dipoleOrbit h s) *
          Complex.exp (-Complex.I * ((μ * s : ℝ) : ℂ))‖ ≤ C * exp (t / 2)) ∧
      (∀ t ∈ Icc 0 (eighthPeriod h),
        IntervalIntegrable (fun s ↦ g (dipoleOrbit h s) *
          Complex.exp (-Complex.I * ((μ * s : ℝ) : ℂ))) volume t (eighthPeriod h) ∧
        ‖∫ s in t..(eighthPeriod h), g (dipoleOrbit h s) *
          Complex.exp (-Complex.I * ((μ * s : ℝ) : ℂ))‖ ≤ C * exp (-t / 2)) := by
  obtain ⟨C, h₀, hC, hh₀, hh₀h, hb, -⟩ := hp.zero_saddle_forcing_decay hcell hg hfg hz
  refine ⟨2 * C, h₀, by positivity, hh₀, hh₀h, ?_⟩
  intro h hh μ
  have hh1 : h < 1 := by linarith [hh.2, hh₀h]
  have hc : Continuous (fun t ↦ g (dipoleOrbit h t)) := by
    apply hg.comp_continuous
      (continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt)
    intro t
    have hm : dipoleOrbit h t ∈ puncturedCell := by
      simpa only [actionAngleInv, div_mul_cancel₀ t (orbitPeriod_pos hh.1 hh1).ne'] using
        actionAngleInv_mem_puncturedCell hh.1 hh1 (t / orbitPeriod h)
    exact hcell (subset_closure hm.1)
  exact forcing_decay_tail_bounds (eighthPeriod_pos hh.1 hh1).le hC.le hc.continuousOn
    (hb h hh) μ

end NoEmbeddedEigenvalues
