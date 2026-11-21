module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.OrdinaryQuarterReconstruction
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterForcingPullback

/-!
# Ordinary weighted forcing data on a common quarter collar

Blueprint: `lem:ordinary-quarter-forcing-data`.

Positive distance moments control both the signed midpoint integral and the
outer distance-weighted reconstruction. The forcing level field itself is L²:
its square is bounded by a constant times d times the three-halves density.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Genuine forcing integrals, an integrable majorant, the distance-square
moment and a bounded distance multiplier, on one frequency-independent collar. -/
theorem ordinary_quarter_forcing_data {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hDw : ∀ j : Fin 2, MemLp (fun p ↦ J [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare))
    (hG : AEStronglyMeasurable (quarterForcingLevelDerivative J)
      (volume.restrict (quarterOrbitStrip r))) :
    ∃ b C : ℝ, 0 < b ∧ b < r ∧
      MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) ⊤
        (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (quarterForcingLevelDerivative J) 2 (volume.restrict (quarterOrbitStrip b)) ∧
      (∀ h ∈ Ioo 0 b,
        (∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ 2) ≤ C) ∧
      ∃ E : ℝ → ℝ, IntegrableOn E (Ioo 0 b) ∧
        (∀ h, 0 ≤ E h) ∧ ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
          ∀ μ : ℝ, ∀ t ∈ Ioo (-eighthPeriod h) (eighthPeriod h),
            IntervalIntegrable (fun u ↦ quarterForcingLevelDerivative J (h, u) *
              Complex.exp (-Complex.I * ((μ * u : ℝ) : ℂ))) volume 0 t ∧
            ‖∫ u in 0..t, quarterForcingLevelDerivative J (h, u) *
              Complex.exp (-Complex.I * ((μ * u : ℝ) : ℂ))‖ ^ 2 ≤ E h := by
  obtain ⟨V, η, hη, _, hV⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨c, M, ρ, hc, hρ, hd⟩ := saddleDist_dipoleOrbit
  obtain ⟨A, a, ha, hA⟩ := integral_saddleDist_rpow_pos_le (p := 1) (by norm_num)
  obtain ⟨C, s, hs, hC⟩ := integral_saddleDist_rpow_pos_le (p := 2) (by norm_num)
  let b := min r (min η (min ρ (min a s))) / 2
  have hb : 0 < b := half_pos (lt_min hr (lt_min hη (lt_min hρ (lt_min ha hs))))
  have hbr : b < r := by dsimp [b]; linarith [min_le_left r (min η (min ρ (min a s)))]
  have hbη : b < η := by
    have := (min_le_right r (min η (min ρ (min a s)))).trans (min_le_left η (min ρ (min a s)))
    dsimp [b]; linarith
  have hbρ : b < ρ := by
    have := (min_le_right r (min η (min ρ (min a s)))).trans
      ((min_le_right η (min ρ (min a s))).trans (min_le_left ρ (min a s)))
    dsimp [b]; linarith
  have hba : b < a := by
    have := (min_le_right r (min η (min ρ (min a s)))).trans
      ((min_le_right η (min ρ (min a s))).trans
        ((min_le_right ρ (min a s)).trans (min_le_left a s)))
    dsimp [b]; linarith
  have hbs : b < s := by
    have := (min_le_right r (min η (min ρ (min a s)))).trans
      ((min_le_right η (min ρ (min a s))).trans
        ((min_le_right ρ (min a s)).trans (min_le_right a s)))
    dsimp [b]; linarith
  have hb1 : b < 1 := hbr.trans hr1
  have hSub : quarterOrbitStrip b ⊆ quarterOrbitStrip r :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans hbr, hq.2.2⟩
  have hGm := hG.mono_measure (Measure.restrict_mono_set _ hSub)
  have hdpos (h : ℝ) (hh : h ∈ Ioo 0 b) (t : ℝ)
      (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      0 < saddleDist (dipoleOrbit h t) :=
    (mul_pos hc (Real.exp_pos _)).trans_le (hd h ⟨hh.1, hh.2.trans hbρ⟩ t (abs_le.2 ht)).1
  have hdM (q : ℝ × ℝ) (hq : q ∈ quarterOrbitStrip b) :
      saddleDist (dipoleOrbit q.1 q.2) ≤ |M| := by
    have h := (hd q.1 ⟨hq.1, hq.2.1.trans hbρ⟩ q.2
      (abs_le.2 ⟨hq.2.2.1.le, hq.2.2.2.le⟩)).2
    exact h.trans ((mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_nonneg _)).trans
      (mul_le_of_le_one_right (abs_nonneg M)
        (Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _)))))
  have hVm (h : ℝ) (hh : h ∈ Ioo 0 b) (t : ℝ)
      (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ |V| / saddleDist (dipoleOrbit h t) :=
    ((hV h ⟨hh.1, hh.2.trans hbη⟩ t (abs_le.2 ht)).1).trans
      (div_le_div_of_nonneg_right (le_abs_self V) (hdpos h hh t ht).le)
  have hdt : MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) ⊤
      (volume.restrict (quarterOrbitStrip b)) := by
    apply memLp_top_of_bound
      ((Complex.continuous_ofReal.comp
        ((Metric.continuous_infDist_pt saddleSet).comp
          continuous_dipoleOrbit)).aestronglyMeasurable) |M|
    filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    change ‖(saddleDist (dipoleOrbit q.1 q.2) : ℂ)‖ ≤ |M|
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ saddleDist (dipoleOrbit q.1 q.2) from Metric.infDist_nonneg)]
    exact hdM q hq
  have hDensity : IntegrableOn (quarterJetDensity 1 (3 / 2) J) (quarterOrbitStrip b) := by
    have he : quarterJetDensity 1 (3 / 2) J = fun q ↦
        ‖J [0] (dipoleOrbit q.1 q.2) /
          (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) (3 / 2) : ℂ)‖ ^ 2 +
        ‖J [1] (dipoleOrbit q.1 q.2) /
          (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) (3 / 2) : ℂ)‖ ^ 2 := by
      funext q
      exact quarterJetDensity_one _ _ _
    rw [he]
    exact ((memLp_comp_quarterOrbitStrip_of_memLp hb1.le (hDw 0)).integrable_norm_pow
      (by norm_num)).add
      ((memLp_comp_quarterOrbitStrip_of_memLp hb1.le (hDw 1)).integrable_norm_pow (by norm_num))
  have hGL : MemLp (quarterForcingLevelDerivative J) 2
      (volume.restrict (quarterOrbitStrip b)) := by
    apply (memLp_two_iff_integrable_sq_norm hGm).2
    apply (hDensity.const_mul (2 * |V| ^ 2 * |M|)).mono' (hGm.norm.pow 2)
    filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ht : q.2 ∈ Icc (-eighthPeriod q.1) (eighthPeriod q.1) := Ioo_subset_Icc_self hq.2.2
    exact (quarterForcingLevelDerivative_sq_le_density J q (abs_nonneg V)
      (hdpos q.1 ⟨hq.1, hq.2.1⟩ q.2 ht) (hVm q.1 ⟨hq.1, hq.2.1⟩ q.2 ht)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdM q hq) (by positivity))
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  obtain ⟨hEnergy, hFib⟩ := quarterWeightedGradient_energy_integrable hb1.le hDw
  let K := 2 * |V| ^ 2 * |A|
  let E := fun h ↦ K * quarterJetEnergy 1 (3 / 2) J h
  refine ⟨b, C, hb, hbr, hdt, hGL, ?_, E, hEnergy.const_mul K, ?_, ?_⟩
  · intro h hh
    simpa only [Real.rpow_two] using hC h ⟨hh.1, hh.2.trans hbs⟩
  · intro h
    exact mul_nonneg (by dsimp [K]; positivity)
      (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  · filter_upwards [hFib, ae_restrict_mem measurableSet_Ioo] with h hh hI
    intro μ
    have hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
        Real.rpow (saddleDist (dipoleOrbit h t)) (2 * (3 / 2) - 2)) ≤ |A| := by
      norm_num
      have hAm : (∫ t in (-eighthPeriod h)..eighthPeriod h,
          saddleDist (dipoleOrbit h t)) ≤ A := by
        simpa only [Real.rpow_one] using hA h ⟨hI.1, hI.2.trans hba⟩
      exact hAm.trans (le_abs_self A)
    have hbound := quarterForcingLevelDerivative_weighted_setIntegral_bound
      ⟨hI.1, hI.2.trans hb1⟩ (abs_nonneg V) hh.2 (hdpos h hI) (hVm h hI) hMoment μ
    have hL := eighthPeriod_pos hI.1 (hI.2.trans hb1)
    intro t ht
    by_cases hpos : 0 ≤ t
    · have hS : Icc 0 t ⊆ Icc (-eighthPeriod h) (eighthPeriod h) := by
        intro u hu
        exact ⟨by linarith [ht.1, hu.1], hu.2.trans ht.2.le⟩
      obtain ⟨hi, hn⟩ := hbound (Icc 0 t) measurableSet_Icc hS
      refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hpos).2 hi, ?_⟩
      rw [intervalIntegral.integral_of_le hpos, ← integral_Icc_eq_integral_Ioc]
      exact hn
    · have hneg : t ≤ 0 := (le_of_not_ge hpos)
      have hS : Icc t 0 ⊆ Icc (-eighthPeriod h) (eighthPeriod h) := by
        intro u hu
        exact ⟨ht.1.le.trans hu.1, by linarith [ht.2, hu.2]⟩
      obtain ⟨hi, hn⟩ := hbound (Icc t 0) measurableSet_Icc hS
      refine ⟨((intervalIntegrable_iff_integrableOn_Icc_of_le hneg).2 hi).symm, ?_⟩
      rw [intervalIntegral.integral_symm, norm_neg, intervalIntegral.integral_of_le hneg,
        ← integral_Icc_eq_integral_Ioc]
      exact hn

end NoEmbeddedEigenvalues
