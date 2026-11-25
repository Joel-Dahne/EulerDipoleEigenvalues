module

public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterNumeratorBounds

/-!
# Weighted first-gradient energy and fixed-time numerator bounds

Blueprint: `lem:weighted-quarter-gradient`, `lem:weighted-numerator-subinterval`,
`lem:weighted-numerator-bulk`.

The specified gradient divided by d^s has genuine L² orbit sections and an
integrable level energy. Pair it with d^s times the orbit-level vector.
Cauchy–Schwarz then uses the complementary time moment d^(2s-2), rather
than the inverse-square moment of the unweighted first-gain argument.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter Real

/-- Weighted first-gradient norms give actual fiber integrability and a finite
level integral, without global measurability outside the physical cell. -/
theorem quarterWeightedGradient_energy_integrable {b s : ℝ} (hb : b ≤ 1)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j : Fin 2, MemLp (fun p ↦ D [j] p /
      (Real.rpow (saddleDist p) s : ℂ)) 2 (volume.restrict cellSquare)) :
    IntegrableOn (quarterJetEnergy 1 s D) (Ioo 0 b) ∧
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), QuarterJetIntegrable 1 s D h ∧
      ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
        (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)) 2
        (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
  have hL (j : Fin 2) := memLp_comp_quarterOrbitStrip_of_memLp hb (hD j)
  have hi : IntegrableOn (quarterJetDensity 1 s D) (quarterOrbitStrip b) := by
    have he : quarterJetDensity 1 s D = fun q ↦
        ‖D [0] (dipoleOrbit q.1 q.2) /
          (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2 +
        ‖D [1] (dipoleOrbit q.1 q.2) /
          (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2 := by
      funext q
      exact quarterJetDensity_one s D q
    rw [he]
    exact ((hL 0).integrable_norm_pow (by norm_num)).add
      ((hL 1).integrable_norm_pow (by norm_num))
  obtain ⟨hmass, hfib⟩ := integrable_quarterStrip_sections hi
  refine ⟨hmass, ?_⟩
  filter_upwards [hfib, ae_all_iff.2 (fun j ↦ memLp_quarterStrip_sections (hL j))]
    with h hh hG
  refine ⟨hh, fun j ↦ ?_⟩
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact hG j

/-- Weighted Cauchy–Schwarz for the actual fixed-time level derivative.
The same full-quarter energy controls every measurable time subset; the
complementary time moment and genuine integrability are explicit. -/
theorem quarterForcingLevelDerivative_weighted_setIntegral_bound
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {h s C A : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hC : 0 ≤ C)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
      (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2)) ≤ A)
    (lam : ℝ) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Icc (-eighthPeriod h) (eighthPeriod h)) :
    IntegrableOn (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) S ∧
    ‖∫ t in S, quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ ^ 2 ≤
      (2 * C ^ 2 * A) * quarterJetEnergy 1 s D h := by
  let L := eighthPeriod h
  let V := fun t ↦ deriv (fun x ↦ dipoleOrbit x t) h
  let F : Fin 2 → ℝ → ℂ := fun j t ↦ D [j] (dipoleOrbit h t) /
    (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)
  let w : Fin 2 → ℝ → ℂ := fun j t ↦
    (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ) *
      (if j = 0 then (V t).1 else (V t).2 : ℝ) *
        Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))
  have hL : 0 < L := eighthPeriod_pos hh.1 hh.2
  have hVc := continuous_orbit_level_derivative hh
  have hdc : Continuous (fun t ↦ saddleDist (dipoleOrbit h t)) :=
    (Metric.continuous_infDist_pt saddleSet).comp (continuous_iff_continuousAt.2
      (fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt))
  have hdp : ContinuousOn (fun t ↦ Real.rpow (saddleDist (dipoleOrbit h t)) s)
      (Icc (-L) L) := hdc.continuousOn.rpow_const (fun t ht ↦ Or.inl (hd t ht).ne')
  have hwc (j : Fin 2) : ContinuousOn (w j) (Icc (-L) L) := by
    have hvj : Continuous (fun t ↦ (if j = 0 then (V t).1 else (V t).2 : ℝ)) := by
      split_ifs
      · exact hVc.fst
      · exact hVc.snd
    exact ((Complex.continuous_ofReal.comp_continuousOn hdp).mul
      (Complex.continuous_ofReal.comp hvj).continuousOn).mul (by fun_prop)
  have hwL (j : Fin 2) : MemLp (w j) 2 (volume.restrict (Icc (-L) L)) := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hwc j)
    exact MemLp.of_bound ((hwc j).aestronglyMeasurable measurableSet_Icc) M
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hM t ht)
  have hwi (j : Fin 2) : IntegrableOn (fun t ↦ w j t * F j t) (Icc (-L) L) :=
    (hwL j).integrable_mul (hG j)
  have hri : IntegrableOn (fun t ↦ Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2))
      (Icc (-L) L) :=
    (hdc.continuousOn.rpow_const (fun t ht ↦ Or.inl (hd t ht).ne')).integrableOn_Icc
  have hphase (t : ℝ) : ‖Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hwbound (j : Fin 2) : (∫ t in Icc (-L) L, ‖w j t‖ ^ 2) ≤ C ^ 2 * A := by
    calc
      _ ≤ ∫ t in Icc (-L) L, C ^ 2 *
          Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2) := by
        apply integral_mono_ae ((hwL j).integrable_norm_pow (by norm_num)) (hri.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hvj : ‖(if j = 0 then (V t).1 else (V t).2 : ℝ)‖ ≤
            C / saddleDist (dipoleOrbit h t) := by
          split_ifs
          · exact (norm_fst_le (V t)).trans (hV t ht)
          · exact (norm_snd_le (V t)).trans (hV t ht)
        have hn : ‖w j t‖ ≤ C * Real.rpow (saddleDist (dipoleOrbit h t)) (s - 1) := by
          dsimp only [w]
          simp only [Real.rpow_eq_pow]
          rw [norm_mul, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (rpow_nonneg (hd t ht).le _), Complex.norm_real]
          calc _ ≤ Real.rpow (saddleDist (dipoleOrbit h t)) s *
                (C / saddleDist (dipoleOrbit h t)) :=
              mul_le_mul_of_nonneg_left hvj (rpow_nonneg (hd t ht).le _)
               _ = _ := by
                simp only [Real.rpow_eq_pow]
                rw [rpow_sub_one (hd t ht).ne']
                ring
        have hs := (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hC (rpow_nonneg (hd t ht).le _))).2 hn
        have he : (Real.rpow (saddleDist (dipoleOrbit h t)) (s - 1)) ^ 2 =
            Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2) := by
          simp only [Real.rpow_eq_pow]
          rw [← rpow_natCast, ← rpow_mul (hd t ht).le]
          congr 1
          ring
        simp only [Real.rpow_eq_pow] at he
        simpa only [Real.rpow_eq_pow, mul_pow, he] using hs
      _ = C ^ 2 * ∫ t in (-L)..L, Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2) := by
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hMoment (sq_nonneg _)
  have he (t : ℝ) (ht : t ∈ Icc (-L) L) : quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)) = w 0 t * F 0 t + w 1 t * F 1 t := by
    have hn : (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos (hd t ht) s).ne'
    dsimp only [quarterForcingLevelDerivative, w, F, V]
    norm_num only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero]
    field_simp [hn]
  have hIntegral : IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-L) L := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -L ≤ L)).2
    exact ((hwi 0).add (hwi 1)).congr_fun (fun t ht ↦ (he t ht).symm) measurableSet_Icc
  refine ⟨((intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith : -L ≤ L)).1 hIntegral).mono_set hS, ?_⟩
  have hE : quarterJetEnergy 1 s D h = (∫ t in Icc (-L) L, ‖F 0 t‖ ^ 2) +
      ∫ t in Icc (-L) L, ‖F 1 t‖ ^ 2 := by
    unfold quarterJetEnergy
    simp only [quarterJetDensity_one]
    rw [← integral_Icc_eq_integral_Ioo,
      integral_add ((hG 0).integrable_norm_pow (by norm_num))
        ((hG 1).integrable_norm_pow (by norm_num))]
  rw [setIntegral_congr_fun hSm (fun t ht ↦ he t (hS ht)),
    integral_add ((hwi 0).mono_set hS) ((hwi 1).mono_set hS)]
  have hsmall (G : ℝ → ℂ) (hGL : MemLp G 2 (volume.restrict (Icc (-L) L))) :
      (∫ t in S, ‖G t‖ ^ 2) ≤ ∫ t in Icc (-L) L, ‖G t‖ ^ 2 :=
    setIntegral_mono_set (hGL.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall hS)
  have hb (j : Fin 2) :=
    (norm_integral_mul_sq_le
      ((hwL j).mono_measure (Measure.restrict_mono_set _ hS))
      ((hG j).mono_measure (Measure.restrict_mono_set _ hS))).trans
      ((mul_le_mul (hsmall _ (hwL j)) (hsmall _ (hG j))
        (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hwbound j) (integral_nonneg fun _ ↦ sq_nonneg _)))
  have hs := (norm_add_sq_le (∫ t in S, w 0 t * F 0 t)
    (∫ t in S, w 1 t * F 1 t)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hb 0) (hb 1)) (by norm_num : (0 : ℝ) ≤ 2))
  rw [hE]
  convert hs using 1
  ring

/-- Weighted Cauchy–Schwarz for the actual fixed-time level derivative.
The complementary time moment and genuine integrability are explicit. -/
theorem quarterForcingLevelDerivative_weighted_integral_bound
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {h s C A : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hC : 0 ≤ C)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
      (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) (2 * s - 2)) ≤ A) (lam : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    ‖∫ t in (-eighthPeriod h)..eighthPeriod h, quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ ^ 2 ≤
      (2 * C ^ 2 * A) * quarterJetEnergy 1 s D h := by
  obtain ⟨hi, hb⟩ := quarterForcingLevelDerivative_weighted_setIntegral_bound hh hC hG hd hV
    hMoment lam (Icc (-eighthPeriod h) (eighthPeriod h)) measurableSet_Icc Subset.rfl
  have hL := eighthPeriod_pos hh.1 hh.2
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hi, ?_⟩
  rwa [intervalIntegral.integral_of_le (by linarith : -eighthPeriod h ≤ eighthPeriod h),
    ← integral_Icc_eq_integral_Ioc]

end EulerDipoleEigenvalues
