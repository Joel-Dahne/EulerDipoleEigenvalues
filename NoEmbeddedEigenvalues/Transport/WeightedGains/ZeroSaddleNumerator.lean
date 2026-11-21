import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterNumeratorBounds
import NoEmbeddedEigenvalues.Transport.WeightedGains.ZeroSaddleForcing
import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals

/-!
# Quantitative first derivatives of zero-saddle forcing numerators

Blueprint: `lem:zero-saddle-numerator-derivative`.

Cauchy--Schwarz uses the actual unweighted gradient fiber energy and the
integrable inverse-square saddle-distance profile. The moving endpoints cost
only h^(-3/2) in squared energy, because the continuous forcing is O(h^(1/4))
there. No global second derivative of the numerator is required.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real
open scoped Topology ContDiff

/-- A fixed-time bulk derivative costs one inverse power of the level times
the unweighted gradient energy. The integrand's genuine integrability is included. -/
theorem quarterForcingLevelDerivative_integral_bound
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {h C A : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hC : 0 ≤ C)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hInv : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      saddleDist (dipoleOrbit h t) ^ (-2 : ℝ)) ≤ A / h) (lam : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    ‖∫ t in (-eighthPeriod h)..eighthPeriod h, quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ ^ 2 ≤
      (2 * C ^ 2 * A / h) * quarterJetEnergy 1 0 D h := by
  let L := eighthPeriod h
  let V := fun t ↦ deriv (fun x ↦ dipoleOrbit x t) h
  let w : Fin 2 → ℝ → ℂ := fun j t ↦
    (if j = 0 then (V t).1 else (V t).2 : ℝ) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))
  have hL : 0 < L := eighthPeriod_pos hh.1 hh.2
  have hVc := continuous_orbit_level_derivative hh
  have hwc (j : Fin 2) : Continuous (w j) := by
    dsimp only [w]
    split_ifs
    · exact (Complex.continuous_ofReal.comp hVc.fst).mul (by fun_prop)
    · exact (Complex.continuous_ofReal.comp hVc.snd).mul (by fun_prop)
  have hwL (j : Fin 2) : MemLp (w j) 2 (volume.restrict (Icc (-L) L)) := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hwc j).continuousOn
    exact MemLp.of_bound ((hwc j).aestronglyMeasurable.restrict) M
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hM t ht)
  have hwi (j : Fin 2) : IntegrableOn (fun t ↦ w j t * D [j] (dipoleOrbit h t)) (Icc (-L) L) :=
    (hwL j).integrable_mul (hG j)
  have hri : IntegrableOn (fun t ↦ saddleDist (dipoleOrbit h t) ^ (-2 : ℝ)) (Icc (-L) L) := by
    apply ContinuousOn.integrableOn_Icc
    exact ((Metric.continuous_infDist_pt saddleSet).comp (continuous_iff_continuousAt.2
      (fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt))).continuousOn.rpow_const
        (fun t ht ↦ Or.inl (hd t ht).ne')
  have hwbound (j : Fin 2) : (∫ t in Icc (-L) L, ‖w j t‖ ^ 2) ≤ C ^ 2 * (A / h) := by
    calc
      _ ≤ ∫ t in Icc (-L) L, C ^ 2 * saddleDist (dipoleOrbit h t) ^ (-2 : ℝ) := by
        apply integral_mono_ae ((hwL j).integrable_norm_pow (by norm_num)) (hri.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hn : ‖w j t‖ ≤ C / saddleDist (dipoleOrbit h t) := by
          dsimp only [w]
          rw [norm_mul, Complex.norm_exp]
          simp only [Complex.mul_re, Complex.neg_re, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, neg_zero,
            exp_zero, mul_one, Complex.norm_real]
          split_ifs
          · exact (norm_fst_le (V t)).trans (hV t ht)
          · exact (norm_snd_le (V t)).trans (hV t ht)
        have hs := (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC (hd t ht).le)).2 hn
        simpa only [Real.rpow_neg (hd t ht).le, Real.rpow_two, div_eq_mul_inv, mul_pow, inv_pow]
          using hs
      _ = C ^ 2 * ∫ t in (-L)..L, saddleDist (dipoleOrbit h t) ^ (-2 : ℝ) := by
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (sq_nonneg _)
  have he (t : ℝ) : quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)) =
      w 0 t * D [0] (dipoleOrbit h t) + w 1 t * D [1] (dipoleOrbit h t) := by
    dsimp [quarterForcingLevelDerivative, w, V]; ring
  have hIntegral : IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-L) L := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -L ≤ L)).2
    simp_rw [he]
    exact (hwi 0).add (hwi 1)
  refine ⟨hIntegral, ?_⟩
  have hE : quarterJetEnergy 1 0 D h = (∫ t in Icc (-L) L, ‖D [0] (dipoleOrbit h t)‖ ^ 2) +
      ∫ t in Icc (-L) L, ‖D [1] (dipoleOrbit h t)‖ ^ 2 := by
    unfold quarterJetEnergy
    simp only [quarterJetDensity_one, Real.rpow_eq_pow, Real.rpow_zero, Complex.ofReal_one, div_one]
    rw [← integral_Icc_eq_integral_Ioo,
      integral_add ((hG 0).integrable_norm_pow (by norm_num))
        ((hG 1).integrable_norm_pow (by norm_num))]
  rw [intervalIntegral.integral_of_le (by linarith : -eighthPeriod h ≤ eighthPeriod h),
    ← integral_Icc_eq_integral_Ioc]
  simp_rw [he]
  rw [integral_add (hwi 0) (hwi 1)]
  have hb (j : Fin 2) := (norm_integral_mul_sq_le (hwL j) (hG j)).trans
    (mul_le_mul_of_nonneg_right (hwbound j) (integral_nonneg (fun _ ↦ sq_nonneg _)))
  have hs := (norm_add_sq_le (∫ t in Icc (-L) L, w 0 t * D [0] (dipoleOrbit h t))
    (∫ t in Icc (-L) L, w 1 t * D [1] (dipoleOrbit h t))).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hb 0) (hb 1)) (by norm_num : (0 : ℝ) ≤ 2))
  rw [hE]
  convert hs using 1
  ring

/-- The unweighted first-jet orbit energy has a genuine finite level integral,
and the raw first derivatives have L² sections on almost every quarter. -/
theorem quarterGradient_energy_integrable {b : ℝ} (hb : b ≤ 1)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j : Fin 2, MemLp (D [j]) 2 (volume.restrict cellSquare)) :
    IntegrableOn (quarterJetEnergy 1 0 D) (Ioo 0 b) ∧
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), QuarterJetIntegrable 1 0 D h ∧
      ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t)) 2
        (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
  have hL (j : Fin 2) := memLp_comp_quarterOrbitStrip_of_memLp hb (hD j)
  have hi : IntegrableOn (quarterJetDensity 1 0 D) (quarterOrbitStrip b) := by
    have he : quarterJetDensity 1 0 D = fun q ↦
        ‖D [0] (dipoleOrbit q.1 q.2)‖ ^ 2 + ‖D [1] (dipoleOrbit q.1 q.2)‖ ^ 2 := by
      funext q
      simp [quarterJetDensity_one, Real.rpow_eq_pow]
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

private theorem sqrt_div_sq {h : ℝ} (hh : 0 < h) : √h / h ^ 2 = 1 / (h * √h) := by
  have hs : 0 < √h := sqrt_pos.2 hh
  apply (div_eq_div_iff (pow_ne_zero 2 hh.ne') (mul_ne_zero hh.ne' hs.ne')).2
  calc √h * (h * √h) = h * (√h) ^ 2 := by ring
       _ = 1 * h ^ 2 := by rw [sq_sqrt hh.le]; ring

/-- Combining the actual bulk and endpoint terms gives the precise singular
powers used in first-gain cell summation, uniformly in the real frequency. -/
theorem quarterNumeratorDerivative_sq_le
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℂ} {h C A B M : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hInv : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      saddleDist (dipoleOrbit h t) ^ (-2 : ℝ)) ≤ A / h)
    (hL : |deriv eighthPeriod h| ≤ B / h)
    (hp : ‖g (dipoleOrbit h (eighthPeriod h))‖ ≤ M * h ^ (1 / 4 : ℝ))
    (hm : ‖g (dipoleOrbit h (-eighthPeriod h))‖ ≤ M * h ^ (1 / 4 : ℝ)) (lam : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    ‖quarterNumeratorDerivative lam g D h‖ ^ 2 ≤
      (4 * C ^ 2 * A / h) * quarterJetEnergy 1 0 D h + (8 * B ^ 2 * M ^ 2) / (h * √h) := by
  obtain ⟨hi, hb⟩ := quarterForcingLevelDerivative_integral_bound hh hC hG hd hV hInv lam
  let Z := ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (eighthPeriod h)) *
      Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) +
     g (dipoleOrbit h (-eighthPeriod h)) *
      Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ)))
  have hphase (t : ℝ) : ‖Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hZ : ‖Z‖ ≤ (B / h) * (2 * M * h ^ (1 / 4 : ℝ)) := by
    dsimp only [Z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hL _ (norm_nonneg _) (div_nonneg hB hh.1.le)
    calc
      _ ≤ ‖g (dipoleOrbit h (eighthPeriod h)) *
          Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ))‖ +
        ‖g (dipoleOrbit h (-eighthPeriod h)) *
          Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ))‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, hphase, mul_one]; linarith
  have hpow : (h ^ (1 / 4 : ℝ)) ^ 2 = √h := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.1.le]
    norm_num [← sqrt_eq_rpow]
  have hZ2 : ‖Z‖ ^ 2 ≤ (4 * B ^ 2 * M ^ 2) / (h * √h) := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (div_nonneg hB hh.1.le)
        (mul_nonneg (mul_nonneg (by norm_num) hM) (Real.rpow_nonneg hh.1.le _)))).2 hZ
    calc
      _ ≤ ((B / h) * (2 * M * h ^ (1 / 4 : ℝ))) ^ 2 := hs
      _ = 4 * B ^ 2 * M ^ 2 * (h ^ (1 / 4 : ℝ)) ^ 2 / h ^ 2 := by ring
      _ = (4 * B ^ 2 * M ^ 2) / (h * √h) := by
        rw [hpow]
        calc
          _ = (4 * B ^ 2 * M ^ 2) * (√h / h ^ 2) := by ring
          _ = _ := by rw [sqrt_div_sq hh.1]; ring
  refine ⟨hi, ?_⟩
  change ‖(∫ t in (-eighthPeriod h)..eighthPeriod h,
    quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) + Z‖ ^ 2 ≤ _
  exact (norm_add_sq_le _ _).trans ((mul_le_mul_of_nonneg_left (add_le_add hb hZ2)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- A supplied first weak gradient of the original continuous zero-saddle
forcing gives the quantitative numerator data on one common collar. -/
theorem IsTransportPair.zero_saddle_numerator_estimates_of_gradient
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ μ : ℝ, HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g D)) ∧
      IntegrableOn (quarterJetEnergy 1 0 D) (Ioo 0 h₀) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), QuarterJetIntegrable 1 0 D h ∧ ∀ μ : ℝ,
        IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
        ‖quarterNumeratorDerivative μ g D h‖ ^ 2 ≤
          K / h * quarterJetEnergy 1 0 D h + K / (h * √h) := by
  obtain ⟨M, rF, hM, hrF, hrFh, -, hEnds⟩ := hp.zero_saddle_forcing_decay hcell hg hfg hz
  obtain ⟨C, rV, hrV, -, hVector⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨A, rI, hrI, hInverse⟩ := integral_saddleDist_rpow_le
  obtain ⟨cL, B, rL, hcL, hB, hrL, -, hPeriod⟩ := eighthPeriod_derivative_bounds
  obtain ⟨c, S, rS, hc, hrS, hDistance⟩ := saddleDist_dipoleOrbit
  let h₀ := min rF (min rV (min rI (min rL rS)))
  have hh₀ : 0 < h₀ := lt_min hrF (lt_min hrV (lt_min hrI (lt_min hrL hrS)))
  have hF₀ : h₀ ≤ rF := min_le_left _ _
  have hV₀ : h₀ ≤ rV := (min_le_right _ _).trans (min_le_left _ _)
  have hI₀ : h₀ ≤ rI :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hL₀ : h₀ ≤ rL :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hS₀ : h₀ ≤ rS :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  have hh₀h : h₀ < 1 / 2 := hF₀.trans_lt hrFh
  have hh₀1 : h₀ < 1 := by linarith
  have hU := hp.isOrbitUnion.1
  have hgs : MemSobolevOn 2 U g := hp.memSobolevOn.congr_ae_on hU.measurableSet
    ((ae_restrict_iff' hU.measurableSet).1 hfg)
  obtain ⟨hE, hFib⟩ := quarterGradient_energy_integrable hh₀1.le
    (fun j ↦ (hDL j).mono_measure (Measure.restrict_mono (subset_closure.trans hcell) le_rfl))
  let K := 4 * |C| ^ 2 * |A| + 8 * B ^ 2 * M ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKA : 4 * |C| ^ 2 * |A| ≤ K := by
    dsimp [K]; nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg M)]
  have hKB : 8 * B ^ 2 * M ^ 2 ≤ K := by
    dsimp [K]; nlinarith [mul_nonneg (sq_nonneg |C|) (abs_nonneg A)]
  refine ⟨K, h₀, hK, hh₀, hh₀h, fun μ ↦ quarterNumerator_derivative_h1Loc
    hU hg hgs.1 hD hDL (subset_closure.trans hcell) hh₀1, hE, ?_⟩
  filter_upwards [hFib, ae_restrict_mem measurableSet_Ioo] with h hFiber hh
  have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, hh.2.trans hh₀1⟩
  have htL := eighthPeriod_pos hh1.1 hh1.2
  have hPer := hPeriod h ⟨hh.1, hh.2.trans_le hL₀⟩
  have hLneg : deriv eighthPeriod h < 0 := by nlinarith [hPer.1, hh.1]
  have hLbound : |deriv eighthPeriod h| ≤ B / h := by
    rw [abs_of_neg hLneg]
    exact (le_div_iff₀ hh.1).2 (by nlinarith [hPer.2.1])
  have hEndp := hEnds h ⟨hh.1, hh.2.trans_le hF₀⟩ (eighthPeriod h)
    (abs_of_pos htL)
  have hEndm := hEnds h ⟨hh.1, hh.2.trans_le hF₀⟩ (-eighthPeriod h)
    (by rw [abs_neg, abs_of_pos htL])
  have hd (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      0 < saddleDist (dipoleOrbit h t) :=
    (mul_pos hc (exp_pos _)).trans_le
      (hDistance h ⟨hh.1, hh.2.trans_le hS₀⟩ t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)).1
  have hv (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ |C| / saddleDist (dipoleOrbit h t) :=
    (hVector h ⟨hh.1, hh.2.trans_le hV₀⟩ t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)).1.trans
      (div_le_div_of_nonneg_right (le_abs_self C) (hd t ht).le)
  have hi := (hInverse h ⟨hh.1, hh.2.trans_le hI₀⟩).1.trans
    (div_le_div_of_nonneg_right (le_abs_self A) hh.1.le)
  refine ⟨hFiber.1, fun μ ↦ ?_⟩
  obtain ⟨hInt, hBound⟩ := quarterNumeratorDerivative_sq_le hh1 (abs_nonneg C) hB.le hM.le
    hFiber.2 hd hv hi hLbound hEndp hEndm μ
  refine ⟨hInt, hBound.trans ?_⟩
  exact add_le_add
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hKA hh.1.le)
      (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (div_le_div_of_nonneg_right hKB (mul_nonneg hh.1.le (sqrt_nonneg _)))

/-- The original transport-pair hypotheses supply a first weak gradient and
all quantitative zero-saddle numerator estimates. Only singleton entries of
`D` are used; no second-jet or global numerator-H² premise is imposed. -/
theorem IsTransportPair.zero_saddle_numerator_estimates
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0) :
    ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
      (∀ j, HasWeakPartialOn U j g (D [j]) ∧ MemLp (D [j]) 2 (volume.restrict U)) ∧
      ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
        (∀ μ : ℝ, HasIntervalH1Loc 0 h₀ (quarterNumerator μ g)
          (quarterNumeratorDerivative μ g D)) ∧
        IntegrableOn (quarterJetEnergy 1 0 D) (Ioo 0 h₀) ∧
        ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), QuarterJetIntegrable 1 0 D h ∧ ∀ μ : ℝ,
          IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
            Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume
              (-eighthPeriod h) (eighthPeriod h) ∧
          ‖quarterNumeratorDerivative μ g D h‖ ^ 2 ≤
            K / h * quarterJetEnergy 1 0 D h + K / (h * √h) := by
  have hU := hp.isOrbitUnion.1
  have hgs : MemSobolevOn 2 U g := hp.memSobolevOn.congr_ae_on hU.measurableSet
    ((ae_restrict_iff' hU.measurableSet).1 hfg)
  choose G hG hGL using hgs.2
  let D : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
    | [] => g
    | [j] => G j
    | _ => 0
  have hD (j : Fin 2) : HasWeakPartialOn U j g (D [j]) := hG j
  have hDL (j : Fin 2) : MemLp (D [j]) 2 (volume.restrict U) := (hGL j).1
  exact ⟨D, fun j ↦ ⟨hD j, hDL j⟩,
    hp.zero_saddle_numerator_estimates_of_gradient hcell hg hfg hz hD hDL⟩

end NoEmbeddedEigenvalues
