import NoEmbeddedEigenvalues.WeightedEndpointValues
import NoEmbeddedEigenvalues.SubcriticalNumerator
import NoEmbeddedEigenvalues.OrbitHalfNumeratorDerivative

/-!
# First derivatives of the weighted full and half numerators

Blueprint: `lem:weighted-first-numerator`, `lem:weighted-half-numerator`.

The moving-endpoint formula costs the actual endpoint value energy, not a
pointwise envelope. Weighted Cauchy–Schwarz controls the bulk with the original
first weak gradient. The continuous endpoint trace theorem supplies its missing
L² energy. Both derivatives have one collar and one integrable majorant for
all real frequencies; the half numerator has no moving midpoint term.
No second numerator derivative or gradient-ray value is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- The exact first derivative costs only bulk first-gradient and endpoint
value energies. All frequencies have the same constants. -/
theorem quarterNumeratorDerivative_weighted_sq_le
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℂ} {h C A B : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
      (Real.rpow (saddleDist (dipoleOrbit h t)) (3 / 2) : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) 1) ≤ A)
    (hL : |deriv eighthPeriod h| ≤ B / h) (μ : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    ‖quarterNumeratorDerivative μ g D h‖ ^ 2 ≤
      4 * C ^ 2 * A * quarterJetEnergy 1 (3 / 2) D h +
        4 * B ^ 2 * quarterEndpointValueEnergy g h := by
  obtain ⟨hi, hb⟩ := quarterForcingLevelDerivative_weighted_integral_bound hh hC hG hd hV
    (by convert hMoment using 1; norm_num) μ
  let Z := ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (eighthPeriod h)) *
      Complex.exp (-Complex.I * ((μ * eighthPeriod h : ℝ) : ℂ)) +
     g (dipoleOrbit h (-eighthPeriod h)) *
      Complex.exp (-Complex.I * ((μ * (-eighthPeriod h) : ℝ) : ℂ)))
  have hphase (t : ℝ) : ‖Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hZ : ‖Z‖ ^ 2 ≤ 2 * B ^ 2 * quarterEndpointValueEnergy g h := by
    dsimp only [Z]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    have hs := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hB hh.1.le)).2 hL
    have hadd := norm_add_sq_le
      (g (dipoleOrbit h (eighthPeriod h)) *
        Complex.exp (-Complex.I * ((μ * eighthPeriod h : ℝ) : ℂ)))
      (g (dipoleOrbit h (-eighthPeriod h)) *
        Complex.exp (-Complex.I * ((μ * (-eighthPeriod h) : ℝ) : ℂ)))
    simp only [norm_mul, hphase, mul_one] at hadd
    apply (mul_le_mul hs hadd (sq_nonneg _) (sq_nonneg _)).trans_eq
    simp only [quarterEndpointValueEnergy, Fintype.sum_bool,
      ← dipoleOrbit_quarterEndpointRay hh.1 hh.2 true,
      ← dipoleOrbit_quarterEndpointRay hh.1 hh.2 false, Bool.false_eq_true, ↓reduceIte]
    ring
  refine ⟨hi, ?_⟩
  change ‖(∫ t in (-eighthPeriod h)..eighthPeriod h,
    quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) + Z‖ ^ 2 ≤ _
  exact (norm_add_sq_le _ _).trans ((mul_le_mul_of_nonneg_left (add_le_add hb hZ)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- The half numerator costs one endpoint only. The same full-quarter bulk
energy controls its shorter integration interval. -/
theorem quarterHalfNumeratorDerivative_weighted_sq_le
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℂ} {h C A B : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
      (Real.rpow (saddleDist (dipoleOrbit h t)) (3 / 2) : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) 1) ≤ A)
    (hL : |deriv eighthPeriod h| ≤ B / h) (μ : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) 0 ∧
    ‖quarterHalfNumeratorDerivative μ g D h‖ ^ 2 ≤
      4 * C ^ 2 * A * quarterJetEnergy 1 (3 / 2) D h +
        2 * B ^ 2 * quarterEndpointValueEnergy g h := by
  have hLp := eighthPeriod_pos hh.1 hh.2
  obtain ⟨hi, hb⟩ := quarterForcingLevelDerivative_weighted_setIntegral_bound hh hC hG hd hV
    (by convert hMoment using 1; norm_num) μ (Icc (-eighthPeriod h) 0) measurableSet_Icc
    (fun t ht ↦ ⟨ht.1, ht.2.trans hLp.le⟩)
  let Z := ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (-eighthPeriod h)) *
      Complex.exp (-Complex.I * ((μ * (-eighthPeriod h) : ℝ) : ℂ)))
  have hphase : ‖Complex.exp (-Complex.I * ((μ * (-eighthPeriod h) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hZ : ‖Z‖ ^ 2 ≤ B ^ 2 * quarterEndpointValueEnergy g h := by
    dsimp only [Z]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_mul, hphase, mul_one]
    have hs := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hB hh.1.le)).2 hL
    apply (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans
    simp only [quarterEndpointValueEnergy, Fintype.sum_bool,
      ← dipoleOrbit_quarterEndpointRay hh.1 hh.2 true,
      ← dipoleOrbit_quarterEndpointRay hh.1 hh.2 false, Bool.false_eq_true, ↓reduceIte]
    convert mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (le_add_of_nonneg_left (sq_nonneg ‖g (dipoleOrbit h (eighthPeriod h))‖))
        (sq_nonneg h)) (sq_nonneg B) using 1
    ring
  have hi' : IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hi
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (by linarith : -eighthPeriod h ≤ 0)] at hb
  refine ⟨hi', ?_⟩
  change ‖(∫ t in (-eighthPeriod h)..0,
    quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) + Z‖ ^ 2 ≤ _
  exact (norm_add_sq_le _ _).trans ((mul_le_mul_of_nonneg_left (add_le_add hb hZ)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- One small cutoff supports the quantitative first-order estimates for the
supplied jet. The same full-fiber energy controls every ordered subinterval. -/
theorem weighted_first_numerator_fiber_bounds
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (g : ℝ × ℝ → ℂ)
    (hDf : ∀ j : Fin 2, MemLp (fun p ↦ D [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare)) :
    ∃ h₀ K : ℝ, 0 < h₀ ∧ h₀ ≤ 1 / 256 ∧ 0 < K ∧
      IntegrableOn (quarterJetEnergy 1 (3 / 2) D) (Ioo 0 h₀) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)),
        QuarterJetIntegrable 1 (3 / 2) D h ∧
        IntegrableOn (fun t ↦ quarterForcingLevelDerivative D (h, t))
          (Ioo (-eighthPeriod h) (eighthPeriod h)) ∧
        ∀ μ : ℝ,
          (∀ a b : ℝ, -eighthPeriod h ≤ a → a ≤ b → b ≤ eighthPeriod h →
            ‖∫ t in a..b, quarterForcingLevelDerivative D (h, t) *
              Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))‖ ^ 2 ≤
                K * quarterJetEnergy 1 (3 / 2) D h) ∧
          ‖quarterNumeratorDerivative μ g D h‖ ^ 2 +
            ‖quarterHalfNumeratorDerivative μ g D h‖ ^ 2 ≤
              K * (quarterJetEnergy 1 (3 / 2) D h + quarterEndpointValueEnergy g h) := by
  obtain ⟨C, rV, hrV, _, hVector⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨A, rI, hrI, hMoment⟩ := integral_saddleDist_rpow_pos_le (by norm_num : (0 : ℝ) < 1)
  obtain ⟨cL, B, rL, hcL, hB, hrL, _, hPeriod⟩ := eighthPeriod_derivative_bounds
  obtain ⟨c, S, rS, hc, hrS, hDistance⟩ := saddleDist_dipoleOrbit
  let h₀ := min (1 / 256) (min rV (min rI (min rL rS)))
  have hh₀ : 0 < h₀ := lt_min (by norm_num) (lt_min hrV (lt_min hrI (lt_min hrL hrS)))
  have hF₀ : h₀ ≤ 1 / 256 := min_le_left _ _
  have hV₀ : h₀ ≤ rV := (min_le_right _ _).trans (min_le_left _ _)
  have hI₀ : h₀ ≤ rI :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hL₀ : h₀ ≤ rL :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hS₀ : h₀ ≤ rS :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  have hh₀1 : h₀ < 1 := by linarith
  obtain ⟨hE, hFib⟩ := quarterWeightedGradient_energy_integrable hh₀1.le hDf
  let K := 8 * |C| ^ 2 * |A| + 6 * B ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKbulk : 8 * |C| ^ 2 * |A| ≤ K := by
    dsimp [K]
    linarith only [sq_nonneg B]
  have hKval : 6 * B ^ 2 ≤ K := by
    dsimp [K]
    linarith only [show 0 ≤ 8 * |C| ^ 2 * |A| by positivity]
  refine ⟨h₀, K, hh₀, hF₀, hK, hE, ?_⟩
  filter_upwards [hFib, ae_restrict_mem measurableSet_Ioo] with h hFiber hh
  have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, hh.2.trans hh₀1⟩
  have hPer := hPeriod h ⟨hh.1, hh.2.trans_le hL₀⟩
  have hLneg : deriv eighthPeriod h < 0 := by nlinarith [hPer.1, hh.1]
  have hLbound : |deriv eighthPeriod h| ≤ B / h := by
    rw [abs_of_neg hLneg]
    exact (le_div_iff₀ hh.1).2 (by nlinarith [hPer.2.1])
  have hd (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      0 < saddleDist (dipoleOrbit h t) :=
    (mul_pos hc (exp_pos _)).trans_le
      (hDistance h ⟨hh.1, hh.2.trans_le hS₀⟩ t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)).1
  have hv (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ |C| / saddleDist (dipoleOrbit h t) :=
    (hVector h ⟨hh.1, hh.2.trans_le hV₀⟩ t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)).1.trans
      (div_le_div_of_nonneg_right (le_abs_self C) (hd t ht).le)
  have hMoment' : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) (2 * (3 / 2 : ℝ) - 2)) ≤ |A| := by
    rw [show 2 * (3 / 2 : ℝ) - 2 = 1 by norm_num]
    exact (hMoment h ⟨hh.1, hh.2.trans_le hI₀⟩).trans (le_abs_self A)
  have hEpos : 0 ≤ quarterJetEnergy 1 (3 / 2) D h :=
    integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hVpos : 0 ≤ quarterEndpointValueEnergy g h :=
    div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
  have hset := quarterForcingLevelDerivative_weighted_setIntegral_bound (D := D)
    hh1 (abs_nonneg C) hFiber.2 hd hv hMoment'
  have hbare := (hset 0 (Ioo (-eighthPeriod h) (eighthPeriod h))
    measurableSet_Ioo Ioo_subset_Icc_self).1
  refine ⟨hFiber.1, by simpa using hbare, fun μ ↦ ⟨?_, ?_⟩⟩
  · intro a b ha hab hb
    have hsub : Icc a b ⊆ Icc (-eighthPeriod h) (eighthPeriod h) := Icc_subset_Icc ha hb
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact ((hset μ (Icc a b) measurableSet_Icc hsub).2).trans
      (mul_le_mul_of_nonneg_right (by
        linarith only [hKbulk, show 0 ≤ |C| ^ 2 * |A| by positivity]) hEpos)
  · have hm : (∫ t in (-eighthPeriod h)..eighthPeriod h,
        Real.rpow (saddleDist (dipoleOrbit h t)) 1) ≤ |A| := by
      simpa only [show 2 * (3 / 2 : ℝ) - 2 = 1 by norm_num] using hMoment'
    have hfull := (quarterNumeratorDerivative_weighted_sq_le (g := g)
      hh1 (abs_nonneg C) hB.le hFiber.2 hd hv hm hLbound μ).2
    have hhalf := (quarterHalfNumeratorDerivative_weighted_sq_le (g := g)
      hh1 (abs_nonneg C) hB.le hFiber.2 hd hv hm hLbound μ).2
    calc
      _ ≤ 8 * |C| ^ 2 * |A| * quarterJetEnergy 1 (3 / 2) D h +
          6 * B ^ 2 * quarterEndpointValueEnergy g h := (add_le_add hfull hhalf).trans_eq (by ring)
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right hKbulk hEpos)
          (mul_le_mul_of_nonneg_right hKval hVpos)

/-- Original weighted forcing and its supplied first weak gradient produce
compatible local H¹ and actual L² derivatives of both numerators on one collar. No character,
pointwise forcing bound or second weak jet is requested. -/
theorem IsTransportPair.weighted_numerator_first_derivatives
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
      | [j] => D j
      | _ => 0
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
      (HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J) ∧
        MemLp (quarterNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀))) ∧
      (HasIntervalH1Loc 0 h₀ (quarterHalfNumerator μ g) (quarterHalfNumeratorDerivative μ g J) ∧
        MemLp (quarterHalfNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀))) := by
  let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
    | [j] => D j
    | _ => 0
  change ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
    (HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J) ∧
      MemLp (quarterNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀))) ∧
    (HasIntervalH1Loc 0 h₀ (quarterHalfNumerator μ g) (quarterHalfNumeratorDerivative μ g J) ∧
      MemLp (quarterHalfNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀)))
  have hU := hp.isOrbitUnion.1
  have hfg' := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hgs : MemSobolevOn 2 U g := hp.memSobolevOn.congr_ae_on hU.measurableSet hfg'
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (J [j]) :=
    (hD j).congr_ae_on hU.measurableSet hfg' (Eventually.of_forall fun _ _ ↦ rfl)
  have hDL (j : Fin 2) : MemLp (J [j]) 2 (volume.restrict U) := by
    obtain ⟨G, hG, hGL⟩ := hp.memSobolevOn.2 j
    exact hGL.1.ae_eq ((ae_restrict_iff' hU.measurableSet).2 (hG.ae_eq hU (hD j)))
  have hfG : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply hf.ae_eq
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hcell) hfg]
      with p hp
    rw [hp]
  obtain ⟨h₀, K, hh₀, hF₀, _, hE, hBounds⟩ :=
    weighted_first_numerator_fiber_bounds g (D := J) hDf
  have hh₀h : h₀ < 1 / 2 := by linarith
  have hh₀1 : h₀ < 1 := by linarith
  have hloc (μ : ℝ) := quarterNumerator_derivative_h1Loc
    (lam := μ) hU hg hgs.1 hDg hDL (subset_closure.trans hcell) hh₀1
  have hhalf (μ : ℝ) := quarterHalfNumerator_derivative_h1Loc
    (lam := μ) hU hg hgs.1 hDg hDL (subset_closure.trans hcell) hh₀1
  have hEnds := weighted_quarter_endpoint_values hU hcell hg hDg hfG hDf hh₀ hF₀
  have hEe (h : ℝ) :
      ‖g (quarterEndpointRay false (quarterEndpointRadius h)) / (h : ℂ)‖ ^ 2 +
        ‖g (quarterEndpointRay true (quarterEndpointRadius h)) / (h : ℂ)‖ ^ 2 =
          quarterEndpointValueEnergy g h := by
    simp only [quarterEndpointValueEnergy, Fintype.sum_bool, norm_div, div_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hEnd : IntegrableOn (quarterEndpointValueEnergy g) (Ioo 0 h₀) :=
    ((hEnds false).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      ((hEnds true).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) |>.congr
        (Eventually.of_forall hEe)
  have hMajor : IntegrableOn (fun h ↦ K * (quarterJetEnergy 1 (3 / 2) J h +
      quarterEndpointValueEnergy g h)) (Ioo 0 h₀) := (hE.add hEnd).const_mul K
  refine ⟨h₀, hh₀, hh₀h, fun μ ↦ ⟨⟨hloc μ, ?_⟩, ⟨hhalf μ, ?_⟩⟩⟩
  · have hm := HasIntervalH1Loc.aestronglyMeasurable_derivative (hloc μ)
    apply (memLp_two_iff_integrable_sq_norm hm).2
    apply hMajor.mono' (hm.norm.pow 2)
    filter_upwards [hBounds] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans ((hh.2.2 μ).2)
  · have hm := HasIntervalH1Loc.aestronglyMeasurable_derivative (hhalf μ)
    apply (memLp_two_iff_integrable_sq_norm hm).2
    apply hMajor.mono' (hm.norm.pow 2)
    filter_upwards [hBounds] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (le_add_of_nonneg_left (sq_nonneg _)).trans ((hh.2.2 μ).2)

/-- Original weighted forcing and its supplied first weak gradient produce
compatible local H¹ and actual L² first numerator derivatives. No character,
pointwise forcing bound or second weak jet is requested. -/
theorem IsTransportPair.weighted_first_numerator_estimates
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
      | [j] => D j
      | _ => 0
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
      HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J) ∧
        MemLp (quarterNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀)) := by
  obtain ⟨h₀, hh₀, hh₀h, hAll⟩ :=
    hp.weighted_numerator_first_derivatives hcell hg hfg hD hf hDf
  exact ⟨h₀, hh₀, hh₀h, fun μ ↦ (hAll μ).1⟩

end NoEmbeddedEigenvalues
