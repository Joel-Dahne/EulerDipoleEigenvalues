import NoEmbeddedEigenvalues.WeightedEndpointValues
import NoEmbeddedEigenvalues.SubcriticalNumerator

/-!
# First numerator regularity from weighted L² forcing

Blueprint: `lem:weighted-first-numerator`.

The moving-endpoint formula costs the actual endpoint value energy, not a
pointwise envelope. Weighted Cauchy–Schwarz controls the bulk with the original
first weak gradient. The continuous endpoint trace theorem supplies its missing
L² energy. No second numerator derivative or gradient-ray value is used.
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
  let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
    | [j] => D j
    | _ => 0
  change ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ ∀ μ : ℝ,
    HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J) ∧
      MemLp (quarterNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀))
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
  have hh₀h : h₀ < 1 / 2 := by linarith
  have hh₀1 : h₀ < 1 := by linarith
  have hloc (μ : ℝ) := quarterNumerator_derivative_h1Loc
    (lam := μ) hU hg hgs.1 hDg hDL (subset_closure.trans hcell) hh₀1
  obtain ⟨hE, hFib⟩ := quarterWeightedGradient_energy_integrable hh₀1.le (D := J) hDf
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
  let K := 4 * |C| ^ 2 * |A| + 4 * B ^ 2 + 1
  have hKA : 4 * |C| ^ 2 * |A| ≤ K := by dsimp [K]; nlinarith [sq_nonneg B]
  have hKB : 4 * B ^ 2 ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg (sq_nonneg |C|) (abs_nonneg A)]
  have hBounds : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∀ μ : ℝ,
      ‖quarterNumeratorDerivative μ g J h‖ ^ 2 ≤
        K * quarterJetEnergy 1 (3 / 2) J h + K * quarterEndpointValueEnergy g h := by
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
    intro μ
    obtain ⟨_, hbound⟩ := quarterNumeratorDerivative_weighted_sq_le hh1 (abs_nonneg C) hB.le
      hFiber.2 hd hv ((hMoment h ⟨hh.1, hh.2.trans_le hI₀⟩).trans (le_abs_self A)) hLbound μ
    apply hbound.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right hKA
        (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (mul_le_mul_of_nonneg_right hKB (div_nonneg
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _)))
  have hMajor : IntegrableOn (fun h ↦ K * quarterJetEnergy 1 (3 / 2) J h +
      K * quarterEndpointValueEnergy g h) (Ioo 0 h₀) := (hE.const_mul K).add (hEnd.const_mul K)
  refine ⟨h₀, hh₀, hh₀h, fun μ ↦ ⟨hloc μ, ?_⟩⟩
  have hm := HasIntervalH1Loc.aestronglyMeasurable_derivative (hloc μ)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply hMajor.mono' (hm.norm.pow 2)
  filter_upwards [hBounds] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hh μ

end NoEmbeddedEigenvalues
