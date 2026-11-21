import NoEmbeddedEigenvalues.Transport.WeightedGains.WeightedQuarterGradient
import NoEmbeddedEigenvalues.Transport.WeightedGains.SubcriticalForcing
import Mathlib.Topology.Compactness.Lindelof

/-!
# First numerator derivatives from subcritical weighted forcing

Blueprint: `lem:subcritical-numerator-derivative`.

The original specified first weak gradient supplies both the exact local
moving-endpoint derivative and its weighted fiber energy. A complementary
positive time moment controls the bulk, while continuous endpoint values
cost h^(-δ) in squared energy. All real frequencies share one collar and
one majorant. No second numerator derivative or weak-gradient ray value is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- Compatible local interval H¹ data make the specified derivative a.e.
strongly measurable on the whole open interval. No global energy is assumed. -/
theorem HasIntervalH1Loc.aestronglyMeasurable_derivative {a b : ℝ} {N N₁ : ℝ → ℂ}
    (hN : HasIntervalH1Loc a b N N₁) :
    AEStronglyMeasurable N₁ (volume.restrict (Ioo a b)) := by
  classical
  have hloc (x : Ioo a b) : ∃ c d : ℝ, a < c ∧ c < x ∧ x < d ∧ d < b ∧
      HasIntervalH1 c d N N₁ := by
    obtain ⟨c, hac, hcx⟩ := exists_between x.property.1
    obtain ⟨d, hxd, hdb⟩ := exists_between x.property.2
    exact ⟨c, d, hac, hcx, hxd, hdb, hN c d hac (hcx.trans hxd) hdb⟩
  choose c d hac hcx hxd hdb hH using hloc
  let W (x : Ioo a b) := Ioo (c x) (d x)
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof (Ioo a b)).elim_countable_subcover
    W (fun _ ↦ isOpen_Ioo)
    (fun x hx ↦ mem_iUnion_of_mem ⟨x, hx⟩ ⟨hcx ⟨x, hx⟩, hxd ⟨x, hx⟩⟩)
  let : Countable s := hs.to_subtype
  have hm : AEStronglyMeasurable N₁ (volume.restrict (⋃ i : s, W i.val)) :=
    AEStronglyMeasurable.iUnion fun i : s ↦ (hH i.val).memLp_derivative.aestronglyMeasurable
  apply hm.mono_measure (Measure.restrict_mono_set _ ?_)
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
  exact mem_iUnion_of_mem ⟨i, hi⟩ hxi

/-- The bulk and original continuous endpoint values give the precise
subcritical squared bound for the moving-endpoint numerator derivative. -/
theorem quarterNumeratorDerivative_subcritical_sq_le
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℂ} {h δ C A B M : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hG : ∀ j : Fin 2, MemLp (fun t ↦ D [j] (dipoleOrbit h t) /
      (Real.rpow (saddleDist (dipoleOrbit h t)) (2 - δ) : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) (2 - 2 * δ)) ≤ A)
    (hL : |deriv eighthPeriod h| ≤ B / h)
    (hp : ‖g (dipoleOrbit h (eighthPeriod h))‖ ≤ M * h ^ ((2 - δ) / 2))
    (hm : ‖g (dipoleOrbit h (-eighthPeriod h))‖ ≤ M * h ^ ((2 - δ) / 2)) (lam : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    ‖quarterNumeratorDerivative lam g D h‖ ^ 2 ≤
      (4 * C ^ 2 * A) * quarterJetEnergy 1 (2 - δ) D h + (8 * B ^ 2 * M ^ 2) * h ^ (-δ) := by
  obtain ⟨hi, hb⟩ := quarterForcingLevelDerivative_weighted_integral_bound hh hC hG hd hV
    (by simpa only [show 2 * (2 - δ) - 2 = 2 - 2 * δ by ring] using hMoment) lam
  let Z := ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (eighthPeriod h)) *
      Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) +
     g (dipoleOrbit h (-eighthPeriod h)) *
      Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ)))
  have hphase (t : ℝ) : ‖Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hZ : ‖Z‖ ≤ (B / h) * (2 * M * h ^ ((2 - δ) / 2)) := by
    dsimp only [Z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hL _ (norm_nonneg _) (div_nonneg hB hh.1.le)
    calc
      _ ≤ ‖g (dipoleOrbit h (eighthPeriod h)) *
          Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ))‖ +
        ‖g (dipoleOrbit h (-eighthPeriod h)) *
          Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ))‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, hphase, mul_one]; linarith
  have hpow : (h ^ ((2 - δ) / 2)) ^ 2 / h ^ 2 = h ^ (-δ) := by
    have he : (h ^ ((2 - δ) / 2)) ^ 2 = h ^ (2 - δ) := by
      rw [← rpow_natCast, ← rpow_mul hh.1.le]
      congr 1
      ring
    rw [he, ← rpow_two, ← rpow_sub hh.1]
    congr 1
    ring
  have hZ2 : ‖Z‖ ^ 2 ≤ (4 * B ^ 2 * M ^ 2) * h ^ (-δ) := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (div_nonneg hB hh.1.le)
        (mul_nonneg (mul_nonneg (by norm_num) hM) (rpow_nonneg hh.1.le _)))).2 hZ
    calc
      _ ≤ ((B / h) * (2 * M * h ^ ((2 - δ) / 2))) ^ 2 := hs
      _ = 4 * B ^ 2 * M ^ 2 * ((h ^ ((2 - δ) / 2)) ^ 2 / h ^ 2) := by ring
      _ = _ := by rw [hpow]
  refine ⟨hi, ?_⟩
  change ‖(∫ t in (-eighthPeriod h)..eighthPeriod h,
    quarterForcingLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) + Z‖ ^ 2 ≤ _
  exact (norm_add_sq_le _ _).trans ((mul_le_mul_of_nonneg_left (add_le_add hb hZ2)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- The supplied first weak gradient gives one common quantitative collar for
all real frequencies. Only δ < 1 is needed for this numerator estimate. -/
theorem IsTransportPair.subcritical_numerator_estimates
    {lam δ : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hb : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U) (hδ : δ < 1)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D [j]))
    (hw : ∀ j, MemLp (fun p ↦ D [j] p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ μ : ℝ, HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g D)) ∧
      IntegrableOn (quarterJetEnergy 1 (2 - δ) D) (Ioo 0 h₀) ∧
      (∀ μ : ℝ, MemLp (quarterNumeratorDerivative μ g D) 2 (volume.restrict (Ioo 0 h₀))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), QuarterJetIntegrable 1 (2 - δ) D h ∧ ∀ μ : ℝ,
        IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
        ‖quarterNumeratorDerivative μ g D h‖ ^ 2 ≤
          K * quarterJetEnergy 1 (2 - δ) D h + K * h ^ (-δ) := by
  have hs : 0 < 2 - δ := by linarith
  obtain ⟨F, hF, hglobal⟩ := exists_cell_forcing_rpow_bound hb hcell hg hs hbound
  obtain ⟨M, rF, hM, hrF, hrFh, _, hEnds⟩ := forcing_rpow_orbit_bounds hs hF hglobal
  obtain ⟨C, rV, hrV, _, hVector⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨A, rI, hrI, hMoment⟩ := integral_saddleDist_rpow_pos_le
    (show 0 < 2 - 2 * δ by linarith)
  obtain ⟨cL, B, rL, hcL, hB, hrL, _, hPeriod⟩ := eighthPeriod_derivative_bounds
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
  have hfg' := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hgs : MemSobolevOn 2 U g := hp.memSobolevOn.congr_ae_on hU.measurableSet hfg'
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (D [j]) :=
    (hD j).congr_ae_on hU.measurableSet hfg' (Eventually.of_forall fun _ _ ↦ rfl)
  have hDL (j : Fin 2) : MemLp (D [j]) 2 (volume.restrict U) := by
    obtain ⟨G, hG, hGL⟩ := hp.memSobolevOn.2 j
    exact hGL.1.ae_eq ((ae_restrict_iff' hU.measurableSet).2 (hG.ae_eq hU (hD j)))
  have hloc (μ : ℝ) := quarterNumerator_derivative_h1Loc
    (lam := μ) hU hg hgs.1 hDg hDL (subset_closure.trans hcell) hh₀1
  obtain ⟨hE, hFib⟩ := quarterWeightedGradient_energy_integrable hh₀1.le hw
  let K := 4 * |C| ^ 2 * |A| + 8 * B ^ 2 * M ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKA : 4 * |C| ^ 2 * |A| ≤ K := by
    dsimp [K]; nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg M)]
  have hKB : 8 * B ^ 2 * M ^ 2 ≤ K := by
    dsimp [K]; nlinarith [mul_nonneg (sq_nonneg |C|) (abs_nonneg A)]
  have hBounds : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), QuarterJetIntegrable 1 (2 - δ) D h ∧
      ∀ μ : ℝ, IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative D (h, t) *
        Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
        ‖quarterNumeratorDerivative μ g D h‖ ^ 2 ≤
          K * quarterJetEnergy 1 (2 - δ) D h + K * h ^ (-δ) := by
    filter_upwards [hFib, ae_restrict_mem measurableSet_Ioo] with h hFiber hh
    have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, hh.2.trans hh₀1⟩
    have htL := eighthPeriod_pos hh1.1 hh1.2
    have hPer := hPeriod h ⟨hh.1, hh.2.trans_le hL₀⟩
    have hLneg : deriv eighthPeriod h < 0 := by nlinarith [hPer.1, hh.1]
    have hLbound : |deriv eighthPeriod h| ≤ B / h := by
      rw [abs_of_neg hLneg]
      exact (le_div_iff₀ hh.1).2 (by nlinarith [hPer.2.1])
    have hEndp := hEnds h ⟨hh.1, hh.2.trans_le hF₀⟩ (eighthPeriod h) (abs_of_pos htL)
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
    have hi := (hMoment h ⟨hh.1, hh.2.trans_le hI₀⟩).trans (le_abs_self A)
    refine ⟨hFiber.1, fun μ ↦ ?_⟩
    obtain ⟨hInt, hBound⟩ := quarterNumeratorDerivative_subcritical_sq_le
      hh1 (abs_nonneg C) hB.le hM.le hFiber.2 hd hv hi hLbound hEndp hEndm μ
    refine ⟨hInt, hBound.trans ?_⟩
    exact add_le_add
      (mul_le_mul_of_nonneg_right hKA
        (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (mul_le_mul_of_nonneg_right hKB (rpow_nonneg hh.1.le _))
  have hInv : IntegrableOn (fun h : ℝ ↦ h ^ (-δ)) (Ioo 0 h₀) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hh₀).2 (by linarith)
  have hMajor : IntegrableOn (fun h ↦ K * quarterJetEnergy 1 (2 - δ) D h + K * h ^ (-δ))
      (Ioo 0 h₀) := (hE.const_mul K).add (hInv.const_mul K)
  refine ⟨K, h₀, hK, hh₀, hh₀h, hloc, hE, fun μ ↦ ?_, hBounds⟩
  have hm := HasIntervalH1Loc.aestronglyMeasurable_derivative (hloc μ)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply hMajor.mono' (hm.norm.pow 2)
  filter_upwards [hBounds] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (hh.2 μ).2

/-- The exact `Fin 2` first gradient of Second transport gain produces the
same data. The list adapter retains its singleton entries definitionally;
all other entries are zero and no second weak derivative is requested. -/
theorem IsTransportPair.subcritical_numerator_estimates_of_first_gradient
    {lam δ : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hb : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U) (hδ : δ < 1)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare)) :
    let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ match w with
      | [j] => D j
      | _ => 0
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ μ : ℝ, HasIntervalH1Loc 0 h₀ (quarterNumerator μ g) (quarterNumeratorDerivative μ g J)) ∧
      IntegrableOn (quarterJetEnergy 1 (2 - δ) J) (Ioo 0 h₀) ∧
      (∀ μ : ℝ, MemLp (quarterNumeratorDerivative μ g J) 2 (volume.restrict (Ioo 0 h₀))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), QuarterJetIntegrable 1 (2 - δ) J h ∧ ∀ μ : ℝ,
        IntervalIntegrable (fun t ↦ quarterForcingLevelDerivative J (h, t) *
          Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
        ‖quarterNumeratorDerivative μ g J h‖ ^ 2 ≤
          K * quarterJetEnergy 1 (2 - δ) J h + K * h ^ (-δ) := by
  exact hp.subcritical_numerator_estimates (D := fun w ↦ match w with
    | [j] => D j
    | _ => 0) hb hcell hδ hg hfg hbound hD hw

end NoEmbeddedEigenvalues
