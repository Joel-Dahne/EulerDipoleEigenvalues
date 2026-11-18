import NoEmbeddedEigenvalues.WeightedTransportH1Data
import NoEmbeddedEigenvalues.OrdinaryQuarterForcing
import NoEmbeddedEigenvalues.WeightedTransportMass
import NoEmbeddedEigenvalues.QuarterTimeDerivative

/-!
# Single-character weighted weak quarter derivatives

Blueprint: `lem:weighted-character-base-derivatives`,
`lem:weighted-character-quarter-derivatives`, `lem:quarter-raw-congruence`.

Scalar midpoint H¹ and the actual signed forcing primitive give the level
weak derivative. The original weak transport identity gives the time weak
derivative. Both are joint fields of the original raw pullback. Constant
rotation characters transfer them to every recentered quarter.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

private theorem restrict_h1 {b c : ℝ} {F G : ℝ → ℂ}
    (h : HasIntervalH1 0 b F G) (hcb : c ≤ b) : HasIntervalH1 0 c F G := by
  have hs : Ioo (0 : ℝ) c ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl hcb
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono_set _ hs),
    h.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hs),
    fun a d ha had hd ↦ h.locally_absolutelyContinuous a d ha had (hd.trans_le hcb),
    h.hasDerivAt_ae.mono fun x hx hxI ↦ hx (hs hxI)⟩

private theorem sin_distance_top (b : ℝ) (j : Fin 2) :
    MemLp (fun q : ℝ × ℝ ↦
      (Real.sin (if j = 0 then (dipoleOrbit q.1 q.2).1 else (dipoleOrbit q.1 q.2).2) : ℂ) /
        (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) ⊤ (volume.restrict (quarterOrbitStrip b)) := by
  have hs : Continuous (fun p : ℝ × ℝ ↦
      (Real.sin (if j = 0 then p.1 else p.2) : ℂ)) := by split_ifs <;> fun_prop
  have hd : Continuous (fun q : ℝ × ℝ ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit)
  apply memLp_top_of_bound
    ((hs.comp continuous_dipoleOrbit).measurable.div hd.measurable).aestronglyMeasurable 1
  exact Eventually.of_forall fun q ↦ by
    change ‖(Real.sin (if j = 0 then (dipoleOrbit q.1 q.2).1 else
      (dipoleOrbit q.1 q.2).2) : ℂ) / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)‖ ≤ 1
    by_cases hz : saddleDist (dipoleOrbit q.1 q.2) = 0
    · simp [hz]
    have hp : 0 < saddleDist (dipoleOrbit q.1 q.2) :=
      lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hz)
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact (div_le_one hp).2 (abs_sin_axis_le_saddleDist _ j)

/-- A restricted raw character transfers jointly to every recentered quarter,
without a global measurable representative or differentiated time shift. -/
theorem HasQuarterCharacterOn.recentered_ae {b : ℝ} (hb : b ≤ 1)
    {κ : ℂ} {F : ℝ × ℝ → ℂ} (hκ : HasQuarterCharacterOn κ cellSquare F)
    (hF : MemLp F 2 (volume.restrict cellSquare)) (k : Fin 4) :
    (fun q ↦ F (recenteredQuarterMap k q)) =ᵐ[volume.restrict (quarterOrbitStrip b)]
      (fun q ↦ κ ^ k.val * F (dipoleOrbit q.1 q.2)) := by
  have hcell : rotLift ⁻¹' cellSquare = cellSquare := by
    ext p
    exact (rotLift_cell_level p).1
  have hm : MeasurePreserving rotLift (volume.restrict cellSquare)
      (volume.restrict cellSquare) := by
    simpa only [hcell] using measurePreserving_rotLift.restrict_preimage
      isOpen_cellSquare.measurableSet
  have hsub : cellSeparatrixStrip (2 * b) ⊆ cellSquare := fun _ hp ↦ hp.1
  have hchar := (HasQuarterCharacterOn.iterate_cell_collar
    (ae_restrict_of_ae_restrict_of_subset hsub hκ) k.val)
  have hAnn : orbitAnnulus 0 b ⊆ cellSeparatrixStrip (2 * b) := by
    rw [cellSeparatrixStrip_eq_orbitAnnulus hb]
  exact ae_eq_comp_quarterOrbitStrip_of_memLp hb hAnn
    (hF.comp_measurePreserving (hm.iterate k.val)) (hF.const_mul (κ ^ k.val)) hchar

/-- The base quarter has genuine weak level/time fields and the two physical
weights, from ordinary scalar data and the original supplied Cartesian gradient. -/
theorem IsTransportPair.weighted_character_base_derivatives
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare))
    (hvκ : HasQuarterCharacterOn κ cellSquare v)
    (hfκ : HasQuarterCharacterOn κ cellSquare f)
    {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) (hscalar : HasQuarterH1ScalarData lam κ g r) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧ ∃ H T : ℝ × ℝ → ℂ,
      HasWeakPartialOn (quarterOrbitStrip b) 0 (fun q ↦ v (dipoleOrbit q.1 q.2)) H ∧
      HasWeakPartialOn (quarterOrbitStrip b) 1 (fun q ↦ v (dipoleOrbit q.1 q.2)) T ∧
      MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * H q) 2
        (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨Q, Q₁, hQ, hfac, hQh, _, hB⟩ := hscalar
  have hr1 : r < 1 := hrh.trans (by norm_num)
  have hcellU : cellSquare ⊆ U := subset_closure.trans hcell
  have hF := hp.memSobolevOn.memLp.mono_measure (Measure.restrict_mono_set _ hcellU)
  have hV := hp.memLp.mono_measure (Measure.restrict_mono_set _ hcellU)
  obtain ⟨J, hJ, hJD⟩ := hp.memSobolevOn.exists_weakJet_two_with_first hp.isOrbitUnion.1 hD
  have hDL (j : Fin 2) : MemLp (D j) 2 (volume.restrict cellSquare) := by
    rw [← hJD j]
    exact (hp.memSobolevOn.memLp_weakJet hp.isOrbitUnion.1 hJ [j] (by simp)).mono_measure
      (Measure.restrict_mono_set _ hcellU)
  have hJG : quarterPullbackDerivative D 0 = quarterForcingLevelDerivative J := by
    funext q
    simp only [quarterPullbackDerivative, quarterForwardVector, ↓reduceIte,
      quarterForcingLevelDerivative, hJD]
  have hImage : quarterImage r ⊆ U := fun p hp ↦ hcellU hp.1.1.1
  have hGf := HasWeakPartialOn.comp_quarterOrbit hr1.le hImage hD hF hDL 0
  rw [hJG] at hGf
  obtain ⟨a, ha, har, hA⟩ := ordinary_midpoint_h1 hr hr1 hQ hQh hB
  obtain ⟨η, hη, hηa, hne⟩ := exists_ae_quarterDivisor_ne_zero hp.ne_zero hκ ha
  have hηr : η < r := hηa.trans har
  have hQsub : quarterOrbitStrip η ⊆ quarterOrbitStrip r :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans hηr, hq.2.2⟩
  obtain ⟨b, C, hb, hbη, hdt, hGL, hMoment, E, hE, hEp, hBound⟩ :=
    ordinary_quarter_forcing_data hη (hηr.trans hr1)
      (fun j ↦ by simpa only [hJD] using hDf j)
      (hGf.mono hQsub).2.1.aestronglyMeasurable
  have hbr : b < r := hbη.trans hηr
  have hba : b < a := hbη.trans hηa
  have hb1 : b < 1 := hbr.trans hr1
  have hSub : quarterOrbitStrip b ⊆ quarterOrbitStrip r :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans hbr, hq.2.2⟩
  have hAnn : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcellU hp.1.1
  have hvChar := ae_restrict_of_ae_restrict_of_subset
    (show orbitAnnulus 0 b ⊆ cellSquare from fun _ hp ↦ hp.1.1) hvκ
  have hfChar := ae_restrict_of_ae_restrict_of_subset
    (show orbitAnnulus 0 b ⊆ cellSquare from fun _ hp ↦ hp.1.1) hfκ
  have hAb := restrict_h1 hA hba.le
  have hneB := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hbη.le) hne
  have hFacB := fun h (hh : h ∈ Ioo 0 b) ↦ hfac h ⟨hh.1, hh.2.trans hbr⟩
  have hRecon := hp.quarterReconstruction_ae hκ hcell hg hfg hb hb1 hvChar hfChar hAb hFacB hneB
  have hGfb := hGf.mono hSub
  have hFg : MemLp g 2 (volume.restrict cellSquare) :=
    (hp.memSobolevOn.memLp.ae_eq hfg).mono_measure (Measure.restrict_mono_set _ hcellU)
  have hfgq := ae_eq_comp_quarterOrbitStrip_of_memLp hb1.le hAnn hF hFg hfg
  have hGg := hGfb.congr_ae_on (measurableSet_quarterOrbitStrip b)
    ((ae_restrict_iff' (measurableSet_quarterOrbitStrip b)).1 hfgq)
    (Eventually.of_forall fun _ _ ↦ rfl)
  have hAloc : HasIntervalH1Loc 0 b (quarterMidpoint lam Q g)
      (quarterMidpointDerivative lam Q Q₁ (deriv (quarterHalfNumerator lam g))) :=
    fun u w hu _ hw ↦
      ⟨hAb.memLp_value.mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo hu.le hw.le)),
        hAb.memLp_derivative.mono_measure
          (Measure.restrict_mono_set _ (Ioo_subset_Ioo hu.le hw.le)),
        fun c d hc hcd hd ↦ hAb.locally_absolutelyContinuous c d (hu.le.trans_lt hc) hcd
          (hd.trans_le hw.le),
        hAb.hasDerivAt_ae.mono fun x hx hxI ↦ hx ⟨hu.le.trans_lt hxI.1, hxI.2.trans_le hw.le⟩⟩
  have hRweak := quarterReconstruction_weak_of_intervalH1Loc hb1.le hAloc hGg lam
  have hZweak := hRweak.congr_ae_on (measurableSet_quarterOrbitStrip b)
    ((ae_restrict_iff' (measurableSet_quarterOrbitStrip b)).1 hRecon)
    (Eventually.of_forall fun _ _ ↦ rfl)
  let R := quarterReconstructionLevel lam
    (quarterMidpointDerivative lam Q Q₁ (deriv (quarterHalfNumerator lam g)))
    (quarterForcingLevelDerivative J)
  let H : ℝ × ℝ → ℂ := fun q ↦ -(lam : ℂ) * R q - quarterForcingLevelDerivative J q
  have hH : HasWeakPartialOn (quarterOrbitStrip b) 0 (fun q ↦ v (dipoleOrbit q.1 q.2)) H := by
    apply (HasWeakPartialOn.add (hZweak.const_mul (-(lam : ℂ)))
      (hGfb.const_mul (-1))).congr_ae_on
      (measurableSet_quarterOrbitStrip b)
    · exact Eventually.of_forall fun q _ ↦ by
        dsimp only [transportUnknown]
        field_simp [Complex.ofReal_ne_zero.mpr hp.ne_zero]
        ring
    · exact Eventually.of_forall fun q _ ↦ by dsimp [H, R]; ring
  have hRnorm := quarterReconstructionLevel_weighted_memLp hb1 hAb.memLp_derivative
    hGL.aestronglyMeasurable hE (Eventually.of_forall hEp) hMoment (hBound.mono fun _ hh ↦ hh lam)
  have hHnorm : MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * H q) 2
      (volume.restrict (quarterOrbitStrip b)) := by
    apply ((hRnorm.const_mul (-(lam : ℂ))).sub (hdt.mul hGL)).ae_eq
    exact Eventually.of_forall fun q ↦ by dsimp [H, R]; ring
  have hFPtime := HasWeakPartialOn.comp_quarterOrbit hb1.le
    (show quarterImage b ⊆ U from fun _ hp ↦ hcellU hp.1.1.1) hD hF hDL 1
  have hsumTime := hp.hasWeakL0On.quarter_time_of_memLp hb1 hAnn (hV.add hF)
    ((hV.const_mul (lam : ℂ)).const_mul Complex.I)
  let T : ℝ × ℝ → ℂ := fun q ↦
    Complex.I * ((lam : ℂ) * v (dipoleOrbit q.1 q.2)) - quarterPullbackDerivative D 1 q
  have hT : HasWeakPartialOn (quarterOrbitStrip b) 1 (fun q ↦ v (dipoleOrbit q.1 q.2)) T := by
    apply (HasWeakPartialOn.add hsumTime (hFPtime.const_mul (-1))).congr_ae_on
      (measurableSet_quarterOrbitStrip b)
    · exact Eventually.of_forall fun q _ ↦ by ring
    · exact Eventually.of_forall fun q _ ↦ by dsimp [T]; ring
  have hQraw : MemLp (fun h ↦ quarterQuotient lam κ g h / (h : ℂ)) 2
      (volume.restrict (Ioo 0 b)) := by
    apply (hQh.mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hbr.le))).ae_eq
    filter_upwards [hneB, ae_restrict_mem measurableSet_Ioo] with h hn hh
    rw [quarterQuotient, ← hFacB h hh, mul_div_cancel_left₀ _ hn]
  have hMass := hp.weighted_character_memLp_of_quotient hκ hcell hg hfg hf hb hvChar hfChar hQraw
  have hMp := memLp_comp_quarterOrbitStrip_of_memLp hb1.le hMass
  have hVd : MemLp (fun q ↦ v (dipoleOrbit q.1 q.2) /
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2 (volume.restrict (quarterOrbitStrip b)) := by
    apply (hdt.mul hMp).ae_eq
    exact Eventually.of_forall fun q ↦ by
      dsimp only [Pi.mul_apply]
      by_cases hz : saddleDist (dipoleOrbit q.1 q.2) = 0
      · simp [hz]
      · field_simp [Complex.ofReal_ne_zero.mpr hz]
  have hDp (j : Fin 2) := memLp_comp_quarterOrbitStrip_of_memLp hb1.le (hDL j)
  have hTf : MemLp (fun q ↦ quarterPullbackDerivative D 1 q /
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2 (volume.restrict (quarterOrbitStrip b)) := by
    apply (((sin_distance_top b 1).mul (hDp 0)).sub
      ((sin_distance_top b 0).mul (hDp 1))).ae_eq
    exact Eventually.of_forall fun q ↦ by
      simp only [Pi.mul_apply, Pi.sub_apply, quarterPullbackDerivative,
        quarterForwardVector, one_ne_zero, ↓reduceIte, dipoleVelocity, Complex.ofReal_neg]
      ring
  have hTnorm : MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
    apply (((hVd.const_mul (lam : ℂ)).const_mul Complex.I).sub hTf).ae_eq
    exact Eventually.of_forall fun q ↦ by dsimp [T]; ring
  exact ⟨b, hb, hbr, H, T, hH, hT, hHnorm, hTnorm⟩

/-- Reconstruct one character's raw weak profiles on all recentered quarters
from ordinary scalar data. This includes the weighted level and time estimates,
not spatial seam gluing (`lem:weighted-character-quarter-derivatives`). -/
theorem IsTransportPair.weighted_character_quarter_derivatives
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare))
    (hvκ : HasQuarterCharacterOn κ cellSquare v)
    (hfκ : HasQuarterCharacterOn κ cellSquare f)
    {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) (hscalar : HasQuarterH1ScalarData lam κ g r) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧ ∃ A B : Fin 4 → ℝ × ℝ → ℂ,
      HasWeightedQuarterDerivatives b v A B := by
  obtain ⟨b, hb, hbr, H, T, hH, hT, hHnorm, hTnorm⟩ :=
    hp.weighted_character_base_derivatives hκ hcell hg hfg hD hf hDf hvκ hfκ hr hrh hscalar
  have hb1 : b ≤ 1 := (hbr.trans (hrh.trans (by norm_num))).le
  let A : Fin 4 → ℝ × ℝ → ℂ := fun k q ↦ κ ^ k.val * H q
  let B : Fin 4 → ℝ × ℝ → ℂ := fun k q ↦ κ ^ k.val * T q
  refine ⟨b, hb, hbr, A, B, fun k ↦ ?_⟩
  have hV := hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell))
  have heq := hvκ.recentered_ae hb1 hV k
  have hEqOn := (ae_restrict_iff' (measurableSet_quarterOrbitStrip b)).1 heq.symm
  refine ⟨(hH.const_mul (κ ^ k.val)).congr_ae_on (measurableSet_quarterOrbitStrip b)
      hEqOn (Eventually.of_forall fun _ _ ↦ rfl),
    (hT.const_mul (κ ^ k.val)).congr_ae_on (measurableSet_quarterOrbitStrip b)
      hEqOn (Eventually.of_forall fun _ _ ↦ rfl), ?_, ?_⟩
  · apply (hHnorm.const_mul (κ ^ k.val)).ae_eq
    exact Eventually.of_forall fun q ↦ by
      dsimp only [A, recenteredQuarterMap]
      rw [saddleDist_rotLift_iterate]
      ring
  · apply (hTnorm.const_mul (κ ^ k.val)).ae_eq
    exact Eventually.of_forall fun q ↦ by
      dsimp only [B, recenteredQuarterMap]
      rw [saddleDist_rotLift_iterate]
      ring

end NoEmbeddedEigenvalues
