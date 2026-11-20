import NoEmbeddedEigenvalues.DiagonalSobolev
import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix
import NoEmbeddedEigenvalues.EvenGradientHardy
import NoEmbeddedEigenvalues.MixedComparison

/-! # Hardy division of the mixed vorticity

A smooth even cutoff in the cosine confines the Hardy argument to the
ordinary Sobolev collar. Off the support of the cutoff defect the
division is harmless; no interior gain for the vorticity is needed.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Real
open scoped ContDiff

/-- A first-odd vorticity in H¹ on a full collar can be divided by `cos a` in L². -/
theorem mixed_vorticity_divided_of_collar {ζ : L2} {e : Bool} (hs : InSector false e ζ)
    {ε : ℝ} (hε : 0 < ε)
    (hζ : MemSobolevLocOn 1 {p | |dipoleLift p| < ε} (liftL2 ζ)) :
    MemLp (fun q ↦ liftL2 ζ (diagInv q) / (cos q.1 : ℂ)) 2
      (volume.restrict mixedOpenCell) := by
  let I := Ioo (-π / 2) (π / 2)
  let J := Ioo (-2 * π) (2 * π)
  let F := liftL2 ζ ∘ diagonalTraceChart 0
  let B : ContDiffBump (0 : ℝ) := ⟨ε / 8, ε / 4, by positivity, by linarith⟩
  let G : ℝ × ℝ → ℂ := fun q ↦ (B (cos q.2) : ℂ) * F q
  have hC : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  let S := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hS : (planeAffine S 0 : (ℝ × ℝ) → ℝ × ℝ) = Prod.swap := by
    funext p
    change p.swap + 0 = p.swap
    exact add_zero _
  have hmS : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hFc : MemSobolevLocOn 1 (diagonalTraceChart 0 ⁻¹' {p | |dipoleLift p| < ε}) F := by
    have h := hζ.comp_diagInv.comp_planeAffine S 0 (by rwa [hS])
    change MemSobolevLocOn 1 ((diagInv ∘ Prod.swap) ⁻¹' _) (liftL2 ζ ∘ diagInv ∘ Prod.swap)
    simpa only [hS, preimage_comp] using! h
  have hGc : MemSobolevLocOn 1 univ G := by
    apply memSobolevLocOn_of_locally
    intro q _
    by_cases hq : |cos q.2| < ε / 2
    · let U := diagonalTraceChart 0 ⁻¹' {p | |dipoleLift p| < ε}
      have hU : IsOpen U := hC.preimage (continuous_diagonalTraceChart 0)
      have hqU : q ∈ U := by
        change |dipoleLift (diagInv q.swap)| < ε
        rw [dipoleLift_eq_diag, diagCoord_diagInv, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        calc
          2 * |cos q.2| * |cos q.1| ≤ 2 * |cos q.2| * 1 :=
            mul_le_mul_of_nonneg_left (abs_cos_le_one _) (by positivity)
          _ < ε := by linarith
      refine ⟨U, hU, hqU, hFc.mul_contDiffOn hU ?_⟩
      exact (Complex.ofRealCLM.contDiff.comp (B.contDiff.comp (by fun_prop))).contDiffOn
    · let W := {p : ℝ × ℝ | ε / 4 < |cos p.2|}
      have hW : IsOpen W := isOpen_lt continuous_const (continuous_cos.comp continuous_snd).abs
      have hqW : q ∈ W := by change ε / 4 < |cos q.2|; linarith
      refine ⟨W, hW, hqW, (MemSobolevOn.zero 1 W).memSobolevLocOn.congr_ae_on ?_⟩
      exact Eventually.of_forall fun p hp ↦ by
        have hz := B.zero_of_le_dist (show B.rOut ≤ dist (cos p.2) 0 by
          rw [Real.dist_eq, sub_zero]; exact (show ε / 4 < |cos p.2| from hp).le)
        simp [G, hz]
  have hG : MemSobolevOn 1 (I ×ˢ J) G := hGc _ (isOpen_Ioo.prod isOpen_Ioo)
    ((isCompact_Icc.prod isCompact_Icc).closure_of_subset
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)) (subset_univ _)
  have ho : ∀ᵐ p : ℝ × ℝ, G (p.1, π - p.2) = -G p := by
    filter_upwards [liftL2_diagonalTraceChart_character_ae hs 0 true] with p hp
    have he : F (p.1, π - p.2) = -F p := by
      simpa only [F, Function.comp_apply, normalReflection_apply,
        show 2 * cellEdgeNormal true = π by simp [cellEdgeNormal]; ring,
        ite_true, paritySign, Bool.false_eq_true, ite_false, neg_one_mul] using hp
    change (B (cos (π - p.2)) : ℂ) * F (p.1, π - p.2) = -((B (cos p.2) : ℂ) * F p)
    rw [Real.cos_pi_sub, B.neg, he, mul_neg]
  have hp (p : ℝ × ℝ) : G (p.1, p.2 + 2 * π) = G p := by
    have he : diagonalTraceChart 0 (p.1, p.2 + 2 * π) =
        liftShift (1, 1) (diagonalTraceChart 0 p) := by
      change diagInv (p.2 + 2 * π, p.1) = liftShift (1, 1) (diagInv p.swap)
      ext <;> simp [liftShift] <;> ring
    simp only [G, cos_add_two_pi, F, Function.comp_apply, he, liftL2_liftShift]
  obtain ⟨D, hD, hDL⟩ := hG.2 1
  have hdiv := memLp_div_cos_snd_of_reflection hD hG.1 hDL ho hp
  have hF : MemLp F 2 (volume.restrict (I ×ˢ I)) := by
    have h := memLp_comp_diagInv (measurableSet_diagRect (I := I) (J := I)
      measurableSet_Ioo measurableSet_Ioo) (memLp_liftL2 ζ
        (isBounded_diagRect (Metric.isBounded_Ioo _ _) (Metric.isBounded_Ioo _ _)))
    have hpre : diagInv ⁻¹' diagRect I I = I ×ˢ I := by ext q; exact mem_diagRect_diagInv
    rw [hpre] at h
    have hswap : Prod.swap ⁻¹' (I ×ˢ I) = I ×ˢ I := by ext p; simp
    have ht := h.comp_measurePreserving (hmS.restrict_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo))
    rwa [hswap] at ht
  let H : ℝ × ℝ → ℂ := fun p ↦ (1 - (B (cos p.2) : ℂ)) / (cos p.2 : ℂ) * F p
  have hH : MemLp H 2 (volume.restrict (I ×ˢ I)) := by
    have hc : Measurable (fun p : ℝ × ℝ ↦
        (1 - (B (cos p.2) : ℂ)) / (cos p.2 : ℂ)) := by
      apply Measurable.div
      · exact measurable_const.sub (Complex.continuous_ofReal.measurable.comp
          (B.continuous.measurable.comp (continuous_cos.measurable.comp measurable_snd)))
      · exact Complex.continuous_ofReal.measurable.comp
          (continuous_cos.measurable.comp measurable_snd)
    apply hF.of_le_mul (c := (ε / 8)⁻¹) (hc.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    exact Eventually.of_forall fun p ↦ by
      change ‖H p‖ ≤ (ε / 8)⁻¹ * ‖F p‖
      by_cases hp : |cos p.2| ≤ ε / 8
      · have hb : B (cos p.2) = 1 := B.one_of_mem_closedBall (by
          change dist (cos p.2) 0 ≤ ε / 8
          simpa [Real.dist_eq] using hp)
        simp only [H, hb, Complex.ofReal_one, sub_self, zero_div, zero_mul, norm_zero]
        positivity
      · dsimp only [H]
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr B.le_one)]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          (1 - B (cos p.2)) / |cos p.2| ≤ 1 / |cos p.2| :=
            div_le_div_of_nonneg_right (by linarith [B.nonneg (x := cos p.2)]) (abs_nonneg _)
          _ ≤ (ε / 8)⁻¹ := by
            simpa only [one_div] using inv_anti₀ (show 0 < ε / 8 by positivity) (le_of_not_ge hp)
  have htotal : MemLp (fun q ↦ F q / (cos q.2 : ℂ)) 2 (volume.restrict (I ×ˢ I)) := by
    apply (hdiv.add hH).ae_eq
    exact Eventually.of_forall fun p ↦ by
      change G p / (cos p.2 : ℂ) + H p = _
      simp only [G, H, div_eq_mul_inv]
      ring
  have hswap : Prod.swap ⁻¹' (I ×ˢ I) = I ×ˢ I := by ext p; simp
  have ht := htotal.comp_measurePreserving (hmS.restrict_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo))
  rw [hswap] at ht
  exact ht

end NoEmbeddedEigenvalues
