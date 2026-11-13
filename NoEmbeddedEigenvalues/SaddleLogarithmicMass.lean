import NoEmbeddedEigenvalues.LogarithmicRadialMass
import NoEmbeddedEigenvalues.DipoleLogMultiplier
import NoEmbeddedEigenvalues.SaddleChartPullback
import NoEmbeddedEigenvalues.SaddleStreamJet

/-!
# Logarithmic quadratic mass near a saddle

Blueprint: `lem:saddle-logarithmic-mass`, `lem:saddle-quadratic-log-gradient`,
`lem:saddle-quadratic-first-jet`.

The normalized factorization bounds the physical logarithm by the crossing
logarithm. A separable power majorant gives integrability after division by
radius. The affine chart preserves volume and Euclidean radius.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A small normalized saddle disk controls the physical logarithm, including
its assigned values on the separatrix. -/
theorem exists_saddle_log_bound {c : ℝ × ℝ} (hc : c ∈ saddleSet) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ q ∈ localDisk 0 ρ,
      dipoleLogWeight (saddleOrthoChart c q) ≤
        (1 + 2 * Real.log 2) * logRectangleWeight q := by
  have hm : Continuous saddleFactor := by
    unfold saddleFactor
    exact (Real.continuous_sinc.comp (by fun_prop)).mul
      (Real.continuous_sinc.comp (by fun_prop))
  have h0 : (0 : ℝ × ℝ) ∈ {q | 1 / 2 < saddleFactor q} := by
    simp [saddleFactor]
    norm_num
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hm).mem_nhds h0)
  refine ⟨min 1 δ, lt_min (by norm_num) hδ, min_le_left _ _, fun q hq ↦ ?_⟩
  have hmq : 1 / 2 < saddleFactor q := hd
    ((dist_le_localRadius 0 q).trans_lt (lt_of_lt_of_le hq (min_le_right _ _)))
  have hmp : 0 < saddleFactor q := by linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hW : 1 ≤ logRectangleWeight q := by
    unfold logRectangleWeight
    linarith [abs_nonneg (Real.log |q.1|), abs_nonneg (Real.log |q.2|)]
  by_cases hz : dipoleLift (saddleOrthoChart c q) = 0
  · rw [dipoleLogWeight, ite_eq_left hz]
    nlinarith
  have hf := saddle_dipole_factorization hc q
  have hx : q.1 ≠ 0 := fun h ↦ hz (by rw [hf, h]; ring)
  have hy : q.2 ≠ 0 := fun h ↦ hz (by rw [hf, h]; ring)
  have he : dipoleLogWeight (saddleOrthoChart c q) =
      1 + Real.log 2 - Real.log |q.1| - Real.log |q.2| - Real.log (saddleFactor q) := by
    rw [dipoleLogWeight, ite_eq_right hz, logLevelWeight, hf, abs_mul, abs_mul,
      abs_of_pos hmp, one_div, Real.log_inv,
      Real.log_div (mul_ne_zero (mul_ne_zero (abs_ne_zero.mpr hx)
        (abs_ne_zero.mpr hy)) hmp.ne') (by norm_num),
      Real.log_mul (mul_ne_zero (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hy)) hmp.ne',
      Real.log_mul (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hy)]
    ring
  have hlm : -Real.log (saddleFactor q) ≤ Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      (show (2 : ℝ)⁻¹ ≤ saddleFactor q by linarith)
    rw [Real.log_inv] at h
    linarith
  rw [he]
  dsimp only [logRectangleWeight]
  nlinarith [neg_le_abs (Real.log |q.1|), neg_le_abs (Real.log |q.2|),
    abs_nonneg (Real.log |q.1|), abs_nonneg (Real.log |q.2|)]

/-- Physical logarithmic mass divided by radius is genuinely integrable on a
small disk about each lifted saddle. No eigenfunction or trace is involved. -/
theorem exists_integrableOn_dipoleLogWeight_div_radius {c : ℝ × ℝ}
    (hc : c ∈ saddleSet) :
    ∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn
      (fun p ↦ dipoleLogWeight p / localRadius c p) (localDisk c ρ) := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := exists_saddle_log_bound hc
  have ho : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hsub : localDisk 0 ρ ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    intro q hq
    have hd : ‖q‖ < 1 := by
      simpa only [dist_zero_right] using
        (dist_le_localRadius 0 q).trans_lt (lt_of_lt_of_le hq hρ1)
    have hx : |q.1| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le q
    have hy : |q.2| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le q
    exact ⟨abs_lt.mp (hx.trans_lt hd), abs_lt.mp (hy.trans_lt hd)⟩
  have hm : Measurable (fun q ↦ dipoleLogWeight (saddleOrthoChart c q) /
      localRadius 0 q) := by
    have hΛ := measurable_dipoleLogWeight.comp
      (show Continuous (saddleOrthoChart c) by unfold saddleOrthoChart; fun_prop).measurable
    exact hΛ.div (by unfold localRadius; fun_prop)
  have hi : IntegrableOn (fun q ↦ dipoleLogWeight (saddleOrthoChart c q) /
      localRadius 0 q) (localDisk 0 ρ) := by
    apply ((integrableOn_logRectangleWeight_div_radius.mono_set hsub).const_mul
      (1 + 2 * Real.log 2)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem ho.measurableSet] with q hq
    have hn : 0 ≤ dipoleLogWeight (saddleOrthoChart c q) / localRadius 0 q :=
      div_nonneg (dipoleLogWeight_bounds _).1 (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hbound q hq)
      (show 0 ≤ localRadius 0 q from Real.sqrt_nonneg _)
  let e := planeAffine (saddleLinear c hc) c
  have he : (e : (ℝ × ℝ) → ℝ × ℝ) = saddleOrthoChart c :=
    planeAffine_saddleLinear c hc
  have hpre : e ⁻¹' localDisk c ρ = localDisk 0 ρ := by
    ext q
    change localRadius c (e q) < ρ ↔ localRadius 0 q < ρ
    rw [he, localRadius_saddleChart hc]
  have hit : Integrable ((fun p ↦ dipoleLogWeight p / localRadius c p) ∘ e)
      (volume.restrict (e ⁻¹' localDisk c ρ)) := by
    rw [hpre]
    simpa only [IntegrableOn, Function.comp_def, he, localRadius_saddleChart hc] using hi
  have ht := e.measurableEmbedding.integrable_map_iff.mpr hit
  have hU : MeasurableSet (localDisk c ρ) := by
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  rw [← Measure.restrict_map e.continuous.measurable hU] at ht
  have hemap : Measure.map e volume = volume := by
    rw [he]
    exact (measurePreserving_saddleChart hc).map_eq
  rw [hemap] at ht
  exact ⟨ρ, hρ, ht⟩

/-- The normalized quadratic contributes logarithmically weighted L² gradient
mass. The disk radius depends on the saddle, not on its coefficient. -/
theorem saddleQuadratic_log_gradient {c : ℝ × ℝ} (hc : c ∈ saddleSet) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (a : ℂ) (j : Fin 2),
      MemLp (fun p ↦ (Real.sqrt (dipoleLogWeight p) : ℂ) *
        classicalComplexJet [j] (saddleQuadratic c a) p /
          (Real.rpow (localRadius c p) (3 / 2) : ℂ)) 2
        (volume.restrict (localDisk c ρ)) := by
  obtain ⟨ρ, hρ, hi⟩ := exists_integrableOn_dipoleLogWeight_div_radius hc
  have hR : Measurable (localRadius c) := by unfold localRadius; fun_prop
  have hbase : MemLp (fun p ↦ (Real.sqrt (dipoleLogWeight p) : ℂ) /
      (Real.sqrt (localRadius c p) : ℂ)) 2 (volume.restrict (localDisk c ρ)) := by
    have hm : Measurable (fun p ↦ (Real.sqrt (dipoleLogWeight p) : ℂ) /
        (Real.sqrt (localRadius c p) : ℂ)) := by
      exact (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp measurable_dipoleLogWeight)).div
        (Complex.continuous_ofReal.measurable.comp
          (Real.continuous_sqrt.measurable.comp hR))
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    have he : (fun p ↦ ‖(Real.sqrt (dipoleLogWeight p) : ℂ) /
        (Real.sqrt (localRadius c p) : ℂ)‖ ^ 2) =
        (fun p ↦ dipoleLogWeight p / localRadius c p) := by
      funext p
      rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (dipoleLogWeight_bounds _).1,
        Real.sq_sqrt (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
    rw [he]
    exact hi
  refine ⟨ρ, hρ, fun a j ↦ ?_⟩
  have hQ : Measurable (classicalComplexJet [j] (saddleQuadratic c a)) := by
    have he : classicalComplexJet [j] (saddleQuadratic c a) = fun p ↦
        (if j = 0 then -1 else 1 : ℂ) * (a * (Real.cos c.1 : ℂ)) *
          ((axisCoord j p - axisCoord j c : ℝ) : ℂ) :=
      funext (first_saddleQuadratic c a j)
    rw [he]
    unfold axisCoord
    split_ifs <;> fun_prop
  have hb : MemLp (fun p ↦ classicalComplexJet [j] (saddleQuadratic c a) p /
      (localRadius c p : ℂ)) ⊤ (volume.restrict (localDisk c ρ)) := by
    apply memLp_top_of_bound (hQ.div (Complex.continuous_ofReal.measurable.comp
      hR)).aestronglyMeasurable ‖a * (Real.cos c.1 : ℂ)‖
    exact Filter.Eventually.of_forall fun p ↦ by
      dsimp only [Pi.div_apply, Function.comp_apply]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
      by_cases hr : localRadius c p = 0
      · simp only [hr, div_zero]
        exact norm_nonneg _
      · apply (div_le_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))).mpr
        exact norm_first_saddleQuadratic_le c a j p
  apply (hb.mul hbase).ae_eq
  exact Filter.Eventually.of_forall fun p ↦ by
    have hr0 : 0 ≤ localRadius c p := Real.sqrt_nonneg _
    have he : Real.rpow (localRadius c p) (3 / 2) =
        localRadius c p * Real.sqrt (localRadius c p) := by
      by_cases hr : localRadius c p = 0
      · simp [hr, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      · rw [Real.sqrt_eq_rpow]
        simp only [Real.rpow_eq_pow]
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (lt_of_le_of_ne hr0 (Ne.symm hr)), Real.rpow_one]
    dsimp only [Pi.mul_apply]
    rw [he]
    push_cast
    rw [div_mul_div_comm]
    ring

end NoEmbeddedEigenvalues
