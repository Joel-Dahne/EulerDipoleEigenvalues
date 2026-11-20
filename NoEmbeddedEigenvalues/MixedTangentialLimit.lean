import NoEmbeddedEigenvalues.MixedTangentialCutoff
import NoEmbeddedEigenvalues.MixedTangentialShell
import NoEmbeddedEigenvalues.Analysis.ZonalCutoff

/-! # Removing both annular cutoffs in the mixed virial -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ENNReal

local notation "Plane" => ℝ × ℝ
local notation "smoothOrder" => ((⊤ : ℕ∞) : WithTop ℕ∞)

private def level (q : Plane) : ℝ := Real.cos q.1 * Real.cos q.2

private theorem continuous_level : Continuous level := by unfold level; fun_prop

private def scale (n : ℕ) : ℝ := (1 / 5) * (1 / ((n : ℝ) + 1))

private theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

private theorem scale_le (n : ℕ) : scale n ≤ 1 / 5 := by
  unfold scale
  have h : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h' : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    linarith
  exact (mul_le_mul_of_nonneg_left h' (by norm_num)).trans_eq (mul_one _)

private theorem scale_limit : Tendsto scale atTop (𝓝 0) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 5 : ℝ)
  rw [mul_zero] at ht
  exact ht

private def lower (ε x : ℝ) : ℝ := Real.smoothTransition (x / ε - 1)

private def cutoff (ε x : ℝ) : ℝ := lower ε x * lower ε (1 - x)

private theorem lower_smooth (ε : ℝ) : ContDiff ℝ smoothOrder (lower ε) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε |>.sub contDiff_const)

private theorem cutoff_smooth (ε : ℝ) : ContDiff ℝ smoothOrder (cutoff ε) :=
  (lower_smooth ε).mul ((lower_smooth ε).comp (contDiff_const.sub contDiff_id))

private theorem lower_zero {ε x : ℝ} (he : 0 < ε) (hx : x ≤ ε) : lower ε x = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ he).2 (by simpa using hx)))

private theorem lower_one {ε x : ℝ} (he : 0 < ε) (hx : 2 * ε ≤ x) : lower ε x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith [(le_div_iff₀ he).2 hx])

private theorem lower_mem (ε x : ℝ) : lower ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem deriv_lower (ε x : ℝ) :
    deriv (lower ε) x = deriv Real.smoothTransition (x / ε - 1) / ε := by
  have hs : ContDiff ℝ smoothOrder Real.smoothTransition := Real.smoothTransition.contDiff
  have h := ((hs.differentiable (by simp)) (x / ε - 1)).hasDerivAt
  have h' := h.comp x (((hasDerivAt_id x).div_const ε).sub_const 1)
  have he : deriv (lower ε) x = deriv Real.smoothTransition (x / ε - 1) * (1 / ε) :=
    h'.deriv
  rw [he, one_div, div_eq_mul_inv (deriv Real.smoothTransition (x / ε - 1)) ε]

private theorem lower_shell {ε x : ℝ} (he : 0 < ε) (hx : deriv (lower ε) x ≠ 0) :
    x ∈ Ioo ε (2 * ε) := by
  rw [deriv_lower] at hx
  have hl : ¬x / ε - 1 ≤ 0 := fun h ↦ hx (by rw [deriv_transition_zero (.inl h), zero_div])
  have hu : ¬1 ≤ x / ε - 1 := fun h ↦ hx (by rw [deriv_transition_zero (.inr h), zero_div])
  exact ⟨by simpa only [one_mul] using (lt_div_iff₀ he).1 (by linarith : 1 < x / ε),
    (div_lt_iff₀ he).1 (by linarith)⟩

private theorem deriv_cutoff {ε x : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 5) :
    deriv (cutoff ε) x = deriv (lower ε) x - deriv (lower ε) (1 - x) := by
  have hd := (lower_smooth ε).differentiable (by simp)
  have h := (hd x).hasDerivAt.mul ((hd (1 - x)).hasDerivAt.comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)))
  change deriv (lower ε * (lower ε ∘ fun y ↦ 1 - y)) x = _
  rw [h.deriv]
  simp only [Function.comp_apply, zero_sub, mul_neg, mul_one]
  by_cases h₀ : deriv (lower ε) x = 0
  · by_cases h₁ : deriv (lower ε) (1 - x) = 0
    · simp [h₀, h₁]
    · have hlarge : 2 * ε ≤ x := by linarith [(lower_shell he h₁).2]
      rw [h₀, lower_one he hlarge]
      ring
  · have hlarge : 2 * ε ≤ 1 - x := by linarith [(lower_shell he h₀).2]
    have h₁ : deriv (lower ε) (1 - x) = 0 := by
      by_contra hn
      exact (lower_shell he hn).2.not_ge hlarge
    rw [h₁, lower_one he hlarge]
    ring

private theorem stream_energy_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (fun q ↦ (‖d.streamA q‖ + ‖d.streamB q‖) ^ 2) mixedOpenCell := by
  let μ := volume.restrict mixedOpenCell
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hC : MemLp (fun q : Plane ↦ Real.cos q.1) ∞ μ :=
    memLp_top_of_bound (by fun_prop) 1 (.of_forall fun q ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one q.1)
  have hS : MemLp (fun q : Plane ↦ Real.sin q.1) ∞ μ :=
    memLp_top_of_bound (by fun_prop) 1 (.of_forall fun q ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one q.1)
  have ha := d.h2.memLp_weakJet hU d.weakJet [0] (by decide)
  have hb := d.h2.memLp_weakJet hU d.weakJet [1] (by decide)
  have hA : MemLp d.streamA 2 μ := (hC.smul ha).sub (hS.smul d.h2.memLp)
  have hB : MemLp d.streamB 2 μ := hC.smul hb
  exact (hA.norm.add hB.norm).integrable_sq

/-- Remove both smooth cutoffs. The lower shell uses antisymmetry and
Hardy estimates; the upper shell uses the vanishing order at the maximum. -/
theorem mixed_tangential_compare {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, mixedVirialDensity d q) =
      ∫ q in mixedOpenCell, mixedNormalVirialDensity d q := by
  let μ := volume.restrict mixedOpenCell
  have hmem := ae_restrict_mem (μ := volume) (measurableSet_Ioo.prod measurableSet_Ioo :
    MeasurableSet mixedOpenCell)
  obtain ⟨M, hM, hbd⟩ := bound_deriv_transition
  have hbound (ε : ℝ) (he : 0 < ε) (x : ℝ) : ‖deriv (lower ε) x‖ ≤ M / ε := by
    rw [deriv_lower, norm_div, Real.norm_of_nonneg he.le, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (hbd _) he.le
  let L (n : ℕ) (q : Plane) := deriv (lower (scale n)) (level q)
  let U (n : ℕ) (q : Plane) := deriv (lower (scale n)) (1 - level q)
  have hdc (n : ℕ) : Continuous (deriv (lower (scale n))) :=
    ((lower_smooth _).of_le (show (1 : WithTop ℕ∞) ≤ smoothOrder by simp)).continuous_deriv
      (by norm_num)
  have hL : Tendsto (fun n ↦ ∫ q, L n q * mixedTangentialCurrent d q ∂μ) atTop (𝓝 0) :=
    mixed_tangential_shell_limit d scale_pos scale_limit (fun n ↦
      ((hdc n).comp continuous_level).measurable) hM
      (fun n q ↦ by simp only [L, level, Prod.fst_swap, Prod.snd_swap, mul_comm])
      (fun n q ↦ hbound _ (scale_pos n) _)
      (fun n q ↦ lower_shell (scale_pos n))
  have hmC : AEStronglyMeasurable (mixedTangentialCurrent d) μ := by
    have h := mixed_tangential_remainder_integrable d
    have hmK : Measurable mixedTangentialCornerKernel := by
      unfold mixedTangentialCornerKernel
      fun_prop
    have hφ := d.continuous.mono (subset_closure : mixedOpenCell ⊆ closure mixedOpenCell)
    have hmφ := hφ.aestronglyMeasurable (μ := volume) (measurableSet_Ioo.prod measurableSet_Ioo)
    exact ((hmK.aestronglyMeasurable.mul (hmφ.norm.pow 2)).add
      (continuous_level.aestronglyMeasurable.mul h.aestronglyMeasurable)).congr
      (hmem.mono fun q hq ↦ (mixed_tangential_current_split d hq).symm)
  let E := fun q ↦ (‖d.streamA q‖ + ‖d.streamB q‖) ^ 2
  have hiE : Integrable E μ := stream_energy_integrable d
  have hmU (n : ℕ) : AEStronglyMeasurable (fun q ↦ U n q * mixedTangentialCurrent d q) μ :=
    ((hdc n).comp (continuous_const.sub continuous_level)).aestronglyMeasurable.mul hmC
  have hUbd (n : ℕ) : ∀ᵐ q ∂μ, ‖U n q * mixedTangentialCurrent d q‖ ≤ (8 * M) * E q := by
    filter_upwards [hmem] with q hq
    by_cases h0 : U n q = 0
    · simp only [h0, zero_mul, norm_zero]
      unfold E
      positivity
    · obtain ⟨hl, hu⟩ := lower_shell (scale_pos n) h0
      change scale n < 1 - level q at hl
      change 1 - level q < 2 * scale n at hu
      have hc : 1 / 2 ≤ level q := by linarith [scale_le n]
      rw [norm_mul]
      calc
        _ ≤ (M / scale n) * (4 * (1 - level q) * E q) :=
          mul_le_mul (hbound _ (scale_pos n) _) (mixed_tangential_center_bound d hq hc)
            (norm_nonneg _) (div_nonneg hM (scale_pos n).le)
        _ ≤ (M / scale n) * (4 * (2 * scale n) * E q) := by
          have he := scale_pos n
          unfold E
          gcongr
        _ = _ := by field_simp [(scale_pos n).ne']; ring
  have hiU (n : ℕ) : Integrable (fun q ↦ U n q * mixedTangentialCurrent d q) μ :=
    (hiE.const_mul _).mono' (hmU n) (hUbd n)
  have hU : Tendsto (fun n ↦ ∫ q, U n q * mixedTangentialCurrent d q ∂μ) atTop (𝓝 0) := by
    conv_rhs => rw [← integral_zero Plane ℝ (μ := μ)]
    apply tendsto_integral_of_dominated_convergence (fun q ↦ (8 * M) * E q)
      hmU (hiE.const_mul _) hUbd
    filter_upwards [mixed_level_lt_one_ae] with q hq
    have ht : Tendsto (fun n ↦ 2 * scale n) atTop (𝓝 0) := by
      simpa only [mul_zero] using scale_limit.const_mul (2 : ℝ)
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hq))] with n hn
    have h0 : U n q = 0 := by
      by_contra hz
      exact hn.not_gt (lower_shell (scale_pos n) hz).2
    rw [h0, zero_mul]
  have hcut (n : ℕ) := mixed_tangential_cutoff_identity hlam hω d (cutoff_smooth (scale n))
    (scale_pos n) (show 1 - scale n < 1 by linarith [scale_pos n])
    (fun x hx ↦ by
      obtain ⟨hl, hu⟩ : lower (scale n) x ≠ 0 ∧ lower (scale n) (1 - x) ≠ 0 :=
        ⟨left_ne_zero_of_mul hx, right_ne_zero_of_mul hx⟩
      refine ⟨le_of_not_gt fun h ↦ hl (lower_zero (scale_pos n) h.le), ?_⟩
      exact le_of_not_gt fun h ↦ hu (lower_zero (scale_pos n) (by linarith)))
  let J := fun q ↦ mixedVirialDensity d q - mixedNormalVirialDensity d q
  have hiJ : Integrable J μ :=
    (mixed_rellich_volume_integrable d).1.sub (mixed_normal_virial_integrable d)
  have hbulk : Tendsto (fun n ↦ ∫ q, cutoff (scale n) (level q) * J q ∂μ)
      atTop (𝓝 (∫ q, J q ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun q ↦ ‖J q‖)
    · intro n
      have hm := ((cutoff_smooth (scale n)).continuous.comp continuous_level)
      exact hm.aestronglyMeasurable.mul hiJ.aestronglyMeasurable
    · exact hiJ.norm
    · intro n
      filter_upwards with q
      obtain ⟨h₁, h₂⟩ := lower_mem (scale n) (level q)
      obtain ⟨h₃, h₄⟩ := lower_mem (scale n) (1 - level q)
      have h0 : 0 ≤ cutoff (scale n) (level q) := mul_nonneg h₁ h₃
      have h1 : cutoff (scale n) (level q) ≤ 1 := (mul_le_of_le_one_left h₃ h₂).trans h₄
      rw [norm_mul, Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    · filter_upwards [hmem, mixed_level_lt_one_ae] with q hq ht
      have hp : 0 < level q := mul_pos
        (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
        (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))
      have h2 : Tendsto (fun n ↦ 2 * scale n) atTop (𝓝 0) := by
        simpa only [mul_zero] using scale_limit.const_mul (2 : ℝ)
      apply tendsto_const_nhds.congr'
      filter_upwards [h2.eventually (gt_mem_nhds hp),
        h2.eventually (gt_mem_nhds (sub_pos.mpr ht))] with n hn hn'
      change 2 * scale n < 1 - level q at hn'
      rw [cutoff, lower_one (scale_pos n) hn.le, lower_one (scale_pos n) hn'.le, one_mul, one_mul]
  have he (n : ℕ) : (∫ q, cutoff (scale n) (level q) * J q ∂μ) =
      (∫ q, L n q * mixedTangentialCurrent d q ∂μ) -
        ∫ q, U n q * mixedTangentialCurrent d q ∂μ := by
    have eq (q : Plane) : deriv (cutoff (scale n)) (level q) * mixedTangentialCurrent d q =
        L n q * mixedTangentialCurrent d q - U n q * mixedTangentialCurrent d q := by
      rw [deriv_cutoff (scale_pos n) (scale_le n)]
      exact sub_mul _ _ _
    have hi : Integrable (fun q ↦ L n q * mixedTangentialCurrent d q) μ :=
      ((hcut n).1.add (hiU n)).congr (.of_forall fun q ↦ by
        change deriv (cutoff (scale n)) (level q) * mixedTangentialCurrent d q + _ = _
        rw [eq]
        ring)
    calc
      _ = ∫ q, deriv (cutoff (scale n)) (level q) * mixedTangentialCurrent d q ∂μ :=
        (hcut n).2
      _ = _ := by simp only [eq, integral_sub hi (hiU n)]
  simp_rw [he] at hbulk
  have hz := tendsto_nhds_unique hbulk (by simpa only [sub_zero] using hL.sub hU)
  rw [integral_sub (mixed_rellich_volume_integrable d).1 (mixed_normal_virial_integrable d)]
    at hz
  linarith

end NoEmbeddedEigenvalues
