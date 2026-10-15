import NoEmbeddedEigenvalues.WeightedBoundary

/-!
# Endpoint cutoff estimates in the weighted boundary domain

Blueprint: `lem:weighted-boundary-multiplier`, `def:boundary-layer-energy`,
`lem:boundary-layer-bound`, `lem:boundary-layer-limits`,
`def:boundary-cutoff-control`, `lem:boundary-cutoff-estimates`, and
`lem:boundary-cutoff-convergence`.

These estimates isolate the analytic part of endpoint cutoff approximation.
The cutoff construction and subsequent interior mollification are separate.

Not used by the main argument: positivity of the boundary form on the weighted
domain is proved directly in `WeightedBoundaryForm.lean`. Kept as infrastructure
(decision of 2026-10-15).
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Interval Topology

/-- Multiplication by a classical C² coefficient preserves the weighted domain. -/
theorem HasWeightedBoundaryH2.mul_boundaryJet {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (J : BoundaryJet) :
    HasWeightedBoundaryH2 (fun x ↦ J.value x * F x)
      (fun x ↦ J.first x * F x + J.value x * D x)
      (fun x ↦ J.second x * F x + 2 * J.first x * D x + J.value x * E x) := by
  have hJ := J.hasWeightedBoundaryH2
  have hV := (memLp_top_of_continuousOn_Icc J.continuous_value).mono_measure
    (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hD := (memLp_top_of_continuousOn_Icc J.continuous_first).mono_measure
    (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hvalue : MemLp (fun x ↦ J.value x * F x) 2 (volume.restrict (Ioo (-1) 1)) := by
    simpa only [Pi.mul_def] using hV.mul h.h1.memLp_value
  have hfirst : MemLp (fun x ↦ J.first x * F x + J.value x * D x) 2
      (volume.restrict (Ioo (-1) 1)) := by
    simpa only [Pi.add_def, Pi.mul_def] using
      (hD.mul h.h1.memLp_value).add (hV.mul h.h1.memLp_derivative)
  have hACV c d hc hcd hd := hJ.h1.locally_absolutelyContinuous c d hc hcd hd
  have hACD c d hc hcd hd := hJ.locally_absolutelyContinuous_first c d hc hcd hd
  refine ⟨⟨hvalue, hfirst, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c d hc hcd hd
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using
      (hACV c d hc hcd hd).smul (h.h1.locally_absolutelyContinuous c d hc hcd hd)
  · filter_upwards [h.h1.hasDerivAt_ae] with x hx hi
    exact (J.deriv_value x (Ioo_subset_Icc_self hi)).mul (hx hi)
  · intro c d hc hcd hd
    simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul, Pi.mul_def] using
      ((hACD c d hc hcd hd).smul (h.h1.locally_absolutelyContinuous c d hc hcd hd)).add
        ((hACV c d hc hcd hd).smul
          (h.locally_absolutelyContinuous_first c d hc hcd hd))
  · filter_upwards [h.h1.hasDerivAt_ae, h.hasDerivAt_first_ae] with x hx he hi
    convert ((J.deriv_first x (Ioo_subset_Icc_self hi)).mul (hx hi)).add
      ((J.deriv_value x (Ioo_subset_Icc_self hi)).mul (he hi)) using 1
    ring
  · have hW : Continuous (fun x ↦ (boundaryWeight x : ℂ)) := by
      unfold boundaryWeight
      fun_prop
    have hC₀ : ContinuousOn (fun x ↦ (boundaryWeight x : ℂ) * J.second x) (Icc (-1) 1) :=
      hW.continuousOn.mul J.continuous_second
    have hC₁ : ContinuousOn (fun x ↦ 2 * (boundaryWeight x : ℂ) * J.first x) (Icc (-1) 1) :=
      (continuousOn_const.mul hW.continuousOn).mul J.continuous_first
    have hC₀Lp := (memLp_top_of_continuousOn_Icc hC₀).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hC₁Lp := (memLp_top_of_continuousOn_Icc hC₁).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hsum : MemLp (fun x ↦ (boundaryWeight x : ℂ) * J.second x * F x +
        2 * (boundaryWeight x : ℂ) * J.first x * D x +
        J.value x * ((boundaryWeight x : ℂ) * E x)) 2 (volume.restrict (Ioo (-1) 1)) := by
      simpa only [Pi.add_def, Pi.mul_def] using ((hC₀Lp.mul h.h1.memLp_value).add
        (hC₁Lp.mul h.h1.memLp_derivative)).add (hV.mul h.memLp_weighted_second)
    convert hsum using 1
    ext x
    ring

/-- The two endpoint layers of width `η`, measured by their squared L² mass. -/
def boundaryLayerEnergy (η : ℝ) (f : ℝ → ℂ) : ℝ :=
  (∫ x in (-1 : ℝ)..(-1 + η), ‖f x‖ ^ 2) +
    ∫ x in (1 - η)..(1 : ℝ), ‖f x‖ ^ 2

/-- A function supported in the endpoint layers is controlled by the mass there. -/
theorem integral_sq_le_boundaryLayers {η C : ℝ} {q f : ℝ → ℂ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hq : MemLp q 2 (volume.restrict (Icc (-1) 1)))
    (hf : MemLp f 2 (volume.restrict (Icc (-1) 1)))
    (hzero : ∀ x ∈ Icc (-1 + η) (1 - η), q x = 0)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖q x‖ ≤ C * ‖f x‖) :
    (∫ x in (-1 : ℝ)..1, ‖q x‖ ^ 2) ≤ C ^ 2 * boundaryLayerEnergy η f := by
  have hqi : IntegrableOn (fun x ↦ ‖q x‖ ^ 2) (Icc (-1 : ℝ) 1) := hq.norm.integrable_sq
  have hfi : IntegrableOn (fun x ↦ ‖f x‖ ^ 2) (Icc (-1 : ℝ) 1) := hf.norm.integrable_sq
  have hqsub {c d : ℝ} (hc : (-1 : ℝ) ≤ c) (hd : d ≤ 1) (hcd : c ≤ d) :
      IntervalIntegrable (fun x ↦ ‖q x‖ ^ 2) volume c d :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mpr
      (hqi.mono_set (Icc_subset_Icc hc hd))
  have hfsub {c d : ℝ} (hc : (-1 : ℝ) ≤ c) (hd : d ≤ 1) (hcd : c ≤ d) :
      IntervalIntegrable (fun x ↦ C ^ 2 * ‖f x‖ ^ 2) volume c d :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mpr
      (hfi.mono_set (Icc_subset_Icc hc hd))).const_mul _
  have hpoint : ∀ x ∈ Icc (-1 : ℝ) 1, ‖q x‖ ^ 2 ≤ C ^ 2 * ‖f x‖ ^ 2 := by
    intro x hx
    have ht := hbound x hx
    have hs := sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans ht) |>.mpr ht
    simpa only [mul_pow] using hs
  have hleft := intervalIntegral.integral_mono_on (by linarith : (-1 : ℝ) ≤ -1 + η)
    (hqsub le_rfl (by linarith) (by linarith))
    (hfsub le_rfl (by linarith) (by linarith))
    (fun x hx ↦ hpoint x ⟨hx.1, by linarith [hx.2]⟩)
  have hright := intervalIntegral.integral_mono_on (by linarith : 1 - η ≤ (1 : ℝ))
    (hqsub (by linarith) le_rfl (by linarith))
    (hfsub (by linarith) le_rfl (by linarith))
    (fun x hx ↦ hpoint x ⟨by linarith [hx.1], hx.2⟩)
  have hmid : (∫ x in (-1 + η)..(1 - η), ‖q x‖ ^ 2) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with x hx
    rw [uIoc_of_le (by linarith)] at hx
    simp [hzero x ⟨hx.1.le, hx.2⟩]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (-1 : ℝ)) (b := -1 + η) (c := 1)
    (hqsub le_rfl (by linarith) (by linarith))
    (hqsub (by linarith) le_rfl (by linarith))
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals
    (a := -1 + η) (b := 1 - η) (c := (1 : ℝ))
    (hqsub (by linarith) (by linarith) (by linarith))
    (hqsub (by linarith) le_rfl (by linarith))
  rw [← hsplit, ← hsplit₂, hmid, zero_add]
  rw [intervalIntegral.integral_const_mul] at hleft hright
  unfold boundaryLayerEnergy
  nlinarith

/-- The moving left edge approaches the endpoint from inside the interval. -/
theorem tendsto_boundaryLayer_left :
    Tendsto (fun η : ℝ ↦ -1 + η) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝[Ioc (-1 : ℝ) 1] (-1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using tendsto_const_nhds.add
      (show Tendsto (fun η : ℝ ↦ η) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact ⟨by linarith [hη.1], by linarith [hη.2]⟩

/-- The moving right edge approaches the endpoint from inside the interval. -/
theorem tendsto_boundaryLayer_right :
    Tendsto (fun η : ℝ ↦ 1 - η) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝[Ico (-1 : ℝ) 1] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using tendsto_const_nhds.sub
      (show Tendsto (fun η : ℝ ↦ η) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact ⟨by linarith [hη.2], by linarith [hη.1]⟩

/-- The L² mass of an integrable function on shrinking endpoint layers tends to zero. -/
theorem tendsto_boundaryLayerEnergy {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    Tendsto (fun η ↦ boundaryLayerEnergy η f) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hfi : IntegrableOn (fun x ↦ ‖f x‖ ^ 2) (uIcc (-1 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hf.norm.integrable_sq
  have hl := intervalIntegral.continuousOn_primitive_interval' hfi.intervalIntegrable
    (show (-1 : ℝ) ∈ uIcc (-1) 1 from left_mem_uIcc)
  have hr := intervalIntegral.continuousOn_primitive_interval_left hfi
  have hl₀ : Tendsto (fun c ↦ ∫ x in (-1 : ℝ)..c, ‖f x‖ ^ 2)
      (𝓝[Ioc (-1 : ℝ) 1] (-1)) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using
      (hl (-1) left_mem_uIcc).mono (by
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact Ioc_subset_Icc_self)
  have hr₀ : Tendsto (fun c ↦ ∫ x in c..(1 : ℝ), ‖f x‖ ^ 2)
      (𝓝[Ico (-1 : ℝ) 1] 1) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using
      (hr 1 right_mem_uIcc).mono (by
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact Ico_subset_Icc_self)
  simpa only [boundaryLayerEnergy, Function.comp_def, add_zero] using
    (hl₀.comp tendsto_boundaryLayer_left).add (hr₀.comp tendsto_boundaryLayer_right)

/-- Values at isolated endpoints do not change the squared-norm interval integral. -/
theorem HasIntervalH1.integral_sq_eq_extension {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    (∫ x in c..d, ‖F x‖ ^ 2) = ∫ x in c..d, ‖intervalH1Extension a b F D x‖ ^ 2 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a, volume.ae_ne b] with x hxa hxb hx
  have hxi := uIcc_subset_Icc hc hd (uIoc_subset_uIcc hx)
  have hxo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxi.1 hxa.symm, lt_of_le_of_ne hxi.2 hxb⟩
  rw [h.extension_eq hab hxo]

/-- The rescaled raw representative has vanishing endpoint mass when both traces vanish. -/
theorem HasIntervalH1.tendsto_boundaryLayerEnergy_div_sq {F D : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 F D)
    (ha : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hb : intervalH1Extension (-1) 1 F D 1 = 0) :
    Tendsto (fun η ↦ boundaryLayerEnergy η F / η ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hl := (h.tendsto_integral_rescaled_left (by norm_num) ha).comp tendsto_boundaryLayer_left
  have hr := (h.tendsto_integral_rescaled_right (by norm_num) hb).comp tendsto_boundaryLayer_right
  have hsum := hl.add hr
  apply Tendsto.congr' _ (by simpa only [zero_add] using hsum)
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hlη : -1 + η ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have hrη : 1 - η ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hη.2], by linarith [hη.1]⟩
  dsimp only [Function.comp_def]
  simp only [show -1 + η - (-1 : ℝ) = η by ring, show 1 - (1 - η) = η by ring]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div, ← add_div]
  unfold boundaryLayerEnergy
  rw [h.integral_sq_eq_extension (by norm_num) ⟨le_rfl, by norm_num⟩ hlη,
    h.integral_sq_eq_extension (by norm_num) hrη ⟨by norm_num, le_rfl⟩]

/-- Quantitative properties used of a C² cutoff. Existence of such a family is
    a separate construction, not built into this predicate. -/
structure BoundaryCutoffControl (η C : ℝ) (J : BoundaryJet) : Prop where
  support_value : Function.support J.value ⊆ Icc (-1 + η / 2) (1 - η / 2)
  core_value : ∀ x ∈ Icc (-1 + η) (1 - η), J.value x = 1
  core_first : ∀ x ∈ Icc (-1 + η) (1 - η), J.first x = 0
  core_second : ∀ x ∈ Icc (-1 + η) (1 - η), J.second x = 0
  value_error_le : ∀ x ∈ Icc (-1 : ℝ) 1, ‖J.value x - 1‖ ≤ 1
  first_le : ∀ x ∈ Icc (-1 : ℝ) 1, ‖J.first x‖ ≤ C / η
  second_le : ∀ x ∈ Icc (-1 : ℝ) 1, ‖J.second x‖ ≤ C / η ^ 2

/-- The cutoff product really has compact support strictly inside the interval. -/
theorem BoundaryCutoffControl.hasCompactSupport_mul {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (F : ℝ → ℂ) :
    HasCompactSupport (fun x ↦ J.value x * F x) := by
  change IsCompact (closure (Function.support (fun x ↦ J.value x * F x)))
  apply (isCompact_Icc : IsCompact (Icc (-1 + η / 2) (1 - η / 2))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply hJ.support_value
  intro hzero
  exact hx (by simp [hzero])

/-- The product support stays strictly inside the interval for positive width. -/
theorem BoundaryCutoffControl.support_mul_subset {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) (F : ℝ → ℂ) :
    Function.support (fun x ↦ J.value x * F x) ⊆ Ioo (-1 : ℝ) 1 := by
  intro x hx
  have hχ : x ∈ Function.support J.value := by
    intro hzero
    exact hx (by simp [hzero])
  have hs := hJ.support_value hχ
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- On a width-`η` endpoint layer the weight is at most `2η`. -/
theorem norm_boundaryWeight_le_layer {η x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hcore : x ∉ Icc (-1 + η) (1 - η)) : ‖(boundaryWeight x : ℂ)‖ ≤ 2 * η := by
  have hw : 0 ≤ boundaryWeight x := by
    unfold boundaryWeight
    nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith [hx.2])
      (show 0 ≤ 1 + x by linarith [hx.1])]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  unfold boundaryWeight
  by_cases hl : x < -1 + η
  · nlinarith [sq_nonneg (x + 1)]
  · have hr : 1 - η < x := lt_of_not_ge (fun hr ↦ hcore ⟨le_of_not_gt hl, hr⟩)
    nlinarith [sq_nonneg (x - 1)]

/-- Multiplication by a continuous coefficient is an L² multiplier on the closed interval. -/
theorem memLp_mul_continuousOn_Icc {g f : ℝ → ℂ}
    (hg : ContinuousOn g (Icc (-1) 1))
    (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    MemLp (fun x ↦ g x * f x) 2 (volume.restrict (Icc (-1) 1)) := by
  simpa only [Pi.mul_def] using (memLp_top_of_continuousOn_Icc hg).mul hf

/-- The undifferentiated cutoff error is controlled by the endpoint mass. -/
theorem BoundaryCutoffControl.value_error_bound {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) (hη₁ : η ≤ 1)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    (∫ x in (-1 : ℝ)..1, ‖(J.value x - 1) * f x‖ ^ 2) ≤ boundaryLayerEnergy η f := by
  have hq := memLp_mul_continuousOn_Icc
    (J.continuous_value.sub (continuousOn_const (c := (1 : ℂ)))) hf
  simpa only [Pi.sub_apply, one_pow, one_mul] using
    integral_sq_le_boundaryLayers (C := 1) hη.le hη₁ hq hf
    (fun x hx ↦ by simp [hJ.core_value x hx])
    (fun x hx ↦ by
      simp only [Pi.sub_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hJ.value_error_le x hx) (norm_nonneg _))

/-- A first derivative of the cutoff costs one inverse layer width. -/
theorem BoundaryCutoffControl.first_error_bound {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) (hη₁ : η ≤ 1)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    (∫ x in (-1 : ℝ)..1, ‖J.first x * f x‖ ^ 2) ≤
      C ^ 2 * (boundaryLayerEnergy η f / η ^ 2) := by
  have hh := integral_sq_le_boundaryLayers hη.le hη₁
    (memLp_mul_continuousOn_Icc J.continuous_first hf) hf
    (fun x hx ↦ by simp [hJ.core_first x hx])
    (fun x hx ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hJ.first_le x hx) (norm_nonneg _))
  simpa only [div_pow, div_mul_eq_mul_div, mul_div_assoc] using hh

/-- The weight cancels the inverse width in the first-derivative error. -/
theorem BoundaryCutoffControl.weighted_first_error_bound {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hC : 0 ≤ C) {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    (∫ x in (-1 : ℝ)..1, ‖(boundaryWeight x : ℂ) * J.first x * f x‖ ^ 2) ≤
      (2 * C) ^ 2 * boundaryLayerEnergy η f := by
  have hw : Continuous (fun x ↦ (boundaryWeight x : ℂ)) := by unfold boundaryWeight; fun_prop
  apply integral_sq_le_boundaryLayers hη.le hη₁
    (memLp_mul_continuousOn_Icc (hw.continuousOn.mul J.continuous_first) hf) hf
  · intro x hx
    simp [hJ.core_first x hx]
  · intro x hx
    simp only [Pi.mul_apply, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases hc : x ∈ Icc (-1 + η) (1 - η)
    · simp [hJ.core_first x hc, hC]
    · calc
        _ ≤ (2 * η) * (C / η) := mul_le_mul (norm_boundaryWeight_le_layer hx hc)
          (hJ.first_le x hx) (norm_nonneg _) (by positivity)
        _ = 2 * C := by field_simp [hη.ne']

/-- In the second-derivative error the weight leaves only one inverse width. -/
theorem BoundaryCutoffControl.weighted_second_error_bound {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hC : 0 ≤ C) {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    (∫ x in (-1 : ℝ)..1, ‖(boundaryWeight x : ℂ) * J.second x * f x‖ ^ 2) ≤
      (2 * C) ^ 2 * (boundaryLayerEnergy η f / η ^ 2) := by
  have hw : Continuous (fun x ↦ (boundaryWeight x : ℂ)) := by unfold boundaryWeight; fun_prop
  have hh := integral_sq_le_boundaryLayers hη.le hη₁
    (memLp_mul_continuousOn_Icc (hw.continuousOn.mul J.continuous_second) hf) hf
    (fun x hx ↦ by simp [hJ.core_second x hx])
    (C := 2 * C / η) (by
      intro x hx
      simp only [Pi.mul_apply, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      by_cases hc : x ∈ Icc (-1 + η) (1 - η)
      · simp only [hJ.core_second x hc, norm_zero, mul_zero]
        positivity
      · calc
          _ ≤ (2 * η) * (C / η ^ 2) := mul_le_mul (norm_boundaryWeight_le_layer hx hc)
            (hJ.second_le x hx) (norm_nonneg _) (by positivity)
          _ = 2 * C / η := by field_simp [hη.ne'])
  calc
    _ ≤ (2 * C / η) ^ 2 * boundaryLayerEnergy η f := by
      simpa only [Pi.mul_apply] using hh
    _ = _ := by field_simp [hη.ne']

/-- Sums preserve convergence in squared L² mass on the interval. -/
theorem tendsto_integral_sq_add {q r : ℝ → ℝ → ℂ}
    (hq : ∀ η, MemLp (q η) 2 (volume.restrict (Icc (-1) 1)))
    (hr : ∀ η, MemLp (r η) 2 (volume.restrict (Icc (-1) 1)))
    (hlq : Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖q η x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0))
    (hlr : Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖r η x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0)) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖q η x + r η x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall fun _ ↦ intervalIntegral.integral_nonneg_of_forall
      (by norm_num) (fun _ ↦ sq_nonneg _)) _
    (by simpa using (hlq.add hlr).const_mul 2)
  apply Eventually.of_forall
  intro η
  have hqi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mpr ((hq η).norm.integrable_sq)
  have hri := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mpr ((hr η).norm.integrable_sq)
  have hsi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mpr (((hq η).add (hr η)).norm.integrable_sq)
  have hh := intervalIntegral.integral_mono (by norm_num : (-1 : ℝ) ≤ 1) hsi
    ((hqi.add hri).const_mul 2) (fun x ↦ by
      change ‖q η x + r η x‖ ^ 2 ≤ _
      have hs := sq_le_sq₀ (norm_nonneg (q η x + r η x))
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr (norm_add_le _ _)
      nlinarith [sq_nonneg (‖q η x‖ - ‖r η x‖)])
  simpa only [Pi.add_apply, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hqi hri] using hh

/-- Constant complex factors preserve convergence in squared L² mass. -/
theorem tendsto_integral_sq_const_mul {q : ℝ → ℝ → ℂ} (z : ℂ)
    (hl : Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖q η x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0)) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖z * q η x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  simp_rw [norm_mul, mul_pow, intervalIntegral.integral_const_mul]
  simpa using hl.const_mul (‖z‖ ^ 2)

/-- Uniformly controlled cutoff values converge strongly to the identity. -/
theorem tendsto_cutoff_value_error {C : ℝ} {J : ℝ → BoundaryJet}
    (hJ : ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (J η))
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖((J η).value x - 1) * f x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ intervalIntegral.integral_nonneg_of_forall
      (by norm_num) (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[Ioc (0 : ℝ) 1] 0, η ∈ Ioc (0 : ℝ) 1)
      (fun η hη ↦ (hJ η hη).value_error_bound hη.1 hη.2 hf))
    (tendsto_boundaryLayerEnergy hf)

/-- The first cutoff derivative times a zero-trace H¹ function tends to zero in L². -/
theorem HasIntervalH1.tendsto_cutoff_first_error {F D : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 F D) {C : ℝ} {J : ℝ → BoundaryJet}
    (hJ : ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (J η))
    (ha : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hb : intervalH1Extension (-1) 1 F D 1 = 0) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖(J η).first x * F x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hF : MemLp F 2 (volume.restrict (Icc (-1) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact h.memLp_value
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ intervalIntegral.integral_nonneg_of_forall
      (by norm_num) (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[Ioc (0 : ℝ) 1] 0, η ∈ Ioc (0 : ℝ) 1)
      (fun η hη ↦ (hJ η hη).first_error_bound hη.1 hη.2 hF))
    (by simpa using (h.tendsto_boundaryLayerEnergy_div_sq ha hb).const_mul (C ^ 2))

/-- The weighted first cutoff derivative times any L² function tends to zero in L². -/
theorem tendsto_cutoff_weighted_first_error {C : ℝ} {J : ℝ → BoundaryJet}
    (hJ : ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (J η)) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Icc (-1) 1))) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1,
      ‖(boundaryWeight x : ℂ) * (J η).first x * f x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ intervalIntegral.integral_nonneg_of_forall
      (by norm_num) (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[Ioc (0 : ℝ) 1] 0, η ∈ Ioc (0 : ℝ) 1)
      (fun η hη ↦ (hJ η hη).weighted_first_error_bound hη.1 hη.2 hC hf))
    (by simpa using (tendsto_boundaryLayerEnergy hf).const_mul ((2 * C) ^ 2))

/-- The weighted second cutoff derivative has the same zero-trace control. -/
theorem HasIntervalH1.tendsto_cutoff_weighted_second_error {F D : ℝ → ℂ}
    (h : HasIntervalH1 (-1) 1 F D) {C : ℝ} {J : ℝ → BoundaryJet}
    (hJ : ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (J η)) (hC : 0 ≤ C)
    (ha : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hb : intervalH1Extension (-1) 1 F D 1 = 0) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1,
      ‖(boundaryWeight x : ℂ) * (J η).second x * F x‖ ^ 2)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hF : MemLp F 2 (volume.restrict (Icc (-1) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact h.memLp_value
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ intervalIntegral.integral_nonneg_of_forall
      (by norm_num) (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[Ioc (0 : ℝ) 1] 0, η ∈ Ioc (0 : ℝ) 1)
      (fun η hη ↦ (hJ η hη).weighted_second_error_bound hη.1 hη.2 hC hF))
    (by simpa using (h.tendsto_boundaryLayerEnergy_div_sq ha hb).const_mul ((2 * C) ^ 2))

/-- The cutoff product has zero value traces, even when the original traces are nonzero. -/
theorem HasWeightedBoundaryH2.cutoff_memH10 {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {η C : ℝ} {J : BoundaryJet}
    (hJ : BoundaryCutoffControl η C J) (hη : 0 < η) :
    MemIntervalH10 (-1) 1 (fun x ↦ J.value x * F x) := by
  have hp := h.mul_boundaryJet J
  have hl : J.value (-1) = 0 := by
    by_contra hn
    have hs := hJ.support_value hn
    linarith [hs.1]
  have hr : J.value 1 = 0 := by
    by_contra hn
    have hs := hJ.support_value hn
    linarith [hs.2]
  have hext := hp.h1.extension_unique (by norm_num)
    (J.continuous_value.mul (h.h1.continuousOn_extension (by norm_num)))
    (fun x hx ↦ by simp only [Pi.mul_apply, h.h1.extension_eq (by norm_num) hx])
  apply (hp.h1.memH10_iff (by norm_num)).mpr
  constructor
  · exact (hext ⟨le_rfl, by norm_num⟩).symm.trans (by simp only [Pi.mul_apply, hl, zero_mul])
  · exact (hext ⟨by norm_num, le_rfl⟩).symm.trans (by simp only [Pi.mul_apply, hr, zero_mul])

/-- Conditional cutoff convergence in all three weighted graph components.
    This theorem assumes a uniformly controlled cutoff family; it does not construct one. -/
theorem HasWeightedBoundaryH2.cutoff_convergence {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {C : ℝ} {J : ℝ → BoundaryJet}
    (hJ : ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (J η)) (hC : 0 ≤ C)
    (ha : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hb : intervalH1Extension (-1) 1 F D 1 = 0) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖(J η).value x * F x - F x‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) ∧
      Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1,
        ‖(J η).first x * F x + (J η).value x * D x - D x‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) ∧
      Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖(boundaryWeight x : ℂ) *
        ((J η).second x * F x + 2 * (J η).first x * D x + (J η).value x * E x - E x)‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hF : MemLp F 2 (volume.restrict (Icc (-1) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact h.h1.memLp_value
  have hD := h.h1.memLp_derivative_Icc
  have hE : MemLp (fun x ↦ (boundaryWeight x : ℂ) * E x) 2
      (volume.restrict (Icc (-1) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact h.memLp_weighted_second
  have hw : Continuous (fun x ↦ (boundaryWeight x : ℂ)) := by unfold boundaryWeight; fun_prop
  have hVD η : MemLp (fun x ↦ ((J η).value x - 1) * D x) 2
      (volume.restrict (Icc (-1) 1)) :=
    memLp_mul_continuousOn_Icc ((J η).continuous_value.sub continuousOn_const) hD
  have hFF η : MemLp (fun x ↦ (J η).first x * F x) 2
      (volume.restrict (Icc (-1) 1)) :=
    memLp_mul_continuousOn_Icc (J η).continuous_first hF
  have hVE η : MemLp (fun x ↦ ((J η).value x - 1) * ((boundaryWeight x : ℂ) * E x)) 2
      (volume.restrict (Icc (-1) 1)) :=
    memLp_mul_continuousOn_Icc ((J η).continuous_value.sub continuousOn_const) hE
  have hWF η : MemLp (fun x ↦ (boundaryWeight x : ℂ) * (J η).first x * D x) 2
      (volume.restrict (Icc (-1) 1)) :=
    memLp_mul_continuousOn_Icc (hw.continuousOn.mul (J η).continuous_first) hD
  have hWS η : MemLp (fun x ↦ (boundaryWeight x : ℂ) * (J η).second x * F x) 2
      (volume.restrict (Icc (-1) 1)) :=
    memLp_mul_continuousOn_Icc (hw.continuousOn.mul (J η).continuous_second) hF
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show ∀ z f : ℂ, z * f - f = (z - 1) * f by intros; ring] using
      tendsto_cutoff_value_error hJ hF
  · have hl := tendsto_integral_sq_add hVD hFF
      (tendsto_cutoff_value_error hJ hD) (h.h1.tendsto_cutoff_first_error hJ ha hb)
    simpa only [show ∀ a b f d : ℂ, a * f + b * d - d = (b - 1) * d + a * f
      by intros; ring] using hl
  · have htwo η : MemLp (fun x ↦ 2 * ((boundaryWeight x : ℂ) * (J η).first x * D x)) 2
        (volume.restrict (Icc (-1) 1)) := (hWF η).const_mul 2
    have hsum η : MemLp (fun x ↦ ((J η).value x - 1) * ((boundaryWeight x : ℂ) * E x) +
        2 * ((boundaryWeight x : ℂ) * (J η).first x * D x)) 2
        (volume.restrict (Icc (-1) 1)) := by
      simpa only [Pi.add_def] using (hVE η).add (htwo η)
    have hl := tendsto_integral_sq_add hsum hWS
      (tendsto_integral_sq_add hVE htwo (tendsto_cutoff_value_error hJ hE)
        (tendsto_integral_sq_const_mul 2 (tendsto_cutoff_weighted_first_error hJ hC hD)))
      (h.h1.tendsto_cutoff_weighted_second_error hJ hC ha hb)
    simpa only [show ∀ w a b c f d e : ℂ,
      w * (c * f + 2 * a * d + b * e - e) =
        ((b - 1) * (w * e) + 2 * (w * a * d)) + w * c * f by intros; ring] using hl

end NoEmbeddedEigenvalues
