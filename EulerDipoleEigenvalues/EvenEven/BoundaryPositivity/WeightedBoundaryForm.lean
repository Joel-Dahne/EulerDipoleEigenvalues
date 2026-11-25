module

public import EulerDipoleEigenvalues.Analysis.Inequalities.IntervalEndpointLimits

/-! # The boundary form on the weighted domain -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Complex ComplexConjugate MeasureTheory Set Filter
open scoped Interval Topology

/-! ### Integrability on the weighted domain -/

/-- Multiplying an `L²(-1,1)` function by a continuous real coefficient keeps it in `L²`. -/
theorem memLp_ofReal_mul_of_continuousOn {g : ℝ → ℝ} {f : ℝ → ℂ}
    (hg : ContinuousOn g (Icc (-1) 1)) (hf : MemLp f 2 (volume.restrict (Ioo (-1) 1))) :
    MemLp (fun x ↦ (g x : ℂ) * f x) 2 (volume.restrict (Ioo (-1) 1)) := by
  have hc : ContinuousOn (fun x ↦ (g x : ℂ)) (Icc (-1) 1) :=
    continuous_ofReal.comp_continuousOn hg
  simpa only [Pi.mul_def] using ((memLp_top_of_continuousOn_Icc hc).mono_measure
    (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)).mul hf

/-- `normSq` of an `L²` function is integrable. -/
theorem integrable_normSq_of_memLp {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    Integrable (fun x ↦ normSq (f x)) μ := by
  simpa [Complex.normSq_eq_norm_sq] using hf.norm.integrable_sq

/-- The current `Im (f * conj g)` of two `L²` functions is integrable. -/
theorem integrable_im_mul_conj_of_memLp {μ : Measure ℝ} {f g : ℝ → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ (f x * conj (g x)).im) μ := by
  refine Integrable.mono' (hf.norm.integrable_sq.add hg.norm.integrable_sq)
    (continuous_im.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.mul
        (continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)))
    (ae_of_all _ fun x ↦ ?_)
  calc ‖(f x * conj (g x)).im‖ ≤ ‖f x * conj (g x)‖ := abs_im_le_norm _
    _ = ‖f x‖ * ‖g x‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 := by nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]

/-- The completed-square expression is square integrable. -/
theorem HasWeightedBoundaryH2.memLp_boundarySquare {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    MemLp (boundarySquare lam F D E) 2 (volume.restrict (Ioo (-1) 1)) := by
  have hx := memLp_ofReal_mul_of_continuousOn continuousOn_id h.h1.memLp_derivative
  convert ((h.memLp_weighted_second.sub hx).add h.h1.memLp_value).sub
    (h.h1.memLp_derivative.const_mul (I * lam)) using 1
  ext x
  simp [boundarySquare, mul_assoc]

/-- The first square in the boundary form is square integrable. -/
theorem HasWeightedBoundaryH2.memLp_formSquare {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    MemLp (fun x ↦ (boundaryWeight x : ℂ) * E x - (2 * x : ℂ) * D x - I * lam * D x) 2
      (volume.restrict (Ioo (-1) 1)) := by
  have hx := memLp_ofReal_mul_of_continuousOn (g := fun x ↦ 2 * x) (by fun_prop)
    h.h1.memLp_derivative
  convert (h.memLp_weighted_second.sub hx).sub
    (h.h1.memLp_derivative.const_mul (I * lam)) using 1
  ext x
  simp [mul_assoc]

/-- The weighted energy `w |D|²` is integrable. -/
theorem HasWeightedBoundaryH2.integrable_weight_normSq {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) :
    Integrable (fun x ↦ boundaryWeight x * normSq (D x)) (volume.restrict (Ioo (-1) 1)) := by
  have hD := integrable_normSq_of_memLp h.h1.memLp_derivative
  have hwc : Continuous boundaryWeight := by
    unfold boundaryWeight
    fun_prop
  refine Integrable.mono' hD (hwc.aestronglyMeasurable.mul hD.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hw0 : 0 ≤ boundaryWeight x := by unfold boundaryWeight; nlinarith [hx.1, hx.2]
  have hw1 : boundaryWeight x ≤ 1 := by unfold boundaryWeight; nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (normSq_nonneg _))]
  nlinarith [normSq_nonneg (D x)]

/-! ### Interior intervals -/

/-- Local absolute continuity of the first derivative on unoriented interior intervals. -/
theorem HasWeightedBoundaryH2.absolutelyContinuous_first {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) : AbsolutelyContinuousOnInterval D x y := by
  rcases le_total x y with hxy | hyx
  · exact h.locally_absolutelyContinuous_first x y hx.1 hxy hy.2
  · exact (h.locally_absolutelyContinuous_first y x hy.1 hyx hx.2).symm

theorem absolutelyContinuousOnInterval_re {G : ℝ → ℂ} {x y : ℝ}
    (hG : AbsolutelyContinuousOnInterval G x y) :
    AbsolutelyContinuousOnInterval (fun t ↦ (G t).re) x y := by
  simpa using! reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hG

theorem absolutelyContinuousOnInterval_im {G : ℝ → ℂ} {x y : ℝ}
    (hG : AbsolutelyContinuousOnInterval G x y) :
    AbsolutelyContinuousOnInterval (fun t ↦ (G t).im) x y := by
  simpa using! imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hG

theorem absolutelyContinuousOnInterval_boundaryWeight (x y : ℝ) :
    AbsolutelyContinuousOnInterval boundaryWeight x y :=
  ContDiffOn.absolutelyContinuousOnInterval (by unfold boundaryWeight; fun_prop)

/-- The flux of two absolutely continuous functions is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_boundaryFlux {F D : ℝ → ℂ} {x y : ℝ}
    (hF : AbsolutelyContinuousOnInterval F x y) (hD : AbsolutelyContinuousOnInterval D x y) :
    AbsolutelyContinuousOnInterval (boundaryFlux F D) x y := by
  have hid : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t) x y :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hw := absolutelyContinuousOnInterval_boundaryWeight x y
  have hFr := absolutelyContinuousOnInterval_re hF
  have hFi := absolutelyContinuousOnInterval_im hF
  have hDr := absolutelyContinuousOnInterval_re hD
  have hDi := absolutelyContinuousOnInterval_im hD
  have hK := ((((hw.const_mul (-(1 / 2 : ℝ))).fun_mul hid).fun_mul
      ((hDr.fun_mul hDr).fun_add (hDi.fun_mul hDi))).fun_sub
    (hw.fun_mul ((hDr.fun_mul hFr).fun_add (hDi.fun_mul hFi)))).fun_sub
    ((hid.const_mul (1 / 2 : ℝ)).fun_mul ((hFr.fun_mul hFr).fun_add (hFi.fun_mul hFi)))
  convert hK using 1
  ext t
  simp [boundaryFlux, normSq_apply, mul_re]

/-- The primitive of the completed square is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_boundaryPrimitive (lam : ℝ) {F D : ℝ → ℂ} {x y : ℝ}
    (hF : AbsolutelyContinuousOnInterval F x y) (hD : AbsolutelyContinuousOnInterval D x y) :
    AbsolutelyContinuousOnInterval (boundaryPrimitive lam F D) x y := by
  have hid : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ (t : ℂ)) x y := by
    simpa using! ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
      (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval (a := x) (b := y))
  have hw : AbsolutelyContinuousOnInterval (fun t ↦ (boundaryWeight t : ℂ)) x y := by
    simpa using! ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
      (absolutelyContinuousOnInterval_boundaryWeight x y)
  have hQ := ((hw.fun_smul hD).fun_add (hid.fun_smul hF)).fun_sub (hF.const_smul (I * lam))
  convert hQ using 1
  ext t
  simp [boundaryPrimitive, smul_eq_mul]

/-- The flux identity integrated over an interior interval. -/
theorem HasWeightedBoundaryH2.integral_boundaryFluxDerivative {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    (∫ t in x..y, boundaryFluxDerivative F D E t) = boundaryFlux F D y - boundaryFlux F D x := by
  have hsub : uIcc x y ⊆ Ioo (-1 : ℝ) 1 := ordConnected_Ioo.uIcc_subset hx hy
  have hK := absolutelyContinuousOnInterval_boundaryFlux (h.h1.absolutelyContinuous hx hy)
    (h.absolutelyContinuous_first hx hy)
  rw [← hK.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [h.h1.hasDerivAt_ae, h.hasDerivAt_first_ae] with t hF hD ht
  have htI := hsub (uIoc_subset_uIcc ht)
  exact (hasDerivAt_boundaryFlux (hF htI) (hD htI)).deriv.symm

/-- The completed square integrated over an interior interval. -/
theorem HasWeightedBoundaryH2.integral_boundarySquare {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    (∫ t in x..y, boundarySquare lam F D E t) =
      boundaryPrimitive lam F D y - boundaryPrimitive lam F D x := by
  have hsub : uIcc x y ⊆ Ioo (-1 : ℝ) 1 := ordConnected_Ioo.uIcc_subset hx hy
  apply complex_integral_eq_sub_of_ac (absolutelyContinuousOnInterval_boundaryPrimitive lam
    (h.h1.absolutelyContinuous hx hy) (h.absolutelyContinuous_first hx hy))
  · have hi : IntegrableOn (boundarySquare lam F D E) (uIcc x y) :=
      ((h.memLp_boundarySquare lam).integrable one_le_two).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    exact hi.intervalIntegrable
  · filter_upwards [h.h1.hasDerivAt_ae, h.hasDerivAt_first_ae] with t hF hD ht
    exact hasDerivAt_boundaryPrimitive lam (hF (hsub ht)) (hD (hsub ht))

/-! ### Endpoint behaviour -/

/-- An interval H¹ function tends to its right trace. -/
theorem HasIntervalH1.tendsto_right {a b : ℝ} {F D : ℝ → ℂ} (h : HasIntervalH1 a b F D)
    (hab : a < b) : Tendsto F (𝓝[<] b) (𝓝 (intervalH1Extension a b F D b)) := by
  have hc := (h.continuousOn_extension hab) b (right_mem_Icc.2 hab.le)
  exact (hc.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsLT hab)
    Ioo_subset_Icc_self)).tendsto.congr'
    (eventually_of_mem (Ioo_mem_nhdsLT hab) fun x hx ↦ h.extension_eq hab hx)

/-- An interval H¹ function tends to its left trace. -/
theorem HasIntervalH1.tendsto_left {a b : ℝ} {F D : ℝ → ℂ} (h : HasIntervalH1 a b F D)
    (hab : a < b) : Tendsto F (𝓝[>] a) (𝓝 (intervalH1Extension a b F D a)) := by
  have hc := (h.continuousOn_extension hab) a (left_mem_Icc.2 hab.le)
  exact (hc.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsGT hab)
    Ioo_subset_Icc_self)).tendsto.congr'
    (eventually_of_mem (Ioo_mem_nhdsGT hab) fun x hx ↦ h.extension_eq hab hx)

/-- Pointwise algebra for the weight on the interval. -/
theorem boundaryWeight_bounds {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ boundaryWeight x ∧ boundaryWeight x ≤ 1 ∧ boundaryWeight x ≤ 2 * (1 - x) ∧
      boundaryWeight x ≤ 2 * (1 + x) := by
  unfold boundaryWeight
  refine ⟨by nlinarith [hx.1, hx.2], by nlinarith, by nlinarith [sq_nonneg (x - 1)],
    by nlinarith [sq_nonneg (x + 1)]⟩

/-- From `w (1 ∓ x) ≤ 2 (1 ∓ x)`: both `w |D|` and `w |D|²` are frequently small, given
    smallness of `(distance to the endpoint) * |D|²`. -/
theorem weight_small_of_mul_sq_lt {D : ℝ → ℂ} {x ε s : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hs : boundaryWeight x ≤ 2 * s)
    (hsD : s * ‖D x‖ ^ 2 < min ε (ε ^ 2) / 2) :
    boundaryWeight x * ‖D x‖ < ε ∧ boundaryWeight x * ‖D x‖ ^ 2 < ε := by
  obtain ⟨hw0, hw1, -, -⟩ := boundaryWeight_bounds hx
  have hq : boundaryWeight x * ‖D x‖ ^ 2 < min ε (ε ^ 2) := by
    nlinarith [sq_nonneg ‖D x‖]
  refine ⟨?_, hq.trans_le (min_le_left _ _)⟩
  have hsq : (boundaryWeight x * ‖D x‖) ^ 2 < ε ^ 2 := by
    calc (boundaryWeight x * ‖D x‖) ^ 2 = boundaryWeight x * (boundaryWeight x * ‖D x‖ ^ 2) := by
          ring
      _ ≤ 1 * (boundaryWeight x * ‖D x‖ ^ 2) := by gcongr
      _ < ε ^ 2 := by linarith [min_le_right ε (ε ^ 2)]
  exact (pow_lt_pow_iff_left₀ (by positivity) hε.le two_ne_zero).1 hsq

/-- Near `1`, both `w |D|` and `w |D|²` are frequently small. -/
theorem frequently_weight_small_right {D : ℝ → ℂ}
    (hD : IntegrableOn (fun x ↦ ‖D x‖ ^ 2) (Ioo (-1) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in 𝓝[<] 1, boundaryWeight x * ‖D x‖ < ε ∧ boundaryWeight x * ‖D x‖ ^ 2 < ε := by
  refine ((frequently_sub_mul_sq_lt_right (by norm_num) hD (by positivity :
    0 < min ε (ε ^ 2) / 2)).and_eventually (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1))).mono ?_
  rintro x ⟨hxD, hx⟩
  exact weight_small_of_mul_sq_lt hε (Ioo_subset_Icc_self hx)
    (boundaryWeight_bounds (Ioo_subset_Icc_self hx)).2.2.1 hxD

/-- Near `-1`, both `w |D|` and `w |D|²` are frequently small. -/
theorem frequently_weight_small_left {D : ℝ → ℂ}
    (hD : IntegrableOn (fun x ↦ ‖D x‖ ^ 2) (Ioo (-1) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in 𝓝[>] (-1), boundaryWeight x * ‖D x‖ < ε ∧ boundaryWeight x * ‖D x‖ ^ 2 < ε := by
  refine ((frequently_sub_mul_sq_lt_left (by norm_num) hD (by positivity :
    0 < min ε (ε ^ 2) / 2)).and_eventually (Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1))).mono ?_
  rintro x ⟨hxD, hx⟩
  refine weight_small_of_mul_sq_lt (s := x - -1) hε (Ioo_subset_Icc_self hx) ?_ hxD
  linarith [(boundaryWeight_bounds (Ioo_subset_Icc_self hx)).2.2.2]

/-- The flux differs from its unweighted part by terms controlled by `w |D|` and `w |D|²`. -/
theorem abs_boundaryFlux_add_le (F D : ℝ → ℂ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |boundaryFlux F D x + (1 / 2) * x * normSq (F x)| ≤
      boundaryWeight x * ‖D x‖ ^ 2 + boundaryWeight x * ‖D x‖ * ‖F x‖ := by
  obtain ⟨hw0, -, -, -⟩ := boundaryWeight_bounds hx
  have hx1 : |x| ≤ 1 := abs_le.2 hx
  have e : boundaryFlux F D x + (1 / 2) * x * normSq (F x) =
      -((1 / 2) * x) * (boundaryWeight x * ‖D x‖ ^ 2) -
        boundaryWeight x * (D x * conj (F x)).re := by
    simp only [boundaryFlux, Complex.normSq_eq_norm_sq]
    ring
  have h1 : |-((1 / 2) * x) * (boundaryWeight x * ‖D x‖ ^ 2)| ≤
      boundaryWeight x * ‖D x‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ boundaryWeight x * ‖D x‖ ^ 2), abs_neg,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := mul_nonneg hw0 (sq_nonneg ‖D x‖)
    nlinarith
  have h2 : |boundaryWeight x * (D x * conj (F x)).re| ≤
      boundaryWeight x * ‖D x‖ * ‖F x‖ := by
    rw [abs_mul, abs_of_nonneg hw0, mul_assoc]
    gcongr
    calc |(D x * conj (F x)).re| ≤ ‖D x * conj (F x)‖ := abs_re_le_norm _
      _ = ‖D x‖ * ‖F x‖ := by rw [norm_mul, Complex.norm_conj]
  rw [e]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- Along a filter on which `F → c`, `x → s` and `w |D|`, `w |D|²` are frequently small,
    the flux comes arbitrarily close to `-s |c|² / 2`. -/
theorem frequently_boundaryFlux_near {l : Filter ℝ} {F D : ℝ → ℂ} {c : ℂ} {s : ℝ}
    (hI : ∀ᶠ x in l, x ∈ Icc (-1 : ℝ) 1) (hF : Tendsto F l (𝓝 c))
    (hs : Tendsto (fun x : ℝ ↦ x) l (𝓝 s))
    (hD : ∀ η > 0, ∃ᶠ x in l, boundaryWeight x * ‖D x‖ < η ∧
      boundaryWeight x * ‖D x‖ ^ 2 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in l, ‖boundaryFlux F D x - (-(1 / 2) * s * normSq c)‖ < ε := by
  set M := ‖c‖ + 1
  have hM : ∀ᶠ x in l, ‖F x‖ < M := hF.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hT : Tendsto (fun x ↦ (1 / 2) * x * normSq (F x)) l (𝓝 ((1 / 2) * s * normSq c)) :=
    (tendsto_const_nhds.mul hs).mul ((continuous_normSq.tendsto c).comp hF)
  have hT' := Metric.tendsto_nhds.1 hT (ε / 2) (half_pos hε)
  have hη : 0 < ε / (2 * (M + 1)) := by positivity
  refine ((hD _ hη).and_eventually ((hM.and hT').and hI)).mono ?_
  rintro x ⟨⟨hD1, hD2⟩, ⟨hFx, hTx⟩, hx⟩
  rw [Real.dist_eq] at hTx
  have hb := abs_boundaryFlux_add_le F D hx
  have hwF : boundaryWeight x * ‖D x‖ * ‖F x‖ ≤ ε / (2 * (M + 1)) * M := by
    gcongr
  have hM0 : M + 1 ≠ 0 := by
    simp only [M]
    positivity
  have hsum : ε / (2 * (M + 1)) + ε / (2 * (M + 1)) * M = ε / 2 := by
    field_simp
    ring
  rw [Real.norm_eq_abs]
  calc |boundaryFlux F D x - (-(1 / 2) * s * normSq c)|
      = |(boundaryFlux F D x + (1 / 2) * x * normSq (F x)) -
          ((1 / 2) * x * normSq (F x) - (1 / 2) * s * normSq c)| := by ring_nf
    _ ≤ |boundaryFlux F D x + (1 / 2) * x * normSq (F x)| +
          |(1 / 2) * x * normSq (F x) - (1 / 2) * s * normSq c| := abs_sub _ _
    _ < ε := by linarith

/-- Along a filter on which `F → c`, `x → s` and `w |D|` is frequently small, the
    primitive of the completed square comes arbitrarily close to `(s - iλ) c`. -/
theorem frequently_boundaryPrimitive_near (lam : ℝ) {l : Filter ℝ} {F D : ℝ → ℂ} {c : ℂ}
    {s : ℝ} (hI : ∀ᶠ x in l, x ∈ Icc (-1 : ℝ) 1) (hF : Tendsto F l (𝓝 c))
    (hs : Tendsto (fun x : ℝ ↦ x) l (𝓝 s))
    (hD : ∀ η > 0, ∃ᶠ x in l, boundaryWeight x * ‖D x‖ < η ∧
      boundaryWeight x * ‖D x‖ ^ 2 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in l, ‖boundaryPrimitive lam F D x - ((s : ℂ) * c - I * lam * c)‖ < ε := by
  have hT : Tendsto (fun x : ℝ ↦ (x : ℂ) * F x - I * lam * F x) l
      (𝓝 ((s : ℂ) * c - I * lam * c)) :=
    ((continuous_ofReal.tendsto s).comp hs |>.mul hF).sub (tendsto_const_nhds.mul hF)
  refine ((hD _ (half_pos hε)).and_eventually
    ((Metric.tendsto_nhds.1 hT (ε / 2) (half_pos hε)).and hI)).mono ?_
  rintro x ⟨⟨hD1, -⟩, hTx, hx⟩
  rw [dist_eq_norm] at hTx
  have hw0 := (boundaryWeight_bounds hx).1
  calc ‖boundaryPrimitive lam F D x - ((s : ℂ) * c - I * lam * c)‖
      = ‖(boundaryWeight x : ℂ) * D x +
          (((x : ℂ) * F x - I * lam * F x) - ((s : ℂ) * c - I * lam * c))‖ := by
        congr 1
        simp only [boundaryPrimitive]
        ring
    _ ≤ ‖(boundaryWeight x : ℂ) * D x‖ +
          ‖((x : ℂ) * F x - I * lam * F x) - ((s : ℂ) * c - I * lam * c)‖ := norm_add_le _ _
    _ < ε := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
      linarith

/-! ### Completion of squares -/

/-- Completion of squares on the weighted domain, with the trace correction. -/
theorem HasWeightedBoundaryH2.completion {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    boundaryForm lam F D E =
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (boundarySquare lam F D E x)) +
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (D x)) -
      (1 / 2 : ℝ) * (normSq (intervalH1Extension (-1) 1 F D 1) +
        normSq (intervalH1Extension (-1) 1 F D (-1))) := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  have hio : ∀ {f : ℝ → ℝ}, Integrable f (volume.restrict (Ioo (-1 : ℝ) 1)) →
      IntervalIntegrable f volume (-1) 1 := fun hf ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hf
  have hA := hio (integrable_normSq_of_memLp (h.memLp_formSquare lam))
  have hB := hio h.integrable_weight_normSq
  have hC := hio (integrable_im_mul_conj_of_memLp h.h1.memLp_derivative h.h1.memLp_value)
  have hS := hio (integrable_normSq_of_memLp (h.memLp_boundarySquare lam))
  have hD := hio (integrable_normSq_of_memLp h.h1.memLp_derivative)
  have hpt : ∀ x, boundaryFluxDerivative F D E x =
      ((1 / 2 : ℝ) * normSq ((boundaryWeight x : ℂ) * E x - (2 * x : ℂ) * D x -
        I * lam * D x) - boundaryWeight x * normSq (D x) + lam * (D x * conj (F x)).im) -
      ((1 / 2 : ℝ) * normSq (boundarySquare lam F D E x) + (1 / 2 : ℝ) * normSq (D x)) := by
    intro x
    have := boundary_density_completion lam x (F x) (D x) (E x)
    simp only [boundaryFluxDerivative, boundarySquare]
    linarith
  have hK : IntervalIntegrable (boundaryFluxDerivative F D E) volume (-1) 1 := by
    have := (((hA.const_mul (1 / 2)).sub hB).add (hC.const_mul lam)).sub
      ((hS.const_mul (1 / 2)).add (hD.const_mul (1 / 2)))
    convert this using 1
    funext x
    exact hpt x
  have hD2 : IntegrableOn (fun x ↦ ‖D x‖ ^ 2) (Ioo (-1) 1) :=
    h.h1.memLp_derivative.norm.integrable_sq
  have hflux := intervalIntegral_eq_of_frequently hab hK
    (fun x hx y hy ↦ h.integral_boundaryFluxDerivative hx hy)
    (fun ε hε ↦ frequently_boundaryFlux_near
      (eventually_of_mem (Ioo_mem_nhdsGT hab) fun _ hx ↦ Ioo_subset_Icc_self hx)
      (h.h1.tendsto_left hab) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      (fun η hη ↦ frequently_weight_small_left hD2 hη) hε)
    (fun ε hε ↦ frequently_boundaryFlux_near
      (eventually_of_mem (Ioo_mem_nhdsLT hab) fun _ hx ↦ Ioo_subset_Icc_self hx)
      (h.h1.tendsto_right hab) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      (fun η hη ↦ frequently_weight_small_right hD2 hη) hε)
  have hid := intervalIntegral.integral_congr (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (fun x _ ↦ hpt x)
  rw [intervalIntegral.integral_sub (((hA.const_mul (1 / 2)).sub hB).add (hC.const_mul lam))
      ((hS.const_mul (1 / 2)).add (hD.const_mul (1 / 2))),
    intervalIntegral.integral_add ((hA.const_mul (1 / 2)).sub hB) (hC.const_mul lam),
    intervalIntegral.integral_sub (hA.const_mul (1 / 2)) hB,
    intervalIntegral.integral_add (hS.const_mul (1 / 2)) (hD.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hflux] at hid
  rw [boundaryForm]
  linear_combination -hid

/-- With zero traces, the weighted boundary form is a sum of squares. -/
theorem HasWeightedBoundaryH2.sum_of_squares {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hneg : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hpos : intervalH1Extension (-1) 1 F D 1 = 0) :
    boundaryForm lam F D E =
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (boundarySquare lam F D E x)) +
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, normSq (D x)) := by
  simpa [hneg, hpos] using h.completion lam

/-! ### Affine splitting and positivity -/

/-- The integral of the completed square, from the traces. -/
theorem HasWeightedBoundaryH2.integral_boundarySquare_eq {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) :
    (∫ x in (-1 : ℝ)..1, boundarySquare lam F D E x) =
      (1 - I * lam) * intervalH1Extension (-1) 1 F D 1 +
        (1 + I * lam) * intervalH1Extension (-1) 1 F D (-1) := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  have hD2 : IntegrableOn (fun x ↦ ‖D x‖ ^ 2) (Ioo (-1) 1) :=
    h.h1.memLp_derivative.norm.integrable_sq
  have hS : IntervalIntegrable (boundarySquare lam F D E) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((h.memLp_boundarySquare lam).integrable one_le_two)
  rw [intervalIntegral_eq_of_frequently hab hS
    (fun x hx y hy ↦ h.integral_boundarySquare lam hx hy)
    (fun ε hε ↦ frequently_boundaryPrimitive_near lam
      (eventually_of_mem (Ioo_mem_nhdsGT hab) fun _ hx ↦ Ioo_subset_Icc_self hx)
      (h.h1.tendsto_left hab) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      (fun η hη ↦ frequently_weight_small_left hD2 hη) hε)
    (fun ε hε ↦ frequently_boundaryPrimitive_near lam
      (eventually_of_mem (Ioo_mem_nhdsLT hab) fun _ hx ↦ Ioo_subset_Icc_self hx)
      (h.h1.tendsto_right hab) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      (fun η hη ↦ frequently_weight_small_right hD2 hη) hε)]
  push_cast
  ring

/-- Subtracting an affine function subtracts it from the traces. -/
theorem HasWeightedBoundaryH2.extension_subAffine {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (a b : ℂ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    intervalH1Extension (-1) 1 (fun x ↦ F x - a - b * (x : ℂ)) (fun x ↦ D x - b) x =
      intervalH1Extension (-1) 1 F D x - a - b * (x : ℂ) := by
  have hD : IntervalIntegrable D volume 0 x :=
    (h.h1.integrableOn_derivative.mono_set
      (uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hx)).intervalIntegrable
  simp only [intervalH1Extension]
  norm_num
  rw [intervalIntegral.integral_sub hD intervalIntegrable_const]
  simp
  ring

/-- Affine splitting on the weighted domain: the mixed terms with the zero-trace
    remainder cancel. -/
theorem HasWeightedBoundaryH2.affine_splitting {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ) (a b : ℂ)
    (hneg : intervalH1Extension (-1) 1 F D (-1) = a - b)
    (hpos : intervalH1Extension (-1) 1 F D 1 = a + b) :
    boundaryForm lam F D E =
      boundaryForm lam (fun x ↦ F x - a - b * (x : ℂ)) (fun x ↦ D x - b) E +
        lam ^ 2 * normSq b + 2 * lam * (b * conj a).im := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  have h₀ := h.subAffine a b
  have h0neg : intervalH1Extension (-1) 1 (fun x ↦ F x - a - b * (x : ℂ))
      (fun x ↦ D x - b) (-1) = 0 := by
    rw [h.extension_subAffine a b (left_mem_Icc.2 hab.le), hneg]
    push_cast
    ring
  have h0pos : intervalH1Extension (-1) 1 (fun x ↦ F x - a - b * (x : ℂ))
      (fun x ↦ D x - b) 1 = 0 := by
    rw [h.extension_subAffine a b (right_mem_Icc.2 hab.le), hpos]
    push_cast
    ring
  have hio : ∀ {f : ℝ → ℂ}, MemLp f 2 (volume.restrict (Ioo (-1 : ℝ) 1)) →
      IntervalIntegrable f volume (-1) 1 := fun hf ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hf.integrable one_le_two)
  have hio' : ∀ {f : ℝ → ℂ}, MemLp f 2 (volume.restrict (Ioo (-1 : ℝ) 1)) →
      IntervalIntegrable (fun x ↦ normSq (f x)) volume (-1) 1 := fun hf ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (integrable_normSq_of_memLp hf)
  have hS0 : (∫ x in (-1 : ℝ)..1, boundarySquare lam (fun x ↦ F x - a - b * (x : ℂ))
      (fun x ↦ D x - b) E x) = 0 := by
    rw [h₀.integral_boundarySquare_eq, h0neg, h0pos]
    ring
  have hD0 : (∫ x in (-1 : ℝ)..1, D x - b) = 0 := by
    exact (h₀.h1.integral_eq_extension_sub hab (left_mem_Icc.2 hab.le)
      (right_mem_Icc.2 hab.le)).trans (by rw [h0neg, h0pos, sub_zero])
  have hS : (∫ x in (-1 : ℝ)..1, normSq (boundarySquare lam F D E x)) =
      (∫ x in (-1 : ℝ)..1, normSq (boundarySquare lam (fun x ↦ F x - a - b * (x : ℂ))
        (fun x ↦ D x - b) E x)) + 2 * normSq (a - I * lam * b) := by
    rw [← integral_normSq_add_const _ (a - I * lam * b) (hio (h₀.memLp_boundarySquare lam))
      (hio' (h₀.memLp_boundarySquare lam)) hS0]
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg normSq
    simp only [boundarySquare]
    ring
  have hD : (∫ x in (-1 : ℝ)..1, normSq (D x)) =
      (∫ x in (-1 : ℝ)..1, normSq (D x - b)) + 2 * normSq b := by
    rw [← integral_normSq_add_const _ b (hio h₀.h1.memLp_derivative)
      (hio' h₀.h1.memLp_derivative) hD0]
    apply intervalIntegral.integral_congr
    intro x _
    simp
  rw [h.completion lam, h₀.completion lam, hS, hD, hpos, hneg, h0neg, h0pos]
  simp [normSq_apply, mul_re, mul_im]
  ring

/-- Positivity of the boundary form on the weighted domain, for equal or opposite
    traces. -/
theorem HasWeightedBoundaryH2.boundaryForm_nonneg {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (lam : ℝ)
    (hends : intervalH1Extension (-1) 1 F D 1 = intervalH1Extension (-1) 1 F D (-1) ∨
      intervalH1Extension (-1) 1 F D 1 = -intervalH1Extension (-1) 1 F D (-1)) :
    0 ≤ boundaryForm lam F D E := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  set T := intervalH1Extension (-1) 1 F D
  let a := (T 1 + T (-1)) / 2
  let b := (T 1 - T (-1)) / 2
  have hneg : T (-1) = a - b := by dsimp [a, b]; ring
  have hpos : T 1 = a + b := by dsimp [a, b]; ring
  have h₀ := h.subAffine a b
  have h0 : 0 ≤ boundaryForm lam (fun x ↦ F x - a - b * (x : ℂ)) (fun x ↦ D x - b) E := by
    rw [h₀.sum_of_squares lam
      (by
        rw [h.extension_subAffine a b (left_mem_Icc.2 hab.le)]
        change T (-1) - _ - _ = 0
        rw [hneg]
        push_cast
        ring)
      (by
        rw [h.extension_subAffine a b (right_mem_Icc.2 hab.le)]
        change T 1 - _ - _ = 0
        rw [hpos]
        push_cast
        ring)]
    have hS := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
      (fun x ↦ normSq_nonneg (boundarySquare lam (fun x ↦ F x - a - b * (x : ℂ))
        (fun x ↦ D x - b) E x))
    have hD := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
      (fun x ↦ normSq_nonneg (D x - b))
    positivity
  rw [h.affine_splitting lam a b hneg hpos]
  rcases hends with hends | hends
  · have hb : b = 0 := by simp [b, hends]
    simpa [hb] using h0
  · have ha : a = 0 := by simp [a, hends]
    simp only [ha, map_zero, mul_zero, zero_im, add_zero]
    simp only [ha] at h0
    exact add_nonneg h0 (mul_nonneg (sq_nonneg lam) (normSq_nonneg b))

end EulerDipoleEigenvalues
