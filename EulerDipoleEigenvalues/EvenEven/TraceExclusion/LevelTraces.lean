module

public import EulerDipoleEigenvalues.EvenEven.GradientTraces.SeparatrixTraces

/-! # Even–even level traces and their limits -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ### Level traces -/

/-- Integrability on a quarter orbit in diagonal coordinates (`lem:quarter-orbit-diagonal`). -/
theorem integrableOn_quarter_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ}
    (h0 : 0 < h) (h1 : h < 1) (f : ℝ × ℝ → E) :
    IntegrableOn (fun t ↦ f (dipoleOrbit h t)) (Ioo (-eighthPeriod h) (eighthPeriod h)) ↔
      IntegrableOn (fun a ↦ (1 / √(cos a ^ 2 - h ^ 2)) • f (diagInv (a, quarterHeight h a)))
        (Ioo (-arccos √h) (arccos √h)) := by
  have hderiv : ∀ t ∈ Ioo (-eighthPeriod h) (eighthPeriod h),
      HasDerivWithinAt (orbitA h) (-√(cos (orbitA h t) ^ 2 - h ^ 2))
        (Ioo (-eighthPeriod h) (eighthPeriod h)) t := fun t ht ↦
    (hasDerivAt_orbitA_quarter h0 h1 (abs_le.2 ⟨ht.1.le, ht.2.le⟩)).hasDerivWithinAt
  have hcv := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv
    ((strictAntiOn_orbitA h0 h1).injOn.mono Ioo_subset_Icc_self)
    (fun a ↦ (1 / √(cos a ^ 2 - h ^ 2)) • f (diagInv (a, quarterHeight h a)))
  rw [image_orbitA_quarter h0 h1] at hcv
  rw [hcv]
  refine integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Ioo
  have htL : |t| ≤ eighthPeriod h := abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have hb := orbitB_pos_of_abs_le h0 h1 htL
  have hlt := lt_cos_orbitA h0 h1 hb.ne'
  have hpos : 0 < √(cos (orbitA h t) ^ 2 - h ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [cos_orbitA_pos h0 h1 t])
  rw [smul_smul, abs_neg, abs_of_pos hpos, mul_one_div_cancel hpos.ne', one_smul,
    ← orbitB_eq_quarterHeight h0 h1 htL, ← dipoleOrbit_eq_diagInv]

/-- Dominated convergence on the quarter orbits. Let `F ≥ 0` be continuous in `b` at `b = π/2`
    on almost every line, dominated on the quarter orbits by `Φ` for `h ≤ 1/4`, and equal on
    the quarter orbits to a measurable `Fr` for `h` outside `N`. Then the quarter integrals of
    `Fr` converge to `∫_{-π/2}^{π/2} F(a, π/2) da / cos a` as `h → 0` outside `N`. -/
theorem tendsto_quarter_integral {F Fr : ℝ × ℝ → ℝ} (hFr : Measurable Fr) (hF0 : ∀ p, 0 ≤ F p)
    {Φ : ℝ → ℝ≥0∞} (hΦm : Measurable Φ) (hΦfin : ∫⁻ a in Ioo (-(π / 2)) (π / 2), Φ a < ∞)
    (hΦ : ∀ h ∈ Ioo (0 : ℝ) (1 / 4), ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
      ENNReal.ofReal (F (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2)) ≤ Φ a)
    (hcont : ∀ᵐ a ∂(volume.restrict (Ioo (-(π / 2)) (π / 2))),
      ContinuousAt (fun b ↦ F (diagInv (a, b))) (π / 2))
    {N : Set ℝ} (hN : ∀ h ∈ Ioo (0 : ℝ) 1 \ N,
      ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        Fr (diagInv (a, quarterHeight h a)) = F (diagInv (a, quarterHeight h a))) :
    (∀ h ∈ Ioo (0 : ℝ) (1 / 4) \ N, IntegrableOn (fun t ↦ Fr (dipoleOrbit h t))
      (Ioo (-eighthPeriod h) (eighthPeriod h))) ∧
    Tendsto (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), Fr (dipoleOrbit h t))
      (𝓝[Ioi 0 \ N] 0) (𝓝 (∫ a in Ioo (-(π / 2)) (π / 2), F (diagInv (a, π / 2)) / cos a)) := by
  have hπ := Real.pi_pos
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  set S : ℝ → Set ℝ := fun h ↦ Ioo (-arccos √h) (arccos √h) with hS
  have hSA (h : ℝ) (h0 : 0 < h) : S h ⊆ A :=
    Ioo_subset_Ioo (by linarith [Real.arccos_lt_pi_div_two.2 (Real.sqrt_pos.2 h0)])
      (Real.arccos_lt_pi_div_two.2 (Real.sqrt_pos.2 h0)).le
  -- The raw integrand in `a`, measurable.
  set Hr : ℝ → ℝ → ℝ := fun h a ↦ (S h).indicator
    (fun a ↦ Fr (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2)) a with hHr
  set H : ℝ → ℝ → ℝ := fun h a ↦ (S h).indicator
    (fun a ↦ F (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2)) a with hH
  have hHrm (h : ℝ) : Measurable (Hr h) := by
    refine Measurable.indicator ?_ measurableSet_Ioo
    have hq : Measurable fun a : ℝ ↦ diagInv (a, quarterHeight h a) := by
      unfold quarterHeight
      have := Real.continuous_arccos.measurable
      exact diagInv.continuous.measurable.comp (by fun_prop)
    exact (hFr.comp hq).div (by fun_prop)
  have hHae (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1 \ N) : Hr h =ᵐ[volume.restrict A] H h := by
    have h' := (ae_restrict_iff' measurableSet_Ioo).1 (hN h hh)
    filter_upwards [ae_restrict_of_ae h'] with a ha
    by_cases haS : a ∈ S h
    · simp only [hHr, hH, indicator_of_mem haS, ha haS]
    · simp only [hHr, hH, indicator_of_notMem haS]
  have hΦlt : ∀ᵐ a ∂(volume.restrict A), Φ a < ∞ :=
    ae_lt_top' hΦm.aemeasurable hΦfin.ne
  have hbound (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4)) :
      ∀ᵐ a ∂(volume.restrict A), ‖H h a‖ ≤ (Φ a).toReal := by
    have h' := (ae_restrict_iff' measurableSet_Ioo).1 (hΦ h hh)
    filter_upwards [ae_restrict_of_ae h', hΦlt] with a ha hlt
    by_cases haS : a ∈ S h
    · simp only [hH, indicator_of_mem haS]
      have hnn : 0 ≤ F (diagInv (a, quarterHeight h a)) / √(cos a ^ 2 - h ^ 2) :=
        div_nonneg (hF0 _) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).1 (ha haS)
    · simp only [hH, indicator_of_notMem haS, norm_zero]
      exact ENNReal.toReal_nonneg
  -- The quarter integral is the integral of `H` over `A`.
  have hquarter (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1 \ N) :
      ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), Fr (dipoleOrbit h t) =
        ∫ a in A, H h a := by
    have h0 := hh.1.1
    rw [integral_quarter_eq h0 hh.1.2, ← integral_congr_ae (hHae h hh), hHr,
      integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.2 (hSA h h0)]
    refine setIntegral_congr_fun measurableSet_Ioo fun a _ ↦ ?_
    simp only [smul_eq_mul]
    ring
  constructor
  · intro h hh
    have hh1 : h ∈ Ioo (0 : ℝ) 1 \ N := ⟨⟨hh.1.1, by linarith [hh.1.2]⟩, hh.2⟩
    rw [integrableOn_quarter_iff hh.1.1 hh1.1.2]
    have hint : IntegrableOn (H h) A :=
      Integrable.mono' (integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable hΦfin.ne)
        ((hHrm h).aestronglyMeasurable.congr (hHae h hh1)) (hbound h hh.1)
    have hint' : IntegrableOn (Hr h) A := hint.congr (hHae h hh1).symm
    have := IntegrableOn.mono_set hint' (hSA h hh.1.1)
    refine (this.congr_fun (fun a ha ↦ ?_) measurableSet_Ioo)
    simp only [hHr, indicator_of_mem ha, smul_eq_mul]
    ring
  -- Dominated convergence.
  have hl : (𝓝[Ioi 0 \ N] (0 : ℝ)).IsCountablyGenerated := inferInstance
  have hev : ∀ᶠ h in 𝓝[Ioi 0 \ N] (0 : ℝ), h ∈ Ioo (0 : ℝ) (1 / 4) \ N := by
    have h1 : ∀ᶠ h in 𝓝[Ioi 0 \ N] (0 : ℝ), h < 1 / 4 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [h1, self_mem_nhdsWithin] with h h1 h2
    exact ⟨⟨h2.1, h1⟩, h2.2⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict A)
    (F := H) (f := fun a ↦ F (diagInv (a, π / 2)) / cos a) (fun a ↦ (Φ a).toReal)
    (by filter_upwards [hev] with h hh
        exact (hHrm h).aestronglyMeasurable.congr
          (hHae h ⟨⟨hh.1.1, by linarith [hh.1.2]⟩, hh.2⟩))
    (by filter_upwards [hev] with h hh
        exact hbound h hh.1)
    (integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable hΦfin.ne)
    (by
      filter_upwards [hcont, ae_restrict_mem measurableSet_Ioo] with a hca ha
      have hc := cos_pos_of_mem_Ioo ha
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      -- Near `h = 0` the point lies on the quarter orbit.
      have harc : ContinuousAt (fun h : ℝ ↦ arccos √h) 0 :=
        (Real.continuous_arccos.comp Real.continuous_sqrt).continuousAt
      have hmem : ∀ᶠ h in 𝓝 (0 : ℝ), a ∈ S h := by
        have h1 : ∀ᶠ h in 𝓝 (0 : ℝ), |a| < arccos √h := by
          have := harc.eventually (lt_mem_nhds (show |a| < arccos √(0 : ℝ) by
            rw [Real.sqrt_zero, Real.arccos_zero]
            exact abs_lt.2 ⟨ha.1, ha.2⟩))
          exact this
        filter_upwards [h1] with h h1
        exact ⟨by linarith [neg_abs_le a], lt_of_le_of_lt (le_abs_self a) h1⟩
      have hβ : ContinuousAt (fun h : ℝ ↦ quarterHeight h a) 0 := by
        unfold quarterHeight
        exact (Real.continuous_arccos.comp (continuous_id.div_const _)).continuousAt
      have hβ0 : quarterHeight 0 a = π / 2 := by
        simp [quarterHeight, Real.arccos_zero]
      have hF : ContinuousAt (fun h : ℝ ↦ F (diagInv (a, quarterHeight h a))) 0 :=
        ContinuousAt.comp_of_eq (g := fun b ↦ F (diagInv (a, b))) hca hβ hβ0
      have hw : ContinuousAt (fun h : ℝ ↦ √(cos a ^ 2 - h ^ 2)) 0 := by fun_prop
      have hw0 : √(cos a ^ 2 - (0 : ℝ) ^ 2) = cos a := by
        rw [sq (0 : ℝ), mul_zero, sub_zero, Real.sqrt_sq hc.le]
      have h1 : Tendsto (fun h : ℝ ↦ F (diagInv (a, quarterHeight h a))) (𝓝 0)
          (𝓝 (F (diagInv (a, π / 2)))) := by
        simpa only [hβ0] using hF.tendsto
      have h2 : Tendsto (fun h : ℝ ↦ √(cos a ^ 2 - h ^ 2)) (𝓝 0) (𝓝 (cos a)) := by
        simpa only [hw0] using hw.tendsto
      refine (h1.div h2 hc.ne').congr' ?_
      filter_upwards [hmem] with h hh
      simp only [hH, indicator_of_mem hh, Pi.div_apply])
  refine (hlim.congr' ?_)
  filter_upwards [hev] with h hh
  exact (hquarter h ⟨⟨hh.1.1, by linarith [hh.1.2]⟩, hh.2⟩).symm

/-- Continuity of `ψₙ` and `ψₜ` along a line `a = const`, where `ρ ≠ 0`. -/
theorem continuousAt_line_normalDeriv {X Y : ℝ × ℝ → ℂ} {a b₀ : ℝ}
    (hX : ContinuousAt (fun b ↦ X (diagInv (a, b))) b₀)
    (hY : ContinuousAt (fun b ↦ Y (diagInv (a, b))) b₀) (hρ : gradNorm (diagInv (a, b₀)) ≠ 0) :
    ContinuousAt (fun b ↦ normalDeriv X Y (diagInv (a, b))) b₀ ∧
      ContinuousAt (fun b ↦ tangentDeriv X Y (diagInv (a, b))) b₀ := by
  have hs1 : Continuous fun b : ℝ ↦ ((sin (diagInv (a, b)).1 : ℝ) : ℂ) := by
    simp only [diagInv_apply]
    fun_prop
  have hs2 : Continuous fun b : ℝ ↦ ((sin (diagInv (a, b)).2 : ℝ) : ℂ) := by
    simp only [diagInv_apply]
    fun_prop
  have hg : Continuous fun b : ℝ ↦ ((gradNorm (diagInv (a, b)) : ℝ) : ℂ) := by
    simp only [gradNorm, diagInv_apply]
    fun_prop
  have hg0 : ((gradNorm (diagInv (a, b₀)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ
  exact ⟨((hs1.continuousAt.mul hX).add (hs2.continuousAt.mul hY)).div hg.continuousAt hg0,
    ((hs2.continuousAt.mul hX).sub (hs1.continuousAt.mul hY)).div hg.continuousAt hg0⟩

/-- Level traces on one quarter orbit (`lem:ee-level-traces`, the quarter `k = 0`): outside a
    null set of levels, the quarter integrals of `|ψₙ|²` tend to `0` and those of `|ψₜ|²` to
    `∫ ½ cosh² s |g'(s)|² ds`, with `g = ψ̃ ∘ γ`. Dominated convergence in diagonal coordinates
    (`ee_quarter_bound`), with the line representatives continuous at `b = π/2` and the traces
    on the arc of `ee_arc_trace_identification`; the raw `ψₓ, ψ_y` agree with the
    representatives on almost every quarter orbit (`ae_quarterGraph_of_ae`). -/
theorem ee_quarter_traces {ω : L2} (hω : InSector true true ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      (∀ h ∈ Ioo (0 : ℝ) (1 / 4) \ N,
        IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
          (Ioo (-eighthPeriod h) (eighthPeriod h)) ∧
        IntegrableOn (fun t ↦ ‖streamTangent ω (dipoleOrbit h t)‖ ^ 2)
          (Ioo (-eighthPeriod h) (eighthPeriod h))) ∧
      Tendsto (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2) (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        ‖streamTangent ω (dipoleOrbit h t)‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∫ s, cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2)) := by
  have hπ := Real.pi_pos
  obtain ⟨Gx, hx⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 0)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨Gy, hy⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 1)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨hodd, -, harc⟩ := ee_arc_trace_identification hω hx hy
  obtain ⟨Φ, hΦm, hΦfin, hΦ⟩ := ee_quarter_bound hω hx hy
  set I : Set ℝ := Ioo (-π) π with hI
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  have hAI : A ⊆ I := Ioo_subset_Ioo (by linarith) (by linarith)
  set Q := diagRect I (Ioo 0 π) with hQ
  have hQm : MeasurableSet Q := measurableSet_diagRect measurableSet_Ioo measurableSet_Ioo
  have hJ2 : π / 2 ∈ Ioo 0 π := ⟨by positivity, by linarith⟩
  -- The raw derivatives agree with the representatives on almost every quarter orbit.
  have hP : ∀ᵐ p, p ∈ Q → Gx p = streamLiftX ω p ∧ Gy p = streamLiftY ω p := by
    have h1 := (ae_restrict_iff' hQm).1 hx.1
    have h2 := (ae_restrict_iff' hQm).1 hy.1
    filter_upwards [h1, h2] with p h1 h2 hp
    exact ⟨h1 hp, h2 hp⟩
  have hq := ae_quarterGraph_of_ae hP
  rw [ae_iff] at hq
  set N := {h : ℝ | ¬(h ∈ Ioo (0 : ℝ) 1 →
    ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
      diagInv (a, quarterHeight h a) ∈ Q →
        Gx (diagInv (a, quarterHeight h a)) = streamLiftX ω (diagInv (a, quarterHeight h a)) ∧
        Gy (diagInv (a, quarterHeight h a)) = streamLiftY ω (diagInv (a, quarterHeight h a)))}
    with hN
  have hinQ (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) (a : ℝ) (ha : a ∈ Ioo (-arccos √h) (arccos √h)) :
      diagInv (a, quarterHeight h a) ∈ Q := by
    have hc := sqrt_lt_cos_of_abs_lt_arccos hh (abs_lt.2 ⟨ha.1, ha.2⟩)
    have hc0 : 0 < cos a := (Real.sqrt_pos.2 hh.1).trans hc
    have hhc : h < cos a := by
      have : h ≤ √h := by
        have := Real.mul_self_sqrt hh.1.le
        nlinarith [Real.sqrt_nonneg h, hh.2]
      linarith
    have hah : arccos √h < π / 2 := Real.arccos_lt_pi_div_two.2 (Real.sqrt_pos.2 hh.1)
    refine mem_diagRect_diagInv.2 ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_, ?_⟩
    · exact Real.arccos_pos.2 ((div_lt_one hc0).2 hhc)
    · exact (Real.arccos_lt_pi_div_two.2 (div_pos hh.1 hc0)).trans (by linarith)
  have hrep (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1 \ N) :
      ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        Gx (diagInv (a, quarterHeight h a)) = streamLiftX ω (diagInv (a, quarterHeight h a)) ∧
        Gy (diagInv (a, quarterHeight h a)) = streamLiftY ω (diagInv (a, quarterHeight h a)) := by
    have h' := not_not.1 hh.2 hh.1
    filter_upwards [h', ae_restrict_mem measurableSet_Ioo] with a ha ham
    exact ha (hinQ h hh.1 a ham)
  -- Measurability of the raw integrands and continuity of the representatives at the arc.
  have hXm : Measurable (streamLiftX ω) := measurable_liftL2 _
  have hYm : Measurable (streamLiftY ω) := measurable_liftL2 _
  have hρm : Measurable fun p : ℝ × ℝ ↦ ((gradNorm p : ℝ) : ℂ) := by
    unfold gradNorm
    fun_prop
  have hnm : Measurable fun p ↦ ‖streamNormal ω p‖ ^ 2 := by
    unfold streamNormal normalDeriv
    fun_prop
  have htm : Measurable fun p ↦ ‖streamTangent ω p‖ ^ 2 := by
    unfold streamTangent tangentDeriv
    fun_prop
  have hcont : ∀ᵐ a ∂(volume.restrict A),
      ContinuousAt (fun b ↦ normalDeriv Gx Gy (diagInv (a, b))) (π / 2) ∧
        ContinuousAt (fun b ↦ tangentDeriv Gx Gy (diagInv (a, b))) (π / 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAI hx.ae_continuousOn,
      ae_restrict_of_ae_restrict_of_subset hAI hy.ae_continuousOn,
      ae_restrict_mem measurableSet_Ioo] with a h1 h2 ha
    have hc := cos_pos_of_mem_Ioo ha
    have hρ : gradNorm (diagInv (a, π / 2)) ≠ 0 := by
      rw [gradNorm, Real.sqrt_ne_zero']
      simp only [diagInv_apply, Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two, neg_sq]
      positivity
    exact continuousAt_line_normalDeriv (h1.continuousAt (isOpen_Ioo.mem_nhds hJ2))
      (h2.continuousAt (isOpen_Ioo.mem_nhds hJ2)) hρ
  have hsum (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4)) := hΦ h ⟨hh.1, by linarith [hh.2]⟩
  -- The normal derivative.
  obtain ⟨hni, hnt⟩ := tendsto_quarter_integral (F := fun p ↦ ‖normalDeriv Gx Gy p‖ ^ 2)
    hnm (fun p ↦ by positivity) hΦm hΦfin
    (fun h hh ↦ by
      filter_upwards [hsum h hh] with a ha
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ha (Or.inr hh.2.le))
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity))
        (Real.sqrt_nonneg _))
    (by filter_upwards [hcont] with a ha
        exact (continuous_norm.continuousAt.comp ha.1).pow 2)
    (fun h hh ↦ by
      filter_upwards [hrep h hh] with a ha
      simp only [streamNormal, normalDeriv, ha.1, ha.2])
  -- The tangential derivative.
  obtain ⟨hti, htt⟩ := tendsto_quarter_integral (F := fun p ↦ ‖tangentDeriv Gx Gy p‖ ^ 2)
    htm (fun p ↦ by positivity) hΦm hΦfin
    (fun h hh ↦ by
      filter_upwards [hsum h hh] with a ha
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ha (Or.inr hh.2.le))
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity))
        (Real.sqrt_nonneg _))
    (by filter_upwards [hcont] with a ha
        exact (continuous_norm.continuousAt.comp ha.2).pow 2)
    (fun h hh ↦ by
      filter_upwards [hrep h hh] with a ha
      simp only [streamTangent, tangentDeriv, ha.1, ha.2])
  refine ⟨N, hq, fun h hh ↦ ⟨hni h hh, hti h hh⟩, ?_, ?_⟩
  · convert hnt using 2
    refine (integral_eq_zero_of_ae ?_).symm
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAI hodd] with a ha
    simp only [Pi.zero_apply]
    rw [ha.2, norm_zero]
    simp
  · convert htt using 2
    calc ∫ s, cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2
        = ∫ s, ‖tangentDeriv Gx Gy (separatrixArc s)‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [harc] with s hs
          exact hs.2.symm
      _ = ∫ a in A, (1 / cos a) • ‖tangentDeriv Gx Gy (diagInv (a, π / 2))‖ ^ 2 :=
          integral_separatrixArc_eq (fun p ↦ ‖tangentDeriv Gx Gy p‖ ^ 2)
      _ = _ := by
          refine setIntegral_congr_fun measurableSet_Ioo fun a _ ↦ ?_
          simp only [smul_eq_mul]
          ring

/-- The level integral as four quarter integrals, assuming only integrability on each
    quarter orbit (`lem:quarter-orbit-decomposition`). -/
theorem levelIntegral_eq_sum_quarter' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (h0 : 0 < h) (h1 : h < 1) {f : ℝ × ℝ → E}
    (hf : ∀ k < 4, IntervalIntegrable (fun t ↦ f (rotLift^[k] (dipoleOrbit h t))) volume
      (-eighthPeriod h) (eighthPeriod h)) :
    levelIntegral h f = ∑ k ∈ Finset.range 4,
      ∫ t in (-eighthPeriod h)..eighthPeriod h, f (rotLift^[k] (dipoleOrbit h t)) := by
  set L := eighthPeriod h
  set φ : ℝ → E := fun t ↦ f (dipoleOrbit h t) with hφ
  have hper : Function.Periodic φ (orbitPeriod h) := fun t ↦
    congrArg f (dipoleOrbit_periodic h0 h1 t)
  set a : ℕ → ℝ := fun k ↦ -L + k * (2 * L) with ha
  have hshift (k : ℕ) (t : ℝ) : φ (t + k * (2 * L)) = f (rotLift^[k] (dipoleOrbit h t)) :=
    congrArg f (dipoleOrbit_add_mul_quarter h0 h1 k t)
  have hak : ∀ k, a k = -L + k * (2 * L) := fun k ↦ rfl
  have hak1 : ∀ k : ℕ, a (k + 1) = L + k * (2 * L) := fun k ↦ by simp only [ha]; push_cast; ring
  have hint : ∀ k < 4, IntervalIntegrable φ volume (a k) (a (k + 1)) := by
    intro k hk
    have := (hf k hk).comp_add_right (-(k * (2 * L)))
    rw [hak, hak1]
    convert this using 2
    all_goals first
      | ring1
      | (rw [← hshift]; congr 1; ring)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ) (a := a)
    (n := 4) fun k hk ↦ hint k hk
  have ha0 : a 0 = -L := by simp [ha]
  have ha4 : a 4 = -L + orbitPeriod h := by simp only [ha, orbitPeriod, L]; push_cast; ring
  have hend : ∫ x in (-L)..(-L + orbitPeriod h), φ x = ∫ x in (a 0)..(a 4), φ x := by
    rw [ha0, ha4]
  rw [levelIntegral, ← zero_add (orbitPeriod h), hper.intervalIntegral_add_eq 0 (-L), hend,
    ← hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk := intervalIntegral.integral_comp_add_right (f := φ) (a := -L) (b := L)
    (k * (2 * L))
  rw [hak, hak1, ← hk]
  congr 1
  funext t
  exact hshift k t

/-- Level traces at the separatrix (`lem:ee-level-traces`): for `ψ` even under both
    reflections, along levels `h → 0` outside a null set, `∮ |ψₙ|² dt → 0` and
    `∮ |ψₜ|² dt → ∑_k ∫ ½ cosh² s |g_k'(s)|² ds`. The level integral is four quarter integrals;
    the `k`-th quarter of `ω` is the `0`-th quarter of the rotated vorticity
    (`streamNormal_iterate_rotate_ae`, transferred to almost every level), so
    `ee_quarter_traces` applies to each. -/
theorem ee_level_traces {ω : L2} (hω : InSector true true ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamTangent ω p‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∑ k ∈ Finset.range 4,
          ∫ s, Real.cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2)) := by
  have hall := fun k ↦ ee_quarter_traces (inSector_iterate_rotate hω k)
  choose Nq hNq hint hn ht using hall
  have hrot := fun k ↦ ae_quarterGraph_of_ae (streamNormal_iterate_rotate_ae ω k)
  set M : ℕ → Set ℝ := fun k ↦ {h | ¬(h ∈ Ioo (0 : ℝ) 1 →
    ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
      streamNormal (rotate^[k] ω) (diagInv (a, quarterHeight h a)) =
          streamNormal ω (rotLift^[k] (diagInv (a, quarterHeight h a))) ∧
        streamTangent (rotate^[k] ω) (diagInv (a, quarterHeight h a)) =
          streamTangent ω (rotLift^[k] (diagInv (a, quarterHeight h a))))} with hM
  have hM0 (k : ℕ) : volume (M k) = 0 := ae_iff.1 (hrot k)
  set N : Set ℝ := ⋃ k, (Nq k ∪ M k) with hNdef
  have hN0 : volume N = 0 := measure_iUnion_null fun k ↦ measure_union_null (hNq k) (hM0 k)
  refine ⟨N, hN0, ?_⟩
  -- On a good level, the `k`-th quarter of `ω` is the `0`-th quarter of `ω_k`.
  have hgood (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1 \ N) (k : ℕ) :
      ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        streamNormal (rotate^[k] ω) (diagInv (a, quarterHeight h a)) =
            streamNormal ω (rotLift^[k] (diagInv (a, quarterHeight h a))) ∧
          streamTangent (rotate^[k] ω) (diagInv (a, quarterHeight h a)) =
            streamTangent ω (rotLift^[k] (diagInv (a, quarterHeight h a))) := by
    have hk : h ∉ M k := fun hm ↦ hh.2 (mem_iUnion.2 ⟨k, Or.inr hm⟩)
    exact not_not.1 hk hh.1
  have hgoodq (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1 \ N) (k : ℕ) : h ∈ Ioo (0 : ℝ) 1 \ Nq k :=
    ⟨hh.1, fun hm ↦ hh.2 (mem_iUnion.2 ⟨k, Or.inl hm⟩)⟩
  have hrotint (G : (ℝ × ℝ → ℂ)) (Gk : ℝ × ℝ → ℂ) (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) (k : ℕ)
      (hG : ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        Gk (diagInv (a, quarterHeight h a)) = G (rotLift^[k] (diagInv (a, quarterHeight h a)))) :
      (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖G (rotLift^[k] (dipoleOrbit h t))‖ ^ 2 =
        ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖Gk (dipoleOrbit h t)‖ ^ 2) ∧
      (IntegrableOn (fun t ↦ ‖Gk (dipoleOrbit h t)‖ ^ 2) (Ioo (-eighthPeriod h) (eighthPeriod h)) →
        IntegrableOn (fun t ↦ ‖G (rotLift^[k] (dipoleOrbit h t))‖ ^ 2)
          (Ioo (-eighthPeriod h) (eighthPeriod h))) := by
    have hae : (fun a ↦ (1 / √(cos a ^ 2 - h ^ 2)) •
          ‖G (rotLift^[k] (diagInv (a, quarterHeight h a)))‖ ^ 2) =ᵐ[volume.restrict
            (Ioo (-arccos √h) (arccos √h))]
        fun a ↦ (1 / √(cos a ^ 2 - h ^ 2)) • ‖Gk (diagInv (a, quarterHeight h a))‖ ^ 2 := by
      filter_upwards [hG] with a ha
      rw [ha]
    constructor
    · rw [integral_quarter_eq hh0 hh1 (fun p ↦ ‖G (rotLift^[k] p)‖ ^ 2),
        integral_quarter_eq hh0 hh1 (fun p ↦ ‖Gk p‖ ^ 2)]
      exact integral_congr_ae hae
    · intro hi
      rw [integrableOn_quarter_iff hh0 hh1 (fun p ↦ ‖Gk p‖ ^ 2)] at hi
      rw [integrableOn_quarter_iff hh0 hh1 (fun p ↦ ‖G (rotLift^[k] p)‖ ^ 2)]
      exact hi.congr hae.symm
  -- The level integral as a sum of quarter integrals of the rotated vorticities.
  have hlevel (G : ℕ → ℝ × ℝ → ℂ) (G0 : ℝ × ℝ → ℂ) (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1)
      (hG : ∀ k < 4, ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        G k (diagInv (a, quarterHeight h a)) = G0 (rotLift^[k] (diagInv (a, quarterHeight h a))))
      (hGi : ∀ k < 4, IntegrableOn (fun t ↦ ‖G k (dipoleOrbit h t)‖ ^ 2)
        (Ioo (-eighthPeriod h) (eighthPeriod h))) :
      levelIntegral h (fun p ↦ ‖G0 p‖ ^ 2) = ∑ k ∈ Finset.range 4,
        ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖G k (dipoleOrbit h t)‖ ^ 2 := by
    have hL := (eighthPeriod_pos hh0 hh1).le
    rw [levelIntegral_eq_sum_quarter' hh0 hh1 fun k hk ↦
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2
        ((hrotint G0 (G k) h hh0 hh1 k (hG k hk)).2 (hGi k hk))]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact (hrotint G0 (G k) h hh0 hh1 k (hG k (Finset.mem_range.1 hk))).1
  have hev : ∀ᶠ h in 𝓝[Ioi 0 \ N] (0 : ℝ), h ∈ Ioo (0 : ℝ) (1 / 4) \ N := by
    have h1 : ∀ᶠ h in 𝓝[Ioi 0 \ N] (0 : ℝ), h < 1 / 4 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [h1, self_mem_nhdsWithin] with h h1 h2
    exact ⟨⟨h2.1, h1⟩, h2.2⟩
  have hmono (k : ℕ) : 𝓝[Ioi 0 \ N] (0 : ℝ) ≤ 𝓝[Ioi 0 \ Nq k] 0 :=
    nhdsWithin_mono _ fun h hh ↦ ⟨hh.1, fun hm ↦ hh.2 (mem_iUnion.2 ⟨k, Or.inl hm⟩)⟩
  have hgood14 (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4) \ N) : h ∈ Ioo (0 : ℝ) 1 \ N :=
    ⟨⟨hh.1.1, by linarith [hh.1.2]⟩, hh.2⟩
  have hqk (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (1 / 4) \ N) (k : ℕ) : h ∈ Ioo (0 : ℝ) (1 / 4) \ Nq k :=
    ⟨hh.1, fun hm ↦ hh.2 (mem_iUnion.2 ⟨k, Or.inl hm⟩)⟩
  constructor
  · have hs := tendsto_finsetSum (Finset.range 4) fun k _ ↦ (hn k).mono_left (hmono k)
    simp only [Finset.sum_const_zero] at hs
    refine hs.congr' ?_
    filter_upwards [hev] with h hh
    exact (hlevel (fun k ↦ streamNormal (rotate^[k] ω)) (streamNormal ω) h hh.1.1
      (by linarith [hh.1.2]) (fun k _ ↦ by
        filter_upwards [hgood h (hgood14 h hh) k] with a ha
        exact ha.1)
      (fun k _ ↦ (hint k h (hqk h hh k)).1)).symm
  · have hs := tendsto_finsetSum (Finset.range 4) fun k _ ↦ (ht k).mono_left (hmono k)
    have htarget : ∀ k, (fun s ↦ deriv (contStream (rotate^[k] ω) ∘ separatrixArc) s) =
        fun s ↦ deriv (contStream ω ∘ cellArc k) s := by
      intro k
      have hcomp : contStream ω ∘ cellArc k = contStream (rotate^[k] ω) ∘ separatrixArc := by
        funext s
        simp only [Function.comp_apply, cellArc, contStream_iterate_rotate]
      rw [hcomp]
    simp only [htarget] at hs
    refine hs.congr' ?_
    filter_upwards [hev] with h hh
    exact (hlevel (fun k ↦ streamTangent (rotate^[k] ω)) (streamTangent ω) h hh.1.1
      (by linarith [hh.1.2]) (fun k _ ↦ by
        filter_upwards [hgood h (hgood14 h hh) k] with a ha
        exact ha.2)
      (fun k _ ↦ (hint k h (hqk h hh k)).2)).symm

end EulerDipoleEigenvalues
