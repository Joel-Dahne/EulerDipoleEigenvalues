module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ACLSlicing
public import NoEmbeddedEigenvalues.Transport.WeightedGains.LogarithmicDivision
public import NoEmbeddedEigenvalues.Transport.WeightedGains.WeightedNumeratorData

/-!
# Summation of recentered quarter reconstructions

The signed interval from the midpoint is handled before summation: negative
and positive times use the same quantitative subinterval estimate. A square
bound on each fiber is integrable over the moving strip when its product
with the logarithmic level weight is integrable. A fiber-integral criterion
also sums the forcing-level derivative directly from the supplied weighted jet
mass and the geometric level-vector bound.

Blueprint: `lem:quarter-fiber-summation`, `lem:quarter-strip-summation`,
`lem:quarter-forcing-level-gain`, `lem:quarter-reconstruction-level-gain`.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Measurability of the moving quarter strip, including its strict time endpoints. -/
theorem measurableSet_quarterOrbitStrip (b : ℝ) : MeasurableSet (quarterOrbitStrip b) := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt (measurable_eighthPeriod.comp measurable_fst).neg measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_eighthPeriod.comp measurable_fst))))

/-- Joint a.e. strong measurability gives measurable sections on almost every
moving time interval. -/
theorem aestronglyMeasurable_quarterStrip_sections {b : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b))) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      AEStronglyMeasurable (fun t ↦ F (h, t))
        (volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))) := by
  have hm := (aestronglyMeasurable_indicator_iff (measurableSet_quarterOrbitStrip b)).2 hF
  have hmp : AEStronglyMeasurable ((quarterOrbitStrip b).indicator F)
      ((volume : Measure ℝ).prod volume) := by rwa [← Measure.volume_eq_prod]
  filter_upwards [ae_restrict_of_ae hmp.prodMk_left, ae_restrict_mem measurableSet_Ioo]
    with h hh hhI
  apply (aestronglyMeasurable_indicator_iff measurableSet_Ioo).1
  convert hh using 1
  funext t
  simp only [quarterOrbitStrip, mem_ofPred_eq, hhI.1, hhI.2, true_and, mem_Ioo,
    indicator_apply]

/-- Integrable bounds on actual fiber square integrals control joint strip L².
No measurability of a dominating density is needed beyond that of its mass. -/
theorem memLp_quarterStrip_of_integral_bound {b : ℝ} {F : ℝ × ℝ → ℂ} {B : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b)))
    (hB : IntegrableOn B (Ioo 0 b))
    (hfiber : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      IntegrableOn (fun t ↦ ‖F (h, t)‖ ^ 2) (Ioo (-eighthPeriod h) (eighthPeriod h)) ∧
        (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖F (h, t)‖ ^ 2) ≤ B h) :
    MemLp F 2 (volume.restrict (quarterOrbitStrip b)) := by
  let S := quarterOrbitStrip b
  let f : ℝ × ℝ → ℝ := S.indicator (fun q ↦ ‖F q‖ ^ 2)
  have hfpos : ∀ q, 0 ≤ f q := indicator_nonneg (fun _ _ ↦ sq_nonneg _)
  have hm : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)) :=
    (aestronglyMeasurable_indicator_iff (measurableSet_quarterOrbitStrip b)).2 (hF.norm.pow 2)
  have hmp : AEStronglyMeasurable f ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hs : ∀ᵐ h : ℝ, Integrable (fun t ↦ f (h, t)) ∧
      (∫ t, ‖f (h, t)‖) ≤ (Ioo 0 b).indicator B h := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hfiber] with h hh
    by_cases hhI : h ∈ Ioo 0 b
    · have heq : (fun t ↦ f (h, t)) =
          (Ioo (-eighthPeriod h) (eighthPeriod h)).indicator (fun t ↦ ‖F (h, t)‖ ^ 2) := by
        funext t
        simp only [f, S, quarterOrbitStrip, mem_ofPred_eq, hhI.1, hhI.2, true_and,
          mem_Ioo, indicator_apply]
      refine ⟨by rw [heq]; exact (hh hhI).1.integrable_indicator measurableSet_Ioo, ?_⟩
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hfpos _)]
      rw [heq, integral_indicator measurableSet_Ioo, indicator_of_mem hhI]
      exact (hh hhI).2
    · have hz : (fun t ↦ f (h, t)) = 0 := by
        funext t
        exact indicator_of_notMem (by intro ht; exact hhI ⟨ht.1, ht.2.1⟩) _
      refine ⟨by rw [hz]; exact integrable_zero _ _ _, ?_⟩
      simp_rw [congrFun hz]
      simp [hhI]
  have hI : Integrable (fun h ↦ ∫ t, ‖f (h, t)‖) :=
    ((integrable_indicator_iff measurableSet_Ioo).2 hB).mono'
      hmp.norm.integral_prod_right' (by
        filter_upwards [hs] with h hh
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t ↦ norm_nonneg (f (h, t)))]
        exact hh.2)
  have hi : Integrable f ((volume : Measure ℝ).prod volume) :=
    (integrable_prod_iff hmp).2 ⟨hs.mono fun _ hh ↦ hh.1, hI⟩
  rw [← Measure.volume_eq_prod] at hi
  exact (memLp_two_iff_integrable_sq_norm hF).2
    ((integrable_indicator_iff (measurableSet_quarterOrbitStrip b)).1 hi)

/-- A logarithmically integrable fiber square bound controls the full moving-strip
L² norm. Both the function and the square bound may be specified only a.e. -/
theorem memLp_quarterStrip_of_sq_bound {b C : ℝ} (hb : b < 1)
    {F : ℝ × ℝ → ℂ} {B : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b)))
    (hB : IntegrableOn (fun h ↦ logLevelWeight h * B h) (Ioo 0 b))
    (hBpos : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), 0 ≤ B h)
    (hL : ∀ h ∈ Ioo 0 b, 2 * eighthPeriod h ≤ C * logLevelWeight h)
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
        ‖F (h, t)‖ ^ 2 ≤ B h) :
    MemLp F 2 (volume.restrict (quarterOrbitStrip b)) := by
  apply memLp_quarterStrip_of_integral_bound hF (hB.const_mul C)
  filter_upwards [aestronglyMeasurable_quarterStrip_sections hF, hBpos, hbound,
    ae_restrict_mem measurableSet_Ioo] with h hm hBh hbh hh
  have hi : IntegrableOn (fun t ↦ ‖F (h, t)‖ ^ 2)
      (Ioo (-eighthPeriod h) (eighthPeriod h)) :=
    (integrable_const (B h)).mono' (hm.norm.pow 2) (by
      filter_upwards [hbh] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact ht)
  refine ⟨hi, ?_⟩
  calc
    (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖F (h, t)‖ ^ 2) ≤
        ∫ _ in Ioo (-eighthPeriod h) (eighthPeriod h), B h :=
      integral_mono_ae hi (integrable_const _) hbh
    _ = (2 * eighthPeriod h) * B h := by
      have hpos := eighthPeriod_pos hh.1 (hh.2.trans hb)
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ eighthPeriod h - -eighthPeriod h)]
      simp only [smul_eq_mul]
      ring
    _ ≤ C * (logLevelWeight h * B h) :=
      (mul_le_mul_of_nonneg_right (hL h hh) hBh).trans_eq (by ring)
/-- The signed Volterra primitive preserves a.e. strong measurability on the
moving strip. Values of the integrand outside that strip do not matter. -/
theorem aestronglyMeasurable_quarterPrimitive {b : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b))) :
    AEStronglyMeasurable (fun q : ℝ × ℝ ↦ ∫ t in 0..q.2, F (q.1, t))
      (volume.restrict (quarterOrbitStrip b)) := by
  let S := quarterOrbitStrip b
  have hm : AEStronglyMeasurable (S.indicator F) (volume : Measure (ℝ × ℝ)) :=
    (aestronglyMeasurable_indicator_iff (measurableSet_quarterOrbitStrip b)).2 hF
  let G := hm.mk (S.indicator F)
  have hG : Measurable G := hm.stronglyMeasurable_mk.measurable
  have heq : S.indicator F =ᵐ[(volume : Measure ℝ).prod volume] G := by
    simpa only [Measure.volume_eq_prod] using hm.ae_eq_mk
  have hp := (ACLSlicing.measurable_sectionPrimitive hG 0).aestronglyMeasurable
    (μ := volume.restrict S)
  apply hp.congr
  have hgood : ∀ᵐ q : ℝ × ℝ, ∀ᵐ t : ℝ,
      S.indicator F (q.1, t) = G (q.1, t) := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ae_of_ae_prod heq)
  filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem (measurableSet_quarterOrbitStrip b)]
    with q hq hqS
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hq] with t ht htI
  have htS : (q.1, t) ∈ S := by
    have hz : -eighthPeriod q.1 < 0 ∧ 0 < eighthPeriod q.1 := by
      constructor <;> linarith [hqS.2.2.1, hqS.2.2.2]
    have htcc := uIoc_subset_uIcc htI
    have htlo := (min_le_iff.mp htcc.1)
    have hthi := (le_max_iff.mp htcc.2)
    exact ⟨hqS.1, hqS.2.1, by rcases htlo with ht | ht <;> linarith [hqS.2.2.1],
      by rcases hthi with ht | ht <;> linarith [hqS.2.2.2]⟩
  simpa only [indicator_of_mem htS] using ht.symm

/-- Specified level derivative of a midpoint variation-of-constants expression.
This is a definition; identifying it as a weak derivative is a separate obligation. -/
def quarterReconstructionLevel (lam : ℝ) (A₁ : ℝ → ℂ) (G : ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)) *
    (A₁ q.1 + Complex.I * ∫ t in 0..q.2,
      G (q.1, t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)))

/-- Factoring the time phase agrees with the unfactored variation-of-constants
formula, including signed intervals and totalized integrals. -/
theorem quarterReconstructionLevel_eq (lam : ℝ) (A₁ : ℝ → ℂ) (G : ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) :
    quarterReconstructionLevel lam A₁ G q =
      Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)) * A₁ q.1 +
        Complex.I * ∫ u in 0..q.2,
          Complex.exp (Complex.I * ((lam * (q.2 - u) : ℝ) : ℂ)) * G (q.1, u) := by
  have hconv : Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ)) *
      (∫ u in 0..q.2, G (q.1, u) * Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))) =
      ∫ u in 0..q.2,
        Complex.exp (Complex.I * ((lam * (q.2 - u) : ℝ) : ℂ)) * G (q.1, u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [mul_comm (G (q.1, u)), ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← hconv]
  dsimp [quarterReconstructionLevel]
  ring

/-- One common good-level set controls both orientations of the midpoint interval. -/
theorem WeightedQuarterNumeratorData.midpoint_integral_bound
    {lam h₀ : ℝ} {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D h₀) (hh₀ : h₀ < 1) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖∫ u in 0..t, quarterForcingLevelDerivative D (h, u) *
        Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))‖ ^ 2 ≤
          d.bound * quarterJetEnergy 1 (3 / 2) D h := by
  filter_upwards [d.subinterval_bound, ae_restrict_mem measurableSet_Ioo] with h hh hI
  intro t ht
  have hL := (eighthPeriod_pos hI.1 (hI.2.trans hh₀)).le
  by_cases hpos : 0 ≤ t
  · exact hh 0 t (by linarith) hpos ht.2
  · rw [intervalIntegral.integral_symm, norm_neg]
    exact hh t 0 ht.1 (le_of_not_ge hpos) hL

/-- The midpoint integrals are genuine signed Bochner integrals on a common
full-measure set of levels, not merely bounded totalized expressions. -/
theorem WeightedQuarterNumeratorData.midpoint_intervalIntegrable
    {lam h₀ : ℝ} {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D h₀) (hh₀ : h₀ < 1) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∀ t ∈ Ioo (-eighthPeriod h) (eighthPeriod h),
      IntervalIntegrable (fun u ↦ quarterForcingLevelDerivative D (h, u) *
        Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))) volume 0 t := by
  filter_upwards [d.fibers_integrable, ae_restrict_mem measurableSet_Ioo] with h hh hI
  intro t ht
  have hL := eighthPeriod_pos hI.1 (hI.2.trans hh₀)
  have hsub : uIcc 0 t ⊆ Ioo (-eighthPeriod h) (eighthPeriod h) := by
    intro u hu
    rcases mem_uIcc.mp hu with hu | hu
    · exact ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
    · exact ⟨ht.1.trans_le hu.1, by linarith [hu.2]⟩
  exact (hh.2.2.2.mono_set hsub).intervalIntegrable.mul_continuousOn (by fun_prop)

/-- A level function that is measurable a.e. lifts to a measurable function on
the moving strip; the first projection is not used as a measure-preserving map. -/
theorem aestronglyMeasurable_level_quarterStrip {b : ℝ} {A : ℝ → ℂ}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 b))) :
    AEStronglyMeasurable (fun q : ℝ × ℝ ↦ A q.1)
      (volume.restrict (quarterOrbitStrip b)) := by
  have hm : AEStronglyMeasurable ((Ioo 0 b).indicator A) (volume : Measure ℝ) :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2 hA
  have hp : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ (Ioo 0 b).indicator A q.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hm.comp_fst
  apply hp.restrict.congr
  filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
  exact indicator_of_mem (show q.1 ∈ Ioo 0 b from ⟨hq.1, hq.2.1⟩) _

/-- Logarithmic control of the midpoint derivative and the specified fiber energy
gives L² for the joint level-reconstruction expression, independently of any
weak-derivative identity for the transported function. -/
theorem WeightedQuarterNumeratorData.reconstruction_level_memLp
    {lam h₀ b : ℝ} {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D h₀)
    (hh₀ : h₀ < 1 / 2) (hb : b ≤ h₀) {A₁ : ℝ → ℂ}
    (hA : MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * A₁ h) 2
      (volume.restrict (Ioo 0 b)))
    (hK : IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 (3 / 2) D h)
      (Ioo 0 b)) :
    MemLp (quarterReconstructionLevel lam A₁ (quarterForcingLevelDerivative D)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  have hb1 : b < 1 := by linarith
  have hlog : ∀ h ∈ Ioo 0 b, 0 < logLevelWeight h := by
    intro h hh
    have := Real.log_nonneg ((one_le_div hh.1).2 (hh.2.trans hb1).le)
    dsimp [logLevelWeight]
    linarith
  have hAm : AEStronglyMeasurable A₁ (volume.restrict (Ioo 0 b)) := by
    have hm := hA.aestronglyMeasurable.div₀
      (show AEStronglyMeasurable (fun h : ℝ ↦ (Real.sqrt (logLevelWeight h) : ℂ))
        (volume.restrict (Ioo 0 b)) from (by
          have : Measurable (fun h : ℝ ↦ (Real.sqrt (logLevelWeight h) : ℂ)) := by
            unfold logLevelWeight
            fun_prop
          exact this.aestronglyMeasurable))
    apply hm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hlog h hh)).ne')
  have hAenergy : IntegrableOn (fun h ↦ logLevelWeight h * ‖A₁ h‖ ^ 2) (Ioo 0 b) := by
    apply (hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hlog h hh).le]
  have hsub : quarterOrbitStrip b ⊆ quarterOrbitStrip h₀ := fun q hq ↦
    ⟨hq.1, hq.2.1.trans_le hb, hq.2.2⟩
  have hG := (d.forcing_level_weak.mono hsub).2.1.aestronglyMeasurable
  have hphase : Measurable (fun q : ℝ × ℝ ↦
      Complex.exp (-Complex.I * ((lam * q.2 : ℝ) : ℂ))) := by fun_prop
  have hP := aestronglyMeasurable_quarterPrimitive (hG.mul hphase.aestronglyMeasurable)
  have hR : AEStronglyMeasurable
      (quarterReconstructionLevel lam A₁ (quarterForcingLevelDerivative D))
      (volume.restrict (quarterOrbitStrip b)) := by
    exact (show AEStronglyMeasurable (fun q : ℝ × ℝ ↦
      Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ))) _ from (by fun_prop)).mul
      ((aestronglyMeasurable_level_quarterStrip hAm).add (hP.const_mul Complex.I))
  have hKpos (h : ℝ) : 0 ≤ quarterJetEnergy 1 (3 / 2) D h :=
    integral_nonneg fun t ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  let B : ℝ → ℝ := fun h ↦ 2 * ‖A₁ h‖ ^ 2 + 2 * d.bound * quarterJetEnergy 1 (3 / 2) D h
  apply memLp_quarterStrip_of_sq_bound (C := 4) (B := B) hb1 hR
  · apply ((hAenergy.const_mul 2).add (hK.const_mul (2 * d.bound))).congr
    exact Filter.Eventually.of_forall fun h ↦ by dsimp [B]; ring
  · exact Filter.Eventually.of_forall fun h ↦ by
      have := d.bound_pos
      have := hKpos h
      dsimp [B]
      positivity
  · intro h hh
    have hL := (eighthPeriod_sub_log_bounds hh.1 ((hh.2.trans_le hb).trans hh₀)).2
    have hl := Real.log_nonneg ((one_le_div hh.1).2 (hh.2.trans hb1).le)
    dsimp [logLevelWeight]
    linarith
  · have hsubI : Ioo 0 b ⊆ Ioo 0 h₀ := fun _ hh ↦ ⟨hh.1, hh.2.trans_le hb⟩
    have hbound := (d.midpoint_integral_bound (by linarith : h₀ < 1)).filter_mono
      (ae_mono (Measure.restrict_mono hsubI le_rfl))
    filter_upwards [hbound] with h hh
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hint := hh t (Ioo_subset_Icc_self ht)
    have he : ‖Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    dsimp [quarterReconstructionLevel, B]
    rw [norm_mul, he, one_mul]
    have hn := norm_add_le (A₁ h) (Complex.I * ∫ u in 0..t,
      quarterForcingLevelDerivative D (h, u) *
        Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ)))
    simp only [norm_mul, Complex.norm_I, one_mul] at hn
    have hsq := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hn
    nlinarith [sq_nonneg (‖A₁ h‖ - ‖∫ u in 0..t,
      quarterForcingLevelDerivative D (h, u) *
        Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))‖)]

/-- The first-order jet density has exactly the two coordinate components. -/
theorem quarterJetDensity_one (s : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    quarterJetDensity 1 s D q =
      ‖D [0] (dipoleOrbit q.1 q.2) / (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2 +
      ‖D [1] (dipoleOrbit q.1 q.2) / (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2 := by
  unfold quarterJetDensity
  calc
    _ = ∑ j : Fin 2, ‖D [j] (dipoleOrbit q.1 q.2) /
        (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2 :=
      Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ (fun w ↦ by
        have hw : List.ofFn w = [w 0] := by simp [List.ofFn_succ]
        simp only [hw]
        rfl)
    _ = _ := Fin.sum_univ_two _

/-- Contracting the orbit-level vector against the forcing gradient costs one
power of saddle distance in the squared weighted-jet density. -/
theorem quarterForcingLevelDerivative_sq_le_density
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hr : 0 < saddleDist (dipoleOrbit q.1 q.2))
    (hV : ‖deriv (fun h ↦ dipoleOrbit h q.2) q.1‖ ≤
      C / saddleDist (dipoleOrbit q.1 q.2)) :
    ‖quarterForcingLevelDerivative D q‖ ^ 2 ≤
      2 * C ^ 2 * saddleDist (dipoleOrbit q.1 q.2) * quarterJetDensity 1 (3 / 2) D q := by
  let r := saddleDist (dipoleOrbit q.1 q.2)
  let V := deriv (fun h ↦ dipoleOrbit h q.2) q.1
  let z₀ := D [0] (dipoleOrbit q.1 q.2)
  let z₁ := D [1] (dipoleOrbit q.1 q.2)
  have hp : 0 < Real.rpow r (3 / 2) := Real.rpow_pos_of_pos hr _
  have hp2 : (Real.rpow r (3 / 2)) ^ 2 = r ^ 3 := by
    change (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (show 0 ≤ r from hr.le)]
    norm_num
  have hn : ‖quarterForcingLevelDerivative D q‖ ≤ C / r * (‖z₀‖ + ‖z₁‖) := by
    calc
      _ ≤ ‖(V.1 : ℂ) * z₀‖ + ‖(V.2 : ℂ) * z₁‖ := norm_add_le _ _
      _ ≤ C / r * ‖z₀‖ + C / r * ‖z₁‖ := by
        simp only [norm_mul, Complex.norm_real]
        exact add_le_add
          (mul_le_mul_of_nonneg_right ((norm_fst_le V).trans hV) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right ((norm_snd_le V).trans hV) (norm_nonneg _))
      _ = _ := by ring
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  rw [quarterJetDensity_one]
  change ‖quarterForcingLevelDerivative D q‖ ^ 2 ≤
    2 * C ^ 2 * r * (‖z₀ / (Real.rpow r (3 / 2) : ℂ)‖ ^ 2 +
      ‖z₁ / (Real.rpow r (3 / 2) : ℂ)‖ ^ 2)
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, div_pow, hp2]
  have heq : 2 * C ^ 2 * r * (‖z₀‖ ^ 2 / r ^ 3 + ‖z₁‖ ^ 2 / r ^ 3) =
      (C / r) ^ 2 * (2 * (‖z₀‖ ^ 2 + ‖z₁‖ ^ 2)) := by
    field_simp
  rw [heq]
  calc
    _ ≤ (C / r * (‖z₀‖ + ‖z₁‖)) ^ 2 := hsq
    _ = (C / r) ^ 2 * (‖z₀‖ + ‖z₁‖) ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖z₀‖ - ‖z₁‖)])
      (sq_nonneg _)

/-- The supplied fiber masses and the orbit-level vector estimate give L² of
the forcing-level derivative on every sufficiently small quarter strip. -/
theorem WeightedQuarterNumeratorData.forcing_level_memLp
    {lam h₀ : ℝ} {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D h₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ b : ℝ, b ≤ h₀ → b ≤ δ →
      MemLp (quarterForcingLevelDerivative D) 2 (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨C, η, hη, hη1, hV⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨c, M, ρ, hc, hρ, hd⟩ := saddleDist_dipoleOrbit
  let δ := min η ρ
  refine ⟨δ, lt_min hη hρ, (min_le_left _ _).trans_lt hη1, ?_⟩
  intro b hb hδ
  have hsub : Ioo 0 b ⊆ Ioo 0 h₀ := fun _ hh ↦ ⟨hh.1, hh.2.trans_le hb⟩
  have hsubS : quarterOrbitStrip b ⊆ quarterOrbitStrip h₀ := fun _ hq ↦
    ⟨hq.1, hq.2.1.trans_le hb, hq.2.2⟩
  have hG := (d.forcing_level_weak.mono hsubS).2.1.aestronglyMeasurable
  let K := 2 * |C| ^ 2 * |M|
  have hbound : ∀ q ∈ quarterOrbitStrip b,
      ‖quarterForcingLevelDerivative D q‖ ^ 2 ≤ K * quarterJetDensity 1 (3 / 2) D q := by
    intro q hq
    have hhη : q.1 ∈ Ioo 0 η :=
      ⟨hq.1, hq.2.1.trans_le (hδ.trans (min_le_left _ _))⟩
    have hhρ : q.1 ∈ Ioo 0 ρ :=
      ⟨hq.1, hq.2.1.trans_le (hδ.trans (min_le_right _ _))⟩
    have ht : |q.2| ≤ eighthPeriod q.1 := abs_le.mpr ⟨hq.2.2.1.le, hq.2.2.2.le⟩
    obtain ⟨hdlo, hdhi⟩ := hd q.1 hhρ q.2 ht
    have hpos : 0 < saddleDist (dipoleOrbit q.1 q.2) :=
      (mul_pos hc (Real.exp_pos _)).trans_le hdlo
    have hdM : saddleDist (dipoleOrbit q.1 q.2) ≤ |M| := calc
      _ ≤ M * Real.exp (-|q.2|) := hdhi
      _ ≤ |M| * Real.exp (-|q.2|) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
      _ ≤ |M| := mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _)))
    have hv := (hV q.1 hhη q.2 ht).1.trans
      (div_le_div_of_nonneg_right (le_abs_self C) hpos.le)
    have hden : 0 ≤ quarterJetDensity 1 (3 / 2) D q :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    exact (quarterForcingLevelDerivative_sq_le_density D q (abs_nonneg C) hpos hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdM (by positivity : 0 ≤ 2 * |C| ^ 2)) hden)
  apply memLp_quarterStrip_of_integral_bound hG
    ((d.mass_integrable.1.mono_set hsub).const_mul K)
  have hfiber := d.fibers_integrable.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hfiber, aestronglyMeasurable_quarterStrip_sections hG,
    ae_restrict_mem measurableSet_Ioo] with h hh hm hhI
  have hle : ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
      ‖quarterForcingLevelDerivative D (h, t)‖ ^ 2 ≤ K * quarterJetDensity 1 (3 / 2) D (h, t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hbound (h, t) ⟨hhI.1, hhI.2, ht⟩
  have hdom := hh.1.const_mul K
  have hi := hdom.mono' (hm.norm.pow 2) (by
    filter_upwards [hle] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ht)
  refine ⟨hi, ?_⟩
  exact (integral_mono_ae hi hdom hle).trans_eq (integral_const_mul _ _)

end NoEmbeddedEigenvalues
