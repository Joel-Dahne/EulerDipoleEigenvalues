import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.SobolevLocal
import NoEmbeddedEigenvalues.SegmentEstimates
import NoEmbeddedEigenvalues.QuarterOrbits

/-!
# Traces of the stream function at the separatrix

Blueprint: `lem:arc-trace-identification`, `lem:ee-arc-energy` (stated), `lem:ee-corner-tails`.

Near the arc `b = π/2` the first derivatives `ψₓ, ψ_y` are handled through representatives that
are locally absolutely continuous on almost every line `a = const` (`IsLineRep`, provided by
`lem:traces`). Any two such representatives agree on almost every whole line, so their values on
`b = π/2` are well defined almost everywhere. Since `ψ` is even under the reflection
`b ↦ π - b`, `ψ_b = ψₓ - ψ_y` vanishes there, and `ψ_a = ψₓ + ψ_y` is the derivative of the trace
of `ψ̃`.

The corner tails use that `ψₙ, ψₜ` are the components of `∇ψ` in an orthonormal frame, so
`|ψₙ|² + |ψₜ|² = |ψₓ|² + |ψ_y|²`, and the segment estimate in diagonal coordinates: on the quarter
orbit `π/2 - β_h(a) ≤ (π/2) h / cos a` and `h ≤ cos² a`, so the segment length times the weight
`1 / cos a` is at most `π/2`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ### Representatives on lines in diagonal coordinates -/

theorem measurable_liftL2 (g : L2) : Measurable (liftL2 g) :=
  (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable

theorem continuous_diagCoord : Continuous diagCoord := by unfold diagCoord; fun_prop

theorem isOpen_diagRect {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J) : IsOpen (diagRect I J) :=
  (hI.preimage (continuous_fst.comp continuous_diagCoord)).inter
    (hJ.preimage (continuous_snd.comp continuous_diagCoord))

theorem measurableSet_diagRect {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    MeasurableSet (diagRect I J) :=
  (hI.preimage (continuous_fst.comp continuous_diagCoord).measurable).inter
    (hJ.preimage (continuous_snd.comp continuous_diagCoord).measurable)

theorem mem_diagRect_diagInv {I J : Set ℝ} {q : ℝ × ℝ} :
    diagInv q ∈ diagRect I J ↔ q ∈ I ×ˢ J := by
  simp only [diagRect, mem_ofPred_eq, diagCoord_diagInv, mem_prod]

theorem isBounded_diagRect {I J : Set ℝ} (hI : Bornology.IsBounded I)
    (hJ : Bornology.IsBounded J) : Bornology.IsBounded (diagRect I J) := by
  have h : diagRect I J = diagInv '' (I ×ˢ J) := by
    ext p
    constructor
    · intro hp
      exact ⟨diagCoord p, mem_diagRect_diagInv.1 (by rwa [diagInv_diagCoord]),
        diagInv_diagCoord p⟩
    · rintro ⟨q, hq, rfl⟩
      exact mem_diagRect_diagInv.2 hq
  rw [h]
  exact (diagInv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).lipschitzWith.isBounded_image (hI.prod hJ)

/-- `dx dy = 2 da db` for nonnegative functions: `∫⁻ F ∘ diagInv = ½ ∫⁻ F`. -/
theorem lintegral_comp_diagInv (F : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ q, F (diagInv q) = ENNReal.ofReal (1 / 2) * ∫⁻ p, F p := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hmap : Measure.map (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) volume =
      ENNReal.ofReal |(LinearMap.det (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_diagInvLinear]; norm_num)
  have key : ∫⁻ q, F (diagInv q) =
      ∫⁻ y, F y ∂Measure.map (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) volume :=
    (diagInv.toHomeomorph.measurableEmbedding.lintegral_map F).symm
  rw [key, hmap, lintegral_smul_measure, det_diagInvLinear, smul_eq_mul]
  norm_num

/-- Almost-everywhere statements in `(x, y)` hold on almost every line `a = const`. -/
theorem ae_ae_diagInv {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p, P p) : ∀ᵐ a, ∀ᵐ b, P (diagInv (a, b)) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hq : ∀ᵐ q : ℝ × ℝ, P (diagInv q) :=
    (Measure.LinearMap.quasiMeasurePreserving volume (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
      (by rw [det_diagInvLinear]; norm_num)).ae hP
  rw [Measure.volume_eq_prod] at hq
  exact Measure.ae_ae_of_ae_prod hq

/-- The restricted version of `ae_ae_diagInv`. -/
theorem ae_ae_diagRect {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p ∂(volume.restrict (diagRect I J)), P p) :
    ∀ᵐ a ∂(volume.restrict I), ∀ᵐ b ∂(volume.restrict J), P (diagInv (a, b)) := by
  rw [ae_restrict_iff' (measurableSet_diagRect hI hJ)] at hP
  rw [ae_restrict_iff' hI]
  filter_upwards [ae_ae_diagInv hP] with a ha haI
  rw [ae_restrict_iff' hJ]
  filter_upwards [ha] with b hb hbJ
  exact hb (mem_diagRect_diagInv.2 ⟨haI, hbJ⟩)

/-- `G` is a representative of `F` on the diagonal rectangle `{a₀ < a < a₁, b₁ < b < b₂}` that is
    locally absolutely continuous on almost every line `a = const`, with derivative `Gb` in `b`;
    `Gb` is measurable and square integrable on the rectangle. -/
def IsLineRep (a₀ a₁ b₁ b₂ : ℝ) (F G Gb : ℝ × ℝ → ℂ) : Prop :=
  (∀ᵐ p ∂(volume.restrict (diagRect (Ioo a₀ a₁) (Ioo b₁ b₂))), G p = F p) ∧
  Measurable Gb ∧ MemLp Gb 2 (volume.restrict (diagRect (Ioo a₀ a₁) (Ioo b₁ b₂))) ∧
  ∀ᵐ a ∂(volume.restrict (Ioo a₀ a₁)),
    (∀ c d, b₁ < c → c ≤ d → d < b₂ →
      AbsolutelyContinuousOnInterval (fun b ↦ G (diagInv (a, b))) c d) ∧
    ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)),
      HasDerivAt (fun b ↦ G (diagInv (a, b))) (Gb (diagInv (a, b))) b

/-- Iterated integrals in diagonal coordinates: `∫_I ∫_J F(a, b) db da = ½ ∫_{diagRect I J} F`. -/
theorem setLIntegral_setLIntegral_diagInv {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) {I J : Set ℝ}
    (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    ∫⁻ a in I, ∫⁻ b in J, F (diagInv (a, b)) =
      ENNReal.ofReal (1 / 2) * ∫⁻ p in diagRect I J, F p := by
  have hFd : Measurable fun q ↦ F (diagInv q) := hF.comp diagInv.continuous.measurable
  have hind : (I ×ˢ J).indicator (fun q ↦ F (diagInv q)) =
      fun q ↦ (diagRect I J).indicator F (diagInv q) := by
    funext q
    by_cases hq : q ∈ I ×ˢ J
    · rw [indicator_of_mem hq, indicator_of_mem (mem_diagRect_diagInv.2 hq)]
    · rw [indicator_of_notMem hq, indicator_of_notMem (fun h ↦ hq (mem_diagRect_diagInv.1 h))]
  rw [← setLIntegral_prod _ hFd.aemeasurable, ← Measure.volume_eq_prod,
    ← lintegral_indicator (hI.prod hJ), hind, lintegral_comp_diagInv,
    lintegral_indicator (measurableSet_diagRect hI hJ)]

/-- The `b`-derivative of a line representative is square integrable in diagonal coordinates. -/
theorem IsLineRep.lintegral_lt_top {a₀ a₁ b₁ b₂ : ℝ} {F G Gb : ℝ × ℝ → ℂ}
    (h : IsLineRep a₀ a₁ b₁ b₂ F G Gb) :
    ∫⁻ a in Ioo a₀ a₁, ∫⁻ b in Ioo b₁ b₂, ENNReal.ofReal (‖Gb (diagInv (a, b))‖ ^ 2) < ∞ := by
  have hm : Measurable fun p ↦ ENNReal.ofReal (‖Gb p‖ ^ 2) := by
    have := h.2.1
    fun_prop
  rw [setLIntegral_setLIntegral_diagInv (F := fun p ↦ ENNReal.ofReal (‖Gb p‖ ^ 2)) hm
    measurableSet_Ioo measurableSet_Ioo]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact ((memLp_two_iff_integrable_sq_norm h.2.1.aestronglyMeasurable).1 h.2.2.1).lintegral_lt_top

/-- Lifts of `H¹(𝕋²)` functions have line representatives on bounded diagonal rectangles, with
    `∂_b = ∂ₓ - ∂_y` (`lem:traces`). -/
theorem exists_isLineRep_liftL2 {g g₀ g₁ : L2} (h₀ : HasFourierPartial 0 g g₀)
    (h₁ : HasFourierPartial 1 g g₁) {a₀ a₁ b₁ b₂ : ℝ} (ha : a₀ < a₁) (hb : b₁ < b₂) :
    ∃ G, IsLineRep a₀ a₁ b₁ b₂ (liftL2 g) G (fun p ↦ liftL2 g₀ p - liftL2 g₁ p) := by
  set U := diagRect (Ioo a₀ a₁) (Ioo b₁ b₂)
  have hU : IsOpen U := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have hUb : Bornology.IsBounded U := isBounded_diagRect (Metric.isBounded_Ioo _ _)
    (Metric.isBounded_Ioo _ _)
  have hL2 (f : L2) : MemLp (liftL2 f) 2 (volume.restrict U) :=
    memSobolevOn_liftL2 (k := 0) (by exact_mod_cast memSobolev_zero f) hU hUb
  obtain ⟨C, -, hC⟩ := exists_acl_trace (b₁ := b₁) (b₂ := b₂) (b₀ := (b₁ + b₂) / 2) ha
    ⟨by linarith, by linarith⟩
  obtain ⟨G, hGF, hline, -⟩ := hC U (liftL2 g) (liftL2 g₀) (liftL2 g₁) hU subset_rfl (hL2 g)
    (hL2 g₀) (hL2 g₁) (hasWeakPartialOn_liftL2 h₀ hU) (hasWeakPartialOn_liftL2 h₁ hU)
  exact ⟨G, hGF, (measurable_liftL2 g₀).sub (measurable_liftL2 g₁), (hL2 g₀).sub (hL2 g₁),
    hline⟩

/-- `|ψₙ|² + |ψₜ|² = |ψₓ|² + |ψ_y|²` where `ρ ≠ 0`: `(sin x, sin y)/ρ` and `(sin y, -sin x)/ρ`
    are orthonormal. -/
theorem norm_normalDeriv_sq_add_norm_tangentDeriv_sq (ψx ψy : ℝ × ℝ → ℂ) {p : ℝ × ℝ}
    (hp : gradNorm p ≠ 0) :
    ‖normalDeriv ψx ψy p‖ ^ 2 + ‖tangentDeriv ψx ψy p‖ ^ 2 = ‖ψx p‖ ^ 2 + ‖ψy p‖ ^ 2 := by
  have hρ : gradNorm p ^ 2 = sin p.1 ^ 2 + sin p.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hρ2 : gradNorm p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have key : ‖(sin p.1 : ℂ) * ψx p + sin p.2 * ψy p‖ ^ 2 +
      ‖(sin p.2 : ℂ) * ψx p - sin p.1 * ψy p‖ ^ 2 =
        (sin p.1 ^ 2 + sin p.2 ^ 2) * (‖ψx p‖ ^ 2 + ‖ψy p‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  simp only [normalDeriv, tangentDeriv, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow,
    sq_abs]
  rw [← add_div, key, ← hρ, mul_div_cancel_left₀ _ hρ2]

/-- Local absolute continuity on all compact subintervals gives continuity on the open
    interval. -/
theorem continuousOn_Ioo_of_absolutelyContinuous {f : ℝ → ℂ} {b₁ b₂ : ℝ}
    (h : ∀ c d, b₁ < c → c ≤ d → d < b₂ → AbsolutelyContinuousOnInterval f c d) :
    ContinuousOn f (Ioo b₁ b₂) := by
  intro b hb
  have hc := (h ((b₁ + b) / 2) ((b + b₂) / 2) (by linarith [hb.1]) (by linarith [hb.1, hb.2])
    (by linarith [hb.2])).continuousOn
  rw [uIcc_of_le (by linarith [hb.1, hb.2])] at hc
  exact (hc.continuousAt (Icc_mem_nhds (by linarith [hb.1]) (by linarith [hb.2])))
    |>.continuousWithinAt

/-- Line representatives are continuous on almost every line. -/
theorem IsLineRep.ae_continuousOn {a₀ a₁ b₁ b₂ : ℝ} {F G Gb : ℝ × ℝ → ℂ}
    (h : IsLineRep a₀ a₁ b₁ b₂ F G Gb) :
    ∀ᵐ a ∂(volume.restrict (Ioo a₀ a₁)),
      ContinuousOn (fun b ↦ G (diagInv (a, b))) (Ioo b₁ b₂) := by
  filter_upwards [h.2.2.2] with a ha
  exact continuousOn_Ioo_of_absolutelyContinuous ha.1

/-- Two functions that agree almost everywhere on a diagonal rectangle and are continuous on
    almost every line `a = const` agree on almost every whole line. -/
theorem ae_eqOn_line {I J : Set ℝ} (hI : MeasurableSet I) (hJ : IsOpen J) {G₁ G₂ : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p ∂(volume.restrict (diagRect I J)), G₁ p = G₂ p)
    (h₁ : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun b ↦ G₁ (diagInv (a, b))) J)
    (h₂ : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun b ↦ G₂ (diagInv (a, b))) J) :
    ∀ᵐ a ∂(volume.restrict I), ∀ b ∈ J, G₁ (diagInv (a, b)) = G₂ (diagInv (a, b)) := by
  filter_upwards [ae_ae_diagRect hI hJ.measurableSet h, h₁, h₂] with a ha c₁ c₂
  exact Measure.eqOn_open_of_ae_eq ha hJ c₁ c₂

/-- The reflection `b ↦ π - b` preserves almost-everywhere statements on `(0, π)`. -/
theorem ae_restrict_Ioo_pi_sub {P : ℝ → Prop} (hP : ∀ᵐ b ∂(volume.restrict (Ioo 0 π)), P b) :
    ∀ᵐ b ∂(volume.restrict (Ioo 0 π)), P (π - b) := by
  rw [ae_restrict_iff' measurableSet_Ioo] at hP ⊢
  have h := (Measure.measurePreserving_sub_left volume π).quasiMeasurePreserving.ae hP
  filter_upwards [h] with b hb hbJ
  exact hb ⟨by linarith [hbJ.2], by linarith [hbJ.1]⟩

/-- Almost-everywhere statements on `(-π/2, π/2)` hold at `a = arcAngle s - π/2` for almost
    every `s`: the inverse `a ↦ -log tan((a + π/2)/2)` is differentiable, so it maps null sets
    to null sets. -/
theorem ae_comp_arcAngle {P : ℝ → Prop}
    (hP : ∀ᵐ a ∂(volume.restrict (Ioo (-(π / 2)) (π / 2))), P a) :
    ∀ᵐ s, P (arcAngle s - π / 2) := by
  set ι : ℝ → ℝ := fun a ↦ -Real.log (tan ((a + π / 2) / 2)) with hι
  rw [ae_restrict_iff' measurableSet_Ioo, ae_iff] at hP
  rw [ae_iff]
  set N := {a | ¬(a ∈ Ioo (-(π / 2)) (π / 2) → P a)}
  have hdiff : DifferentiableOn ℝ ι N := fun a ha ↦ by
    simp only [N, mem_ofPred_eq, not_imp] at ha
    have hc0 : 0 < (a + π / 2) / 2 := by linarith [ha.1.1]
    have hc1 : (a + π / 2) / 2 < π / 2 := by linarith [ha.1.2]
    have hcos : cos ((a + π / 2) / 2) ≠ 0 :=
      (cos_pos_of_mem_Ioo ⟨by linarith, hc1⟩).ne'
    have htan : tan ((a + π / 2) / 2) ≠ 0 := (tan_pos_of_pos_of_lt_pi_div_two hc0 hc1).ne'
    have h1 : DifferentiableAt ℝ (fun a : ℝ ↦ (a + π / 2) / 2) a := by fun_prop
    have h2 := (Real.hasDerivAt_tan hcos).differentiableAt.comp a h1
    exact ((h2.log htan).neg).differentiableWithinAt
  have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) hdiff hP
  refine measure_mono_null (fun s hs ↦ ?_) him
  have hmem := arcAngle_mem_Ioo s
  refine ⟨arcAngle s - π / 2, ?_, ?_⟩
  · simp only [N, mem_ofPred_eq, not_imp]
    exact ⟨⟨by linarith [hmem.1], by linarith [hmem.2]⟩, hs⟩
  · simp only [hι, arcAngle]
    rw [show (2 * arctan (exp (-s)) - π / 2 + π / 2) / 2 = arctan (exp (-s)) by ring,
      Real.tan_arctan, Real.log_exp, neg_neg]

/-! ### Traces on the arc -/

/-- Traces on the arc (`lem:arc-trace-identification`). Let `ψ` be even under both reflections and
    let `Gx, Gy` be line representatives of `ψₓ, ψ_y` near the arc `b = π/2`. For almost every
    `a`: `ψ_b = Gx - Gy` vanishes at `(a, π/2)`, so the normal derivative does; and
    `ψ_a = Gx + Gy` at `(a, π/2)` is the derivative of `a ↦ ψ̃(a, π/2)`. For almost every `s`,
    `g = ψ̃ ∘ γ` has derivative `T = sin y Gx - sin x Gy` at `γ(s)`, and
    `|ψₜ|² = ½ cosh² s |g'|²` there, since `ρ = √2 sech s` on the arc. -/
theorem ee_arc_trace_identification {ω : L2} (hω : InSector true true ω)
    {Gx Gy Gxb Gyb : ℝ × ℝ → ℂ} (hx : IsLineRep (-π) π 0 π (streamLiftX ω) Gx Gxb)
    (hy : IsLineRep (-π) π 0 π (streamLiftY ω) Gy Gyb) :
    (∀ᵐ a ∂(volume.restrict (Ioo (-π) π)),
      Gx (diagInv (a, π / 2)) = Gy (diagInv (a, π / 2)) ∧
        normalDeriv Gx Gy (diagInv (a, π / 2)) = 0) ∧
    (∀ᵐ a ∂(volume.restrict (Ioo (-π) π)),
      HasDerivAt (fun a ↦ contStream ω (diagInv (a, π / 2)))
        (Gx (diagInv (a, π / 2)) + Gy (diagInv (a, π / 2))) a) ∧
    ∀ᵐ s, HasDerivAt (contStream ω ∘ separatrixArc)
        (sin (separatrixArc s).2 * Gx (separatrixArc s) -
          sin (separatrixArc s).1 * Gy (separatrixArc s)) s ∧
      ‖tangentDeriv Gx Gy (separatrixArc s)‖ ^ 2 =
        cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2 := by
  set I : Set ℝ := Ioo (-π) π with hI
  set J : Set ℝ := Ioo 0 π with hJ
  set Q := diagRect I J with hQ
  have hπ := Real.pi_pos
  have hJ2 : π / 2 ∈ J := ⟨by positivity, by linarith⟩
  have hcx := hx.ae_continuousOn
  have hcy := hy.ae_continuousOn
  -- The reflection `b ↦ π - b` across the arc, for the raw partials.
  obtain ⟨h₂x, h₂y⟩ := hω.reflect₂_streamPartial
  simp only [paritySign, ite_true, one_smul] at h₂x h₂y
  have hS₂ (p : ℝ × ℝ) : torusProj (p.2 + Real.pi, p.1 + Real.pi) = S₂ (torusProj p) := by
    simp [torusProj, S₂, add_comm]
  have lift {T : Torus → Torus} {hT : MeasurePreserving T} {g h : L2}
      (heq : pullback T hT g = h) {M : ℝ × ℝ → ℝ × ℝ}
      (hM : ∀ p, torusProj (M p) = T (torusProj p)) :
      ∀ᵐ p, liftL2 g (M p) = liftL2 h p := by
    filter_upwards [ae_torusProj (ae_comp_of_pullback_eq heq)] with p hp
    simpa only [liftL2, hM] using hp
  have hrefl (g : L2) (a b : ℝ) :
      liftL2 g ((diagInv (a, b)).2 + π, (diagInv (a, b)).1 + π) =
        liftL2 g (diagInv (a, π - b)) := by
    have := ((isPeriodicLift_liftL2 g) (diagInv (a, π - b))).2
    rw [← this]
    simp only [diagInv_apply]
    congr 1
    ext <;> ring
  have hrx := ae_ae_diagInv (lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂x hS₂)
  have hry := ae_ae_diagInv (lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂y hS₂)
  simp only [hrefl] at hrx hry
  have hGx := ae_ae_diagRect measurableSet_Ioo measurableSet_Ioo hx.1
  have hGy := ae_ae_diagRect measurableSet_Ioo measurableSet_Ioo hy.1
  -- `ψ_b = Gx - Gy` is odd across the arc, so it vanishes on it.
  have hodd : ∀ᵐ a ∂(volume.restrict I), Gx (diagInv (a, π / 2)) = Gy (diagInv (a, π / 2)) := by
    filter_upwards [hcx, hcy, hGx, hGy, ae_restrict_of_ae hrx, ae_restrict_of_ae hry]
      with a cx cy gx gy rx ry
    set D : ℝ → ℂ := fun b ↦ Gx (diagInv (a, b)) - Gy (diagInv (a, b)) with hD
    have hmaps : MapsTo (fun b : ℝ ↦ π - b) J J := fun b hb ↦
      ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have hc1 : ContinuousOn (fun b ↦ D (π - b)) J :=
      (cx.sub cy).comp (continuousOn_const.sub continuousOn_id) hmaps
    have hc2 : ContinuousOn (fun b ↦ -D b) J := (cx.sub cy).neg
    have hae : (fun b ↦ D (π - b)) =ᵐ[volume.restrict J] fun b ↦ -D b := by
      filter_upwards [gx, gy, ae_restrict_Ioo_pi_sub gx, ae_restrict_Ioo_pi_sub gy,
        ae_restrict_of_ae rx, ae_restrict_of_ae ry] with b h1 h2 h3 h4 h5 h6
      simp only [hD, h1, h2, h3, h4, h5, h6, streamLiftX, streamLiftY]
      ring
    have := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc1 hc2 hJ2
    simp only [show π - π / 2 = π / 2 by ring, hD] at this
    exact sub_eq_zero.1 (CharZero.eq_neg_self_iff.1 this)
  refine ⟨?_, ?_⟩
  · filter_upwards [hodd] with a ha
    refine ⟨ha, ?_⟩
    rw [normalDeriv, ha]
    simp only [diagInv_apply, Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two]
    push_cast
    ring
  -- `ψ_a = Gx + Gy` on the arc is the derivative of the trace of `ψ̃`.
  have hU : IsOpen Q := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have hb : Bornology.IsBounded Q :=
    isBounded_diagRect (Metric.isBounded_Ioo _ _) (Metric.isBounded_Ioo _ _)
  have hrep := streamLift_ae_eq_contStream ω
  have hH2 : MemSobolevOn 2 Q (contStream ω) :=
    (memSobolevOn_liftL2 (memSobolev_two_invLap ω) hU hb).congr_ae hrep
  have hwx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0) hU).congr_left hrep
  have hwy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1) hU).congr_left hrep
  obtain ⟨H, hHae, hHac, -, hHder, -⟩ := absolutelyContinuous_trace_of_H2 hU (a₀ := -π)
    (a₁ := π) (b₁ := 0) (b₂ := π) (b₀ := π / 2) (by linarith) subset_rfl hJ2
    (continuous_contStream ω).continuousOn hH2 hwx hwy
  have hcH : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun b ↦ H (diagInv (a, b))) J := by
    filter_upwards [hHac] with a ha
    exact continuousOn_Ioo_of_absolutelyContinuous ha
  have hsum := ae_eqOn_line (G₁ := fun p ↦ Gx p + Gy p) (G₂ := H) measurableSet_Ioo isOpen_Ioo
    (by filter_upwards [hx.1, hy.1, hHae] with p h1 h2 h3
        simp only [h1, h2, h3, streamLiftX, streamLiftY])
    (by filter_upwards [hcx, hcy] with a h1 h2; exact h1.add h2) hcH
  have hder : ∀ᵐ a ∂(volume.restrict I), HasDerivAt (fun a ↦ contStream ω (diagInv (a, π / 2)))
      (Gx (diagInv (a, π / 2)) + Gy (diagInv (a, π / 2))) a := by
    filter_upwards [hsum, hHder] with a h1 h2
    rw [h1 _ hJ2]
    exact h2
  refine ⟨hder, ?_⟩
  -- The arc: `g = f ∘ φ` with `f(a) = ψ̃(a, π/2)` and `φ(s) = arcAngle s - π/2`.
  have hsub : Ioo (-(π / 2)) (π / 2) ⊆ I := Ioo_subset_Ioo (by linarith) (by linarith)
  filter_upwards [ae_comp_arcAngle (ae_restrict_of_ae_restrict_of_subset hsub hder)] with s hs
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - π / 2 with hφ
  have hpt : diagInv (φ s, π / 2) = separatrixArc s := by
    simp only [hφ, diagInv_apply, separatrixArc]
    congr 1 <;> ring
  have hcomp : contStream ω ∘ separatrixArc =
      (fun a ↦ contStream ω (diagInv (a, π / 2))) ∘ φ := by
    funext t
    simp only [Function.comp_apply, hφ, diagInv_apply, separatrixArc]
    congr 2 <;> ring
  have hφ' : HasDerivAt φ (-(1 / cosh s)) s := (hasDerivAt_arcAngle s).sub_const _
  have hd := hs.scomp s hφ'
  rw [← hcomp, hpt] at hd
  have hval : (-(1 / cosh s)) • (Gx (separatrixArc s) + Gy (separatrixArc s)) =
      sin (separatrixArc s).2 * Gx (separatrixArc s) -
        sin (separatrixArc s).1 * Gy (separatrixArc s) := by
    simp only [separatrixArc, Real.sin_sub_pi, sin_arcAngle, Complex.real_smul]
    push_cast
    ring
  rw [hval] at hd
  refine ⟨hd, ?_⟩
  have hc := cosh_pos s
  have hρ : gradNorm (separatrixArc s) ^ 2 = 2 / cosh s ^ 2 := by
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    simp only [separatrixArc, Real.sin_sub_pi, neg_sq, sin_arcAngle]
    ring
  rw [hd.deriv, tangentDeriv, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs, hρ]
  field_simp

/-- The energy of the arc traces (`lem:ee-arc-energy`): for `ψ` even under both reflections,
    `∫ cosh² s |g_k'(s)|² ds < ∞` on each arc, with `g_k = ψ̃ ∘ γ_k`. By
    `ee_arc_trace_identification` and `lintegral_separatrixArc_eq` the energy of `g₀` is
    `∫ |ψ_a(a, π/2)|² da / cos a`; the trace of `ψ_a` has finite Gagliardo seminorm
    (`lem:traces`), and near `a = ±π/2` it is odd, so the local odd Hardy inequality bounds the
    weight `1 / cos a`. -/
theorem ee_arc_energy {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω) :
    ∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2 := by
  sorry

/-! ### Corner tails -/

/-- Corner tails (`lem:ee-corner-tails`). Let `ψ` be even under both reflections and let
    `Gx, Gy` be line representatives of `ψₓ, ψ_y` near the arc. Then the parts of the quarter
    integrals of `|ψₙ|² + |ψₜ|²` over `|a| > π/2 - δ` (in the diagonal form of
    `lem:quarter-orbit-diagonal`) are small for small `δ`, uniformly in `h ∈ (0, 1)`. -/
theorem ee_corner_tails {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω)
    {Gx Gy Gxb Gyb : ℝ × ℝ → ℂ} (hx : IsLineRep (-π) π 0 π (streamLiftX ω) Gx Gxb)
    (hy : IsLineRep (-π) π 0 π (streamLiftY ω) Gy Gyb) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) 1,
      ∫⁻ a in {a | π / 2 - δ < |a|} ∩ Ioo (-arccos √h) (arccos √h),
        ENNReal.ofReal ((‖normalDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2 +
          ‖tangentDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2) / √(cos a ^ 2 - h ^ 2)) <
        ε := by
  have hπ := Real.pi_pos
  obtain ⟨hodd, hder, harc⟩ := ee_arc_trace_identification hω hx hy
  set f : ℝ → ℂ := fun a ↦ contStream ω (diagInv (a, π / 2)) with hf
  set I : Set ℝ := Ioo (-π) π with hI
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  have hAI : A ⊆ I := Ioo_subset_Ioo (by linarith) (by linarith)
  -- The `b`-derivative energy on the line `a`, and the arc term.
  set Kx : ℝ → ℝ≥0∞ := fun a ↦ ∫⁻ b in Ioo 0 π, ENNReal.ofReal (‖Gxb (diagInv (a, b))‖ ^ 2)
  set Ky : ℝ → ℝ≥0∞ := fun a ↦ ∫⁻ b in Ioo 0 π, ENNReal.ofReal (‖Gyb (diagInv (a, b))‖ ^ 2)
  set C : ℝ → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (‖deriv f a‖ ^ 2 / (2 * cos a))
  set Φ : ℝ → ℝ≥0∞ := fun a ↦ 4 * (ENNReal.ofReal (π / 2) * (Kx a + Ky a) + C a) with hΦ
  have hKxm : Measurable Kx := by
    have := hx.2.1
    exact Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ ↦
      ENNReal.ofReal (‖Gxb (diagInv q)‖ ^ 2)) (by fun_prop)
  have hKym : Measurable Ky := by
    have := hy.2.1
    exact Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ ↦
      ENNReal.ofReal (‖Gyb (diagInv q)‖ ^ 2)) (by fun_prop)
  have hCm : Measurable C := by
    have := measurable_deriv f
    fun_prop
  -- The arc term is finite by the energy of the arc trace.
  have hq₀ (a : ℝ) (ha : a ∈ A) : gradNorm (diagInv (a, π / 2)) ≠ 0 := by
    have hc := cos_pos_of_mem_Ioo ha
    rw [gradNorm, Real.sqrt_ne_zero']
    simp only [diagInv_apply, Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two, neg_sq]
    positivity
  have hCeq : ∀ᵐ a ∂(volume.restrict A), C a =
      ENNReal.ofReal (1 / cos a) *
        ENNReal.ofReal (‖tangentDeriv Gx Gy (diagInv (a, π / 2))‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAI hodd,
      ae_restrict_of_ae_restrict_of_subset hAI hder, ae_restrict_mem measurableSet_Ioo]
      with a ⟨h1, h2⟩ h3 ha
    have hc := cos_pos_of_mem_Ioo ha
    have hn := norm_normalDeriv_sq_add_norm_tangentDeriv_sq Gx Gy (hq₀ a ha)
    rw [h2, norm_zero, h1] at hn
    change ENNReal.ofReal (‖deriv f a‖ ^ 2 / (2 * cos a)) = _
    rw [h3.deriv, h1, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : Gy (diagInv (a, π / 2)) + Gy (diagInv (a, π / 2)) = 2 * Gy (diagInv (a, π / 2)) := by
      ring
    rw [this, norm_mul, Complex.norm_ofNat]
    field_simp
    nlinarith [hn]
  have hCfin : ∫⁻ a in A, C a < ∞ := by
    rw [lintegral_congr_ae hCeq, ← lintegral_separatrixArc_eq
      (fun p ↦ ENNReal.ofReal (‖tangentDeriv Gx Gy p‖ ^ 2))]
    have hE := (ee_arc_energy h0 hω 0 (by norm_num)).lintegral_lt_top
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hE
    filter_upwards [harc] with s hs
    rw [hs.2]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ cosh s ^ 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2 := by positivity
    change cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2 ≤
      cosh s ^ 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2
    linarith
  have hKfin : ∫⁻ a in A, (Kx a + Ky a) < ∞ := by
    rw [lintegral_add_left hKxm]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (lintegral_mono_set hAI) hx.lintegral_lt_top,
      lt_of_le_of_lt (lintegral_mono_set hAI) hy.lintegral_lt_top⟩
  have hΦfin : ∫⁻ a in A, Φ a ≠ ∞ := by
    rw [hΦ, lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_const_mul _ (by fun_prop)]
    exact (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin, hCfin⟩)).ne
  -- Absolute continuity of the integral gives `δ`.
  obtain ⟨η, hη, hηε⟩ := exists_pos_setLIntegral_lt_of_measure_lt hΦfin hε.ne'
  obtain ⟨r, -, hr0, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  set δ := min (π / 6) (r / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδπ : δ ≤ π / 6 := min_le_left _ _
  refine ⟨δ, hδ0, fun h hh ↦ ?_⟩
  set T : Set ℝ := {a | π / 2 - δ < |a|} ∩ A with hT
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter measurableSet_Ioo
  have hTvol : (volume.restrict A) T < η := by
    refine lt_of_le_of_lt ?_ hrη
    rw [Measure.restrict_apply hTm]
    have hsub : T ∩ A ⊆ Ioo (π / 2 - δ) (π / 2) ∪ Ioo (-(π / 2)) (-(π / 2) + δ) := by
      rintro a ⟨⟨h1, h2⟩, -⟩
      simp only [mem_ofPred_eq] at h1
      rcases le_total 0 a with ha | ha
      · rw [abs_of_nonneg ha] at h1
        exact Or.inl ⟨h1, h2.2⟩
      · rw [abs_of_nonpos ha] at h1
        exact Or.inr ⟨h2.1, by linarith⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith [min_le_right (π / 6) (r / 2)])
  have hTint := hηε T hTvol
  rw [Measure.restrict_restrict hTm, inter_eq_left.2 inter_subset_right] at hTint
  -- The quarter-orbit range lies in `T`.
  have h0 := hh.1
  have hsq0 : 0 < √h := Real.sqrt_pos.2 h0
  have hsq1 : √h < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith [hh.2]
  have hhsq : h ≤ √h := by
    have := Real.mul_self_sqrt h0.le
    nlinarith
  have hah : arccos √h < π / 2 := Real.arccos_lt_pi_div_two.2 hsq0
  set S : Set ℝ := {a | π / 2 - δ < |a|} ∩ Ioo (-arccos √h) (arccos √h) with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter measurableSet_Ioo
  have hST : S ⊆ T := fun a ha ↦ ⟨ha.1, by linarith [ha.2.1], by linarith [ha.2.2]⟩
  have hSI : S ⊆ I := fun a ha ↦ hAI (hST ha).2
  -- Pointwise facts on `S`.
  have hgeom (a : ℝ) (ha : a ∈ S) : √h < cos a ∧ 1 / 2 ≤ |sin a| := by
    have h1 : |a| < arccos √h := abs_lt.2 ⟨ha.2.1, ha.2.2⟩
    have hcos : cos (arccos √h) < cos |a| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg a) (Real.arccos_le_pi _) h1
    rw [Real.cos_arccos (by linarith) hsq1.le, Real.cos_abs] at hcos
    refine ⟨hcos, ?_⟩
    have h2 : cos |a| ≤ cos (π / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith)
        (by linarith [show π / 2 - δ < |a| from ha.1])
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    have h3 := sin_sq_add_cos_sq a
    have h4 : 0 ≤ cos a := by linarith
    have h5 : (1 / 2 : ℝ) ^ 2 ≤ |sin a| ^ 2 := by rw [sq_abs]; nlinarith
    nlinarith [abs_nonneg (sin a)]
  set β : ℝ → ℝ := quarterHeight h with hβdef
  set w : ℝ → ℝ := fun a ↦ 1 / cos a with hwdef
  have hβ (a : ℝ) (ha : a ∈ S) : β a ∈ Ioo 0 π ∧ w a * |β a - π / 2| ≤ π / 2 := by
    obtain ⟨hc, -⟩ := hgeom a ha
    have hc0 : 0 < cos a := hsq0.trans hc
    have hhc : h < cos a := lt_of_le_of_lt hhsq hc
    obtain ⟨hlo, hhi⟩ := pi_div_two_sub_quarterHeight_le h0.le hc0 hhc.le
    have hlt : h / cos a < 1 := (div_lt_one hc0).2 hhc
    have hlt' : π / 2 * (h / cos a) < π / 2 := by nlinarith
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have hhc2 : h ≤ cos a ^ 2 := by nlinarith [Real.sq_sqrt h0.le]
    rw [abs_of_nonpos (by linarith), neg_sub]
    calc w a * (π / 2 - β a) ≤ 1 / cos a * (π / 2 * (h / cos a)) := by
          simp only [hwdef]
          gcongr
      _ = π / 2 * (h / cos a ^ 2) := by field_simp
      _ ≤ π / 2 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).2 hhc2
      _ = π / 2 := mul_one _
  have hJ2 : π / 2 ∈ Ioo 0 π := ⟨by positivity, by linarith⟩
  have hw0 (a : ℝ) (ha : a ∈ S) : 0 ≤ w a := one_div_nonneg.2 (hsq0.trans (hgeom a ha).1).le
  have hsegx := ae_segment_le (G := fun q ↦ Gx (diagInv q)) (Gb := fun q ↦ Gxb (diagInv q))
    (hx.2.1.comp diagInv.continuous.measurable) hSm hJ2 (fun a ha ↦ (hβ a ha).1) hw0
    (ae_restrict_of_ae_restrict_of_subset hSI hx.2.2.2)
  have hsegy := ae_segment_le (G := fun q ↦ Gy (diagInv q)) (Gb := fun q ↦ Gyb (diagInv q))
    (hy.2.1.comp diagInv.continuous.measurable) hSm hJ2 (fun a ha ↦ (hβ a ha).1) hw0
    (ae_restrict_of_ae_restrict_of_subset hSI hy.2.2.2)
  refine lt_of_le_of_lt ?_ hTint
  refine (lintegral_mono_ae ?_).trans (lintegral_mono_set hST)
  filter_upwards [hsegx, hsegy, ae_restrict_of_ae_restrict_of_subset hSI hodd,
    ae_restrict_of_ae_restrict_of_subset hSI hder, ae_restrict_mem hSm]
    with a hsx hsy h12 h3 ha
  have h1 := h12.1
  obtain ⟨hc, hsin⟩ := hgeom a ha
  obtain ⟨⟨hβ0, hβπ⟩, hβw⟩ := hβ a ha
  have hc0 : 0 < cos a := hsq0.trans hc
  have hhc2 : h ≤ cos a ^ 2 := by nlinarith [Real.sq_sqrt h0.le]
  set q := diagInv (a, β a) with hq
  set q₀ := diagInv (a, π / 2) with hq₀
  -- `ρ ≠ 0` on the quarter orbit, so `|ψₙ|² + |ψₜ|² = |Gx|² + |Gy|²`.
  have hρ : gradNorm q ≠ 0 := by
    have hsb := sin_pos_of_pos_of_lt_pi hβ0 hβπ
    rw [gradNorm, Real.sqrt_ne_zero', hq, diagInv_apply, Real.sin_add, Real.sin_sub]
    nlinarith [sq_nonneg (sin a * cos (β a)), mul_pos hc0 hsb]
  rw [norm_normalDeriv_sq_add_norm_tangentDeriv_sq Gx Gy hρ]
  have hwt := one_div_sqrt_cos_sq_sub_le_corner h0.le hc0 hhc2 hsin
  -- Split each value into its difference from the arc trace and the arc trace.
  set X := ‖Gx q - Gx q₀‖ ^ 2 with hX
  set Y := ‖Gy q - Gy q₀‖ ^ 2 with hY
  set Z := ‖Gx q₀‖ ^ 2 + ‖Gy q₀‖ ^ 2 with hZ
  have hsplit (u v : ℂ) : ‖u‖ ^ 2 ≤ 2 * ‖u - v‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    have h := norm_add_le (u - v) v
    rw [sub_add_cancel] at h
    nlinarith [sq_nonneg (‖u - v‖ - ‖v‖), norm_nonneg u, norm_nonneg (u - v), norm_nonneg v]
  have hreal : (‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2) / √(cos a ^ 2 - h ^ 2) ≤
      4 * (X * w a) + 4 * (Y * w a) + 4 * (Z / cos a) := by
    have hsx' := hsplit (Gx q) (Gx q₀)
    have hsy' := hsplit (Gy q) (Gy q₀)
    have hnn : 0 ≤ ‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2 := by positivity
    calc (‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2) / √(cos a ^ 2 - h ^ 2)
        = (‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2) * (1 / √(cos a ^ 2 - h ^ 2)) := by ring
      _ ≤ (‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2) * (2 / cos a) := by gcongr
      _ ≤ (2 * X + 2 * ‖Gx q₀‖ ^ 2 + (2 * Y + 2 * ‖Gy q₀‖ ^ 2)) * (2 / cos a) := by
          gcongr
      _ = 4 * (X * w a) + 4 * (Y * w a) + 4 * (Z / cos a) := by
          simp only [hwdef, hZ]
          ring
  have hZ' : Z / cos a = ‖deriv f a‖ ^ 2 / (2 * cos a) := by
    rw [h3.deriv, hZ, h1]
    have : Gy q₀ + Gy q₀ = 2 * Gy q₀ := by ring
    rw [this, norm_mul, Complex.norm_ofNat]
    field_simp
    ring
  have hXb : ENNReal.ofReal (X * w a) ≤ ENNReal.ofReal (π / 2) * Kx a :=
    hsx.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hβw) le_rfl)
  have hYb : ENNReal.ofReal (Y * w a) ≤ ENNReal.ofReal (π / 2) * Ky a :=
    hsy.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hβw) le_rfl)
  have hX0 : 0 ≤ X * w a := mul_nonneg (by positivity) (hw0 a ha)
  have hY0 : 0 ≤ Y * w a := mul_nonneg (by positivity) (hw0 a ha)
  have hZ0 : 0 ≤ Z / cos a := div_nonneg (by positivity) hc0.le
  calc ENNReal.ofReal ((‖Gx q‖ ^ 2 + ‖Gy q‖ ^ 2) / √(cos a ^ 2 - h ^ 2))
      ≤ ENNReal.ofReal (4 * (X * w a) + 4 * (Y * w a) + 4 * (Z / cos a)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 4 * ENNReal.ofReal (X * w a) + 4 * ENNReal.ofReal (Y * w a) + 4 * C a := by
        have h4 (t : ℝ) : ENNReal.ofReal (4 * t) = 4 * ENNReal.ofReal t := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), h4, h4, h4, hZ']
    _ ≤ 4 * (ENNReal.ofReal (π / 2) * Kx a) + 4 * (ENNReal.ofReal (π / 2) * Ky a) + 4 * C a := by
        gcongr
    _ = Φ a := by
        simp only [hΦ]
        ring

end NoEmbeddedEigenvalues
