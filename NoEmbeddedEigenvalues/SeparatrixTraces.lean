import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.SobolevLocal
import NoEmbeddedEigenvalues.SegmentEstimates
import NoEmbeddedEigenvalues.QuarterOrbits
import NoEmbeddedEigenvalues.OddHardy

/-!
# Traces of the stream function at the separatrix

Blueprint: `def:line-representative`, `lem:line-representatives`, `lem:normal-tangent-frame`,
`lem:continuous-stream-symmetries`, `lem:normal-tangent-rotation`, `lem:quarter-null-sets`,
`lem:arc-trace-identification`, `lem:ee-arc-energy`, `lem:ee-quarter-bound`,
`lem:ee-corner-tails`, `lem:ee-level-traces`. All proved; the only admitted inputs are
`lem:traces` and `lem:local-to-global`.

Near the arc `b = π/2` the first derivatives `ψₓ, ψ_y` are handled through representatives that
are locally absolutely continuous on almost every line `a = const` (`IsLineRep`, provided by
`lem:traces`). Any two such representatives agree on almost every whole line, so their values on
`b = π/2` are well defined almost everywhere. Since `ψ` is even under the reflection
`b ↦ π - b`, `ψ_b = ψₓ - ψ_y` vanishes there, and `ψ_a = ψₓ + ψ_y` is the derivative of the trace
of `ψ̃`.

The corner tails use that `ψₙ, ψₜ` are the components of `∇ψ` in an orthonormal frame, so
`|ψₙ|² + |ψₜ|² = |ψₓ|² + |ψ_y|²`, and the segment estimate in diagonal coordinates: on the quarter
orbit `π/2 - β_h(a) ≤ (π/2) h / cos a` and `h ≤ cos² a`, so the segment length times the weight
`1 / cos a` is at most `π/2`. This bound holds on the whole quarter orbit once `h ≤ 1/4`
(`ee_quarter_bound`), so the level traces follow by dominated convergence in `a`, with the
representatives continuous in `b` on almost every line. The raw derivatives agree with the
representatives on almost every level by Fubini in `(a, h)` (`ae_quarterGraph_of_ae`), without
the coarea formula. The arc energy uses the local odd Hardy inequality at `a = ±π/2`, where
`ψ_a(·, π/2)` is odd since `ψ̃` is even under `S₁` and periodic. The other arcs and quarters are
those of the rotated vorticity.
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
    memSobolevOn_liftL2 (k := 0) (by exact_mod_cast memSobolev_zero f) hUb
  obtain ⟨C, -, hC⟩ := exists_acl_trace (b₁ := b₁) (b₂ := b₂) (b₀ := (b₁ + b₂) / 2) ha
    ⟨by linarith, by linarith⟩
  obtain ⟨G, hGF, hline, -⟩ := hC U (liftL2 g) (liftL2 g₀) (liftL2 g₁) hU subset_rfl (hL2 g)
    (hL2 g₀) (hL2 g₁) (hasWeakPartialOn_liftL2 h₀ U) (hasWeakPartialOn_liftL2 h₁ U)
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
    (memSobolevOn_liftL2 (memSobolev_two_invLap ω) hb).congr_ae hrep
  have hwx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0) Q).congr_left hrep
  have hwy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1) Q).congr_left hrep
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

/-- The normal derivative `ψₙ` of the stream function of `ω` (outward from `{Ψ > 2h}`). -/
abbrev streamNormal (ω : L2) : ℝ × ℝ → ℂ := normalDeriv (streamLiftX ω) (streamLiftY ω)

/-- The tangential derivative `ψₜ` of the stream function of `ω`. -/
abbrev streamTangent (ω : L2) : ℝ × ℝ → ℂ := tangentDeriv (streamLiftX ω) (streamLiftY ω)

/-! ### Rotations of the stream derivatives -/

theorem measurePreserving_rotLift : MeasurePreserving rotLift volume volume := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  rw [← Measure.volume_eq_prod] at h
  convert h using 1
  funext p
  rfl

theorem liftL2_rotate_ae (g : L2) : ∀ᵐ p, liftL2 (rotate g) p = liftL2 g (rotLift p) := by
  have hr := Lp.coeFn_compMeasurePreserving g measurePreserving_R
  change (rotate g : Torus → ℂ) =ᵐ[volume] (fun t ↦ g (R t)) at hr
  have hp (p : ℝ × ℝ) : torusProj (rotLift p) = R (torusProj p) := by
    ext <;> simp [torusProj, rotLift, R, Real.Angle.coe_neg]
  filter_upwards [ae_torusProj hr] with p hp'
  simpa only [liftL2, hp] using hp'

/-- The chain rule for the quarter rotation `R(x, y) = (y, -x)`:
    `∂ₓ(ψ ∘ R) = -ψ_y ∘ R` and `∂_y(ψ ∘ R) = ψₓ ∘ R`. -/
theorem streamPartial_rotate (ω : L2) :
    streamPartial 0 (rotate ω) = -rotate (streamPartial 1 ω) ∧
      streamPartial 1 (rotate ω) = rotate (streamPartial 0 ω) := by
  have h0 := rotationSymmetry.streamPartial_action (j := 0) (j' := 1) (σ := -1)
    (fun k ↦ by simp [rotationSymmetry, frequencyComponent]) ω
  have h1 := rotationSymmetry.streamPartial_action (j := 1) (j' := 0) (σ := 1)
    (fun k ↦ by simp [rotationSymmetry, frequencyComponent]) ω
  constructor
  · change streamPartial 0 (rotationSymmetry.action ω) = -rotationSymmetry.action _
    rw [h0]
    simp
  · change streamPartial 1 (rotationSymmetry.action ω) = rotationSymmetry.action _
    rw [h1]
    simp

/-- `ψₙ` and `ψₜ` are geometric: for the rotated vorticity they are those of `ω` at `R p`. -/
theorem streamNormal_rotate_ae (ω : L2) :
    ∀ᵐ p, streamNormal (rotate ω) p = streamNormal ω (rotLift p) ∧
      streamTangent (rotate ω) p = streamTangent ω (rotLift p) := by
  obtain ⟨h0, h1⟩ := streamPartial_rotate ω
  filter_upwards [liftL2_rotate_ae (streamPartial 1 ω), liftL2_rotate_ae (streamPartial 0 ω),
    ae_torusProj (Lp.coeFn_neg (rotate (streamPartial 1 ω)))] with p hy hx hneg
  have hX : streamLiftX (rotate ω) p = -streamLiftY ω (rotLift p) := by
    change liftL2 (streamPartial 0 (rotate ω)) p = _
    rw [h0]
    change ((-rotate (streamPartial 1 ω) : L2) : Torus → ℂ) (torusProj p) = _
    rw [hneg]
    change -liftL2 (rotate (streamPartial 1 ω)) p = _
    rw [hy]
    rfl
  have hY : streamLiftY (rotate ω) p = streamLiftX ω (rotLift p) := by
    change liftL2 (streamPartial 1 (rotate ω)) p = _
    rw [h1, hx]
    rfl
  have hρ : gradNorm (rotLift p) = gradNorm p := by
    simp only [gradNorm, rotLift, Real.sin_neg, neg_sq, add_comm]
  simp only [streamNormal, streamTangent, normalDeriv, tangentDeriv, hX, hY, hρ]
  simp only [rotLift, Real.sin_neg]
  constructor <;> push_cast <;> ring

theorem streamNormal_iterate_rotate_ae (ω : L2) (k : ℕ) :
    ∀ᵐ p, streamNormal (rotate^[k] ω) p = streamNormal ω (rotLift^[k] p) ∧
      streamTangent (rotate^[k] ω) p = streamTangent ω (rotLift^[k] p) := by
  induction k generalizing ω with
  | zero => exact Eventually.of_forall fun p ↦ ⟨rfl, rfl⟩
  | succ k ih =>
    have hq := (measurePreserving_rotLift.quasiMeasurePreserving.iterate k).ae
      (streamNormal_rotate_ae ω)
    filter_upwards [ih (rotate ω), hq] with p h1 h2
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', h1.1, h1.2, h2.1, h2.2]
    exact ⟨rfl, rfl⟩

/-! ### Null sets on the quarter orbits -/

/-- On the quarter orbit, `|a| < arccos √h` gives `√h < cos a`. -/
theorem sqrt_lt_cos_of_abs_lt_arccos {h a : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (ha : |a| < arccos √h) : √h < cos a := by
  have hsq1 : √h < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith [hh.2]
  have hcos : cos (arccos √h) < cos |a| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg a) (Real.arccos_le_pi _) ha
  rwa [Real.cos_arccos (by linarith [Real.sqrt_nonneg h]) hsq1.le, Real.cos_abs] at hcos

/-- A null set of the plane meets almost every quarter orbit, written as the graph
    `b = β_h(a)` over `|a| < arccos √h`, in a null set of `a`. For fixed `a` the map
    `h ↦ β_h(a)` has the differentiable inverse `b ↦ cos a cos b`, so this is Fubini in `(a, h)`
    after `(a, b)`. -/
theorem ae_quarterGraph_of_ae {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p, P p) :
    ∀ᵐ h, h ∈ Ioo (0 : ℝ) 1 → ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
      P (diagInv (a, quarterHeight h a)) := by
  set Z := toMeasurable volume {p | ¬P p} with hZ
  have hZm : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hZ0 : volume Z = 0 := by
    rw [hZ, measure_toMeasurable]
    exact hP
  have hnZ : ∀ᵐ p, p ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  set B : Set (ℝ × ℝ) := {q | q.2 ∈ Ioo 0 1 ∧ |q.1| < arccos √q.2 ∧
    diagInv (q.1, quarterHeight q.2 q.1) ∈ Z} with hB
  have hBm : MeasurableSet {q : ℝ × ℝ | ¬(q.1, q.2) ∈ B} := by
    have hq : Measurable fun q : ℝ × ℝ ↦ diagInv (q.1, quarterHeight q.2 q.1) := by
      unfold quarterHeight
      have := Real.continuous_arccos.measurable
      exact diagInv.continuous.measurable.comp (by fun_prop)
    have harc : Measurable fun q : ℝ × ℝ ↦ arccos √q.2 :=
      Real.continuous_arccos.measurable.comp (Real.continuous_sqrt.measurable.comp measurable_snd)
    have h1 : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Ioo 0 1} :=
      measurableSet_Ioo.preimage measurable_snd
    have h2 : MeasurableSet {q : ℝ × ℝ | |q.1| < arccos √q.2} :=
      measurableSet_lt (by fun_prop) harc
    have h3 : MeasurableSet {q : ℝ × ℝ | diagInv (q.1, quarterHeight q.2 q.1) ∈ Z} :=
      hZm.preimage hq
    exact (h1.inter (h2.inter h3)).compl
  have hline : ∀ᵐ a, ∀ᵐ h, ¬(a, h) ∈ B := by
    filter_upwards [ae_ae_diagInv hnZ] with a ha
    rw [ae_iff] at ha ⊢
    have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
      (f := fun b ↦ cos a * cos b) (by fun_prop) ha
    refine measure_mono_null (fun h hBh ↦ ?_) him
    simp only [mem_ofPred_eq, not_not] at hBh
    obtain ⟨hh, ha', hz⟩ := hBh
    refine ⟨quarterHeight h a, by simpa using hz, ?_⟩
    have hc := sqrt_lt_cos_of_abs_lt_arccos hh ha'
    have hc0 : 0 < cos a := (Real.sqrt_pos.2 hh.1).trans hc
    have hhc : h < cos a := by
      have : h ≤ √h := by
        have := Real.mul_self_sqrt hh.1.le
        nlinarith [Real.sqrt_nonneg h, hh.2]
      linarith
    simp only [quarterHeight]
    rw [Real.cos_arccos (by
        have : 0 ≤ h / cos a := div_nonneg hh.1.le hc0.le
        linarith) ((div_le_one hc0).2 hhc.le)]
    field_simp
  have hswap := (Measure.ae_ae_comm hBm).1 hline
  filter_upwards [hswap] with h hh hh01
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hh] with a haB haI
  by_contra hPa
  exact haB ⟨hh01, abs_lt.2 ⟨haI.1, haI.2⟩, subset_toMeasurable _ _ hPa⟩

/-! ### Symmetries of the continuous stream representative -/

/-- If the stream function of `ω` composed with a continuous measure-preserving map `T` is the
    stream function of `ω'`, the same holds pointwise for the continuous representatives. -/
theorem continuousRep_invLap_comp {T : Torus → Torus} {hT : MeasurePreserving T}
    (hTc : Continuous T) {ω ω' : L2} (h : pullback T hT (invLap ω) = invLap ω') (t : Torus) :
    continuousRep (invLap ω) (T t) = continuousRep (invLap ω') t := by
  have hi := coeFn_invLap_eq_continuousRep ω
  have hi' := coeFn_invLap_eq_continuousRep ω'
  have hc := hT.quasiMeasurePreserving.ae_eq_comp hi
  have hr := Lp.coeFn_compMeasurePreserving (invLap ω) hT
  change (pullback T hT (invLap ω) : Torus → ℂ) =ᵐ[volume] (fun t ↦ invLap ω (T t)) at hr
  rw [h] at hr
  have ha : (fun t ↦ continuousRep (invLap ω) (T t)) =ᵐ[volume] continuousRep (invLap ω') := by
    filter_upwards [hr, hc, hi'] with t ht hct hit
    simp only [Function.comp_apply] at hct
    rw [← hct, ← ht, hit]
  have : (volume : Measure Torus).IsOpenPosMeasure := by
    change (volume : Measure (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi))).IsOpenPosMeasure
    infer_instance
  exact congrFun (Measure.eq_of_ae_eq ha ((continuousRep (invLap ω)).continuous.comp hTc)
    (continuousRep (invLap ω')).continuous) t

/-- `ψ̃` of the rotated vorticity is `ψ̃ ∘ R`. -/
theorem contStream_rotate (ω : L2) (p : ℝ × ℝ) :
    contStream (rotate ω) p = contStream ω (rotLift p) := by
  have hR : Continuous R := by unfold R; fun_prop
  have h := continuousRep_invLap_comp (hT := measurePreserving_R) hR (ω := ω) (ω' := rotate ω)
    (by exact rotationSymmetry.invLap_commute ω)
  have hp : torusProj (rotLift p) = R (torusProj p) := by
    ext <;> simp [torusProj, rotLift, R, Real.Angle.coe_neg]
  change _ = continuousRep (invLap ω) (torusProj (rotLift p))
  rw [hp, h]
  rfl

theorem contStream_iterate_rotate (ω : L2) (k : ℕ) (p : ℝ × ℝ) :
    contStream (rotate^[k] ω) p = contStream ω (rotLift^[k] p) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, contStream_rotate, ← Function.iterate_succ_apply' rotLift]

theorem inSector_iterate_rotate {ω : L2} (hω : InSector true true ω) (k : ℕ) :
    InSector true true (rotate^[k] ω) := by
  induction k with
  | zero => exact hω
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.rotate

/-- `ψ̃` is even under `S₁(x, y) = (π - y, π - x)` when `ω` is. -/
theorem contStream_reflect₁ {ω : L2} {ε : Bool} (hω : InSector true ε ω) (p : ℝ × ℝ) :
    contStream ω (π - p.2, π - p.1) = contStream ω p := by
  have h1 : pullback S₁ measurePreserving_S₁ (invLap ω) = invLap ω := by
    change symmetry₁.action (invLap ω) = _
    rw [symmetry₁.invLap_commute]
    change invLap (reflect₁ ω) = _
    rw [hω.1]
    simp [paritySign]
  have hS : Continuous S₁ := by unfold S₁; fun_prop
  have h := continuousRep_invLap_comp hS h1
  have hp : torusProj (π - p.2, π - p.1) = S₁ (torusProj p) := by
    simp [torusProj, S₁]
  change continuousRep (invLap ω) (torusProj _) = continuousRep (invLap ω) (torusProj p)
  rw [hp, h]

theorem contStream_add_two_pi (ω : L2) (p : ℝ × ℝ) :
    contStream ω (p.1 + 2 * π, p.2 + 2 * π) = contStream ω p := by
  change continuousRep (invLap ω) (torusProj _) = continuousRep (invLap ω) (torusProj p)
  congr 1
  simp only [torusProj, Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]

/-! ### The energy of the arc traces -/

/-- Reflection `u ↦ c - u` of a set integral over an interval. -/
theorem setLIntegral_Ioo_comp_sub_left (g : ℝ → ℝ≥0∞) (c α β : ℝ) :
    ∫⁻ u in Ioo (c - β) (c - α), g (c - u) = ∫⁻ a in Ioo α β, g a := by
  have h := (Measure.measurePreserving_sub_left volume c).setLIntegral_comp_preimage_emb
    (Homeomorph.subLeft c).measurableEmbedding g (Ioo α β)
  have hpre : (fun u ↦ c - u) ⁻¹' Ioo α β = Ioo (c - β) (c - α) := by
    ext u
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [← h]
  change _ = ∫⁻ a in (fun u ↦ c - u) ⁻¹' Ioo α β, g (c - a)
  rw [hpre]

/-- Translation `u ↦ u + c` of a set integral over an interval. -/
theorem setLIntegral_Ioo_comp_add_right (g : ℝ → ℝ≥0∞) (c α β : ℝ) :
    ∫⁻ u in Ioo (α - c) (β - c), g (u + c) = ∫⁻ a in Ioo α β, g a := by
  have h := (measurePreserving_add_right volume c).setLIntegral_comp_preimage_emb
    (Homeomorph.addRight c).measurableEmbedding g (Ioo α β)
  have hpre : (fun u ↦ u + c) ⁻¹' Ioo α β = Ioo (α - c) (β - c) := by
    ext u
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [← h]
  change _ = ∫⁻ a in (fun u ↦ u + c) ⁻¹' Ioo α β, g (a + c)
  rw [hpre]

/-- The energy of the arc trace in diagonal coordinates (`lem:arc-trace-identification`): with
    `f(a) = ψ̃(a, π/2)`, `∫ cosh² s |g'(s)|² ds = ∫_{-π/2}^{π/2} |f'(a)|² da / cos a`. -/
theorem lintegral_arc_energy_eq {ω : L2} (hω : InSector true true ω) :
    ∫⁻ s, ENNReal.ofReal (cosh s ^ 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2) =
      ∫⁻ a in Ioo (-(π / 2)) (π / 2),
        ENNReal.ofReal (‖deriv (fun a ↦ contStream ω (diagInv (a, π / 2))) a‖ ^ 2 / cos a) := by
  have hπ := Real.pi_pos
  obtain ⟨Gx, hx⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 0)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨Gy, hy⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 1)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨hodd, hder, harc⟩ := ee_arc_trace_identification hω hx hy
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  have hAI : A ⊆ Ioo (-π) π := Ioo_subset_Ioo (by linarith) (by linarith)
  calc ∫⁻ s, ENNReal.ofReal (cosh s ^ 2 * ‖deriv (contStream ω ∘ separatrixArc) s‖ ^ 2)
      = ∫⁻ s, ENNReal.ofReal (2 * ‖tangentDeriv Gx Gy (separatrixArc s)‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [harc] with s hs
        rw [hs.2]
        ring_nf
    _ = ∫⁻ a in A, ENNReal.ofReal (1 / cos a) *
          ENNReal.ofReal (2 * ‖tangentDeriv Gx Gy (diagInv (a, π / 2))‖ ^ 2) :=
        lintegral_separatrixArc_eq (fun p ↦ ENNReal.ofReal (2 * ‖tangentDeriv Gx Gy p‖ ^ 2))
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hAI hodd,
          ae_restrict_of_ae_restrict_of_subset hAI hder, ae_restrict_mem measurableSet_Ioo]
          with a h12 h3 ha
        have hc := cos_pos_of_mem_Ioo ha
        have hρ : gradNorm (diagInv (a, π / 2)) ≠ 0 := by
          rw [gradNorm, Real.sqrt_ne_zero']
          simp only [diagInv_apply, Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two, neg_sq]
          positivity
        have hn := norm_normalDeriv_sq_add_norm_tangentDeriv_sq Gx Gy hρ
        rw [h12.2, norm_zero, h12.1] at hn
        rw [h3.deriv, h12.1, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Gy (diagInv (a, π / 2)) + Gy (diagInv (a, π / 2)) = 2 * Gy (diagInv (a, π / 2)) := by
          ring
        rw [this, norm_mul, Complex.norm_ofNat]
        field_simp
        nlinarith [hn]

/-- The arc trace has finite energy: with `f(a) = ψ̃(a, π/2)`,
    `∫_{-π/2}^{π/2} |f'(a)|² da / cos a < ∞`. The trace `f' = ψ_a(·, π/2)` has finite Gagliardo
    seminorm (`lem:traces`), and `f` is even about `±π/2` (`S₁` and periodicity), so `f'` is odd
    there and the local odd Hardy inequality controls `1/cos a ≤ (π/2)/|a ∓ π/2|`. -/
theorem lintegral_arcTrace_lt_top {ω : L2} (hω : InSector true true ω) :
    ∫⁻ a in Ioo (-(π / 2)) (π / 2),
      ENNReal.ofReal (‖deriv (fun a ↦ contStream ω (diagInv (a, π / 2))) a‖ ^ 2 / cos a) < ∞ := by
  have hπ := Real.pi_pos
  set f : ℝ → ℂ := fun a ↦ contStream ω (diagInv (a, π / 2)) with hf
  set t : ℝ → ℂ := deriv f with ht
  set I : Set ℝ := Ioo (-π) π with hI
  set Q := diagRect I (Ioo 0 π) with hQ
  have hJ2 : π / 2 ∈ Ioo 0 π := ⟨by positivity, by linarith⟩
  have htm : Measurable t := measurable_deriv f
  -- The trace of `ψ_a` is `t`, by the line representatives of `ψₓ, ψ_y`.
  obtain ⟨Gx, hx⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 0)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨Gy, hy⟩ := exists_isLineRep_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 1)
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1)
    (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π) (by linarith) hπ
  obtain ⟨-, hder, -⟩ := ee_arc_trace_identification hω hx hy
  -- The Gagliardo bound for the trace of `ψ_a = ψₓ + ψ_y` (`lem:traces`).
  have hU : IsOpen Q := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have hUb : Bornology.IsBounded Q :=
    isBounded_diagRect (Metric.isBounded_Ioo _ _) (Metric.isBounded_Ioo _ _)
  have hL2 (g : L2) : MemLp (liftL2 g) 2 (volume.restrict Q) :=
    memSobolevOn_liftL2 (k := 0) (by exact_mod_cast memSobolev_zero g) hUb
  obtain ⟨C, -, hC⟩ := exists_acl_trace (a₀ := -π) (a₁ := π) (b₁ := 0) (b₂ := π)
    (b₀ := π / 2) (by linarith) hJ2
  have hwx := (hasWeakPartialOn_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0) Q).add
    (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial_streamSecondPartial ω 0 1) Q)
  have hwy := (hasWeakPartialOn_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 0) Q).add
    (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1) Q)
  obtain ⟨G, hGF, hGline, hGag⟩ := hC Q _ _ _ hU subset_rfl ((hL2 _).add (hL2 _))
    ((hL2 _).add (hL2 _)) ((hL2 _).add (hL2 _)) hwx hwy
  have hcG : ∀ᵐ a ∂(volume.restrict I), ContinuousOn (fun b ↦ G (diagInv (a, b))) (Ioo 0 π) := by
    filter_upwards [hGline] with a ha
    exact continuousOn_Ioo_of_absolutelyContinuous ha.1
  have hsum := ae_eqOn_line (G₁ := G) (G₂ := fun p ↦ Gx p + Gy p) measurableSet_Ioo isOpen_Ioo
    (by filter_upwards [hx.1, hy.1, hGF] with p h1 h2 h3
        rw [h3, h1, h2]
        rfl)
    hcG (by filter_upwards [hx.ae_continuousOn, hy.ae_continuousOn] with a h1 h2
            exact h1.add h2)
  have hGt : ∀ᵐ a ∂(volume.restrict I), G (diagInv (a, π / 2)) = t a := by
    filter_upwards [hsum, hder] with a h1 h2
    rw [h1 _ hJ2, ht, h2.deriv]
  set K : ℝ → ℝ → ℝ≥0∞ := fun a a' ↦ ENNReal.ofReal (‖t a - t a'‖ ^ 2 / (a - a') ^ 2) with hK
  have hKfin : ∫⁻ a in I, ∫⁻ a' in I, K a a' < ∞ := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hGag ENNReal.ofReal_lt_top)
    refine lintegral_congr_ae ?_
    filter_upwards [hGt] with a ha
    refine lintegral_congr_ae ?_
    filter_upwards [hGt] with a' ha'
    simp only [hK, ha, ha']
  -- `f` is even about `π/2` and `-π/2`, so `t` is odd there.
  have hfe1 (a : ℝ) : f (π - a) = f a := by
    simp only [hf]
    rw [← contStream_reflect₁ hω (diagInv (a, π / 2))]
    congr 1
    simp only [diagInv_apply]
    ext <;> ring
  have hfe2 (a : ℝ) : f (-π - a) = f a := by
    rw [← hfe1 a]
    simp only [hf]
    rw [← contStream_add_two_pi ω (diagInv (-π - a, π / 2))]
    congr 1
    simp only [diagInv_apply]
    ext <;> ring
  have hto1 (a : ℝ) : t (π - a) = -t a := by
    have h := deriv_comp_const_sub (f := f) (a := π) (x := a)
    rw [show (fun x ↦ f (π - x)) = f from funext hfe1] at h
    simp only [ht, h, neg_neg]
  have hto2 (a : ℝ) : t (-π - a) = -t a := by
    have h := deriv_comp_const_sub (f := f) (a := -π) (x := a)
    rw [show (fun x ↦ f (-π - x)) = f from funext hfe2] at h
    simp only [ht, h, neg_neg]
  -- The local odd Hardy inequality at both ends.
  have hHardy (r : ℝ → ℂ) (hr : Measurable r) (hodd : ∀ u, r (-u) = -r u)
      (hK' : ∫⁻ u in Ioo 0 (π / 2), ∫⁻ w in Ioo (-(π / 2)) (π / 2),
        ENNReal.ofReal (‖r u - r w‖ ^ 2 / (u - w) ^ 2) ≤ ∫⁻ a in I, ∫⁻ a' in I, K a a') :
      ∫⁻ u in Ioo 0 (π / 2), ENNReal.ofReal (‖r u‖ ^ 2 / u) < ∞ :=
    lt_of_le_of_lt (lintegral_sq_div_le_localGagliardoSq hr.aemeasurable fun u _ ↦ hodd u)
      (ENNReal.mul_lt_top (by norm_num) (lt_of_le_of_lt hK' hKfin))
  have hK1 : ∫⁻ u in Ioo 0 (π / 2), ∫⁻ w in Ioo (-(π / 2)) (π / 2),
      ENNReal.ofReal (‖t (π / 2 - u) - t (π / 2 - w)‖ ^ 2 / (u - w) ^ 2) ≤
        ∫⁻ a in I, ∫⁻ a' in I, K a a' := by
    have hin (u : ℝ) : ∫⁻ w in Ioo (-(π / 2)) (π / 2),
        ENNReal.ofReal (‖t (π / 2 - u) - t (π / 2 - w)‖ ^ 2 / (u - w) ^ 2) =
          ∫⁻ a' in Ioo 0 π, K (π / 2 - u) a' := by
      rw [← setLIntegral_Ioo_comp_sub_left _ (π / 2) 0 π]
      rw [show π / 2 - π = -(π / 2) by ring, sub_zero]
      refine setLIntegral_congr_fun measurableSet_Ioo fun w _ ↦ ?_
      simp only [hK]
      congr 2
      ring
    simp_rw [hin]
    rw [show (Ioo 0 (π / 2) : Set ℝ) = Ioo (π / 2 - π / 2) (π / 2 - 0) by
      rw [sub_self, sub_zero], setLIntegral_Ioo_comp_sub_left
      (fun a ↦ ∫⁻ a' in Ioo 0 π, K a a') (π / 2) 0 (π / 2)]
    refine (lintegral_mono_set (Ioo_subset_Ioo (by linarith) (by linarith))).trans
      (lintegral_mono fun a ↦ lintegral_mono_set (Ioo_subset_Ioo (by linarith) le_rfl))
  have hK2 : ∫⁻ u in Ioo 0 (π / 2), ∫⁻ w in Ioo (-(π / 2)) (π / 2),
      ENNReal.ofReal (‖t (u + -(π / 2)) - t (w + -(π / 2))‖ ^ 2 / (u - w) ^ 2) ≤
        ∫⁻ a in I, ∫⁻ a' in I, K a a' := by
    have hin (u : ℝ) : ∫⁻ w in Ioo (-(π / 2)) (π / 2),
        ENNReal.ofReal (‖t (u + -(π / 2)) - t (w + -(π / 2))‖ ^ 2 / (u - w) ^ 2) =
          ∫⁻ a' in Ioo (-π) 0, K (u + -(π / 2)) a' := by
      rw [← setLIntegral_Ioo_comp_add_right _ (-(π / 2)) (-π) 0]
      rw [show -π - -(π / 2) = -(π / 2) by ring, show (0 : ℝ) - -(π / 2) = π / 2 by ring]
      refine setLIntegral_congr_fun measurableSet_Ioo fun w _ ↦ ?_
      simp only [hK]
      congr 2
      ring
    simp_rw [hin]
    rw [show (Ioo 0 (π / 2) : Set ℝ) = Ioo (-(π / 2) - -(π / 2)) (0 - -(π / 2)) by
      congr 1 <;> ring, setLIntegral_Ioo_comp_add_right
      (fun a ↦ ∫⁻ a' in Ioo (-π) 0, K a a') (-(π / 2)) (-(π / 2)) 0]
    refine (lintegral_mono_set (Ioo_subset_Ioo (by linarith) (by linarith))).trans
      (lintegral_mono fun a ↦ lintegral_mono_set (Ioo_subset_Ioo le_rfl (by linarith)))
  have hR := hHardy (fun u ↦ t (π / 2 - u)) (htm.comp (by fun_prop))
    (fun u ↦ by
      have h := hto1 (π / 2 - u)
      rw [show π - (π / 2 - u) = π / 2 + u by ring] at h
      simpa [sub_neg_eq_add] using h) hK1
  have hL := hHardy (fun u ↦ t (u + -(π / 2))) (htm.comp (by fun_prop))
    (fun u ↦ by
      have := hto2 (u + -(π / 2))
      rw [show -π - (u + -(π / 2)) = -u + -(π / 2) by ring] at this
      exact this) hK2
  -- The weight: `cos a ≥ (2/π) (π/2 - |a|)`.
  have hright : ∫⁻ a in Ioo 0 (π / 2), ENNReal.ofReal (‖t a‖ ^ 2 / cos a) ≤
      ENNReal.ofReal (π / 2) * ∫⁻ u in Ioo 0 (π / 2), ENNReal.ofReal (‖t (π / 2 - u)‖ ^ 2 / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hcv := setLIntegral_Ioo_comp_sub_left
      (fun a ↦ ENNReal.ofReal (‖t a‖ ^ 2 / cos a)) (π / 2) 0 (π / 2)
    rw [sub_self, sub_zero] at hcv
    rw [← hcv]
    refine setLIntegral_mono' measurableSet_Ioo fun u hu ↦ ?_
    have hu0 : u ≠ 0 := hu.1.ne'
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := mul_le_sin hu.1.le hu.2.le
    rw [cos_pi_div_two_sub]
    have hsin : 0 < sin u := sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2])
    rw [div_le_iff₀ hsin]
    calc ‖t (π / 2 - u)‖ ^ 2 = π / 2 * (‖t (π / 2 - u)‖ ^ 2 / u) * (2 / π * u) := by
          field_simp
      _ ≤ π / 2 * (‖t (π / 2 - u)‖ ^ 2 / u) * sin u :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (by positivity)
            (div_nonneg (by positivity) hu.1.le))
  have hleft : ∫⁻ a in Ioo (-(π / 2)) 0, ENNReal.ofReal (‖t a‖ ^ 2 / cos a) ≤
      ENNReal.ofReal (π / 2) *
        ∫⁻ u in Ioo 0 (π / 2), ENNReal.ofReal (‖t (u + -(π / 2))‖ ^ 2 / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [show (Ioo 0 (π / 2) : Set ℝ) = Ioo (-(π / 2) - -(π / 2)) (0 - -(π / 2)) by
      congr 1 <;> ring]
    rw [← setLIntegral_Ioo_comp_add_right
      (fun a ↦ ENNReal.ofReal (‖t a‖ ^ 2 / cos a)) (-(π / 2)) (-(π / 2)) 0]
    refine setLIntegral_mono' measurableSet_Ioo fun u hu ↦ ?_
    have hu' : u ∈ Ioo 0 (π / 2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hu0 : u ≠ 0 := hu'.1.ne'
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := mul_le_sin hu'.1.le hu'.2.le
    rw [show u + -(π / 2) = -(π / 2 - u) by ring, cos_neg, cos_pi_div_two_sub]
    have hsin : 0 < sin u := sin_pos_of_pos_of_lt_pi hu'.1 (by linarith [hu'.2])
    rw [div_le_iff₀ hsin, show -(π / 2 - u) = u + -(π / 2) by ring]
    calc ‖t (u + -(π / 2))‖ ^ 2 = π / 2 * (‖t (u + -(π / 2))‖ ^ 2 / u) * (2 / π * u) := by
          field_simp
      _ ≤ π / 2 * (‖t (u + -(π / 2))‖ ^ 2 / u) * sin u :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (by positivity)
            (div_nonneg (by positivity) hu'.1.le))
  -- Assemble: `(-π/2, π/2) ⊆ (-π/2, 0) ∪ [0, π/2)`, and `[0, π/2) = (0, π/2)` a.e.
  have hsplit : Ioo (-(π / 2)) (π / 2) ⊆ Ioo (-(π / 2)) 0 ∪ Ico 0 (π / 2) := fun a ha ↦ by
    rcases lt_or_ge a 0 with h | h
    · exact Or.inl ⟨ha.1, h⟩
    · exact Or.inr ⟨h, ha.2⟩
  refine lt_of_le_of_lt ((lintegral_mono_set hsplit).trans (lintegral_union_le _ _ _)) ?_
  rw [setLIntegral_congr Ioo_ae_eq_Ico.symm]
  exact ENNReal.add_lt_top.2
    ⟨lt_of_le_of_lt hleft (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL),
      lt_of_le_of_lt hright (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR)⟩

/-- The energy of the arc traces (`lem:ee-arc-energy`): for `ψ` even under both reflections,
    `∫ cosh² s |g_k'(s)|² ds < ∞` on each arc, with `g_k = ψ̃ ∘ γ_k`. For `k = 0` this is
    `lintegral_arc_energy_eq` and `lintegral_arcTrace_lt_top`; the other arcs are the arc
    `γ₀` for the rotated vorticity, which is again even under both reflections. -/
theorem ee_arc_energy {ω : L2} (hω : InSector true true ω) :
    ∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2 := by
  intro k _
  have hcomp : contStream ω ∘ cellArc k = contStream (rotate^[k] ω) ∘ separatrixArc := by
    funext s
    simp only [Function.comp_apply, cellArc, contStream_iterate_rotate]
  rw [hcomp]
  have hm : Measurable fun s ↦
      Real.cosh s ^ 2 * ‖deriv (contStream (rotate^[k] ω) ∘ separatrixArc) s‖ ^ 2 := by
    have := measurable_deriv (contStream (rotate^[k] ω) ∘ separatrixArc)
    fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s ↦ by positivity),
    lintegral_arc_energy_eq (inSector_iterate_rotate hω k)]
  exact lintegral_arcTrace_lt_top (inSector_iterate_rotate hω k)

/-! ### A dominating function on the quarter orbits -/

/-- The flow-time weight is at most `2 / cos a` near the corners, and everywhere on the quarter
    orbit once `h ≤ 1/4`. -/
theorem one_div_sqrt_cos_sq_sub_le_two_div {h a : ℝ} (h0 : 0 ≤ h) (hc : 0 < cos a)
    (hh : h ≤ cos a ^ 2) (hcase : 1 / 2 ≤ |sin a| ∨ h ≤ 1 / 4) :
    1 / √(cos a ^ 2 - h ^ 2) ≤ 2 / cos a := by
  by_cases hs : 1 / 2 ≤ |sin a|
  · exact one_div_sqrt_cos_sq_sub_le_corner h0 hc hh hs
  have h4 : h ≤ 1 / 4 := hcase.resolve_left hs
  replace hs := not_le.1 hs
  have hs2 : sin a ^ 2 < 1 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (sin a)]
  have hc2 : 3 / 4 < cos a ^ 2 := by nlinarith [sin_sq_add_cos_sq a]
  have hle : (cos a / 2) ^ 2 ≤ cos a ^ 2 - h ^ 2 := by nlinarith
  have hsq : cos a / 2 ≤ √(cos a ^ 2 - h ^ 2) := Real.le_sqrt_of_sq_le hle
  have hpos : 0 < √(cos a ^ 2 - h ^ 2) := lt_of_lt_of_le (by positivity) hsq
  rw [div_le_div_iff₀ hpos hc]
  linarith

/-- A dominating function on the quarter orbits (`lem:ee-quarter-bound`). For line
    representatives `Gx, Gy` of `ψₓ, ψ_y` there is `Φ` with `∫_{-π/2}^{π/2} Φ < ∞` such that, for
    `h ∈ (0, 1)` and almost every `a` on the quarter orbit `|a| < arccos √h` with
    `|sin a| ≥ 1/2` or `h ≤ 1/4`, `(|ψₙ|² + |ψₜ|²)(a, β_h(a)) / √(cos² a - h²) ≤ Φ(a)`.
    Here `Φ = 4 ((π/2)(K_x + K_y) + |f'|² / (2 cos a))`, with `K` the line energies of
    `∂_b Gx, ∂_b Gy` and `f(a) = ψ̃(a, π/2)`: by `|ψₙ|² + |ψₜ|² = |Gx|² + |Gy|²`, the
    splitting `|G(β)|² ≤ 2 |G(β) - G(π/2)|² + 2 |G(π/2)|²`, the segment estimate with
    `(π/2 - β_h)/cos a ≤ π/2`, and the arc traces. -/
theorem ee_quarter_bound {ω : L2} (hω : InSector true true ω)
    {Gx Gy Gxb Gyb : ℝ × ℝ → ℂ} (hx : IsLineRep (-π) π 0 π (streamLiftX ω) Gx Gxb)
    (hy : IsLineRep (-π) π 0 π (streamLiftY ω) Gy Gyb) :
    ∃ Φ : ℝ → ℝ≥0∞, Measurable Φ ∧ ∫⁻ a in Ioo (-(π / 2)) (π / 2), Φ a < ∞ ∧
      ∀ h ∈ Ioo (0 : ℝ) 1, ∀ᵐ a ∂(volume.restrict (Ioo (-arccos √h) (arccos √h))),
        (1 / 2 ≤ |sin a| ∨ h ≤ 1 / 4) →
        ENNReal.ofReal ((‖normalDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2 +
          ‖tangentDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2) /
            √(cos a ^ 2 - h ^ 2)) ≤ Φ a := by
  have hπ := Real.pi_pos
  obtain ⟨hodd, hder, -⟩ := ee_arc_trace_identification hω hx hy
  set f : ℝ → ℂ := fun a ↦ contStream ω (diagInv (a, π / 2)) with hf
  set I : Set ℝ := Ioo (-π) π with hI
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  have hAI : A ⊆ I := Ioo_subset_Ioo (by linarith) (by linarith)
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
  have hCfin : ∫⁻ a in A, C a < ∞ := by
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioo fun a ha ↦ ?_)
      (lintegral_arcTrace_lt_top hω)
    have hc := cos_pos_of_mem_Ioo ha
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hc ?_)
    linarith
  have hKfin : ∫⁻ a in A, (Kx a + Ky a) < ∞ := by
    rw [lintegral_add_left hKxm]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (lintegral_mono_set hAI) hx.lintegral_lt_top,
      lt_of_le_of_lt (lintegral_mono_set hAI) hy.lintegral_lt_top⟩
  refine ⟨Φ, by fun_prop, ?_, fun h hh ↦ ?_⟩
  · rw [hΦ, lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin, hCfin⟩)
  -- The quarter orbit for `h`.
  have h0 := hh.1
  have hsq0 : 0 < √h := Real.sqrt_pos.2 h0
  have hhsq : h ≤ √h := by
    have := Real.mul_self_sqrt h0.le
    nlinarith [hh.2]
  have hah : arccos √h < π / 2 := Real.arccos_lt_pi_div_two.2 hsq0
  set S : Set ℝ := Ioo (-arccos √h) (arccos √h) with hS
  have hSm : MeasurableSet S := measurableSet_Ioo
  have hSA : S ⊆ A := Ioo_subset_Ioo (by linarith) hah.le
  have hSI : S ⊆ I := hSA.trans hAI
  set β : ℝ → ℝ := quarterHeight h with hβdef
  set w : ℝ → ℝ := fun a ↦ 1 / cos a with hwdef
  have hcS (a : ℝ) (ha : a ∈ S) : √h < cos a :=
    sqrt_lt_cos_of_abs_lt_arccos hh (abs_lt.2 ⟨ha.1, ha.2⟩)
  have hβ (a : ℝ) (ha : a ∈ S) : β a ∈ Ioo 0 π ∧ w a * |β a - π / 2| ≤ π / 2 := by
    have hc := hcS a ha
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
  have hw0 (a : ℝ) (ha : a ∈ S) : 0 ≤ w a := one_div_nonneg.2 (hsq0.trans (hcS a ha)).le
  have hsegx := ae_segment_le (G := fun q ↦ Gx (diagInv q)) (Gb := fun q ↦ Gxb (diagInv q))
    (hx.2.1.comp diagInv.continuous.measurable) hSm hJ2 (fun a ha ↦ (hβ a ha).1) hw0
    (ae_restrict_of_ae_restrict_of_subset hSI hx.2.2.2)
  have hsegy := ae_segment_le (G := fun q ↦ Gy (diagInv q)) (Gb := fun q ↦ Gyb (diagInv q))
    (hy.2.1.comp diagInv.continuous.measurable) hSm hJ2 (fun a ha ↦ (hβ a ha).1) hw0
    (ae_restrict_of_ae_restrict_of_subset hSI hy.2.2.2)
  filter_upwards [hsegx, hsegy, ae_restrict_of_ae_restrict_of_subset hSI hodd,
    ae_restrict_of_ae_restrict_of_subset hSI hder, ae_restrict_mem hSm]
    with a hsx hsy h12 h3 ha hcase
  have h1 := h12.1
  have hc := hcS a ha
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
  have hwt := one_div_sqrt_cos_sq_sub_le_two_div h0.le hc0 hhc2 hcase
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

/-! ### Corner tails -/

/-- Corner tails (`lem:ee-corner-tails`). Let `ψ` be even under both reflections and let
    `Gx, Gy` be line representatives of `ψₓ, ψ_y` near the arc. Then the parts of the quarter
    integrals of `|ψₙ|² + |ψₜ|²` over `|a| > π/2 - δ` (in the diagonal form of
    `lem:quarter-orbit-diagonal`) are small for small `δ`, uniformly in `h ∈ (0, 1)`: they are
    bounded by the integral of the dominating function of `ee_quarter_bound` over
    `π/2 - δ < |a| < π/2`, a set of measure `2δ`. -/
theorem ee_corner_tails {ω : L2} (hω : InSector true true ω)
    {Gx Gy Gxb Gyb : ℝ × ℝ → ℂ} (hx : IsLineRep (-π) π 0 π (streamLiftX ω) Gx Gxb)
    (hy : IsLineRep (-π) π 0 π (streamLiftY ω) Gy Gyb) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) 1,
      ∫⁻ a in {a | π / 2 - δ < |a|} ∩ Ioo (-arccos √h) (arccos √h),
        ENNReal.ofReal ((‖normalDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2 +
          ‖tangentDeriv Gx Gy (diagInv (a, quarterHeight h a))‖ ^ 2) / √(cos a ^ 2 - h ^ 2)) <
        ε := by
  have hπ := Real.pi_pos
  obtain ⟨Φ, -, hΦfin, hΦ⟩ := ee_quarter_bound hω hx hy
  set A : Set ℝ := Ioo (-(π / 2)) (π / 2) with hA
  obtain ⟨η, hη, hηε⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := volume.restrict A)
    hΦfin.ne hε.ne'
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
  have hsq0 : 0 < √h := Real.sqrt_pos.2 hh.1
  have hah : arccos √h < π / 2 := Real.arccos_lt_pi_div_two.2 hsq0
  set S : Set ℝ := {a | π / 2 - δ < |a|} ∩ Ioo (-arccos √h) (arccos √h) with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter measurableSet_Ioo
  have hST : S ⊆ T := fun a ha ↦ ⟨ha.1, by linarith [ha.2.1], by linarith [ha.2.2]⟩
  refine lt_of_le_of_lt ?_ hTint
  refine (setLIntegral_mono_ae' hSm ?_).trans (lintegral_mono_set hST)
  have hb := hΦ h hh
  rw [ae_restrict_iff' measurableSet_Ioo] at hb
  filter_upwards [hb] with a ha haS
  refine ha haS.2 (Or.inl ?_)
  -- Near the corners `|a| > π/2 - δ ≥ π/3`, so `|sin a| ≥ 1/2`.
  have h1 : |a| < π / 2 := lt_of_lt_of_le (abs_lt.2 ⟨haS.2.1, haS.2.2⟩) hah.le
  have h2 : cos |a| ≤ cos (π / 3) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith)
      (by linarith [show π / 2 - δ < |a| from haS.1])
  rw [Real.cos_abs, Real.cos_pi_div_three] at h2
  have h3 := sin_sq_add_cos_sq a
  have h4 : 0 ≤ cos a := by
    rw [← Real.cos_abs]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg a], h1.le⟩
  have h5 : (1 / 2 : ℝ) ^ 2 ≤ |sin a| ^ 2 := by rw [sq_abs]; nlinarith
  nlinarith [abs_nonneg (sin a)]

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

end NoEmbeddedEigenvalues
