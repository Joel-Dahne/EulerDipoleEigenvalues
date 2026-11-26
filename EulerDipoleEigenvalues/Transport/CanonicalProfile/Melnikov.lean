module

public import EulerDipoleEigenvalues.Transport.ResonantVanishing
public import EulerDipoleEigenvalues.EvenEven.TraceExclusion.LevelTraces
public import EulerDipoleEigenvalues.Transport.PeriodicComparison.TransportODE
public import EulerDipoleEigenvalues.Analysis.TorusSobolev.SobolevHolder
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalToGlobal

/-!
# The Melnikov condition

Blueprint: `lem:melnikov`; also the Melnikov component of `lem:ee-transport-traces`.
The pairing limit and full eigenfunction transport-trace assembly are in `PairingLimit.lean`.

Let `(v, f)` be a transport pair near the closed cell with rotation character `κ` and `f`
continuous, and let `g = f ∘ γ` be its trace on the separatrix arc. Then `g' ∈ L¹` and
`∫ g' e^{-iλs} ds = 0`.

* The arc is the segment `b = π/2` in diagonal coordinates, so `g` is a straight-line trace
  after the change of variable `a = arcAngle s - π/2`, with `da = ds / cosh s`.
* At a resonant level `kb(h) = λ` with `e^{iπk/2} = κ`, resonant vanishing and the rotation
  character give `∫_{-L}^{L} e^{-iλt} f(γ_h(t)) dt = 0`. Orbit comparison and Hölder
  continuity of `f` near the arc make this close to the same integral of `g`.
* Integration by parts is done only on `g`; the boundary term tends to
  `e^{iλL}(κ c₊ - c₋) = 0`.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real MeasureTheory Filter Topology Set Complex
open scoped ENNReal Interval

/-! ### The separatrix segment and the arc trace -/

section ArcTrace

/-- The closed separatrix segment `b = π/2`, `|a| ≤ π/2`, joining the saddles `(π, 0)` and
`(0, -π)`. -/
def arcSegment : Set (ℝ × ℝ) := diagInv '' (Icc (-(π / 2)) (π / 2) ×ˢ {π / 2})

theorem isCompact_arcSegment : IsCompact arcSegment :=
  (isCompact_Icc.prod isCompact_singleton).image diagInv.continuous

theorem arcSegment_subset_closure_cellSquare : arcSegment ⊆ closure cellSquare := by
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  have hb' : b = π / 2 := hb
  have hc : Continuous fun t : ℝ ↦ diagInv (t * a, t * b) := by fun_prop
  refine mem_closure_of_tendsto (f := fun t : ℝ ↦ diagInv (t * a, t * b)) (b := 𝓝[<] 1) ?_ ?_
  · simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hpi := pi_pos
    change |(diagCoord (diagInv (t * a, t * b))).1| < π / 2 ∧
      |(diagCoord (diagInv (t * a, t * b))).2| < π / 2
    rw [diagCoord_diagInv]
    have ha' : |a| ≤ π / 2 := abs_le.2 ⟨ha.1, ha.2⟩
    constructor
    · change |t * a| < π / 2
      rw [abs_mul, abs_of_pos ht.1]
      nlinarith [ht.2, abs_nonneg a, mul_le_mul_of_nonneg_left ha' ht.1.le]
    · change |t * b| < π / 2
      rw [abs_mul, abs_of_pos ht.1, hb', abs_of_pos (by linarith : (0 : ℝ) < π / 2)]
      nlinarith [ht.2]

theorem separatrixArc_eq (s : ℝ) : separatrixArc s = diagInv (arcAngle s - π / 2, π / 2) := by
  simp only [separatrixArc, diagInv_apply]
  congr 1 <;> ring

theorem separatrixArc_mem_arcSegment (s : ℝ) : separatrixArc s ∈ arcSegment := by
  have := arcAngle_mem_Ioo s
  exact ⟨(arcAngle s - π / 2, π / 2), ⟨⟨by linarith [this.1], by linarith [this.2]⟩, rfl⟩,
    (separatrixArc_eq s).symm⟩

theorem saddle_neg_mem_arcSegment : ((π, 0) : ℝ × ℝ) ∈ arcSegment :=
  ⟨(π / 2, π / 2), ⟨⟨by linarith [pi_pos], le_rfl⟩, rfl⟩, by simp⟩

theorem saddle_pos_mem_arcSegment : ((0, -π) : ℝ × ℝ) ∈ arcSegment :=
  ⟨(-(π / 2), π / 2), ⟨⟨le_rfl, by linarith [pi_pos]⟩, rfl⟩, by
    simp only [diagInv_apply]; congr 1 <;> ring⟩

/-- A diagonal rectangle around the segment inside an open neighbourhood of it. -/
theorem exists_diagRect_subset {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hK : arcSegment ⊆ U) :
    ∃ ε > 0, diagRect (Ioo (-(π / 2) - ε) (π / 2 + ε)) (Ioo (π / 2 - ε) (π / 2 + ε)) ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_arcSegment.exists_thickening_subset_open hU hK
  refine ⟨δ / 2, by positivity, fun p hp ↦ hsub ?_⟩
  obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hp
  set a := (diagCoord p).1
  set b := (diagCoord p).2
  set a' := max (-(π / 2)) (min (π / 2) a)
  have ha' : a' ∈ Icc (-(π / 2)) (π / 2) := ⟨le_max_left _ _, max_le (by linarith [pi_pos])
    (min_le_left _ _)⟩
  have hq : diagInv (a', π / 2) ∈ arcSegment := ⟨(a', π / 2), ⟨ha', rfl⟩, rfl⟩
  have hda : |a - a'| < δ / 2 := by
    rw [abs_lt]
    constructor
    · simp only [a']
      rcases le_total (π / 2) a with h | h
      · rw [min_eq_left h, max_eq_right (by linarith [pi_pos])]; linarith
      · rw [min_eq_right h]
        rcases le_total (-(π / 2)) a with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith
    · simp only [a']
      rcases le_total (π / 2) a with h | h
      · rw [min_eq_left h, max_eq_right (by linarith [pi_pos])]; linarith
      · rw [min_eq_right h]
        rcases le_total (-(π / 2)) a with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith
  have hdb : |b - π / 2| < δ / 2 := by rw [abs_lt]; constructor <;> linarith
  have hp : p = diagInv (a, b) := by
    ext <;> simp only [a, b, diagCoord, diagInv_apply] <;> ring
  rw [Metric.mem_thickening_iff]
  refine ⟨_, hq, ?_⟩
  rw [hp, Prod.dist_eq, diagInv_apply, diagInv_apply, Real.dist_eq, Real.dist_eq]
  refine max_lt ?_ ?_
  · calc |a + b - (a' + π / 2)| ≤ |a - a'| + |b - π / 2| := by
          rw [show a + b - (a' + π / 2) = (a - a') + (b - π / 2) by ring]; exact abs_add_le _ _
      _ < δ := by linarith
  · calc |a - b - (a' - π / 2)| ≤ |a - a'| + |b - π / 2| := by
          rw [show a - b - (a' - π / 2) = (a - a') - (b - π / 2) by ring]; exact abs_sub _ _
      _ < δ := by linarith

theorem injective_arcAngle : Function.Injective arcAngle := by
  intro s t h
  simp only [arcAngle, mul_eq_mul_left_iff, two_ne_zero, or_false] at h
  have := arctan_strictMono.injective h
  simpa using Real.exp_injective this

/-- The trace of a continuous `H²` function on the separatrix arc is locally absolutely
continuous, differentiable almost everywhere, and has integrable derivative: after
`a = arcAngle s - π/2` it is the straight-line trace on `b = π/2`, and `da = ds / cosh s`. -/
theorem arcTrace_regularity {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hK : arcSegment ⊆ U)
    {f : ℝ × ℝ → ℂ} (hfc : ContinuousOn f U) (hf : MemSobolevOn 2 U f) :
    (∀ c d, AbsolutelyContinuousOnInterval (f ∘ separatrixArc) c d) ∧
    (∀ᵐ s, DifferentiableAt ℝ (f ∘ separatrixArc) s) ∧
    Integrable (deriv (f ∘ separatrixArc)) := by
  obtain ⟨ε, hε, hQ⟩ := exists_diagRect_subset hUo hK
  have hpi := pi_pos
  obtain ⟨Fx, hx, -⟩ := hf.2 0
  obtain ⟨Fy, hy, -⟩ := hf.2 1
  obtain ⟨H, -, -, hac, hder, hmem⟩ := absolutelyContinuous_trace_of_H2 hUo
    (a₀ := -(π / 2) - ε) (a₁ := π / 2 + ε) (b₁ := π / 2 - ε) (b₂ := π / 2 + ε) (b₀ := π / 2)
    (by linarith) hQ ⟨by linarith, by linarith⟩ hfc hf hx hy
  set G : ℝ → ℂ := fun a ↦ f (diagInv (a, π / 2))
  set D : ℝ → ℂ := fun a ↦ H (diagInv (a, π / 2))
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - π / 2
  have hcomp : f ∘ separatrixArc = G ∘ φ := by
    funext s
    simp only [Function.comp_apply, G, φ, separatrixArc_eq]
  have hφa : Antitone φ := fun s t hst ↦ by simpa [φ] using antitone_arcAngle hst
  have hφL : LipschitzWith 1 φ := LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa [φ, Real.dist_eq] using lipschitzWith_arcAngle.dist_le_mul x y
  have hφr (s : ℝ) : φ s ∈ Ioo (-(π / 2)) (π / 2) := by
    have := arcAngle_mem_Ioo s
    exact ⟨by simp only [φ]; linarith [this.1], by simp only [φ]; linarith [this.2]⟩
  have hφr' (s : ℝ) : φ s ∈ Ioo (-(π / 2) - ε) (π / 2 + ε) :=
    ⟨by linarith [(hφr s).1], by linarith [(hφr s).2]⟩
  have hφd (s : ℝ) : HasDerivAt φ (-(1 / Real.cosh s)) s := (hasDerivAt_arcAngle s).sub_const _
  -- Absolute continuity.
  have hacs (c d : ℝ) : AbsolutelyContinuousOnInterval (f ∘ separatrixArc) c d := by
    rw [hcomp]
    have hle : φ (max c d) ≤ φ (min c d) := hφa min_le_max
    refine AbsolutelyContinuousOnInterval.comp_antitoneOn
      (hac _ _ (hφr' _).1 hle (hφr' _).2) hφL.lipschitzOnWith (hφa.antitoneOn _) fun s hs ↦ ?_
    rw [uIcc_of_le hle]
    exact ⟨hφa hs.2, hφa hs.1⟩
  -- The derivative almost everywhere.
  have hderφ : ∀ᵐ s, HasDerivAt (f ∘ separatrixArc) ((-(1 / Real.cosh s)) • D (φ s)) s := by
    have h1 : ∀ᵐ a ∂(volume.restrict (Ioo (-(π / 2)) (π / 2))), HasDerivAt G (D a) a :=
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo (by linarith) (by linarith)) hder
    filter_upwards [ae_comp_arcAngle h1] with s hs
    rw [hcomp]
    exact hs.scomp s (hφd s)
  refine ⟨hacs, hderφ.mono fun s hs ↦ hs.differentiableAt, ?_⟩
  have hae : deriv (f ∘ separatrixArc) =ᵐ[volume] fun s ↦ (-(1 / Real.cosh s)) • D (φ s) :=
    hderφ.mono fun s hs ↦ hs.deriv
  refine ⟨(measurable_deriv _).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr_ae (hae.mono fun s hs ↦ by rw [hs])]
  -- Change of variables `a = φ(s)`.
  have hφi : Function.Injective φ := fun s t h ↦ injective_arcAngle (by simpa [φ] using h)
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun s _ ↦ (hφd s).hasDerivWithinAt) hφi.injOn (fun a ↦ ‖D a‖ₑ)
  have hfin : ∫⁻ a in Ioo (-(π / 2) - ε) (π / 2 + ε), ‖D a‖ₑ < ⊤ := by
    have : IsFiniteMeasure (volume.restrict (Ioo (-(π / 2) - ε) (π / 2 + ε))) :=
      isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
    exact (memLp_one_iff_integrable.1 (hmem.mono_exponent (by norm_num))).2
  calc ∫⁻ s, ‖(-(1 / Real.cosh s)) • D (φ s)‖ₑ
      = ∫⁻ s in univ, ENNReal.ofReal |-(1 / Real.cosh s)| * ‖D (φ s)‖ₑ := by
        rw [setLIntegral_univ]
        congr 1
        funext s
        rw [eNorm_smul, Real.eNorm_eq_ofReal_abs]
    _ = ∫⁻ a in φ '' univ, ‖D a‖ₑ := hcv.symm
    _ ≤ ∫⁻ a in Ioo (-(π / 2) - ε) (π / 2 + ε), ‖D a‖ₑ :=
        lintegral_mono_set (image_subset_iff.2 fun s _ ↦ hφr' s)
    _ < ⊤ := hfin

end ArcTrace

/-! ### Hölder continuity near the separatrix segment -/

section Holder

/-- The covering map does not increase distances. -/
theorem dist_torusProj_le (p q : ℝ × ℝ) : dist (torusProj p) (torusProj q) ≤ dist p q := by
  have h (x y : ℝ) : dist (x : Real.Angle) (y : Real.Angle) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← Real.Angle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le_max (h _ _) (h _ _)

/-- A neighbourhood of the segment of width less than `π` projects injectively to the torus. -/
theorem injOn_torusProj_thickening {δ : ℝ} (hδ : δ ≤ 1) :
    InjOn torusProj (Metric.thickening δ arcSegment) := by
  have hbound {p : ℝ × ℝ} (hp : p ∈ Metric.thickening δ arcSegment) :
      -1 < p.1 ∧ p.1 < π + 1 ∧ -π - 1 < p.2 ∧ p.2 < 1 := by
    obtain ⟨_, ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hd⟩ := Metric.mem_thickening_iff.1 hp
    have hb' : b = π / 2 := hb
    rw [Prod.dist_eq, diagInv_apply, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt,
      abs_lt] at hd
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hd
    subst hb'
    exact ⟨by linarith [ha.1], by linarith [ha.2], by linarith [ha.1], by linarith [ha.2]⟩
  have hcoord {x y : ℝ} (hxy : (x : Real.Angle) = y) (h : |x - y| < 2 * π) : x = y := by
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hxy
    have hm0 : m = 0 := by
      have h' : |(m : ℝ)| * (2 * π) < 1 * (2 * π) := by
        rw [one_mul, ← abs_of_pos two_pi_pos, ← abs_mul, abs_of_pos two_pi_pos, mul_comm, ← hm]
        exact h
      have h1 : |(m : ℝ)| < 1 := lt_of_mul_lt_mul_right h' two_pi_pos.le
      have h2 : |m| < 1 := by exact_mod_cast h1
      exact Int.abs_lt_one_iff.1 h2
    rw [hm0] at hm
    simp at hm
    linarith
  intro p hp q hq hpq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hbound hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hbound hq
  have hpi := Real.two_le_pi
  obtain ⟨e1, e2⟩ := Prod.mk.inj hpq
  exact Prod.ext (hcoord e1 (by rw [abs_lt]; constructor <;> linarith))
    (hcoord e2 (by rw [abs_lt]; constructor <;> linarith))

/-- A continuous `H²` function on a neighbourhood of the separatrix segment is Hölder continuous
near it, with any exponent `α < 1`: cut it off, periodize it to the torus and use the torus
embedding. -/
theorem exists_holder_near_arcSegment {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hK : arcSegment ⊆ U)
    {f : ℝ × ℝ → ℂ} (hfc : ContinuousOn f U) (hf : MemSobolevOn 2 U f) {α : NNReal}
    (hα0 : 0 < α) (hα : α < 1) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Metric.thickening ρ arcSegment,
      ∀ q ∈ Metric.thickening ρ arcSegment, ‖f p - f q‖ ≤ C * dist p q ^ (α : ℝ) := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_arcSegment.exists_thickening_subset_open hUo hK
  set δ₀ := min δ 1
  have hδ₀ : 0 < δ₀ := lt_min hδ one_pos
  set V := Metric.thickening δ₀ arcSegment
  have hVo : IsOpen V := Metric.isOpen_thickening
  have hVU : V ⊆ U := (Metric.thickening_mono (min_le_left _ _) _).trans hsub
  have hinj : InjOn torusProj V := injOn_torusProj_thickening (min_le_right _ _)
  -- A cutoff equal to `1` on the `δ₀/2`-neighbourhood.
  set V₂ := Metric.thickening (3 * δ₀ / 4) arcSegment
  set C₁ := Metric.cthickening (δ₀ / 2) arcSegment
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (s := V₂) (t := C₁) Metric.isOpen_thickening Metric.isClosed_cthickening
    (Metric.cthickening_subset_thickening' (by positivity) (by linarith) _)
  have hts : tsupport θ ⊆ Metric.cthickening (3 * δ₀ / 4) arcSegment := by
    rw [tsupport, hθs]
    exact Metric.closure_thickening_subset_cthickening _ _
  have hχ : IsTestFunctionOn V (fun p ↦ (θ p : ℂ)) := by
    refine ⟨ofRealCLM.contDiff.comp hθ, ?_, ?_⟩
    · refine (isCompact_arcSegment.cthickening (r := 3 * δ₀ / 4)).of_isClosed_subset
        (isClosed_tsupport _) ((tsupport_comp_subset ofReal_zero θ).trans hts)
    · exact (tsupport_comp_subset ofReal_zero θ).trans (hts.trans
        (Metric.cthickening_subset_thickening' hδ₀ (by linarith) _))
  have hloc : MemSobolevLocOn 2 V f := fun V' _ _ hV' ↦
    hf.mono (subset_closure.trans (hV'.trans hVU))
  obtain ⟨g, hg2, hgeq, -⟩ := exists_memSobolev_periodize hVo hinj hloc hχ
  obtain ⟨Ch, hCh⟩ := exists_holderWith_of_memSobolev_two hα
  obtain ⟨u, hgu, hu, -⟩ := hCh g hg2
  -- `θ f = u ∘ π` on `V`.
  have hEq : EqOn (fun p ↦ (θ p : ℂ) * f p) (fun p ↦ u (torusProj p)) V := by
    have hae : (fun p ↦ (θ p : ℂ) * f p) =ᵐ[volume.restrict V] fun p ↦ u (torusProj p) := by
      filter_upwards [hgeq, ae_restrict_of_ae (ae_torusProj hgu)] with p h1 h2
      rw [← h1, ← h2]
      rfl
    refine Measure.eqOn_open_of_ae_eq hae hVo ?_ ?_
    · exact (continuous_ofReal.comp hθ.continuous).continuousOn.mul (hfc.mono hVU)
    · exact ((hu.continuous hα0).comp isOpenQuotientMap_torusProj.continuous).continuousOn
  refine ⟨δ₀ / 2, by positivity, Ch * Real.toNNReal √(sobolevNormSq 2 g), by positivity,
    fun p hp q hq ↦ ?_⟩
  have hW (x : ℝ × ℝ) (hx : x ∈ Metric.thickening (δ₀ / 2) arcSegment) :
      f x = u (torusProj x) := by
    have hxC : x ∈ C₁ := Metric.thickening_subset_cthickening _ _ hx
    have hxV : x ∈ V := Metric.thickening_mono (by linarith) _ hx
    have h := hEq hxV
    simp only [(hθ1 x).1 hxC, ofReal_one, one_mul] at h
    exact h
  rw [hW p hp, hW q hq, ← dist_eq_norm]
  refine (hu.dist_le _ _).trans ?_
  push_cast
  gcongr
  exact dist_torusProj_le p q

end Holder

/-! ### Resonant levels -/

section Resonant

/-- Arbitrarily close to the separatrix there are resonant levels in every
residue class of the absolute angular mode modulo four. -/
theorem exists_resonant_level_index {lam : ℝ} (hlam : lam ≠ 0) (r : ℕ)
    {η : ℝ} (hη : 0 < η) :
    let σ : ℤ := if 0 < lam then 1 else -1
    ∃ h, 0 < h ∧ h < η ∧ h < 1 ∧ ∃ k : ℤ, (k : ℝ) * orbitFrequency h = lam ∧
      Complex.exp (-(2 * I * lam * eighthPeriod h)) =
        Complex.exp (-(I * ((σ * π * r / 2 : ℝ) : ℂ))) := by
  let σ : ℤ := if 0 < lam then 1 else -1
  have hpi := pi_pos
  set η' := min η (1 / 2) / 2
  have hη'0 : 0 < η' := by positivity
  have hη'η : η' < η := by have := min_le_left η (1 / 2); simp only [η']; linarith
  have hη'1 : η' < 1 := by have := min_le_right η (1 / 2); simp only [η']; linarith
  set μ := |lam|
  have hμ : 0 < μ := abs_pos.2 hlam
  obtain ⟨m, hm⟩ := exists_nat_gt (orbitPeriod η' * μ / (8 * π))
  set n : ℕ := 4 * (m + 1) + r
  have hn : (4 * ((m : ℝ) + 1)) ≤ n := by
    simp only [n]; push_cast; linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
  set T := 2 * π * n / μ
  have hT : orbitPeriod η' ≤ T := by
    have h1 : orbitPeriod η' * μ < 8 * π * m := by
      rwa [div_lt_iff₀ (by positivity), mul_comm (m : ℝ)] at hm
    simp only [T]
    rw [le_div_iff₀ hμ]
    nlinarith
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), T ≤ orbitPeriod h ∧ h < η' :=
    (tendsto_orbitPeriod_atTop.eventually_ge_atTop T).and
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hη'0) fun h hh ↦ hh.2)
  obtain ⟨h', ⟨hT', hh'⟩, hh'0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hh'0' : (0 : ℝ) < h' := hh'0
  have hsub : Icc h' η' ⊆ Ioo 0 1 := fun x hx ↦ ⟨hh'0'.trans_le hx.1, hx.2.trans_lt hη'1⟩
  obtain ⟨h, hhI, hhT⟩ := intermediate_value_Icc' hh'.le
    (continuousOn_orbitPeriod.mono hsub) ⟨hT, hT'⟩
  refine ⟨h, hh'0'.trans_le hhI.1, hhI.2.trans_lt hη'η, hhI.2.trans_lt hη'1, ?_⟩
  have hσμ : lam = σ * μ := by
    simp only [σ, μ]
    split_ifs with h
    · simp [abs_of_pos h]
    · push_cast; rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hlam)]; ring
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  refine ⟨σ * n, ?_, ?_⟩
  · simp only [orbitFrequency, hhT, T]
    push_cast
    rw [hσμ]
    field_simp
  · have hL : eighthPeriod h = T / 8 := by
      have := hhT; unfold orbitPeriod at this; linarith
    have h2L : 2 * lam * eighthPeriod h = σ * π * n / 2 := by
      rw [hL, hσμ]
      simp only [T]
      field_simp
      linear_combination
    have hc : -(2 * I * (lam : ℂ) * (eighthPeriod h : ℂ)) =
        ((-(σ * (m + 1)) : ℤ) : ℂ) * (2 * π * I) + -(I * ((σ * π * r / 2 : ℝ) : ℂ)) := by
      have : ((2 * lam * eighthPeriod h : ℝ) : ℂ) = ((σ * π * n / 2 : ℝ) : ℂ) := by rw [h2L]
      push_cast at this ⊢
      simp only [n] at this
      push_cast at this
      linear_combination (-I) * this
    rw [hc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- Resonant levels whose backward quarter phase is the inverse of any of
the four quarter-rotation characters. -/
theorem exists_resonant_level_character {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ}
    (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I) {η : ℝ} (hη : 0 < η) :
    ∃ h, 0 < h ∧ h < η ∧ h < 1 ∧ ∃ k : ℤ, (k : ℝ) * orbitFrequency h = lam ∧
      Complex.exp (-(2 * I * lam * eighthPeriod h)) * κ = 1 := by
  have hphase (r : ℕ) (hr :
      Complex.exp (-(I * (((if 0 < lam then 1 else -1 : ℤ) * π * r / 2 : ℝ) : ℂ))) *
        κ = 1) :
      ∃ h, 0 < h ∧ h < η ∧ h < 1 ∧ ∃ k : ℤ, (k : ℝ) * orbitFrequency h = lam ∧
        Complex.exp (-(2 * I * lam * eighthPeriod h)) * κ = 1 := by
    obtain ⟨h, h0, hη', h1, k, hk, he⟩ := exists_resonant_level_index hlam r hη
    exact ⟨h, h0, hη', h1, k, hk, by rw [he]; exact hr⟩
  have hpow (r : ℕ) :
      exp (-(I * (((if 0 < lam then 1 else -1 : ℤ) * π * r / 2 : ℝ) : ℂ))) =
        (if 0 < lam then -I else I) ^ r := by
    by_cases h : 0 < lam
    · simp only [h, ite_true, Int.cast_one, one_mul]
      rw [← Complex.exp_neg_pi_div_two_mul_I, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    · simp only [h, ite_false, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      calc
        _ = exp ((r : ℂ) * (π / 2 * I)) := by
          congr 1
          push_cast
          ring
        _ = I ^ r := by rw [Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rcases hκ with rfl | rfl | rfl | rfl
  · exact hphase 0 (by rw [hpow]; simp)
  · apply hphase 2
    rw [hpow]
    split_ifs <;> simp [Complex.I_sq]
  · by_cases h : 0 < lam
    · apply hphase 1
      rw [hpow]
      simp [h, ← pow_two, Complex.I_sq]
    · apply hphase 3
      rw [hpow]
      simp [h, show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring,
        ← pow_two, Complex.I_sq]
  · by_cases h : 0 < lam
    · apply hphase 3
      rw [hpow]
      simp [h, show (-I) ^ 3 = I by rw [pow_succ, neg_sq, Complex.I_sq]; ring,
        ← pow_two, Complex.I_sq]
    · apply hphase 1
      rw [hpow]
      simp [h, ← pow_two, Complex.I_sq]

end Resonant

/-- Real-character specialization of the resonant-level lemma. -/
theorem exists_resonant_level {lam : ℝ} (hlam : lam ≠ 0) {κ : ℝ} (hκ : κ = 1 ∨ κ = -1)
    {η : ℝ} (hη : 0 < η) :
    ∃ h, 0 < h ∧ h < η ∧ h < 1 ∧ ∃ k : ℤ, (k : ℝ) * orbitFrequency h = lam ∧
      Complex.exp (-(2 * I * lam * eighthPeriod h)) = κ := by
  have hc : (κ : ℂ) = 1 ∨ (κ : ℂ) = -1 ∨ (κ : ℂ) = I ∨ (κ : ℂ) = -I := by
    rcases hκ with rfl | rfl <;> simp
  obtain ⟨h, h0, hη', h1, k, hk, he⟩ := exists_resonant_level_character hlam hc hη
  refine ⟨h, h0, hη', h1, k, hk, ?_⟩
  rcases hκ with rfl | rfl
  · simpa using he
  · simp only [ofReal_neg, ofReal_one, mul_neg, mul_one] at he
    simpa using congrArg Neg.neg he

/-! ### The resonant quarter integral -/

section Quarter

theorem rotLift_iterate_mem {U : Set (ℝ × ℝ)} (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U)
    {p : ℝ × ℝ} (hp : p ∈ U) (j : ℕ) : rotLift^[j] p ∈ U := by
  induction j with
  | zero => exact hp
  | succ j ih => rw [Function.iterate_succ_apply']; exact hUR _ ih

theorem apply_rotLift_iterate {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {κ : ℂ}
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    {p : ℝ × ℝ} (hp : p ∈ U) (j : ℕ) : f (rotLift^[j] p) = (κ : ℂ) ^ j * f p := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', rotLift, hfR _ (rotLift_iterate_mem hUR hp j), ih, pow_succ]
    ring

/-- At a resonant level with `e^{-2iλL} κ = 1`, the four quarters of the resonant mode are equal,
so resonant vanishing gives `∫_{-L}^{L} e^{-iλt} f(γ_h(t)) dt = 0`. -/
theorem integral_quarter_eq_zero_of_resonant {lam : ℝ} {κ : ℂ}
    {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U) {h : ℝ} (h0 : 0 < h) (h1 : h < 1) {k : ℤ}
    (hk : (k : ℝ) * orbitFrequency h = lam)
    (he : Complex.exp (-(2 * I * lam * eighthPeriod h)) * κ = 1) :
    ∫ t in (-eighthPeriod h)..eighthPeriod h,
      Complex.exp (-(I * lam * t)) * f (dipoleOrbit h t) = 0 := by
  set L := eighthPeriod h
  set φ : ℝ → ℂ := fun t : ℝ ↦ Complex.exp (-(I * lam * (t : ℂ))) * f (dipoleOrbit h t)
  have hcell (t : ℝ) : dipoleOrbit h t ∈ U :=
    hU (subset_closure (dipoleOrbit_mem_cellSquare h0 h1 t))
  have hγc : Continuous fun t ↦ dipoleOrbit h t := by
    have := continuous_dipoleOrbit.comp (Continuous.prodMk_right (X := ℝ) h)
    exact this
  have hφc : Continuous φ :=
    (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-(I * lam * (t : ℂ)))).mul
      (hfc.comp_continuous hγc hcell)
  have hshift (j : ℕ) (t : ℝ) : φ (t + j * (2 * L)) = φ t := by
    simp only [φ]
    rw [dipoleOrbit_add_mul_quarter h0 h1 j t, apply_rotLift_iterate hUR hfR (hcell t) j]
    have hexp : Complex.exp (-(I * lam * ((t + j * (2 * L) : ℝ) : ℂ))) =
        Complex.exp (-(I * lam * t)) * Complex.exp (-(2 * I * lam * L)) ^ j := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp, mul_assoc, ← mul_assoc (exp (-(2 * I * lam * L)) ^ j),
      ← mul_pow, he, one_pow, one_mul]
  have hS : orbitPeriod h = 4 * (2 * L) := by simp only [orbitPeriod, L]; ring
  have hper : Function.Periodic φ (orbitPeriod h) := fun t ↦ by
    rw [hS]
    exact_mod_cast hshift 4 t
  -- The resonant mode is the period integral of `φ`.
  have hmode : angularMode h k f = (orbitPeriod h : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..orbitPeriod h, φ t := by
    unfold angularMode
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [φ]
    have : ((k : ℝ) : ℂ) * (orbitFrequency h : ℂ) = (lam : ℂ) := by exact_mod_cast hk
    congr 2
    push_cast at this ⊢
    linear_combination (-(I * t)) * this
  -- The period integral is four quarter integrals.
  have hsum : ∫ t in (0 : ℝ)..orbitPeriod h, φ t = 4 * ∫ t in (-L)..L, φ t := by
    rw [← zero_add (orbitPeriod h), hper.intervalIntegral_add_eq 0 (-L)]
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ)
      (a := fun j : ℕ ↦ -L + j * (2 * L)) (n := 4) fun j _ ↦ hφc.intervalIntegrable _ _
    have hpiece (j : ℕ) : ∫ t in (-L + j * (2 * L))..(-L + (j + 1 : ℕ) * (2 * L)), φ t =
        ∫ t in (-L)..L, φ t := by
      have hc := intervalIntegral.integral_comp_add_right φ (j * (2 * L)) (a := -L) (b := L)
      rw [show -L + ((j + 1 : ℕ) : ℝ) * (2 * L) = L + j * (2 * L) by push_cast; ring, ← hc]
      congr 1
      funext t
      exact hshift j t
    simp only [hpiece, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hadj
    rw [hadj]
    congr 1
    · simp
    · rw [hS]
  have hA : orbitAnnulus (h / 2) ((h + 1) / 2) ⊆ U := fun p hp ↦ hU (subset_closure hp.1.1)
  have hres := (resonant_vanishing hp (h₁ := h / 2) (h₂ := (h + 1) / 2) (by linarith)
    (by linarith) (by linarith) hA).2.2 hfc k h ⟨by linarith, by linarith⟩ hk
  rw [hmode, hsum] at hres
  have hSne : (orbitPeriod h : ℂ) ≠ 0 := ofReal_ne_zero.2 (orbitPeriod_pos h0 h1).ne'
  simpa [hSne] using hres

end Quarter

/-! ### Integration by parts on the arc trace and a decay rate -/

section Parts

theorem continuous_of_absolutelyContinuous {g : ℝ → ℂ}
    (hac : ∀ c d, AbsolutelyContinuousOnInterval g c d) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have h := (hac (t - 1) (t + 1)).continuousOn
  rw [uIcc_of_le (by linarith)] at h
  exact h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- `∫_{-L}^{L} g' e^{-iλt} = [g e^{-iλt}]_{-L}^{L} + iλ ∫_{-L}^{L} g e^{-iλt}` for a locally
absolutely continuous `g` with integrable derivative. -/
theorem integral_deriv_mul_exp_eq {g : ℝ → ℂ}
    (hac : ∀ c d, AbsolutelyContinuousOnInterval g c d) (hdiff : ∀ᵐ s, DifferentiableAt ℝ g s)
    (hgi : Integrable (deriv g)) (lam L : ℝ) :
    ∫ t in (-L)..L, deriv g t * Complex.exp (-(I * lam * t)) =
      g L * Complex.exp (-(I * lam * L)) - g (-L) * Complex.exp (-(I * lam * (-L : ℝ))) +
        I * lam * ∫ t in (-L)..L, g t * Complex.exp (-(I * lam * t)) := by
  obtain ⟨e, he_def⟩ : ∃ e : ℝ → ℂ, e = fun t : ℝ ↦ Complex.exp (-(I * lam * (t : ℂ))) :=
    ⟨_, rfl⟩
  suffices H : ∫ t in (-L)..L, deriv g t * e t =
      g L * e L - g (-L) * e (-L) + I * lam * ∫ t in (-L)..L, g t * e t by
    simpa only [he_def] using H
  have hecd : ContDiff ℝ 1 e := by
    rw [he_def]
    exact Complex.contDiff_exp.comp ((contDiff_const.mul ofRealCLM.contDiff).neg)
  have he (t : ℝ) : HasDerivAt e (-(I * lam) * e t) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ -(I * lam * (s : ℂ))) (-(I * lam)) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_mul (I * lam)).neg
      simpa [Pi.neg_def, Function.comp_def] using this
    rw [he_def]
    simpa only [mul_comm] using h1.cexp
  have hgc := continuous_of_absolutelyContinuous hac
  have hec := hecd.continuous
  have heac : AbsolutelyContinuousOnInterval e (-L) L :=
    hecd.contDiffOn.absolutelyContinuousOnInterval
  have hW0 := (hac (-L) L).fun_smul heac
  have hW : AbsolutelyContinuousOnInterval (fun t ↦ g t * e t) (-L) L := hW0
  have hi1 : IntervalIntegrable (fun t ↦ deriv g t * e t) volume (-L) L :=
    hgi.intervalIntegrable.mul_continuousOn hec.continuousOn
  have hi2 : IntervalIntegrable (fun t ↦ g t * e t) volume (-L) L :=
    (hgc.mul hec).intervalIntegrable _ _
  have hDi : IntervalIntegrable (fun t ↦ deriv g t * e t + -(I * lam) * (g t * e t))
      volume (-L) L := hi1.add (hi2.const_mul _)
  have hderiv : ∀ᵐ t, t ∈ uIcc (-L) L → HasDerivAt (fun t ↦ g t * e t)
      (deriv g t * e t + -(I * lam) * (g t * e t)) t := by
    filter_upwards [hdiff] with t ht _
    exact (ht.hasDerivAt.mul (he t)).congr_deriv (by ring)
  have hFTC := complex_integral_eq_sub_of_ac hW hDi hderiv
  rw [intervalIntegral.integral_add hi1 (hi2.const_mul _),
    intervalIntegral.integral_const_mul] at hFTC
  linear_combination hFTC

/-- `(A + B log(1/h)) h^{1/4} → 0` as `h → 0⁺`. -/
theorem tendsto_log_mul_rpow_quarter (A B : ℝ) :
    Tendsto (fun h : ℝ ↦ (A + B * Real.log (1 / h)) * h ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun h : ℝ ↦ h ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 4) (by norm_num)
  have h3 := (h1.const_mul A).add ((h2.const_mul (-B)))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [one_div, Real.log_inv]
  ring

end Parts

/-! ### The Melnikov condition -/

/-- The Melnikov condition. Let `(v, f)` be a transport pair on a neighbourhood of the closed
    cell square that transforms with any fourth-root character under the rotation
    `R(x, y) = (y, -x)`, with `f` continuous. Then the trace `g = f ∘ γ` on the separatrix arc
    has `g' ∈ L¹` and `∫ g'(s) e^{-iλs} ds = 0`. -/
theorem melnikov_character {lam : ℝ} {κ : ℂ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U)
    (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U) :
    Integrable (deriv (f ∘ separatrixArc)) ∧
      ∫ s, profileIntegrand lam (f ∘ separatrixArc) s = 0 := by
  have hUo : IsOpen U := hp.isOrbitUnion.1
  have hK : arcSegment ⊆ U := arcSegment_subset_closure_cellSquare.trans hU
  set g := f ∘ separatrixArc with hg_def
  obtain ⟨hac, hdiff, hgi⟩ := arcTrace_regularity hUo hK hfc hp.memSobolevOn
  refine ⟨hgi, ?_⟩
  have hlam := hp.ne_zero
  have hκ0 : κ ≠ 0 := by rcases hκ with rfl | rfl | rfl | rfl <;> simp
  -- Hölder continuity near the arc, orbit comparison and the logarithmic size of `L`.
  obtain ⟨ρ, hρ, CH, hCH, hH⟩ := exists_holder_near_arcSegment hUo hK hfc hp.memSobolevOn
    (α := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Co, ho, hho, hclose⟩ := orbit_close_arc
  obtain ⟨Ce, hCe⟩ := exp_eighthPeriod_le
  set Co' := max Co 0
  have hCo' : 0 ≤ Co' := le_max_right _ _
  -- Resonant levels tending to the separatrix.
  have hseq (n : ℕ) :=
    exists_resonant_level_character hlam hκ (η := 1 / ((n : ℝ) + 1)) (by positivity)
  choose hs hs0 hsn hs1 ks hks hes using hseq
  have hlim0 : Tendsto hs atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hs0 n).le) (fun n ↦ (hsn n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto hs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim0, Eventually.of_forall fun n ↦ hs0 n⟩
  set Ls : ℕ → ℝ := fun n ↦ eighthPeriod (hs n)
  have hLtop : Tendsto Ls atTop atTop := by
    have := (tendsto_orbitPeriod_atTop.comp hlim).atTop_div_const (by norm_num : (0 : ℝ) < 8)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, orbitPeriod, Ls]
    ring
  -- The exponential.
  obtain ⟨e, he_def⟩ : ∃ e : ℝ → ℂ, e = fun t : ℝ ↦ Complex.exp (-(I * lam * (t : ℂ))) :=
    ⟨_, rfl⟩
  have hen (t : ℝ) : ‖e t‖ = 1 := by
    rw [he_def, Complex.norm_exp]
    simp
  have hec : Continuous e := by rw [he_def]; fun_prop
  -- The integrals over `[-L, L]` tend to the full integral.
  have hP : Integrable (profileIntegrand lam g) := by
    have := hgi.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun t ↦ (hen t).le)
    rw [he_def] at this
    exact this
  have hI := intervalIntegral_tendsto_integral hP (tendsto_neg_atTop_atBot.comp hLtop) hLtop
  have hIBP (n : ℕ) : ∫ t in (-Ls n)..Ls n, profileIntegrand lam g t =
      (g (Ls n) * e (Ls n) - g (-Ls n) * e (-Ls n)) +
        I * lam * ∫ t in (-Ls n)..Ls n, g t * e t := by
    have := integral_deriv_mul_exp_eq hac hdiff hgi lam (Ls n)
    simpa only [profileIntegrand, he_def] using this
  -- The backward phase is κ⁻¹, cancelling c₊ = κ c₋ at the endpoints.
  have hc : f (0, -π) = κ * f (π, 0) := by
    have := hfR (π, 0) (hK saddle_neg_mem_arcSegment)
    simpa using this
  have hcont {p : ℝ × ℝ} (hp : p ∈ U) : ContinuousAt f p := hfc.continuousAt (hUo.mem_nhds hp)
  have hgp : Tendsto (fun n ↦ g (Ls n)) atTop (𝓝 (f (0, -π))) :=
    (hcont (hK saddle_pos_mem_arcSegment)).tendsto.comp (tendsto_separatrixArc_atTop.comp hLtop)
  have hgm : Tendsto (fun n ↦ g (-Ls n)) atTop (𝓝 (f (π, 0))) :=
    (hcont (hK saddle_neg_mem_arcSegment)).tendsto.comp
      (tendsto_separatrixArc_atBot.comp (tendsto_neg_atTop_atBot.comp hLtop))
  have hB : Tendsto (fun n ↦ g (Ls n) * e (Ls n) - g (-Ls n) * e (-Ls n)) atTop (𝓝 0) := by
    have hlimit : Tendsto (fun n ↦ κ⁻¹ * g (Ls n) - g (-Ls n)) atTop (𝓝 0) := by
      have := (hgp.const_mul κ⁻¹).sub hgm
      rwa [hc, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul, sub_self] at this
    rw [tendsto_zero_iff_norm_tendsto_zero] at hlimit ⊢
    refine hlimit.congr fun n ↦ ?_
    have hphase : Complex.exp (-(2 * I * lam * eighthPeriod (hs n))) = κ⁻¹ := by
      rw [← one_div, eq_div_iff hκ0]
      exact hes n
    have heL : e (Ls n) = e (-Ls n) * κ⁻¹ := by
      rw [he_def, ← hphase, ← Complex.exp_add]
      simp only [Ls]
      push_cast
      apply congrArg Complex.exp
      ring
    rw [heL, show g (Ls n) * (e (-Ls n) * κ⁻¹) - g (-Ls n) * e (-Ls n) =
      e (-Ls n) * (κ⁻¹ * g (Ls n) - g (-Ls n)) by ring, norm_mul, hen, one_mul]
  -- The interior term: compare with the resonant orbit, whose integral vanishes.
  have hJ : Tendsto (fun n ↦ ∫ t in (-Ls n)..Ls n, g t * e t) atTop (𝓝 0) := by
    set A := 2 * CH * Co' ^ (1 / 2 : ℝ)
    have hA : 0 ≤ A := by positivity
    have hF : Tendsto (fun n ↦ A * ((Real.log Ce + 1 / 2 * Real.log (1 / hs n)) *
        hs n ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
      have := ((tendsto_log_mul_rpow_quarter (Real.log Ce) (1 / 2)).const_mul A).comp hlim
      simpa only [mul_zero, Function.comp_def] using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun n ↦ Co' * √(hs n)) atTop (𝓝 0) := by
      have := ((by fun_prop : Continuous fun x : ℝ ↦ Co' * √x).tendsto 0).comp hlim0
      simpa [Function.comp_def] using this
    have hsmall : ∀ᶠ n in atTop, hs n < ho ∧ Co' * √(hs n) < ρ :=
      (hlim0.eventually (gt_mem_nhds hho)).and (hsq.eventually (gt_mem_nhds hρ))
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hF
    filter_upwards [hsmall] with n ⟨hn1, hn2⟩
    set h := hs n
    have h0 := hs0 n
    have h1 := hs1 n
    set L := Ls n
    have hγc : Continuous fun t ↦ dipoleOrbit h t := by
      have := continuous_dipoleOrbit.comp (Continuous.prodMk_right (X := ℝ) h)
      exact this
    have hcell (t : ℝ) : dipoleOrbit h t ∈ U :=
      hU (subset_closure (dipoleOrbit_mem_cellSquare h0 h1 t))
    have hgc := continuous_of_absolutelyContinuous hac
    have hfγ : Continuous fun t ↦ f (dipoleOrbit h t) := hfc.comp_continuous hγc hcell
    have hq := integral_quarter_eq_zero_of_resonant hp hU hUR hfR hfc h0 h1 (hks n) (hes n)
    have hq' : ∫ t in (-L)..L, f (dipoleOrbit h t) * e t = 0 := by
      rw [← hq, he_def]
      congr 1
      funext t
      ring
    have hsplit : ∫ t in (-L)..L, g t * e t =
        ∫ t in (-L)..L, (g t - f (dipoleOrbit h t)) * e t := by
      have i1 : IntervalIntegrable (fun t ↦ g t * e t) volume (-L) L :=
        (hgc.mul hec).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun t ↦ f (dipoleOrbit h t) * e t) volume (-L) L :=
        (hfγ.mul hec).intervalIntegrable _ _
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub i1 i2, hq', sub_zero]
    rw [hsplit]
    -- Pointwise: `|g - g_h| ≤ C_H (C √h)^{1/2}` on the quarter orbit.
    have hpt : ∀ t ∈ Ι (-L) L, ‖(g t - f (dipoleOrbit h t)) * e t‖ ≤
        CH * (Co' * √h) ^ (1 / 2 : ℝ) := by
      intro t ht
      have htL : |t| ≤ L := by
        rw [uIoc_of_le (by linarith [eighthPeriod_pos h0 h1])] at ht
        exact abs_le.2 ⟨ht.1.le, ht.2⟩
      have hd := hclose h ⟨h0, hn1⟩ t htL
      have hd' : dist (separatrixArc t) (dipoleOrbit h t) ≤ Co' * √h := by
        rw [dist_comm, dist_eq_norm]
        exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
      have hm1 : separatrixArc t ∈ Metric.thickening ρ arcSegment :=
        Metric.self_subset_thickening hρ _ (separatrixArc_mem_arcSegment t)
      have hm2 : dipoleOrbit h t ∈ Metric.thickening ρ arcSegment :=
        Metric.mem_thickening_iff.2 ⟨_, separatrixArc_mem_arcSegment t, by
          rw [dist_comm]; exact hd'.trans_lt hn2⟩
      have hHt := hH _ hm1 _ hm2
      rw [norm_mul, hen, mul_one]
      refine hHt.trans (mul_le_mul_of_nonneg_left ?_ hCH)
      exact Real.rpow_le_rpow dist_nonneg (by simpa using hd') (by norm_num)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
    -- `2L ≤ 2(log C_e + ½ log(1/h))` and `(C √h)^{1/2} = C^{1/2} h^{1/4}`.
    have hLpos : 0 < L := eighthPeriod_pos h0 h1
    have hLle : L ≤ Real.log Ce + 1 / 2 * Real.log (1 / h) := by
      have hb := hCe h ⟨h0, h1⟩
      have hpos : 0 < Ce / √h := (Real.exp_pos _).trans_le hb
      have hCe0 : 0 < Ce := by
        have := Real.sqrt_pos.2 h0
        exact (div_pos_iff.1 hpos).elim (fun h ↦ h.1) (fun h ↦ absurd h.2 (not_lt.2 this.le))
      have := (Real.le_log_iff_exp_le hpos).2 hb
      rw [Real.log_div hCe0.ne' (Real.sqrt_pos.2 h0).ne', Real.log_sqrt h0.le] at this
      have hlog : Real.log (1 / h) = -Real.log h := by rw [one_div, Real.log_inv]
      change eighthPeriod h ≤ _
      rw [hlog]
      linarith
    have hpow : (Co' * √h) ^ (1 / 2 : ℝ) = Co' ^ (1 / 2 : ℝ) * h ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow hCo' (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul h0.le,
        show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    rw [hpow, show |L - -L| = 2 * L by rw [abs_of_pos (by linarith)]; ring]
    have hh4 : 0 ≤ h ^ (1 / 4 : ℝ) := Real.rpow_nonneg h0.le _
    have hk : 0 ≤ CH * Co' ^ (1 / 2 : ℝ) * h ^ (1 / 4 : ℝ) := by positivity
    calc CH * (Co' ^ (1 / 2 : ℝ) * h ^ (1 / 4 : ℝ)) * (2 * L)
        = 2 * (CH * Co' ^ (1 / 2 : ℝ) * h ^ (1 / 4 : ℝ)) * L := by ring
      _ ≤ 2 * (CH * Co' ^ (1 / 2 : ℝ) * h ^ (1 / 4 : ℝ)) *
          (Real.log Ce + 1 / 2 * Real.log (1 / h)) :=
          mul_le_mul_of_nonneg_left hLle (by positivity)
      _ = A * ((Real.log Ce + 1 / 2 * Real.log (1 / h)) * h ^ (1 / 4 : ℝ)) := by
          simp only [A]; ring
  -- Conclusion.
  have hzero : Tendsto (fun n ↦ ∫ t in (-Ls n)..Ls n, profileIntegrand lam g t) atTop (𝓝 0) := by
    have := hB.add (hJ.const_mul (I * lam))
    rw [mul_zero, add_zero] at this
    exact this.congr fun n ↦ (hIBP n).symm
  exact tendsto_nhds_unique hI hzero

/-- The real-character case of the Melnikov condition, for the equal-parity sectors. -/
theorem melnikov {lam κ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U) :
    Integrable (deriv (f ∘ separatrixArc)) ∧
      ∫ s, profileIntegrand lam (f ∘ separatrixArc) s = 0 := by
  apply melnikov_character hp hU _ hUR hfR hfc
  rcases hκ with rfl | rfl <;> simp

/-! ### Eigenfunctions -/

/-- The Melnikov identity on the arcs (`lem:ee-transport-traces`): for an eigenfunction with
    rotation character `κ`, the arc trace `g = ψ̃ ∘ γ_k` has integrable derivative and
    `∫ g' e^{-iλt} dt = 0`. From `melnikov` on `γ₀` and `g = κᵏ (ψ̃ ∘ γ₀)`. -/
theorem ee_melnikov {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (k : ℕ) :
    Integrable (deriv (contStream ω ∘ cellArc k)) ∧
      ∫ t, profileIntegrand lam (contStream ω ∘ cellArc k) t = 0 := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hU := isOrbitUnion_cellNeighbourhood
  have hp := isTransportPair_contStream hlam hω hU isBounded_cellNeighbourhood
  have hfR : ∀ p ∈ cellNeighbourhood, contStream ω (p.2, -p.1) = c * contStream ω p := by
    intro p _
    rw [hcc]
    exact contStream_rotLift hκ p
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  obtain ⟨hg, hM⟩ := melnikov hp closure_cellSquare_subset_cellNeighbourhood hc hUR hfR
    (continuous_contStream ω).continuousOn
  have hArc : (contStream ω ∘ cellArc k) =
      fun s ↦ paritySign κ ^ k * (contStream ω ∘ separatrixArc) s := by
    funext s
    exact contStream_iterate_rotLift hκ k (separatrixArc s)
  rw [hArc]
  refine ⟨by simpa only [deriv_const_mul_field'] using hg.const_mul (paritySign κ ^ k), ?_⟩
  simp only [profileIntegrand, deriv_const_mul_field', mul_assoc, integral_const_mul]
  simp only [profileIntegrand, mul_assoc] at hM
  rw [hM, mul_zero]

end EulerDipoleEigenvalues
