module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.WeightedEndpointGradients
public import EulerDipoleEigenvalues.Transport.WeightedForcing.OrbitNumeratorSecondDerivative

/-!
# Tangential endpoint derivatives from the affine ray trace

Blueprint: `lem:local-h1-classical-derivative`, `lem:nondegenerate-scalar-ae`,
`lem:quarter-ray-tangential-derivative`, `def:quarter-endpoint-level-trace`,
`lem:endpoint-tangential-trace-identity`, `lem:weighted-endpoint-tangential-trace`,
`lem:endpoint-coefficient-bounds`, `lem:weighted-numerator-endpoint-derivative`.

The same continuous forcing value is differentiated along its affine endpoint
ray and along the normalized orbit chart. Uniqueness of the scalar derivative
identifies the tangential contraction, without asserting invariance of arbitrary
transverse gradient traces under changes of chart.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Compatible local H¹ data give an a.e. classical derivative on the whole open
interval. No global value or derivative norm is required. -/
theorem HasIntervalH1Loc.hasDerivAt_ae {a b : ℝ} {F D : ℝ → ℂ}
    (hF : HasIntervalH1Loc a b F D) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt F (D x) x := by
  apply ae_restrict_of_ae_restrict_inter_Ioo
  intro c d hc hd hcd
  have hs : Ioo a b ∩ Ioo c d = Ioo c d :=
    inter_eq_right.mpr (Ioo_subset_Ioo hc.1.le hd.2.le)
  rw [hs]
  filter_upwards [ae_restrict_of_ae (hF c d hc.1 hcd hd.2).hasDerivAt_ae,
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  exact hx hxI

/-- A nonzero Jacobian transports null exceptional sets back through a smooth
injective scalar parameter. The property itself need not be measurable. -/
theorem ae_comp_of_hasDerivWithinAt_ne_zero {s t : Set ℝ} {r r₁ : ℝ → ℝ}
    (hs : MeasurableSet s) (hr : Measurable r) (hr₁ : Measurable r₁)
    (hd : ∀ x ∈ s, HasDerivWithinAt r (r₁ x) s x) (hi : InjOn r s)
    (hne : ∀ x ∈ s, r₁ x ≠ 0) (hst : r '' s ⊆ t)
    {p : ℝ → Prop} (hp : ∀ᵐ y ∂volume.restrict t, p y) :
    ∀ᵐ x ∂volume.restrict s, p (r x) := by
  have hmap : Measure.map r ((volume.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal |r₁ x|)) = volume.restrict (r '' s) := by
    simpa only [ContinuousLinearMap.det_toSpanSingleton] using
      map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
        (fun x hx ↦ (hd x hx).hasFDerivWithinAt) hi
  have hp' : ∀ᵐ x ∂(volume.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal |r₁ x|), p (r x) := by
    apply ae_of_ae_map hr.aemeasurable
    rw [hmap]
    exact hp.filter_mono (ae_mono (Measure.restrict_mono_set _ hst))
  have hpos := (ae_withDensity_iff
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hr₁))).1 hp'
  filter_upwards [hpos, ae_restrict_mem hs] with x hx hxS
  exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (hne x hxS))))

/-- Radial differentiation of the continuous forcing along either endpoint ray
uses only the corresponding canonical Cartesian gradient trace. -/
theorem quarterEndpointRay_hasIntervalH1 {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {g : ℝ × ℝ → ℂ}
    (hg : ContinuousOn g U) (hgs : MemSobolevOn 2 U g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j g (D j))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) (side : Bool) :
    HasIntervalH1 a b (fun r ↦ g (quarterEndpointRay side r))
      (fun r ↦ if side then quarterGradientTrace D side 1 r
        else -quarterGradientTrace D side 0 r) := by
  let Φ := quarterEndpointChart side
  let R := Ioo a b ×ˢ Ioo (-a / 2) (a / 2)
  let j : Fin 2 := if side then 1 else 0
  let n : Fin 2 := if side then 0 else 1
  let c : ℂ := if side then 1 else -1
  have hRU : R ⊆ Φ ⁻¹' U := by
    intro q hq
    apply hcell
    apply subset_closure
    apply (quarterEndpointChart_cone side (q := q) ?_).1
    exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans hb⟩,
      (abs_lt.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩).trans hq.1.1⟩
  have hmp : MeasurePreserving
      (planeAffine (endpointRayLinear side) (quarterEndpointRay side 0)) := by
    rw [planeAffine_endpointRayLinear]
    exact measurePreserving_quarterEndpointChart side
  have hP {F : ℝ × ℝ → ℂ} (h : MemLp F 2 (volume.restrict U)) :
      MemLp (F ∘ Φ) 2 (volume.restrict R) := by
    have hp := memLp_comp_planeAffine _ _ hmp hU.measurableSet h
    rw [planeAffine_endpointRayLinear] at hp
    exact hp.mono_measure (Measure.restrict_mono_set _ hRU)
  have hDs (i : Fin 2) : MemSobolevOn 1 U (D i) := (hD i).memSobolevOn hU hgs
  choose E hE hEL using fun i ↦ (hDs i).2
  have hx : HasWeakPartialOn R 0 (fun q ↦ c * g (Φ q)) (D j ∘ Φ) := by
    have h := (HasWeakPartialOn.comp_planeAffine _ _ hmp hU hD 0).const_mul c
    rw [planeAffine_endpointRayLinear] at h
    cases side <;>
      simpa [Φ, c, j, affineCoeff, planeDirection, endpointRayLinear, axisCoord,
        rotLinear, rotLift, Function.comp_def] using h.mono hRU
  have hy : HasWeakPartialOn R 1 (D j ∘ Φ) (E j n ∘ Φ) := by
    have h := HasWeakPartialOn.comp_planeAffine _ _ hmp hU (hE j) 1
    rw [planeAffine_endpointRayLinear] at h
    cases side <;>
      simpa [Φ, j, n, affineCoeff, planeDirection, endpointRayLinear, axisCoord,
        rotLinear, rotLift, Function.comp_def] using h.mono hRU
  have hΦ : Continuous Φ := continuous_rotatedQuarterEndpointChart 0 side
  have hFc : ContinuousOn (fun q ↦ c * g (Φ q)) R := continuousOn_const.mul
    (hg.comp hΦ.continuousOn hRU)
  have hFcL : MemLp (fun q ↦ c * g (Φ q)) 2 (volume.restrict R) := by
    exact (hP hgs.1).const_smul c
  have h := HasWeakPartialOn.trace_hasIntervalH1 hab (by linarith : -a / 2 < a / 2)
    (by constructor <;> linarith : (0 : ℝ) ∈ Ioo (-a / 2) (a / 2)) hFc
    hFcL (hP (hDs j).1) (hP (hEL j n)) hx hy
  have h := h.smul c
  change HasIntervalH1 a b (fun r ↦ c * (c * g (Φ (r, 0))))
    (fun r ↦ c * interiorSectionTrace (fun s ↦ D j (Φ (r, 0 + s)))) at h
  cases side <;>
    simpa [c, j, Φ, quarterEndpointRay, quarterEndpointChart, quarterGradientTrace,
      interiorChartTrace, rotatedQuarterEndpointChart, Function.comp_def,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul] using h

/-- Radius substitution preserves a.e. properties, including nonmeasurable
classical derivative predicates. Its strictly positive Jacobian is essential. -/
theorem ae_quarterEndpointRadius {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {p : ℝ → Prop}
    (hp : ∀ᵐ r ∂volume.restrict (Ioo 0 ρ), p r) :
    ∀ᵐ h ∂volume.restrict (Ioo 0 b), p (quarterEndpointRadius h) := by
  let δ := fun h : ℝ ↦ 1 / (Real.sqrt h * Real.sqrt (1 - h))
  have hδ (h : ℝ) (hh : h ∈ Ioo 0 b) : 0 < δ h := by
    exact div_pos zero_lt_one (mul_pos (Real.sqrt_pos.mpr hh.1)
      (Real.sqrt_pos.mpr (sub_pos.mpr (hh.2.trans hb))))
  apply ae_comp_of_hasDerivWithinAt_ne_zero measurableSet_Ioo
    (by unfold quarterEndpointRadius; fun_prop) (show Measurable δ by dsimp [δ]; fun_prop)
    (fun h hh ↦ (hasDerivAt_quarterEndpointRadius hh.1 (hh.2.trans hb)).hasDerivWithinAt)
    ?_ (fun h hh ↦ (hδ h hh).ne') ?_ hp
  · intro x hx y hy he
    have he' : Real.arcsin (Real.sqrt x) = Real.arcsin (Real.sqrt y) := by
      unfold quarterEndpointRadius at he
      linarith
    have hs := congrArg Real.sin he'
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg x])
        (Real.sqrt_le_one.mpr (hx.2.trans hb).le),
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg y])
        (Real.sqrt_le_one.mpr (hy.2.trans hb).le)] at hs
    have hs' := congrArg (fun z : ℝ ↦ z ^ 2) hs
    simpa only [Real.sq_sqrt hx.1.le, Real.sq_sqrt hy.1.le] using hs'
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨quarterEndpointRadius_pos hh.1,
      (monotone_quarterEndpointRadius hh.2.le).trans_lt hρ⟩

/-- The normalized level contraction at the actual quarter endpoint. It includes
period drift and is not defined by evaluating the raw gradient on a ray. -/
def quarterEndpointLevelTrace (D : Fin 2 → ℝ × ℝ → ℂ) (side : Bool) (h : ℝ) : ℂ :=
  interiorSectionTrace (fun s ↦ actionAnglePullbackGradient D 0
    (h, ((if side then 1 else -1 : ℝ) / 8) + s))

/-- The normalized endpoint derivative equals the radius Jacobian times the
canonical affine *tangential* gradient trace, almost everywhere. This does not
identify the individual transverse gradient traces in the two charts. -/
theorem IsTransportPair.quarterEndpointLevelTrace_eq_ae
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    {b : ℝ} (hb : b < 1) (hρ : quarterEndpointRadius b < 1 / 2) (side : Bool) :
    quarterEndpointLevelTrace D side =ᵐ[volume.restrict (Ioo 0 b)]
      (fun h ↦ ((1 / (Real.sqrt h * Real.sqrt (1 - h)) : ℝ) : ℂ) *
        (if side then quarterGradientTrace D side 1 (quarterEndpointRadius h)
         else -quarterGradientTrace D side 0 (quarterEndpointRadius h))) := by
  have hU := hp.isOrbitUnion.1
  have he := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hgs : MemSobolevOn 2 U g := hp.memSobolevOn.congr_ae_on hU.measurableSet he
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (D j) :=
    (hD j).congr_ae_on hU.measurableSet he (Eventually.of_forall fun _ _ ↦ rfl)
  have hR : HasIntervalH1Loc 0 (1 / 2) (fun r ↦ g (quarterEndpointRay side r))
      (fun r ↦ if side then quarterGradientTrace D side 1 r
        else -quarterGradientTrace D side 0 r) := by
    intro a c ha hac hc
    exact quarterEndpointRay_hasIntervalH1 hU hcell hg hgs hDg ha hac hc side
  let ε : ℝ := if side then 1 else -1
  have hε : ε = -1 ∨ ε = 1 := by cases side <;> simp [ε]
  have hO : HasIntervalH1Loc 0 b
      (fun h ↦ g (quarterEndpointRay side (quarterEndpointRadius h)))
      (quarterEndpointLevelTrace D side) := by
    intro a c ha hac hc
    have h := (hp.quarterEndpoint_forcing_h1Loc hcell hg hfg hD hb hε) a c ha hac hc
    apply h.congr_Ioo
    intro h hh
    have hh0 : 0 < h := ha.trans hh.1
    have hh1 : h < 1 := (hh.2.trans hc).trans hb
    have hpoint := dipoleOrbit_quarterEndpointRay hh0 hh1 side
    cases side <;> simpa [ε, quarterEndpointLevelTrace] using congrArg g hpoint
  filter_upwards [ae_quarterEndpointRadius hb hρ hR.hasDerivAt_ae,
    hO.hasDerivAt_ae, ae_restrict_mem measurableSet_Ioo] with h hr ho hh
  have hd := hr.scomp h (hasDerivAt_quarterEndpointRadius hh.1 (hh.2.trans hb))
  simpa only [Complex.real_smul] using ho.unique hd

/-- Original weighted gradient data give an actual global L² norm for the
canonical normalized endpoint-value derivative. The value forcing weight and a
continuous gradient are unnecessary for this critical tangential estimate. -/
theorem IsTransportPair.quarterEndpointLevelTrace_memLp
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 256) :
    ∀ side, MemLp (quarterEndpointLevelTrace D side) 2 (volume.restrict (Ioo 0 b)) := by
  have hb1 : b < 1 := by linarith
  have hρ : quarterEndpointRadius b < 1 / 2 := by
    have hs : Real.sqrt b ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hb hb1]
  have hT := (hp.weighted_gradient_endpoint_traces hcell hD hDw hb hb').2.2
  have hcoef : MemLp (fun h : ℝ ↦ (1 / Real.sqrt (1 - h) : ℝ)) ⊤
      (volume.restrict (Ioo 0 b)) := by
    apply memLp_top_of_bound
      (show Measurable (fun h : ℝ ↦ 1 / Real.sqrt (1 - h)) by fun_prop).aestronglyMeasurable 2
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hpos : 0 < Real.sqrt (1 - h) := Real.sqrt_pos.mpr (by linarith [hh.2])
    have hlow : (1 / 2 : ℝ) ≤ Real.sqrt (1 - h) :=
      Real.le_sqrt_of_sq_le (by nlinarith [hh.2])
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hpos)]
    exact (div_le_iff₀ hpos).2 (by linarith)
  have hcoefC : MemLp (fun h : ℝ ↦ ((1 / Real.sqrt (1 - h) : ℝ) : ℂ)) ⊤
      (volume.restrict (Ioo 0 b)) := hcoef.ofReal
  intro side
  have hR : MemLp (fun h ↦
      (if side then quarterGradientTrace D side 1 (quarterEndpointRadius h)
       else -quarterGradientTrace D side 0 (quarterEndpointRadius h)) / (Real.sqrt h : ℂ))
      2 (volume.restrict (Ioo 0 b)) := by
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_div]
      exact (hT false 0).neg
    · exact hT true 1
  have hprod : MemLp (fun h ↦ ((1 / Real.sqrt (1 - h) : ℝ) : ℂ) *
      ((if side then quarterGradientTrace D side 1 (quarterEndpointRadius h)
        else -quarterGradientTrace D side 0 (quarterEndpointRadius h)) / (Real.sqrt h : ℂ)))
      2 (volume.restrict (Ioo 0 b)) := hcoefC.mul hR
  apply hprod.ae_eq
  filter_upwards [hp.quarterEndpointLevelTrace_eq_ae hcell hg hfg hD hb1 hρ side,
    ae_restrict_mem measurableSet_Ioo] with h he hh
  rw [he]
  push_cast
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

/-- Explicit derivative of the endpoint scalar coefficient. Both signs of the
endpoint and every real frequency are allowed. -/
theorem hasDerivAt_quarterEndpointCoefficient {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (μ ε : ℝ) : HasDerivAt (quarterEndpointCoefficient μ ε)
      (((deriv (deriv eighthPeriod) h : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((μ * (ε * eighthPeriod h) : ℝ) : ℂ)) +
       ((deriv eighthPeriod h : ℝ) : ℂ) *
        ((-Complex.I * ((μ * (ε * deriv eighthPeriod h) : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((μ * (ε * eighthPeriod h) : ℝ) : ℂ)))) h := by
  have hL := (contDiffOn_eighthPeriod.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hh)
  have hCd : ContDiffOn ℝ ∞ (deriv eighthPeriod) (Ioo (0 : ℝ) 1) :=
    contDiffOn_eighthPeriod.deriv_of_isOpen isOpen_Ioo (by simp)
  have hL' := (hCd.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hh)
  convert hL'.hasDerivAt.ofReal_comp.mul
    (((hL.hasDerivAt.const_mul ε).const_mul μ).ofReal_comp.const_mul (-Complex.I)).cexp
      using 1
  · rfl
  · ring

/-- The two scalar coefficients needed for h times the endpoint-flux derivative
are uniformly bounded in h; their bounds may depend on the frequency. -/
theorem quarterEndpointCoefficient_weighted_bounds :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∀ μ : ℝ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ ε : ℝ, (ε = -1 ∨ ε = 1) → ∀ h ∈ Ioo 0 b,
        ‖(h : ℂ) * quarterEndpointCoefficient μ ε h‖ ≤ K ∧
        ‖((h ^ 2 : ℝ) : ℂ) * deriv (quarterEndpointCoefficient μ ε) h‖ ≤ K := by
  obtain ⟨c, C, r, hc, hC, hr, hr1, hL⟩ := eighthPeriod_derivative_bounds
  let b := min r (1 / 256)
  refine ⟨b, lt_min hr (by norm_num), by dsimp [b]; linarith [min_le_right r (1 / 256)],
    fun μ ↦ ⟨C + C ^ 2 * |μ|, by positivity, ?_⟩⟩
  intro ε hε h hh
  have hhr : h ∈ Ioo (0 : ℝ) r := ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩
  have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, hhr.2.trans hr1⟩
  have hneg : deriv eighthPeriod h ≤ 0 := by
    have := (hL h hhr).1
    nlinarith [hh.1]
  have hfirst : h * |deriv eighthPeriod h| ≤ C := by
    rw [abs_of_nonpos hneg]
    nlinarith [(hL h hhr).2.1]
  have hphase : ‖Complex.exp (-Complex.I * ((μ * (ε * eighthPeriod h) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · simp only [quarterEndpointCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh.1, hphase, mul_one]
    exact hfirst.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg C) (abs_nonneg μ)))
  · rw [(hasDerivAt_quarterEndpointCoefficient hh1 μ ε).deriv, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg h)).trans
    simp only [norm_mul, hphase, mul_one, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, hεabs]
    have hs := (sq_le_sq₀ (mul_nonneg hh.1.le (abs_nonneg _)) hC.le).2 hfirst
    nlinarith [(hL h hhr).2.2, mul_nonneg (abs_nonneg μ)
      (sub_nonneg.mpr hs)]

/-- The complete derivative of the endpoint-value flux has genuine h-weighted
L² mass under the original forcing hypotheses. This is one of the two boundary
contributions to the second numerator candidate, not the first-bulk flux. -/
theorem IsTransportPair.weighted_numerator_endpoint_derivative
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D [j]))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDw : ∀ j, MemLp (fun p ↦ D [j] p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∀ μ : ℝ,
      MemLp (fun h : ℝ ↦ (h : ℂ) * quarterNumeratorEndpointDerivative μ g D h) 2
        (volume.restrict (Ioo 0 b)) := by
  have hU := hp.isOrbitUnion.1
  have he := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (D [j]) :=
    (hD j).congr_ae_on hU.measurableSet he (Eventually.of_forall fun _ _ ↦ rfl)
  have hfG : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply hf.ae_eq
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hcell) hfg]
      with p hp
    rw [hp]
  obtain ⟨r, hr, hrh, hK⟩ := quarterEndpointCoefficient_weighted_bounds
  let b := min r (1 / 256)
  have hb : 0 < b := lt_min hr (by norm_num)
  have hbr : b ≤ r := min_le_left _ _
  have hbsmall : b ≤ 1 / 256 := min_le_right _ _
  have hbh : b < 1 / 2 := lt_of_le_of_lt hbr hrh
  have hb1 : b < 1 := by linarith
  have hs : Ioo (0 : ℝ) b ⊆ Ioo 0 1 := Ioo_subset_Ioo le_rfl hb1.le
  have hT := hp.quarterEndpointLevelTrace_memLp hcell hg hfg hD hDw hb hbsmall
  have hV := weighted_quarter_endpoint_values hU hcell hg hDg hfG hDw hb hbsmall
  refine ⟨b, hb, hbh, fun μ ↦ ?_⟩
  obtain ⟨K, _, hKb⟩ := hK μ
  have hcoef (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
      MemLp (fun h : ℝ ↦ (h : ℂ) * quarterEndpointCoefficient μ ε h) ⊤
          (volume.restrict (Ioo 0 b)) ∧
      MemLp (fun h ↦ ((h ^ 2 : ℝ) : ℂ) * deriv (quarterEndpointCoefficient μ ε) h) ⊤
          (volume.restrict (Ioo 0 b)) := by
    have hc := contDiffOn_quarterEndpointCoefficient μ ε
    have hcd : ContDiffOn ℝ ∞ (deriv (quarterEndpointCoefficient μ ε)) (Ioo (0 : ℝ) 1) :=
      hc.deriv_of_isOpen isOpen_Ioo (by simp)
    have hcm : ContinuousOn (fun h : ℝ ↦ (h : ℂ) * quarterEndpointCoefficient μ ε h)
        (Ioo 0 b) := Complex.continuous_ofReal.continuousOn.mul (hc.continuousOn.mono hs)
    have hcdm : ContinuousOn
        (fun h ↦ ((h ^ 2 : ℝ) : ℂ) * deriv (quarterEndpointCoefficient μ ε) h) (Ioo 0 b) :=
      (by fun_prop : ContinuousOn (fun h : ℝ ↦ ((h ^ 2 : ℝ) : ℂ)) (Ioo 0 b)).mul
        (hcd.continuousOn.mono hs)
    constructor
    · apply memLp_top_of_bound (hcm.aestronglyMeasurable measurableSet_Ioo) K
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      exact (hKb ε hε h ⟨hh.1, hh.2.trans_le hbr⟩).1
    · apply memLp_top_of_bound (hcdm.aestronglyMeasurable measurableSet_Ioo) K
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      exact (hKb ε hε h ⟨hh.1, hh.2.trans_le hbr⟩).2
  let ε : Bool → ℝ := fun side ↦ if side then 1 else -1
  have hε (side : Bool) : ε side = -1 ∨ ε side = 1 := by cases side <;> simp [ε]
  have hpart (side : Bool) : MemLp (fun h : ℝ ↦ (h : ℂ) *
      (deriv (quarterEndpointCoefficient μ (ε side)) h *
        g (dipoleOrbit h (ε side * eighthPeriod h)) +
       quarterEndpointCoefficient μ (ε side) h * quarterEndpointLevelTrace (fun j ↦ D [j]) side h))
      2 (volume.restrict (Ioo 0 b)) := by
    have hv : MemLp (fun h ↦ g (dipoleOrbit h (ε side * eighthPeriod h)) / (h : ℂ))
        2 (volume.restrict (Ioo 0 b)) := by
      apply (hV side).ae_eq
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      have hpoint := dipoleOrbit_quarterEndpointRay hh.1 (hh.2.trans hb1) side
      cases side <;> simpa [ε] using congrArg (fun p ↦ g p / (h : ℂ)) hpoint.symm
    have hsum : MemLp _ 2 (volume.restrict (Ioo 0 b)) :=
      ((hcoef (ε side) (hε side)).2.mul hv).add
      ((hcoef (ε side) (hε side)).1.mul (hT side))
    apply hsum.ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    change (((h ^ 2 : ℝ) : ℂ) * deriv (quarterEndpointCoefficient μ (ε side)) h) *
        (g (dipoleOrbit h (ε side * eighthPeriod h)) / (h : ℂ)) +
        ((h : ℂ) * quarterEndpointCoefficient μ (ε side) h) *
          quarterEndpointLevelTrace (fun j ↦ D [j]) side h = _
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hh.1.ne']
  apply ((hpart true).add (hpart false)).ae_eq
  exact Eventually.of_forall fun h ↦ by
    simp only [Pi.add_apply, ε, quarterEndpointLevelTrace, quarterNumeratorEndpointDerivative,
      Bool.false_eq_true, ↓reduceIte]
    ring

/-- The original weighted inputs produce the continuous representative, a true
second jet retaining the supplied first entries, the local second formula and
the global weighted endpoint-value contribution, on one all-frequency collar. -/
theorem IsTransportPair.exists_weighted_numerator_endpoint_data
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ (g : ℝ × ℝ → ℂ) (J : List (Fin 2) → ℝ × ℝ → ℂ) (b : ℝ),
      ContinuousOn g U ∧ f =ᵐ[volume.restrict U] g ∧ HasWeakJetOn 2 U f J ∧
      (∀ j, J [j] = D j) ∧ 0 < b ∧ b < 1 / 2 ∧ ∀ μ : ℝ,
        HasIntervalH2Loc 0 b (quarterNumerator μ g) (deriv (quarterNumerator μ g))
          (quarterNumeratorSecondDerivative μ g J) ∧
        MemLp (fun h : ℝ ↦ (h : ℂ) * quarterNumeratorEndpointDerivative μ g J h) 2
          (volume.restrict (Ioo 0 b)) := by
  obtain ⟨g, J, hg, hfg, hJ, hJD, hN⟩ :=
    hp.exists_quarterNumerator_second_derivative hcell hD
  have hJfirst (j : Fin 2) : HasWeakPartialOn U j f (J [j]) := by
    rw [hJD j]
    exact hD j
  have hJw (j : Fin 2) : MemLp
      (fun p ↦ J [j] p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare) := by
    rw [hJD j]
    exact hDw j
  obtain ⟨b, hb, hbh, hE⟩ :=
    hp.weighted_numerator_endpoint_derivative hcell hg hfg hJfirst hf hJw
  exact ⟨g, J, b, hg, hfg, hJ, hJD, hb, hbh, fun μ ↦ ⟨hN b (by linarith) μ, hE μ⟩⟩

end EulerDipoleEigenvalues
