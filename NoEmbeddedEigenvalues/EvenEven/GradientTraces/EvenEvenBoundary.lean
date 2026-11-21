module

public import NoEmbeddedEigenvalues.EvenEven.NormalVirial.NormalVirial
public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.CanonicalBoundaryForm
public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.LevelTraces
public import NoEmbeddedEigenvalues.Transport.PeriodicComparison.PairingLimit

/-!
# Boundary profiles and even–even inputs

Blueprint: `lem:ee-neumann`, `lem:ee-first-trace-limit`, `lem:ee-gradient-traces`,
`lem:arc-trace-ac`, `lem:h2-laplacian-reconstruction`, `lem:laplacian-symmetries`,
`lem:even-h2-arc-regularity`, `lem:canonical-boundary-regularity`,
`lem:ee-boundary-regularity` and `lem:ee-canonical-arc-nonneg`.

Assemble the gradient limits from `SeparatrixTraces.lean` and the first-order
trace estimate. Arc absolute continuity, Melnikov and the weighted canonical
profile bound put the boundary unknown in the weighted interval domain after
`ξ = tanh s`. Its endpoint character and the interval boundary positivity
theorem then make each canonical arc contribution nonnegative.

Even H² torus functions inherit these arc estimates by inverse-Laplacian reconstruction
up to their mean. The abstract canonical-profile theorem supplies weighted interval
regularity, forcing identification and endpoint values independently of the sector.

The normal-field virial is in `NormalVirial.lean`, transport traces are in
`PairingLimit.lean`, and the exclusion assembly is in `EvenEven.lean`.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Neumann condition (`lem:ee-neumann`): in the even–even sector `ψₙ` is odd and `ψₜ` is even
    under the reflections `S₂(x, y) = (y + π, x + π)` and `S₁(x, y) = (π - y, π - x)` across
    the lines carrying the separatrix arcs. -/
theorem ee_neumann {ω : L2} (hω : InSector true true ω) :
    (∀ᵐ p, streamNormal ω (p.2 + Real.pi, p.1 + Real.pi) = -streamNormal ω p ∧
      streamTangent ω (p.2 + Real.pi, p.1 + Real.pi) = streamTangent ω p) ∧
    (∀ᵐ p, streamNormal ω (Real.pi - p.2, Real.pi - p.1) = -streamNormal ω p ∧
      streamTangent ω (Real.pi - p.2, Real.pi - p.1) = streamTangent ω p) := by
  obtain ⟨h₁x, h₁y⟩ := hω.reflect₁_streamPartial
  obtain ⟨h₂x, h₂y⟩ := hω.reflect₂_streamPartial
  simp only [paritySign, ite_true, neg_smul, one_smul] at h₁x h₁y h₂x h₂y
  have hS₁ (p : ℝ × ℝ) : torusProj (Real.pi - p.2, Real.pi - p.1) = S₁ (torusProj p) := by
    simp [torusProj, S₁]
  have hS₂ (p : ℝ × ℝ) : torusProj (p.2 + Real.pi, p.1 + Real.pi) = S₂ (torusProj p) := by
    simp [torusProj, S₂, add_comm]
  have lift {T : Torus → Torus} {hT : MeasurePreserving T} {g h : L2}
      (heq : pullback T hT g = h) {M : ℝ × ℝ → ℝ × ℝ}
      (hM : ∀ p, torusProj (M p) = T (torusProj p)) :
      ∀ᵐ p, liftL2 g (M p) = liftL2 h p := by
    filter_upwards [ae_torusProj (ae_comp_of_pullback_eq heq)] with p hp
    simpa only [liftL2, hM] using hp
  have hneg (g : L2) : ∀ᵐ p, liftL2 (-g) p = -liftL2 g p :=
    ae_torusProj (Lp.coeFn_neg g)
  have hρ₁ (p : ℝ × ℝ) : gradNorm (Real.pi - p.2, Real.pi - p.1) = gradNorm p := by
    simp only [gradNorm, Real.sin_pi_sub, add_comm]
  have hρ₂ (p : ℝ × ℝ) : gradNorm (p.2 + Real.pi, p.1 + Real.pi) = gradNorm p := by
    simp only [gradNorm, Real.sin_add_pi, neg_sq]
    rw [add_comm]
  constructor
  · filter_upwards [lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂x hS₂,
      lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂y hS₂] with p hx hy
    simp only [streamNormal, streamTangent, normalDeriv, tangentDeriv, streamLiftX,
      streamLiftY, hx, hy, hρ₂, Real.sin_add_pi]
    constructor <;> push_cast <;> ring
  · filter_upwards [lift (M := fun p ↦ (Real.pi - p.2, Real.pi - p.1)) h₁x hS₁,
      lift (M := fun p ↦ (Real.pi - p.2, Real.pi - p.1)) h₁y hS₁,
      hneg (streamPartial 0 ω), hneg (streamPartial 1 ω)] with p hx hy hnx hny
    simp only [streamNormal, streamTangent, normalDeriv, tangentDeriv, streamLiftX,
      streamLiftY, hx, hy, hnx, hny, hρ₁, Real.sin_pi_sub]
    constructor <;> ring

/-! ### Gradient traces at the separatrix -/

/-- `ρ²` is invariant under the quarter rotation, so its level integral is four quarter
    integrals: `∮ ρ² dt = 4 ∫_{-L}^{L} ρ²(γ_h(t)) dt`. -/
theorem levelIntegral_gradNorm_sq {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    levelIntegral h (fun p ↦ gradNorm p ^ 2) =
      4 * ∫ t in (-eighthPeriod h)..eighthPeriod h, gradNorm (dipoleOrbit h t) ^ 2 := by
  set f : ℝ → ℝ := fun t ↦ gradNorm (dipoleOrbit h t) ^ 2 with hf
  have hγ : Continuous fun t ↦ dipoleOrbit h t :=
    Continuous.comp (g := fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) continuous_dipoleOrbit
      (f := fun t : ℝ ↦ (h, t)) (by fun_prop)
  have hfc : Continuous f := by
    simp only [hf, gradNorm]
    fun_prop
  have hper : Function.Periodic f (2 * eighthPeriod h) := fun t ↦ by
    simp only [hf, dipoleOrbit_add_quarter h0 h1, gradNorm, Real.sin_neg, neg_sq, add_comm]
  have h4 := hper.intervalIntegral_add_zsmul_eq 4 0 fun t₁ t₂ ↦ hfc.intervalIntegrable t₁ t₂
  have hshift := hper.intervalIntegral_add_eq 0 (-eighthPeriod h)
  rw [levelIntegral, orbitPeriod]
  change ∫ t in (0 : ℝ)..8 * eighthPeriod h, f t =
    4 * ∫ t in (-eighthPeriod h)..eighthPeriod h, f t
  rw [show 8 * eighthPeriod h = 0 + (4 : ℤ) • (2 * eighthPeriod h) by simp; ring, h4,
    zsmul_eq_mul, hshift, show -eighthPeriod h + 2 * eighthPeriod h = eighthPeriod h by ring]
  push_cast
  ring

/-- `∮ ρ² dt` stays bounded as the levels approach the separatrix, although the period
    `S(h) → ∞`: `ρ ≤ C d` and `∫ d² dt ≤ C` on the quarter orbit. -/
theorem levelIntegral_gradNorm_sq_le : ∃ K h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, h < 1 →
    levelIntegral h (fun p ↦ gradNorm p ^ 2) ≤ K := by
  obtain ⟨Cρ, hCρ⟩ := gradNorm_le_saddleDist
  obtain ⟨Cd, h₀, hh₀, hCd⟩ := integral_saddleDist_rpow_pos_le (p := 2) two_pos
  refine ⟨4 * (4 * Cρ ^ 2 * Cd), h₀, hh₀, fun h hh h1 ↦ ?_⟩
  have h0 := hh.1
  have hL := (eighthPeriod_pos h0 h1).le
  have hγ : Continuous fun t ↦ dipoleOrbit h t :=
    Continuous.comp (g := fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) continuous_dipoleOrbit
      (f := fun t : ℝ ↦ (h, t)) (by fun_prop)
  rw [levelIntegral_gradNorm_sq h0 h1]
  gcongr
  have hd := hCd h hh
  simp only [Real.rpow_two] at hd
  calc ∫ t in (-eighthPeriod h)..eighthPeriod h, gradNorm (dipoleOrbit h t) ^ 2
      ≤ ∫ t in (-eighthPeriod h)..eighthPeriod h,
          4 * Cρ ^ 2 * saddleDist (dipoleOrbit h t) ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((by simp only [gradNorm]; fun_prop : Continuous fun t ↦
            gradNorm (dipoleOrbit h t) ^ 2).intervalIntegrable _ _)
          ((continuous_const.mul ((Metric.continuous_infDist_pt _).comp hγ |>.pow 2)
            ).intervalIntegrable _ _) fun t _ ↦ ?_
        have hc := hCρ _ (dipoleOrbit_mem_cellSquare h0 h1 t)
        have hg0 : 0 ≤ gradNorm (dipoleOrbit h t) := Real.sqrt_nonneg _
        nlinarith
    _ = 4 * Cρ ^ 2 * ∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ 4 * Cρ ^ 2 * Cd := by gcongr

/-- Cauchy–Schwarz on a level for a bounded measurable value and an L² normal
    component. No relation between the two functions is required. -/
theorem abs_levelIntegral_first_le_of_bounded {f n : ℝ × ℝ → ℂ}
    (mf : Measurable f) (mn : Measurable n)
    {M K h : ℝ} (hM0 : 0 ≤ M) (h0 : 0 < h) (h1 : h < 1)
    (hK : levelIntegral h (fun p ↦ gradNorm p ^ 2) ≤ K)
    (hn : IntegrableOn (fun t ↦ ‖n (dipoleOrbit h t)‖ ^ 2)
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖f (dipoleOrbit h t)‖ ≤ M) :
    |levelIntegral h (fun p ↦ gradNorm p * (f p * (starRingEnd ℂ) (n p)).re)| ≤
      M * √(K * levelIntegral h (fun p ↦ ‖n p‖ ^ 2)) := by
  set I := Ico (-2 * eighthPeriod h) (6 * eighthPeriod h) with hI
  set γ : ℝ → ℝ × ℝ := fun t ↦ dipoleOrbit h t with hγ
  have hγm : Measurable γ :=
    (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have hρm : Measurable fun t ↦ gradNorm (γ t) := by
    simp only [gradNorm]
    fun_prop
  have hnm : Measurable fun t ↦ n (γ t) := mn.comp hγm
  have hsm : Measurable fun t ↦ f (γ t) := mf.comp hγm
  have hρ0 (t : ℝ) : 0 ≤ gradNorm (γ t) := Real.sqrt_nonneg _
  have hρle (t : ℝ) : gradNorm (γ t) ^ 2 ≤ 2 := by
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    nlinarith [Real.sin_sq_le_one (γ t).1, Real.sin_sq_le_one (γ t).2]
  have hre (u v : ℂ) : |(u * (starRingEnd ℂ) v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have iρ : Integrable (fun t ↦ gradNorm (γ t) ^ 2) (volume.restrict I) :=
    (integrable_const (2 : ℝ)).mono' (hρm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (by positivity)]; exact hρle t)
  have iN : Integrable (fun t ↦ ‖n (γ t)‖ ^ 2) (volume.restrict I) := hn
  have iρn : Integrable (fun t ↦ gradNorm (γ t) * ‖n (γ t)‖) (volume.restrict I) :=
    (iρ.add iN).mono' (hρm.mul hnm.norm).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (norm_nonneg _)), Pi.add_apply]
        nlinarith [sq_nonneg (gradNorm (γ t) - ‖n (γ t)‖)])
  have hfm : AEStronglyMeasurable (fun t ↦ gradNorm (γ t) *
      (f (γ t) * (starRingEnd ℂ) (n (γ t))).re) (volume.restrict I) :=
    (hρm.mul (Complex.measurable_re.comp
      (hsm.mul (Complex.continuous_conj.measurable.comp hnm)))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict I), ‖gradNorm (γ t) *
      (f (γ t) * (starRingEnd ℂ) (n (γ t))).re‖ ≤
        M * (gradNorm (γ t) * ‖n (γ t)‖) := by
    filter_upwards [hM] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 t)]
    calc gradNorm (γ t) * |(f (γ t) * (starRingEnd ℂ) (n (γ t))).re|
        ≤ gradNorm (γ t) * (‖f (γ t)‖ * ‖n (γ t)‖) :=
          mul_le_mul_of_nonneg_left (hre _ _) (hρ0 t)
      _ ≤ gradNorm (γ t) * (M * ‖n (γ t)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (hρ0 t)
      _ = M * (gradNorm (γ t) * ‖n (γ t)‖) := by ring
  have iA := (iρn.const_mul M).mono' hfm hbound
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict I)
    Real.HolderConjugate.two_two (Eventually.of_forall fun t ↦ hρ0 t)
    (Eventually.of_forall fun t ↦ norm_nonneg (n (γ t)))
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hρm.aestronglyMeasurable).2 iρ)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hnm.norm.aestronglyMeasurable).2 iN)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  rw [levelIntegral_eq_setIntegral h0 h1] at hK ⊢
  rw [levelIntegral_eq_setIntegral h0 h1]
  calc _ ≤ ∫ t in I, ‖gradNorm (γ t) *
        (f (γ t) * (starRingEnd ℂ) (n (γ t))).re‖ :=
        (abs_integral_le_integral_abs).trans_eq rfl
    _ ≤ ∫ t in I, M * (gradNorm (γ t) * ‖n (γ t)‖) :=
        integral_mono_ae iA.norm (iρn.const_mul M) hbound
    _ = M * ∫ t in I, gradNorm (γ t) * ‖n (γ t)‖ := integral_const_mul _ _
    _ ≤ M * (√(∫ t in I, gradNorm (γ t) ^ 2) * √(∫ t in I, ‖n (γ t)‖ ^ 2)) := by
        gcongr
    _ ≤ M * √(K * ∫ t in I, ‖n (γ t)‖ ^ 2) := by
        rw [Real.sqrt_mul' _ (integral_nonneg fun t ↦ by positivity)]
        gcongr

/-- The first-order trace term on one level: if `|ψ| ≤ M` along the level and `∮ ρ² dt ≤ K`,
    then `|∮ Re(ψ ψ̄ₙ) dℓ| ≤ M (K ∮ |ψₙ|² dt)^{1/2}` (Cauchy–Schwarz). -/
theorem abs_levelIntegral_first_le (ω : L2) {M K h : ℝ} (hM0 : 0 ≤ M) (h0 : 0 < h) (h1 : h < 1)
    (hK : levelIntegral h (fun p ↦ gradNorm p ^ 2) ≤ K)
    (hn : IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) :
    |levelIntegral h fun p ↦
        gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re| ≤
      M * √(K * levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2) := by
  apply abs_levelIntegral_first_le_of_bounded
    ((Lp.stronglyMeasurable (invLap ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable) ?_ hM0 h0 h1 hK hn hM
  have hx := (Lp.stronglyMeasurable (streamPartial 0 ω)).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  have hy := (Lp.stronglyMeasurable (streamPartial 1 ω)).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  change Measurable (liftL2 (streamPartial 0 ω)) at hx
  change Measurable (liftL2 (streamPartial 1 ω)) at hy
  unfold streamNormal normalDeriv gradNorm streamLiftX streamLiftY
  fun_prop

/-- The first-order trace term (`lem:ee-first-trace-limit`): if `∮ |ψₙ|² dt → 0` along levels
    outside `N`, then `∮ Re(ψ ψ̄ₙ) dℓ → 0` outside a larger null set, by Cauchy–Schwarz with
    `|ψ| ≤ ‖ψ̃‖_∞` and `∮ ρ² dt ≤ C` (`ρ ≤ C d` and `lem:orbit-time-integrals`). -/
theorem ee_first_trace_limit (ω : L2) {N : Set ℝ}
    (hn : Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
      (𝓝[Ioi 0 \ N] 0) (𝓝 0)) :
    ∃ N' : Set ℝ, volume N' = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦
          gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re)
        (𝓝[Ioi 0 \ (N ∪ N')] 0) (𝓝 0) := by
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  -- `|ψ| ≤ M` and `|ψₙ|²` integrable along almost every level.
  set M := ‖continuousRep (invLap ω)‖
  have hM : ∀ᵐ p ∂(volume.restrict cellSquare), ‖streamLift ω p‖ ≤ M := by
    refine ae_restrict_of_ae ?_
    filter_upwards [streamLift_ae_eq_contStream ω] with p hp
    rw [hp, contStream]
    exact (continuousRep (invLap ω)).norm_coe_le_norm _
  have hMlev := ae_level_of_ae_cellSquare (P := fun p ↦ ‖streamLift ω p‖ ≤ M)
    (measurableSet_le (hmeas (invLap ω)).norm measurable_const) hM
  have hAs : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  have hnm : Measurable (streamNormal ω) := by
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    change Measurable fun p ↦ normalDeriv (streamLiftX ω) (streamLiftY ω) p
    simp only [normalDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have hni : IntegrableOn (fun p ↦ ‖streamNormal ω p‖ ^ 2) cellSquare := by
    refine (((hsq (streamPartial 0 ω)).add (hsq (streamPartial 1 ω))).const_mul 2).mono'
      (hnm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    have := norm_normalDeriv_le (streamLiftX ω) (streamLiftY ω) p
    have h0 := norm_nonneg (streamNormal ω p)
    rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
    simp only [streamNormal, streamLiftX, streamLiftY] at this h0 ⊢
    nlinarith [sq_nonneg (‖liftL2 (streamPartial 0 ω) p‖ - ‖liftL2 (streamPartial 1 ω) p‖),
      norm_nonneg (liftL2 (streamPartial 0 ω) p), norm_nonneg (liftL2 (streamPartial 1 ω) p)]
  -- The exceptional levels.
  have hgood := hMlev.and (integral_cellSquare_eq hni).1
  set N' : Set ℝ := {h | h ∈ Ioo 0 1 ∧ ¬ ((∀ᵐ t ∂(volume.restrict
    (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))), ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) ∧
    IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))}
  have hN' : volume N' = 0 := by
    have := (ae_restrict_iff' measurableSet_Ioo).1 hgood
    rw [ae_iff] at this
    refine measure_mono_null (fun h hh ↦ ?_) this
    exact fun himp ↦ hh.2 (himp hh.1)
  refine ⟨N', hN', ?_⟩
  -- The bound `|∮ Re(ψ ψ̄ₙ) dℓ| ≤ M (K ∮ |ψₙ|² dt)^{1/2}` on good levels near the separatrix.
  obtain ⟨K, h₀, hh₀, hK⟩ := levelIntegral_gradNorm_sq_le
  have hfilt : 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  have hup : Tendsto (fun h ↦ M * √(K * levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2))
      (𝓝[Ioi 0 \ (N ∪ N')] 0) (𝓝 0) := by
    have := ((hn.mono_left hfilt).const_mul K).sqrt.const_mul M
    simpa using this
  refine squeeze_zero_norm' ?_ hup
  have hsmall : ∀ᶠ h in 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0, h ∈ Ioo 0 (min h₀ 1) := by
    have h1 : Ioo (0 : ℝ) (min h₀ 1) ∈ 𝓝[Ioi 0] 0 := Ioo_mem_nhdsGT (lt_min hh₀ one_pos)
    exact nhdsWithin_mono _ sdiff_subset h1
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hmem
  have h1 : h < 1 := hh.2.trans_le (min_le_right _ _)
  have hgh : (∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) ∧
      IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
        (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)) := by
    by_contra hc
    exact hmem.2 (Or.inr ⟨⟨hh.1, h1⟩, hc⟩)
  obtain ⟨hMh, hnh⟩ := hgh
  rw [Real.norm_eq_abs]
  exact abs_levelIntegral_first_le ω (norm_nonneg _) hh.1 h1
    (hK h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩ h1) hnh hMh

/-- Weighted gradient traces (`lem:ee-gradient-traces`). For `ψ` even under both reflections,
    along levels `h → 0` outside a null set: `∮ |ψₙ|² dt → 0`,
    `∮ |ψₜ|² dt → ∑_γ ∫ ½ cosh² s |g_γ'(s)|² ds` with `g_γ = ψ̃ ∘ γ` the arc traces (on an arc
    `|ψₜ|² = ½ cosh² s |g'|²`), and `∮ Re(ψ ψ̄ₙ) dℓ → 0`. Assembled from `ee_arc_energy`,
    `ee_level_traces` and `ee_first_trace_limit`. -/
theorem ee_gradient_traces {ω : L2} (hω : InSector true true ω) :
    (∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamTangent ω p‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∑ k ∈ Finset.range 4,
          ∫ s, Real.cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2)) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦
          gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  obtain ⟨N, hN, hn, ht⟩ := ee_level_traces hω
  obtain ⟨N', hN', hf⟩ := ee_first_trace_limit ω hn
  have hmono : 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  exact ⟨ee_arc_energy hω, N ∪ N', measure_union_null hN hN', hn.mono_left hmono,
    ht.mono_left hmono, hf⟩

/-! ### The trace of the stream function on the arcs -/

/-- The trace of `ψ̃` on the separatrix arc `γ₀` is locally absolutely continuous and
    differentiable almost everywhere (`lem:arc-trace-ac`). The arc is the segment of the line
    `b = π/2` with `a = arcAngle s - π/2`, and along this line the continuous `H²` function
    `ψ̃` is absolutely continuous (`lem:traces`); `s ↦ a` is antitone and `1`-Lipschitz. -/
theorem absolutelyContinuous_contStream_separatrixArc (ω : L2) :
    (∀ c d, AbsolutelyContinuousOnInterval (contStream ω ∘ separatrixArc) c d) ∧
    ∀ᵐ s, DifferentiableAt ℝ (contStream ω ∘ separatrixArc) s := by
  set U : Set (ℝ × ℝ) := diagRect (Ioo (-Real.pi) Real.pi) (Ioo 0 Real.pi) with hU_def
  have hdc : Continuous diagCoord := by unfold diagCoord; fun_prop
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage (continuous_fst.comp hdc)).inter
      (isOpen_Ioo.preimage (continuous_snd.comp hdc))
  have hb : Bornology.IsBounded U := by
    refine (isCompact_Icc (a := ((-2 * Real.pi, -2 * Real.pi) : ℝ × ℝ))
      (b := (2 * Real.pi, 2 * Real.pi))).isBounded.subset fun p hp ↦ ?_
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    simp only [diagCoord] at h1 h2 h3 h4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith [Real.pi_pos]
  have hrep := streamLift_ae_eq_contStream ω
  have hH2 : MemSobolevOn 2 U (contStream ω) :=
    (memSobolevOn_liftL2 (memSobolev_two_invLap ω) hb).congr_ae hrep
  have hx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0) U).congr_left hrep
  have hy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1) U).congr_left hrep
  obtain ⟨-, -, -, hac, -, -⟩ := absolutelyContinuous_trace_of_H2 hU (a₀ := -Real.pi)
    (a₁ := Real.pi) (b₁ := 0) (b₂ := Real.pi) (b₀ := Real.pi / 2) (by linarith [Real.pi_pos])
    subset_rfl ⟨by positivity, by linarith [Real.pi_pos]⟩ (continuous_contStream ω).continuousOn
    hH2 hx hy
  set f : ℝ → ℂ := fun a ↦ contStream ω (diagInv (a, Real.pi / 2)) with hf_def
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - Real.pi / 2 with hφ_def
  have hcomp : contStream ω ∘ separatrixArc = f ∘ φ := by
    funext s
    simp only [Function.comp_apply, hf_def, hφ_def, diagInv_apply, separatrixArc]
    congr 2 <;> ring
  have hφa : Antitone φ := fun s t hst ↦ by simpa [hφ_def] using antitone_arcAngle hst
  have hφL : LipschitzWith 1 φ := LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa [hφ_def, Real.dist_eq] using lipschitzWith_arcAngle.dist_le_mul x y
  have hφr (s : ℝ) : φ s ∈ Ioo (-Real.pi) Real.pi := by
    have := arcAngle_mem_Ioo s
    exact ⟨by simp only [hφ_def]; linarith [this.1, Real.pi_pos],
      by simp only [hφ_def]; linarith [this.2, Real.pi_pos]⟩
  have hacs (c d : ℝ) : AbsolutelyContinuousOnInterval (contStream ω ∘ separatrixArc) c d := by
    rw [hcomp]
    have hle : φ (max c d) ≤ φ (min c d) := hφa (min_le_max)
    refine AbsolutelyContinuousOnInterval.comp_antitoneOn
      (hac _ _ (hφr _).1 hle (hφr _).2) hφL.lipschitzOnWith (hφa.antitoneOn _) fun s hs ↦ ?_
    rw [uIcc_of_le hle]
    exact ⟨hφa hs.2, hφa hs.1⟩
  refine ⟨hacs, ?_⟩
  have hn : ∀ n : ℕ, ∀ᵐ s, s ∈ uIcc (-(n : ℝ)) n →
      DifferentiableAt ℝ (contStream ω ∘ separatrixArc) s := fun n ↦
    (hacs _ _).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [ae_all_iff.2 hn] with s hs
  obtain ⟨n, hn⟩ := exists_nat_ge |s|
  exact hs n (by rw [uIcc_of_le (by linarith [abs_nonneg s])]; exact abs_le.1 hn)

/-! ### Even H² functions and their arc traces -/

/-- An H² torus function has an L² Fourier Laplacian. -/
theorem MemSobolev.exists_hasFourierLaplacian {φ : L2} (hφ : MemSobolev 2 φ) :
    ∃ ζ : L2, HasFourierLaplacian φ ζ := by
  obtain ⟨dx, hdx⟩ := (hφ.mono (by norm_num : (1 : ℝ) ≤ 2)).exists_hasFourierPartial 0
  obtain ⟨dy, hdy⟩ := (hφ.mono (by norm_num : (1 : ℝ) ≤ 2)).exists_hasFourierPartial 1
  have hφ' : MemSobolev ((1 : ℝ) + 1) φ := by
    norm_num
    exact hφ
  have hx : MemSobolev 1 dx := hφ'.of_hasFourierPartial hdx
  have hy : MemSobolev 1 dy := hφ'.of_hasFourierPartial hdy
  obtain ⟨dxx, hdxx⟩ := hx.exists_hasFourierPartial 0
  obtain ⟨dyy, hdyy⟩ := hy.exists_hasFourierPartial 1
  exact ⟨dxx + dyy, hasFourierLaplacian_of_second
    ((hasFourierPartial_iff_second hdx).mp hdxx) ((hasFourierPartial_iff_second hdy).mp hdyy)⟩

/-- Reconstruction by the inverse Laplacian loses only the constant Fourier mode. -/
theorem HasFourierLaplacian.continuousRep_eq {φ ζ : L2} (h : HasFourierLaplacian φ ζ)
    (hφ : MemSobolev 2 φ) (t : Torus) :
    continuousRep φ t = continuousRep (invLap ζ) t + fourierCoeff φ 0 := by
  have hsum := (hφ.hasSum_continuousRep t).sub ((memSobolev_two_invLap ζ).hasSum_continuousRep t)
  have hz : continuousRep φ t - continuousRep (invLap ζ) t = fourierCoeff φ 0 := by
    rw [← hsum.tsum_eq, tsum_eq_single 0]
    · simp [fourierCoeff_invLap, char_zero]
    · intro k hk
      have hn : (normSq k : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos k hk).ne'
      have hc : fourierCoeff (invLap ζ) k = fourierCoeff φ k := by
        simp only [fourierCoeff_invLap, hk, ite_false, h k]
        field_simp
      simp only [hc, sub_self]
  linear_combination hz

/-- The Fourier Laplacian commutes with the character symmetries. -/
theorem CharacterSymmetry.hasFourierLaplacian (s : CharacterSymmetry) {φ ζ : L2}
    (h : HasFourierLaplacian φ ζ) :
    HasFourierLaplacian (s.action φ) (s.action ζ) := by
  intro l
  obtain ⟨k, rfl⟩ := s.onto l
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr (s.phase_ne_zero k))
  rw [s.coefficient, s.normSq_eq, mul_left_comm, s.coefficient, h k]

/-- Taking the Fourier Laplacian preserves evenness under both reflections. -/
theorem InSector.even_laplacian {φ ζ : L2} (hs : InSector true true φ)
    (h : HasFourierLaplacian φ ζ) : InSector true true ζ := by
  simp only [InSector, paritySign, ite_true, one_smul] at hs ⊢
  have h1 := symmetry₁.hasFourierLaplacian h
  have h2 := symmetry₂.hasFourierLaplacian h
  change HasFourierLaplacian (reflect₁ φ) (reflect₁ ζ) at h1
  change HasFourierLaplacian (reflect₂ φ) (reflect₂ ζ) at h2
  rw [hs.1] at h1
  rw [hs.2] at h2
  exact ⟨fourierCoeff_ext fun k ↦ (h1 k).trans (h k).symm,
    fourierCoeff_ext fun k ↦ (h2 k).trans (h k).symm⟩

/-- An even H² function has locally absolutely continuous arc traces and finite
    cosh-weighted derivative energy. Subtracting its mean reduces this to stream traces. -/
theorem even_sobolev_arc_regularity {φ : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) {k : ℕ} (hk : k < 4) :
    (∀ c d, AbsolutelyContinuousOnInterval
      (fun s ↦ continuousRep φ (torusProj (cellArc k s))) c d) ∧
    (∀ᵐ s, DifferentiableAt ℝ
      (fun s ↦ continuousRep φ (torusProj (cellArc k s))) s) ∧
    Integrable (fun s ↦ Real.cosh s ^ 2 *
      ‖deriv (fun t ↦ continuousRep φ (torusProj (cellArc k t))) s‖ ^ 2) := by
  obtain ⟨ζ, hζ⟩ := hφ.exists_hasFourierLaplacian
  have hcomp : (fun s ↦ continuousRep φ (torusProj (cellArc k s))) =
      fun s ↦ (contStream (rotate^[k] ζ) ∘ separatrixArc) s + fourierCoeff φ 0 := by
    funext s
    change continuousRep φ (torusProj (rotLift^[k] (separatrixArc s))) =
      contStream (rotate^[k] ζ) (separatrixArc s) + _
    rw [contStream_iterate_rotate]
    exact hζ.continuousRep_eq hφ _
  obtain ⟨hac, hd⟩ := absolutelyContinuous_contStream_separatrixArc (rotate^[k] ζ)
  refine ⟨?_, ?_, ?_⟩
  · intro c d
    rw [hcomp]
    exact (hac c d).add
      ((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval)
  · filter_upwards [hd] with s hs
    rw [hcomp]
    exact hs.add_const _
  · have hg : (fun s ↦ continuousRep φ (torusProj (cellArc k s))) =
        fun s ↦ (contStream ζ ∘ cellArc k) s + fourierCoeff φ 0 :=
      funext fun s ↦ hζ.continuousRep_eq hφ _
    rw [hg]
    simpa only [deriv_add_const] using ee_arc_energy (hs.even_laplacian hζ) k hk

/-! ### Functions of `ξ = tanh s` -/

/-- `artanh' = 1/(1 - ξ²)` on `(-1, 1)`. -/
theorem hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / boundaryWeight x) x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hq : DifferentiableAt ℝ (fun x : ℝ ↦ (1 + x) / (1 - x)) x :=
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).differentiableAt.div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).differentiableAt
      (by linarith [hx.2])
  have hc : ContinuousAt Real.artanh x := by
    have hd : DifferentiableAt ℝ (fun x : ℝ ↦ (1 / 2) * Real.log ((1 + x) / (1 - x))) x :=
      (hq.log hp.ne').const_mul _
    refine hd.continuousAt.congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
  have hw : boundaryWeight x ≠ 0 := by
    unfold boundaryWeight
    nlinarith [hx.1, hx.2]
  have h := (hasDerivAt_tanh (Real.artanh x)).of_local_left_inverse hc
    (by rw [Real.tanh_artanh hx]; unfold boundaryWeight at hw; exact hw)
    (by filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy; exact Real.tanh_artanh hy)
  rw [Real.tanh_artanh hx] at h
  simpa [boundaryWeight, one_div] using h

/-- Almost-everywhere statements in `s` hold at `artanh ξ` for almost every `ξ ∈ (-1, 1)`. -/
theorem ae_comp_artanh {P : ℝ → Prop} (hP : ∀ᵐ s, P s) :
    ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → P (Real.artanh x) := by
  rw [ae_iff] at hP ⊢
  have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (f := Real.tanh) (s := {s | ¬P s})
    (fun s _ ↦ (hasDerivAt_tanh s).differentiableAt.differentiableWithinAt) hP
  refine measure_mono_null (fun x hx ↦ ?_) him
  simp only [mem_ofPred_eq, not_imp] at hx
  exact ⟨Real.artanh x, hx.2, Real.tanh_artanh hx.1⟩

/-- Integrability on `(-1, 1)` in terms of `s = artanh ξ`, `dξ = ds / cosh² s`. -/
theorem integrableOn_Ioo_iff_tanh {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) :
    IntegrableOn f (Ioo (-1) 1) ↔ Integrable fun s ↦ (1 / Real.cosh s ^ 2) • f (Real.tanh s) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_tanh x).hasDerivWithinAt) Real.tanh_injective.injOn f
  rw [Real.tanh_bijOn.image_eq, integrableOn_univ] at h
  rw [h]
  refine integrable_congr (Eventually.of_forall fun s ↦ ?_)
  simp only
  rw [one_sub_tanh_sq, abs_of_pos (by have := Real.cosh_pos s; positivity)]

/-- Composition with `artanh` keeps local absolute continuity on `(-1, 1)`. -/
theorem absolutelyContinuousOnInterval_comp_artanh {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} (hf : ∀ c d, AbsolutelyContinuousOnInterval f c d) {c d : ℝ} (hc : -1 < c)
    (hcd : c ≤ d) (hd : d < 1) : AbsolutelyContinuousOnInterval (f ∘ Real.artanh) c d := by
  have hsub : uIcc c d ⊆ Ioo (-1) 1 := by
    rw [uIcc_of_le hcd]
    exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- On `[c, d]`, `1/(1 - x²) ≤ 1/m` with `m = min (1 - c²) (1 - d²) > 0`.
  set m := min (1 - c ^ 2) (1 - d ^ 2) with hm
  have hm0 : 0 < m := lt_min (by nlinarith) (by nlinarith)
  have hbound : ∀ x ∈ uIcc c d, ‖1 / boundaryWeight x‖₊ ≤ Real.toNNReal (1 / m) := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    have hw : m ≤ boundaryWeight x := by
      unfold boundaryWeight
      rcases le_total 0 x with h0 | h0
      · exact (min_le_right _ _).trans (by nlinarith [hx.2])
      · exact (min_le_left _ _).trans (by nlinarith [hx.1])
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity),
      Real.norm_of_nonneg (by have := hm0.trans_le hw; positivity)]
    exact one_div_le_one_div_of_le hm0 hw
  have hL := (convex_uIcc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx ↦ (hasDerivAt_artanh (hsub hx)).hasDerivWithinAt) hbound
  refine AbsolutelyContinuousOnInterval.comp_monotoneOn (hf (Real.artanh c) (Real.artanh d)) hL
    (fun x hx y hy h ↦ Real.artanh_le_artanh (hsub hx).1 (hsub hy).2 h) fun x hx ↦ ?_
  rw [uIcc_of_le hcd] at hx
  rw [uIcc_of_le (Real.artanh_le_artanh hc hd hcd)]
  exact ⟨Real.artanh_le_artanh hc (hsub (by rw [uIcc_of_le hcd]; exact hx)).2 hx.1,
    Real.artanh_le_artanh (hsub (by rw [uIcc_of_le hcd]; exact hx)).1 hd hx.2⟩

/-- The primitive of an integrable complex function is absolutely continuous on every
    interval (real and imaginary parts separately). -/
theorem absolutelyContinuousOnInterval_primitive {p : ℝ → ℂ} (hp : Integrable p) (c d : ℝ) :
    AbsolutelyContinuousOnInterval (fun s ↦ ∫ t in (0 : ℝ)..s, p t) c d := by
  have hR (q : ℝ → ℝ) (hq : Integrable q) :
      AbsolutelyContinuousOnInterval (fun s ↦ ((∫ t in (0 : ℝ)..s, q t : ℝ) : ℂ)) c d := by
    have h := IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (hq.intervalIntegrable (a := c) (b := d)) (c := c) left_mem_uIcc
    have heq : (fun s ↦ ∫ t in (0 : ℝ)..s, q t) =
        fun s ↦ (∫ t in (0 : ℝ)..c, q t) + ∫ t in c..s, q t := funext fun s ↦
      (intervalIntegral.integral_add_adjacent_intervals hq.intervalIntegrable
        hq.intervalIntegrable).symm
    have hac : AbsolutelyContinuousOnInterval (fun s ↦ ∫ t in (0 : ℝ)..s, q t) c d := by
      rw [heq]
      exact ((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval).add h
    exact Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval hac
  have heq : (fun s ↦ ∫ t in (0 : ℝ)..s, p t) = fun s ↦
      ((∫ t in (0 : ℝ)..s, (p t).re : ℝ) : ℂ) +
        Complex.I • ((∫ t in (0 : ℝ)..s, (p t).im : ℝ) : ℂ) := by
    funext s
    have hre : IntervalIntegrable (fun t ↦ ((p t).re : ℂ)) volume 0 s :=
      (hp.re.ofReal (𝕜 := ℂ)).intervalIntegrable
    have him : IntervalIntegrable (fun t ↦ ((p t).im : ℂ) * Complex.I) volume 0 s :=
      ((hp.im.ofReal (𝕜 := ℂ)).mul_const _).intervalIntegrable
    conv_lhs => rw [show p = fun t ↦ ((p t).re : ℂ) + ((p t).im : ℂ) * Complex.I from
      funext fun t ↦ (Complex.re_add_im _).symm]
    rw [intervalIntegral.integral_add hre him, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, smul_eq_mul, mul_comm]
  rw [heq]
  exact (hR _ hp.re).add ((hR _ hp.im).const_smul Complex.I)

theorem continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1) 1) := fun _ hx ↦
  (hasDerivAt_artanh hx).continuousAt.continuousWithinAt

theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

/-- `artanh ξ → ∞` as `ξ → 1⁻`. -/
theorem tendsto_artanh_nhdsLT_one : Tendsto Real.artanh (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  have hb : Real.tanh b < 1 := Real.tanh_lt_one b
  filter_upwards [Ioo_mem_nhdsLT hb] with x hx
  calc b = Real.artanh (Real.tanh b) := (Real.artanh_tanh b).symm
    _ ≤ Real.artanh x := Real.artanh_le_artanh (Real.neg_one_lt_tanh b) hx.2 hx.1.le

/-- `artanh ξ → -∞` as `ξ → -1⁺`. -/
theorem tendsto_artanh_nhdsGT_neg_one : Tendsto Real.artanh (𝓝[>] (-1)) atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  have hb : -1 < Real.tanh b := Real.neg_one_lt_tanh b
  filter_upwards [Ioo_mem_nhdsGT hb] with x hx
  calc Real.artanh x ≤ Real.artanh (Real.tanh b) :=
        Real.artanh_le_artanh hx.1 (Real.tanh_lt_one b) hx.2.le
    _ = b := Real.artanh_tanh b

/-- `L²` on `(-1, 1)` in terms of `s = artanh ξ`. -/
theorem memLp_two_Ioo_of_tanh {Φ : ℝ → ℂ}
    (hm : AEStronglyMeasurable Φ (volume.restrict (Ioo (-1) 1)))
    (h : Integrable fun s ↦ 1 / Real.cosh s ^ 2 * ‖Φ (Real.tanh s)‖ ^ 2) :
    MemLp Φ 2 (volume.restrict (Ioo (-1) 1)) :=
  (memLp_two_iff_integrable_sq_norm hm).2
    ((integrableOn_Ioo_iff_tanh (fun x ↦ ‖Φ x‖ ^ 2)).2 (by simpa only [smul_eq_mul] using h))

/-- A canonical profile with a weighted arc derivative and zero Melnikov integral gives
    the weighted interval domain, the actual forcing trace, and its endpoint values.
    This one-dimensional result does not assume an eigenvalue equation. -/
theorem canonical_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {g : ℝ → ℂ}
    (hgac : ∀ c d, AbsolutelyContinuousOnInterval g c d)
    (hgd : ∀ᵐ s, DifferentiableAt ℝ g s)
    (hg1 : Integrable (deriv g))
    (hg2 : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2)
    {M : ℝ} (hgb : ∀ s, ‖g s‖ ≤ M)
    (hM : ∫ t, profileIntegrand lam g t = 0)
    {cp cm : ℂ} (hgp : Tendsto g atTop (𝓝 cp)) (hgm : Tendsto g atBot (𝓝 cm)) :
    ∃ D E : ℝ → ℂ,
      HasWeightedBoundaryH2 (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) D E ∧
      MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ -
        lam * canonicalUnknown lam g (Real.artanh ξ)) ∧
      (∀ ξ ∈ Ioo (-1 : ℝ) 1, -Complex.I * boundaryWeight ξ * D ξ -
        lam * canonicalUnknown lam g (Real.artanh ξ) = g (Real.artanh ξ)) ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) D 1 =
        -cp / lam ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ)) D (-1) =
        -cm / lam := by
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam
  /- The canonical profile `Ω`. -/
  set Ω : ℝ → ℂ := canonicalProfile lam g with hΩ_def
  have hΩp : Tendsto Ω atTop (𝓝 0) := tendsto_canonicalProfile_atTop hg1
  have hΩm : Tendsto Ω atBot (𝓝 0) := (tendsto_canonicalProfile_atBot_iff hg1).2 hM
  have hΩd : ∀ᵐ s, HasDerivAt Ω (Complex.I * lam * Ω s - deriv g s) s :=
    ae_hasDerivAt_canonicalProfile hg1
  have hzd : ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (Complex.I * -Ω s) s :=
    ae_hasDerivAt_canonicalUnknown hlam hg1 hgd
  -- The weighted bound, compared with `cosh` (`cosh ≤ e^{|s|} ≤ 2 cosh`).
  have hΩw := eLpNorm_exp_mul_canonicalProfile_le (lam := lam) hg1 hM
  have hexp (s : ℝ) : Real.cosh s ≤ Real.exp |s| ∧ Real.exp |s| ≤ 2 * Real.cosh s := by
    rw [Real.cosh_eq]
    have h1 := Real.exp_pos s
    have h2 := Real.exp_pos (-s)
    rcases abs_cases s with ⟨hs, h0⟩ | ⟨hs, h0⟩ <;> rw [hs]
    · have := Real.exp_le_exp.2 (show -s ≤ s by linarith)
      constructor <;> linarith
    · have := Real.exp_le_exp.2 (show s ≤ -s by linarith)
      constructor <;> linarith
  have hΩc : Continuous Ω := continuous_canonicalProfile hg1
  have hgm' : Measurable (deriv g) := measurable_deriv g
  have hRHS : MemLp (fun s ↦ (Real.exp |s| : ℂ) * deriv g s) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 ((hg2.const_mul 4).mono'
      (by fun_prop) (Eventually.of_forall fun s ↦ ?_))
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have := (hexp s).2
    have h0 := (Real.exp_pos |s|).le
    nlinarith [sq_nonneg ‖deriv g s‖, mul_le_mul this this h0 (by linarith)]
  have hLHS : MemLp (fun s ↦ (Real.exp |s| : ℂ) * Ω s) 2 volume := hΩw.trans_lt hRHS
  have hΩ2 : Integrable fun s ↦ Real.cosh s ^ 2 * ‖Ω s‖ ^ 2 := by
    refine ((memLp_two_iff_integrable_sq_norm (by fun_prop)).1 hLHS).mono' (by fun_prop)
      (Eventually.of_forall fun s ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have := (hexp s).1
    have h0 := (Real.cosh_pos s).le
    nlinarith [sq_nonneg ‖Ω s‖, mul_le_mul this this h0 (by linarith [Real.exp_pos |s|])]
  -- `|Ω(s)| ≤ ‖g'‖_{L¹}`, from the definition.
  have hΩb : ∀ s, ‖Ω s‖ ≤ ∫ t, ‖deriv g t‖ := by
    intro s
    rw [hΩ_def, norm_canonicalProfile]
    calc ‖∫ t in Ioi s, profileIntegrand lam g t‖
        ≤ ∫ t in Ioi s, ‖profileIntegrand lam g t‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Ioi s, ‖deriv g t‖ := by
          congr 1
          funext t
          rw [profileIntegrand, norm_mul, norm_exp_neg_I_mul, mul_one]
      _ ≤ ∫ t, ‖deriv g t‖ :=
          setIntegral_le_integral hg1.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
  -- `Ω` is an exponential times an indefinite integral of an integrable function.
  have hΩac : ∀ c d, AbsolutelyContinuousOnInterval Ω c d :=
    fun c d ↦ absolutelyContinuousOnInterval_canonicalProfile hg1 c d
  /- The functions in `ξ = tanh s`: `F = z ∘ artanh`, `D = F'`, `E = D'`. With
     `w = 1 - ξ² = sech² s`: `wF' = z' = -iΩ` and `w²D' = -i((iλ + 2ξ)Ω - g')`. -/
  set F : ℝ → ℂ := fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ) with hF_def
  set D : ℝ → ℂ := fun ξ ↦ -Complex.I * Ω (Real.artanh ξ) / boundaryWeight ξ with hD_def
  set E : ℝ → ℂ := fun ξ ↦ -Complex.I * ((Complex.I * lam + 2 * ξ) * Ω (Real.artanh ξ) -
    deriv g (Real.artanh ξ)) / (boundaryWeight ξ : ℂ) ^ 2 with hE_def
  -- Common facts: `w > 0` on `(-1, 1)`, `w(tanh s) = 1/cosh² s`, and `z` is continuous,
  -- locally absolutely continuous and bounded.
  have hw (ξ : ℝ) (hξ : ξ ∈ Ioo (-1 : ℝ) 1) : 0 < boundaryWeight ξ := by
    unfold boundaryWeight
    nlinarith [hξ.1, hξ.2]
  have hwt (s : ℝ) : boundaryWeight (Real.tanh s) = 1 / Real.cosh s ^ 2 := boundaryWeight_tanh s
  have hmemt (s : ℝ) : Real.tanh s ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩
  have hgc : Continuous g := continuous_of_absolutelyContinuous hgac
  have hz_eq : canonicalUnknown lam g = fun s ↦ -(lam : ℂ)⁻¹ * (Ω s + g s) := by
    funext s
    rw [canonicalUnknown, hΩ_def]
    field_simp
  have hzc : Continuous (canonicalUnknown lam g) := by
    rw [hz_eq]
    exact continuous_const.mul (hΩc.add hgc)
  have hzac (c d : ℝ) : AbsolutelyContinuousOnInterval (canonicalUnknown lam g) c d := by
    rw [hz_eq]
    convert ((hΩac c d).add (hgac c d)).const_smul (-(lam : ℂ)⁻¹) using 1
  set B : ℝ := ∫ t, ‖deriv g t‖
  have hzb (s : ℝ) : ‖canonicalUnknown lam g s‖ ≤ ‖(lam : ℂ)⁻¹‖ * (B + M) := by
    rw [hz_eq, norm_mul, norm_neg]
    gcongr
    exact (norm_add_le _ _).trans (add_le_add (hΩb s) (hgb s))
  -- `F` is bounded, `∫|D|² dξ = ∫ cosh² |Ω|² ds`, and the chain rule under `artanh`.
  have hDt (s : ℝ) : D (Real.tanh s) = -Complex.I * Ω s * (Real.cosh s ^ 2 : ℝ) := by
    simp only [hD_def, Real.artanh_tanh, hwt]
    have := (Real.cosh_pos s).ne'
    push_cast
    field_simp
  have hDc : ContinuousOn D (Ioo (-1) 1) := by
    refine ((continuous_const.mul hΩc).comp_continuousOn continuousOn_artanh).div
      (Complex.continuous_ofReal.comp (by unfold boundaryWeight; fun_prop)).continuousOn
      fun ξ hξ ↦ ?_
    exact Complex.ofReal_ne_zero.2 (hw ξ hξ).ne'
  have hFH1 : HasIntervalH1 (-1) 1 F D := by
    refine ⟨?_, ?_, fun c d hc hcd hd ↦ absolutelyContinuousOnInterval_comp_artanh hzac hc hcd hd,
      ?_⟩
    · exact MemLp.of_bound ((hzc.comp_continuousOn continuousOn_artanh).aestronglyMeasurable
        measurableSet_Ioo) _ (Eventually.of_forall fun ξ ↦ hzb _)
    · refine memLp_two_Ioo_of_tanh (hDc.aestronglyMeasurable measurableSet_Ioo)
        (hΩ2.congr (Eventually.of_forall fun s ↦ ?_))
      have hc := (Real.cosh_pos s).ne'
      beta_reduce
      rw [hDt, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      field_simp
    · filter_upwards [ae_comp_artanh hzd] with ξ hξ hmem
      have h := (hξ hmem).scomp ξ (hasDerivAt_artanh hmem)
      convert h using 1
      · rfl
      · simp only [hD_def, Complex.real_smul]
        push_cast
        ring
  -- `D = (1/w) • (-iΩ ∘ artanh)`, with `1/w` smooth on compact subintervals.
  have hDeq : D = fun ξ ↦ ((1 / boundaryWeight ξ : ℝ) : ℂ) * (-Complex.I * Ω (Real.artanh ξ)) := by
    funext ξ
    simp only [hD_def]
    push_cast
    ring
  have hwd (ξ : ℝ) : HasDerivAt boundaryWeight (-2 * ξ) ξ := by
    unfold boundaryWeight
    simpa using ((hasDerivAt_id ξ).pow 2).const_sub 1
  have hDac : ∀ c d, -1 < c → c ≤ d → d < 1 → AbsolutelyContinuousOnInterval D c d := by
    intro c d hc hcd hd
    have hsub : uIcc c d ⊆ Ioo (-1) 1 := by
      rw [uIcc_of_le hcd]
      exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : AbsolutelyContinuousOnInterval (fun ξ ↦ -Complex.I * Ω (Real.artanh ξ)) c d := by
      convert (absolutelyContinuousOnInterval_comp_artanh hΩac hc hcd hd).const_smul
        (-Complex.I) using 1
      funext ξ
      rfl
    have h2 : AbsolutelyContinuousOnInterval
        (fun ξ ↦ ((1 / boundaryWeight ξ : ℝ) : ℂ)) c d := by
      refine ContDiffOn.absolutelyContinuousOnInterval ?_
      refine Complex.ofRealCLM.contDiff.comp_contDiffOn
        (contDiffOn_const.div (by unfold boundaryWeight; fun_prop) fun x hx ↦ ?_)
      exact (hw x (hsub hx)).ne'
    rw [hDeq]
    exact h2.smul h1
  have hDd : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt D (E x) x := by
    filter_upwards [ae_comp_artanh hΩd] with ξ hξ hmem
    have hw0 := (hw ξ hmem).ne'
    have hΩ' := ((hξ hmem).scomp ξ (hasDerivAt_artanh hmem)).const_mul (-Complex.I)
    have hinv := ((hasDerivAt_const ξ (1 : ℝ)).div (hwd ξ) hw0).ofReal_comp
    have hprod := hinv.mul hΩ'
    rw [hDeq]
    convert hprod using 1
    · rfl
    · simp only [hE_def, Complex.real_smul, Function.comp_apply, Pi.div_apply]
      have hw0' : (boundaryWeight ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw0
      push_cast
      field_simp
      ring_nf
  -- `|wE(tanh s)|² / cosh² s = cosh² s |(iλ + 2 tanh s)Ω - g'|²`.
  have hEm : Measurable E := by
    have := measurable_artanh
    have := hΩc.measurable
    simp only [hE_def, boundaryWeight]
    fun_prop
  have hwE : MemLp (fun x ↦ (boundaryWeight x : ℂ) * E x) 2 (volume.restrict (Ioo (-1) 1)) := by
    refine memLp_two_Ioo_of_tanh (by unfold boundaryWeight; fun_prop) ?_
    have hbound : Integrable fun s ↦ 2 * ((|lam| + 2) ^ 2 * (Real.cosh s ^ 2 * ‖Ω s‖ ^ 2)) +
        2 * (Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2) :=
      ((hΩ2.const_mul _).const_mul 2).add (hg2.const_mul 2)
    have hmeasL : Measurable fun s ↦ 1 / Real.cosh s ^ 2 *
        ‖(boundaryWeight (Real.tanh s) : ℂ) * E (Real.tanh s)‖ ^ 2 := by
      have htm : Measurable Real.tanh :=
        (continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_tanh s).continuousAt).measurable
      unfold boundaryWeight
      fun_prop
    refine hbound.mono' hmeasL.aestronglyMeasurable (Eventually.of_forall fun s ↦ ?_)
    have hc := Real.cosh_pos s
    have hval : (boundaryWeight (Real.tanh s) : ℂ) * E (Real.tanh s) =
        -Complex.I * ((Complex.I * lam + 2 * Real.tanh s) * Ω s - deriv g s) *
          (Real.cosh s ^ 2 : ℝ) := by
      simp only [hE_def, Real.artanh_tanh, hwt]
      push_cast
      field_simp
    have hcoef : ‖Complex.I * lam + 2 * (Real.tanh s : ℂ)‖ ≤ |lam| + 2 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
        have := abs_lt.2 ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩
        nlinarith [abs_nonneg (Real.tanh s)]
    rw [Real.norm_of_nonneg (by positivity), hval, norm_mul, norm_mul, norm_neg, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    set a := ‖(Complex.I * lam + 2 * (Real.tanh s : ℂ)) * Ω s - deriv g s‖
    have ha : a ≤ (|lam| + 2) * ‖Ω s‖ + ‖deriv g s‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have ha0 : 0 ≤ a := norm_nonneg _
    have hsq : a ^ 2 ≤ 2 * ((|lam| + 2) ^ 2 * ‖Ω s‖ ^ 2) + 2 * ‖deriv g s‖ ^ 2 := by
      nlinarith [sq_nonneg ((|lam| + 2) * ‖Ω s‖ - ‖deriv g s‖), norm_nonneg (Ω s),
        norm_nonneg (deriv g s), abs_nonneg lam]
    have hc2 : 0 < Real.cosh s ^ 2 := by positivity
    calc 1 / Real.cosh s ^ 2 * (a * Real.cosh s ^ 2) ^ 2 = Real.cosh s ^ 2 * a ^ 2 := by
          field_simp
      _ ≤ Real.cosh s ^ 2 * (2 * ((|lam| + 2) ^ 2 * ‖Ω s‖ ^ 2) + 2 * ‖deriv g s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hc2.le
      _ = _ := by ring
  have hW : HasWeightedBoundaryH2 F D E := ⟨hFH1, hDac, hDd, hwE⟩
  /- `G = -iwD - λF` is the trace `g ∘ artanh` on `(-1, 1)`, and
     `∫|G'|² dξ = ∫ cosh² |g'|² ds` (`hg2`, `hgac`, `integral_tanh_subst`). -/
  have htrace (ξ : ℝ) (hξ : ξ ∈ Ioo (-1 : ℝ) 1) :
      -Complex.I * boundaryWeight ξ * D ξ - lam * F ξ = g (Real.artanh ξ) := by
    have hw0' : (boundaryWeight ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hw ξ hξ).ne'
    simp only [hD_def, hF_def, hz_eq]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hG : MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ - lam * F ξ) := by
    set Dg : ℝ → ℂ := fun ξ ↦ deriv g (Real.artanh ξ) / boundaryWeight ξ with hDg_def
    have hgH1 : HasIntervalH1 (-1) 1 (fun ξ ↦ g (Real.artanh ξ)) Dg := by
      refine ⟨?_, ?_,
        fun c d hc hcd hd ↦ absolutelyContinuousOnInterval_comp_artanh hgac hc hcd hd, ?_⟩
      · exact MemLp.of_bound ((hgc.comp_continuousOn continuousOn_artanh).aestronglyMeasurable
          measurableSet_Ioo) _ (Eventually.of_forall fun ξ ↦ hgb _)
      · have hDgm : Measurable Dg := by
          have := measurable_artanh
          simp only [hDg_def, boundaryWeight]
          fun_prop
        refine memLp_two_Ioo_of_tanh hDgm.aestronglyMeasurable
          (hg2.congr (Eventually.of_forall fun s ↦ ?_))
        have hc := (Real.cosh_pos s).ne'
        beta_reduce
        rw [hDg_def]
        simp only [Real.artanh_tanh, hwt]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        field_simp
      · filter_upwards [ae_comp_artanh hgd] with ξ hξ hmem
        have h := (hξ hmem).hasDerivAt.scomp ξ (hasDerivAt_artanh hmem)
        convert h using 1
        · rfl
        · simp only [hDg_def, Complex.real_smul]
          push_cast
          ring
    exact ⟨Dg, hgH1.congr_Ioo fun ξ hξ ↦ (htrace ξ hξ).symm⟩
  /- End values: the extension is continuous up to `±1` (`HasIntervalH1.continuousOn_
     extension`) and equals `F` inside, while `z(s) → -(0 + c±)/λ` (`hΩp`, `hΩm`, `hgp`, `hgm`). -/
  have hcont := hFH1.continuousOn_extension (by norm_num : (-1 : ℝ) < 1)
  have hext := hFH1.extension_eq (by norm_num : (-1 : ℝ) < 1)
  have hzlim {l : Filter ℝ} {c : ℂ} (hΩl : Tendsto Ω l (𝓝 0)) (hgl : Tendsto g l (𝓝 c)) :
      Tendsto (canonicalUnknown lam g) l (𝓝 (-c / lam)) := by
    rw [hz_eq]
    convert (hΩl.add hgl).const_mul (-(lam : ℂ)⁻¹) using 2
    field_simp
    ring
  have hend1 : intervalH1Extension (-1) 1 F D 1 = -cp / lam := by
    have hlimF : Tendsto F (𝓝[<] 1) (𝓝 (-cp / lam)) :=
      (hzlim hΩp hgp).comp tendsto_artanh_nhdsLT_one
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT (by norm_num)
    have hlimE : Tendsto (intervalH1Extension (-1) 1 F D) (𝓝[<] 1)
        (𝓝 (intervalH1Extension (-1) 1 F D 1)) :=
      (hcont 1 ⟨by norm_num, le_rfl⟩).tendsto.mono_left
        (nhdsWithin_le_of_mem (mem_of_superset hmem fun x hx ↦ ⟨hx.1.le, hx.2.le⟩))
    refine tendsto_nhds_unique hlimE (hlimF.congr' ?_)
    filter_upwards [hmem] with x hx
    exact (hext hx).symm
  have hend2 : intervalH1Extension (-1) 1 F D (-1) = -cm / lam := by
    have hlimF : Tendsto F (𝓝[>] (-1)) (𝓝 (-cm / lam)) :=
      (hzlim hΩm hgm).comp tendsto_artanh_nhdsGT_neg_one
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[>] (-1) := Ioo_mem_nhdsGT (by norm_num)
    have hlimE : Tendsto (intervalH1Extension (-1) 1 F D) (𝓝[>] (-1))
        (𝓝 (intervalH1Extension (-1) 1 F D (-1))) :=
      (hcont (-1) ⟨le_rfl, by norm_num⟩).tendsto.mono_left
        (nhdsWithin_le_of_mem (mem_of_superset hmem fun x hx ↦ ⟨hx.1.le, hx.2.le⟩))
    refine tendsto_nhds_unique hlimE (hlimF.congr' ?_)
    filter_upwards [hmem] with x hx
    exact (hext hx).symm
  exact ⟨D, E, hW, hG, htrace, hend1, hend2⟩

/-- Regularity of the boundary unknown (`lem:ee-boundary-regularity`). For an even–even
    eigenfunction with rotation character `κ`, on each arc `γ` the canonical transport unknown
    `z` of `g = ψ̃ ∘ γ`, written `F(ξ) = z(artanh ξ)`, lies in the weighted domain, `G =
    -iwF' - λF ∈ H¹(-1, 1)`, its endpoint values are `-c±/λ` with `c±` the saddle values of
    `ψ̃` at the ends of the arc, and `c₊ = κ c₋`. -/
theorem ee_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) {k : ℕ} (hk : k < 4) :
    ∃ D E : ℝ → ℂ,
      HasWeightedBoundaryH2 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D E ∧
      MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ -
        lam * canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D 1 = -contStream ω (rotLift^[k] (0, -Real.pi)) / lam ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D (-1) = -contStream ω (rotLift^[k] (Real.pi, 0)) / lam ∧
      contStream ω (rotLift^[k] (0, -Real.pi)) =
        paritySign κ * contStream ω (rotLift^[k] (Real.pi, 0)) := by
  -- Each step names the result it comes from.
  set g : ℝ → ℂ := contStream ω ∘ cellArc k with hg_def
  set cp : ℂ := contStream ω (rotLift^[k] (0, -Real.pi)) with hcp_def
  set cm : ℂ := contStream ω (rotLift^[k] (Real.pi, 0)) with hcm_def
  /- The trace `g = ψ̃ ∘ γ_k` on the arc. -/
  -- From the transport traces and the weighted gradient traces.
  have hg1 : Integrable (deriv g) := (ee_melnikov hlam hω hκ k).1
  have hg2 : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2 :=
    ee_arc_energy hs k hk
  -- Bounded, since `ψ̃` is a continuous periodic function.
  have hgb : ∀ s, ‖g s‖ ≤ ‖continuousRep (invLap ω)‖ := fun s ↦
    (continuousRep (invLap ω)).norm_coe_le_norm _
  -- Absolute continuity on `γ₀` (`lem:arc-trace-ac`), and `g = κᵏ (ψ̃ ∘ γ₀)`.
  have hArc : g = fun s ↦ paritySign κ ^ k * (contStream ω ∘ separatrixArc) s :=
    funext fun s ↦ contStream_iterate_rotLift hκ k (separatrixArc s)
  obtain ⟨hac0, hd0⟩ := absolutelyContinuous_contStream_separatrixArc ω
  have hgac : ∀ c d, AbsolutelyContinuousOnInterval g c d := fun c d ↦ by
    rw [hArc]
    simpa only [smul_eq_mul] using (hac0 c d).const_smul (paritySign κ ^ k)
  have hgd : ∀ᵐ s, DifferentiableAt ℝ g s := by
    filter_upwards [hd0] with s hs
    rw [hArc]
    exact hs.const_mul _
  -- The Melnikov identity (`ee_melnikov`).
  have hM : ∫ t, profileIntegrand lam g t = 0 := (ee_melnikov hlam hω hκ k).2
  -- End values: `tendsto_separatrixArc_atTop/atBot`, continuity of `ψ̃` and `rotLift`.
  have hRc : Continuous fun p ↦ contStream ω (rotLift^[k] p) :=
    (continuous_contStream ω).comp (Continuous.iterate (by unfold rotLift; fun_prop) k)
  have hgp : Tendsto g atTop (𝓝 cp) := (hRc.tendsto _).comp tendsto_separatrixArc_atTop
  have hgm : Tendsto g atBot (𝓝 cm) := (hRc.tendsto _).comp tendsto_separatrixArc_atBot
  obtain ⟨D, E, hW, hG, _, hend1, hend2⟩ :=
    canonical_boundary_regularity hlam hgac hgd hg1 hg2 hgb hM hgp hgm
  /- The rotation maps one saddle to the other: `R(π, 0) = (0, -π)`. -/
  have hκc : cp = paritySign κ * cm := by
    rw [hcp_def, hcm_def, show ((0 : ℝ), -Real.pi) = rotLift (Real.pi, 0) by simp [rotLift],
      ← Function.iterate_succ_apply, Function.iterate_succ_apply', contStream_rotLift hκ]
  exact ⟨D, E, hW, hG, hend1, hend2, hκc⟩

/-- Positivity on each canonical arc, from the weighted-domain positivity theorem. -/
theorem ee_canonicalArcForm_nonneg {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) {k : ℕ} (hk : k < 4)
    (hg : Integrable (deriv (contStream ω ∘ cellArc k)))
    (he : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2) :
    0 ≤ canonicalArcForm lam (contStream ω ∘ cellArc k) := by
  obtain ⟨D, E, hF, _, hp, hm, hc⟩ := ee_boundary_regularity hlam hω hs hκ hk
  rw [canonicalArcForm_eq_flowBoundaryForm hlam hg he hF]
  apply hF.flowBoundaryForm_nonneg
  have hends : intervalH1Extension (-1) 1
      (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) D 1 =
      paritySign κ * intervalH1Extension (-1) 1
        (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) D (-1) := by
    rw [hp, hm, hc]
    ring
  cases κ
  · exact Or.inr (by simpa [paritySign] using hends)
  · exact Or.inl (by simpa [paritySign] using hends)


end NoEmbeddedEigenvalues
