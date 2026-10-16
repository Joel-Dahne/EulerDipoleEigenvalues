import NoEmbeddedEigenvalues.LiftIntegration
import NoEmbeddedEigenvalues.SobolevTorus

/-!
# Periodic lifts and functions on the torus

Blueprint: `lem:lift-torus`, `lem:lift-sobolev`, `liftL2` of `def:torus-of-lift`, and
`def:stream-lifts`.

A continuous periodic lift `u : ℝ² → ℂ` descends to a continuous function on the
torus, `torusOfLift u`, with `torusOfLift u (x, y) = u (x, y)`. Classical partial
derivatives of `C¹` lifts are then classical, hence Fourier, partial derivatives on the
torus, and periodic `Cᵏ` lifts lie in `Hᵏ(𝕋²)`. Integrals of lifts `G ∘ π` of
a.e. strongly measurable torus functions over the period square are torus integrals.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory

/-- The covering map `ℝ² → 𝕋²`. -/
def torusProj (p : ℝ × ℝ) : Torus := ((p.1 : Angle), (p.2 : Angle))

theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj :=
  (QuotientAddGroup.isOpenQuotientMap_mk).prodMap QuotientAddGroup.isOpenQuotientMap_mk

theorem torusProj_surjective : Function.Surjective torusProj :=
  isOpenQuotientMap_torusProj.surjective

variable {E : Type*}

/-- Periodic lifts are constant on the fibres of `ℝ² → 𝕋²`. -/
theorem IsPeriodicLift.eq_of_torusProj_eq {u : ℝ × ℝ → E} (hu : IsPeriodicLift u)
    {a b : ℝ × ℝ} (h : torusProj a = torusProj b) : u a = u b := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h1
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h2
  have hx : Function.Periodic (fun x ↦ u (x, a.2)) (2 * π) := fun x ↦ (hu (x, a.2)).1
  have hy : Function.Periodic (fun y ↦ u (b.1, y)) (2 * π) := fun y ↦ (hu (b.1, y)).2
  calc u a = u (b.1 + k * (2 * π), a.2) := by
        congr 1
        ext
        · change a.1 = b.1 + k * (2 * π)
          linarith
        · rfl
    _ = u (b.1, a.2) := hx.int_mul k b.1
    _ = u (b.1, b.2 + m * (2 * π)) := by
        congr 1
        ext
        · rfl
        · change a.2 = b.2 + m * (2 * π)
          linarith
    _ = u b := hy.int_mul m b.2

/-- The function on the torus induced by a periodic lift. -/
def torusOfLift (u : ℝ × ℝ → E) (t : Torus) : E :=
  u (Function.surjInv torusProj_surjective t)

theorem torusOfLift_torusProj {u : ℝ × ℝ → E} (hu : IsPeriodicLift u) (p : ℝ × ℝ) :
    torusOfLift u (torusProj p) = u p :=
  hu.eq_of_torusProj_eq (Function.surjInv_eq torusProj_surjective _)

theorem continuous_torusOfLift [TopologicalSpace E] {u : ℝ × ℝ → E} (hc : Continuous u)
    (hu : IsPeriodicLift u) :
    Continuous (torusOfLift u) := by
  rw [isOpenQuotientMap_torusProj.isQuotientMap.continuous_iff]
  convert hc using 1
  funext p
  exact torusOfLift_torusProj hu p

/-! ### Classical derivatives and Sobolev regularity -/

/-- A continuous periodic lift as a continuous function on the torus. -/
def torusFun {u : ℝ × ℝ → ℂ} (hc : Continuous u) (hu : IsPeriodicLift u) : C(Torus, ℂ) :=
  ⟨torusOfLift u, continuous_torusOfLift hc hu⟩

/-- A continuous periodic lift as an element of `L²(𝕋²)`. -/
def torusL2 {u : ℝ × ℝ → ℂ} (hc : Continuous u) (hu : IsPeriodicLift u) : L2 :=
  ContinuousMap.toLp 2 volume ℂ (torusFun hc hu)

theorem continuous_partialX_of_contDiff {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u) :
    Continuous (partialX u) :=
  (contDiff_partialX (n := 0) (by simpa using hu)).continuous

theorem continuous_partialY_of_contDiff {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u) :
    Continuous (partialY u) :=
  (contDiff_partialY (n := 0) (by simpa using hu)).continuous

/-- The `x` derivative of a periodic `C¹` lift is a classical partial derivative on the torus. -/
theorem hasClassicalPartial_torusFun_x {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (hp : IsPeriodicLift u) :
    HasClassicalPartial 0 (torusFun hu.continuous hp)
      (torusFun (continuous_partialX_of_contDiff hu) hp.partialX) := by
  intro q t
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective q
  have hline : (fun s ↦ torusFun hu.continuous hp (coordinateLine 0 (torusProj (x, y)) s)) =
      fun s ↦ u (s, y) := by
    funext s
    simp only [torusFun, ContinuousMap.coe_mk, coordinateLine, ite_true]
    exact torusOfLift_torusProj hp (s, y)
  have hval : torusFun (continuous_partialX_of_contDiff hu) hp.partialX
      (coordinateLine 0 (torusProj (x, y)) t) = partialX u (t, y) := by
    simp only [torusFun, ContinuousMap.coe_mk, coordinateLine, ite_true]
    exact torusOfLift_torusProj hp.partialX (t, y)
  rw [hline, hval]
  exact hasDerivAt_partialX (p := (t, y)) (hu.differentiable one_ne_zero _)

/-- The `y` derivative of a periodic `C¹` lift is a classical partial derivative on the torus. -/
theorem hasClassicalPartial_torusFun_y {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (hp : IsPeriodicLift u) :
    HasClassicalPartial 1 (torusFun hu.continuous hp)
      (torusFun (continuous_partialY_of_contDiff hu) hp.partialY) := by
  intro q t
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective q
  have hline : (fun s ↦ torusFun hu.continuous hp (coordinateLine 1 (torusProj (x, y)) s)) =
      fun s ↦ u (x, s) := by
    funext s
    simp only [torusFun, ContinuousMap.coe_mk, coordinateLine, one_ne_zero, ite_false]
    exact torusOfLift_torusProj hp (x, s)
  have hval : torusFun (continuous_partialY_of_contDiff hu) hp.partialY
      (coordinateLine 1 (torusProj (x, y)) t) = partialY u (x, t) := by
    simp only [torusFun, ContinuousMap.coe_mk, coordinateLine, one_ne_zero, ite_false]
    exact torusOfLift_torusProj hp.partialY (x, t)
  rw [hline, hval]
  exact hasDerivAt_partialY (p := (x, t)) (hu.differentiable one_ne_zero _)

/-- Classical partial derivatives of a periodic `C¹` lift are its Fourier partial derivatives. -/
theorem hasFourierPartial_torusL2_x {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (hp : IsPeriodicLift u) :
    HasFourierPartial 0 (torusL2 hu.continuous hp)
      (torusL2 (continuous_partialX_of_contDiff hu) hp.partialX) :=
  (hasClassicalPartial_torusFun_x hu hp).hasFourierPartial

theorem hasFourierPartial_torusL2_y {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (hp : IsPeriodicLift u) :
    HasFourierPartial 1 (torusL2 hu.continuous hp)
      (torusL2 (continuous_partialY_of_contDiff hu) hp.partialY) :=
  (hasClassicalPartial_torusFun_y hu hp).hasFourierPartial

/-- Periodic `Cᵏ` lifts lie in `Hᵏ(𝕋²)`. -/
theorem memSobolev_torusL2 (n : ℕ) {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ n u)
    (hc : Continuous u) (hp : IsPeriodicLift u) : MemSobolev n (torusL2 hc hp) := by
  induction n generalizing u with
  | zero => simpa using memSobolev_zero (torusL2 hc hp)
  | succ n ih =>
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hux : ContDiff ℝ n (partialX u) := contDiff_partialX (by exact_mod_cast hu)
    have huy : ContDiff ℝ n (partialY u) := contDiff_partialY (by exact_mod_cast hu)
    have h0 := ih (hu.of_le (by exact_mod_cast Nat.le_succ n)) hc hp
    have hx := ih hux (continuous_partialX_of_contDiff hu1) hp.partialX
    have hy := ih huy (continuous_partialY_of_contDiff hu1) hp.partialY
    push_cast
    exact memSobolev_add_one_of_hasFourierPartial h0 (hasFourierPartial_torusL2_x hu1 hp)
      (hasFourierPartial_torusL2_y hu1 hp) hx hy

/-- Smooth periodic lifts lie in every `Hˢ(𝕋²)`. -/
theorem memSobolev_torusL2_of_smooth {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ ⊤ u)
    (hc : Continuous u) (hp : IsPeriodicLift u) (s : ℝ) : MemSobolev s (torusL2 hc hp) :=
  (memSobolev_torusL2 ⌈s⌉₊ (hu.of_le le_top) hc hp).mono (Nat.le_ceil s)

/-! ### Integrals -/

/-- The covering map is measure preserving on each translate of the fundamental square. -/
theorem measurePreserving_torusProj_square (a b : ℝ) :
    MeasurePreserving torusProj
      (volume.restrict (Set.Ioc a (a + 2 * π) ×ˢ Set.Ioc b (b + 2 * π))) volume := by
  change MeasurePreserving
    (Prod.map (fun x : ℝ ↦ (x : AddCircle (2 * π)))
      (fun x : ℝ ↦ (x : AddCircle (2 * π)))) _
    (volume : Measure (AddCircle (2 * π) × AddCircle (2 * π)))
  have h₁ := AddCircle.measurePreserving_mk (2 * π) a
  have h₂ := AddCircle.measurePreserving_mk (2 * π) b
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using h₁.prod h₂

/-- Integration over a period of an `Angle`-periodic function. -/
theorem integral_angle_eq (f : Angle → ℂ) :
    ∫ a : Angle, f a = ∫ x in (0 : ℝ)..(2 * π), f (x : Angle) := by
  have h := AddCircle.intervalIntegral_preimage (2 * π) 0 f
  rw [zero_add] at h
  exact h.symm

/-- The integral over the period square is the integral over the torus. -/
theorem squareIntegral_eq_integral_torus {u : ℝ × ℝ → ℂ} (hc : Continuous u)
    (hp : IsPeriodicLift u) : squareIntegral u = ∫ t : Torus, torusOfLift u t := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hT : Continuous (torusOfLift u) := continuous_torusOfLift hc hp
  have hTi : Integrable (torusOfLift u) (volume : Measure Torus) :=
    hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Measure.volume_eq_prod] at hTi ⊢
  rw [integral_prod _ hTi, integral_angle_eq]
  simp_rw [integral_angle_eq]
  rw [squareIntegral, periodSquare, Measure.volume_eq_prod,
    setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrableOn_periodSquare hc),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ]
  congr 1
  funext x
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ]
  congr 1
  funext y
  exact (torusOfLift_torusProj hp (x, y)).symm

/-- The pairing on the lift is the `L²` inner product on the torus:
    `⟨u, v⟩ = ∫ u v̄ = ⟪v, u⟫`. -/
theorem squarePairing_eq_inner {u v : ℝ × ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hpu : IsPeriodicLift u) (hpv : IsPeriodicLift v) :
    squarePairing u v = inner ℂ (torusL2 hv hpv) (torusL2 hu hpu) := by
  have hpuv : IsPeriodicLift (fun p ↦ u p * (starRingEnd ℂ) (v p)) := fun q ↦ by
    simp only [(hpu q).1, (hpu q).2, (hpv q).1, (hpv q).2, and_self]
  rw [squarePairing, squareIntegral_eq_integral_torus (by fun_prop) hpuv,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (torusFun hu hpu),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (torusFun hv hpv)] with t htu htv
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  simp only [torusL2]
  rw [htu, htv, RCLike.inner_apply, torusOfLift_torusProj hpuv]
  change u q * (starRingEnd ℂ) (v q) =
    torusOfLift u (torusProj q) * (starRingEnd ℂ) (torusOfLift v (torusProj q))
  rw [torusOfLift_torusProj hpu, torusOfLift_torusProj hpv]

theorem torusFun_torusProj {u : ℝ × ℝ → ℂ} (hc : Continuous u) (hp : IsPeriodicLift u)
    (q : ℝ × ℝ) : torusFun hc hp (torusProj q) = u q :=
  torusOfLift_torusProj hp q

theorem partialX_ofReal {u : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u) :
    partialX (fun q ↦ (u q : ℂ)) = fun q ↦ ((partialX u q : ℝ) : ℂ) :=
  funext fun q ↦ (hasDerivAt_partialX (hu q)).ofReal_comp.deriv

theorem partialY_ofReal {u : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u) :
    partialY (fun q ↦ (u q : ℂ)) = fun q ↦ ((partialY u q : ℝ) : ℂ) :=
  funext fun q ↦ (hasDerivAt_partialY (hu q)).ofReal_comp.deriv

open Set in
/-- Integrals over the period square of lifts `G ∘ π` are torus integrals. -/
theorem squareIntegral_comp_torusProj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Torus → E} (hG : AEStronglyMeasurable G volume) :
    squareIntegral (fun q ↦ G (torusProj q)) = ∫ t, G t := by
  have hmp := measurePreserving_torusProj_square 0 0
  have hsq : ∫ q in Ioc 0 (0 + 2 * Real.pi) ×ˢ Ioc 0 (0 + 2 * Real.pi), G (torusProj q) =
      ∫ t, G t := by
    have h := integral_map (μ := volume.restrict (Ioc 0 (0 + 2 * Real.pi) ×ˢ
      Ioc 0 (0 + 2 * Real.pi))) hmp.measurable.aemeasurable (f := G)
      (by rw [hmp.map_eq]; exact hG)
    rw [hmp.map_eq] at h
    exact h.symm
  have hnull (c : ℝ) : volume {q : ℝ × ℝ | q.1 = c} = 0 ∧ volume {q : ℝ × ℝ | q.2 = c} = 0 := by
    rw [Measure.volume_eq_prod]
    constructor
    · rw [show {q : ℝ × ℝ | q.1 = c} = {c} ×ˢ univ by ext; simp, Measure.prod_prod]
      simp
    · rw [show {q : ℝ × ℝ | q.2 = c} = univ ×ˢ {c} by ext; simp, Measure.prod_prod]
      simp
  have hae : periodSquare =ᵐ[volume] Ioc 0 (0 + 2 * Real.pi) ×ˢ Ioc 0 (0 + 2 * Real.pi) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun q hq ↦ ?_) (measure_union_null (hnull 0).1 (hnull 0).2)
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hn⟩ := hq
      simp only [mem_prod, mem_Ioc, zero_add, not_and_or, not_lt] at hn
      simp only [mem_union, mem_ofPred_eq]
      rcases hn with (hn | hn) | hn | hn
      · exact Or.inl (le_antisymm hn h1)
      · exact absurd h2 (not_le.2 (by linarith))
      · exact Or.inr (le_antisymm hn h3)
      · exact absurd h4 (not_le.2 (by linarith))
    · refine measure_mono_null (fun q hq ↦ ?_) measure_empty
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hn⟩ := hq
      exact hn ⟨⟨h1.le, by linarith⟩, h3.le, by linarith⟩
  rw [squareIntegral, setIntegral_congr_set hae, hsq]

/-- The lift `g ∘ π` of an element of `L²(𝕋²)` to `ℝ²`, through its a.e. representative. -/
def liftL2 (g : L2) (p : ℝ × ℝ) : ℂ := g (torusProj p)

/-- The lift of the stream function `ψ = Δ⁻¹ω`. -/
def streamLift (ω : L2) : ℝ × ℝ → ℂ := liftL2 (invLap ω)

/-- The lift of `ψₓ = ∂ₓΔ⁻¹ω`. -/
def streamLiftX (ω : L2) : ℝ × ℝ → ℂ := liftL2 (streamPartial 0 ω)

/-- The lift of `ψ_y = ∂_yΔ⁻¹ω`. -/
def streamLiftY (ω : L2) : ℝ × ℝ → ℂ := liftL2 (streamPartial 1 ω)

/-- The lift of the continuous representative `ψ̃` of the stream function. -/
def contStream (ω : L2) (p : ℝ × ℝ) : ℂ := continuousRep (invLap ω) (torusProj p)

end NoEmbeddedEigenvalues
