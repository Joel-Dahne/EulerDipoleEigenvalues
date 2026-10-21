import NoEmbeddedEigenvalues.SobolevLocal
import NoEmbeddedEigenvalues.LiftPeriodization
import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.CanonicalProfile
import NoEmbeddedEigenvalues.SeparatrixArc
import NoEmbeddedEigenvalues.OrbitCoordinates

/-!
# Transport pairs

Blueprint: `def:transport-pair`, `lem:transport-unknown`, `lem:transport-pair-eigen`,
`lem:good-windows`, `lem:good-level-selection`, `lem:weak-gradient-transport`.
`lem:coarea` is proved in `OrbitRestriction.lean`.
The good-level selector preserves any a.e. level property and avoids an arbitrary null set.
Also proves that weak partial derivatives give the weak transport derivative, using the
separated coefficients of the dipole field and no approximation argument.
The proofs of `lem:resonant-vanishing`, `lem:melnikov` and `lem:pairing-limit` are in
`ResonantVanishing.lean`, `Melnikov.lean` and `PairingLimit.lean`.

The eigenvalue equation `H(ω + ψ) = λω`, with `H = -i L₀` and `L₀ = Y · ∇`, is a transport
equation along the orbits of the dipole flow. A transport pair `(v, f)` on an open union of
orbits `U ⊆ ℝ²` abstracts it: `v ∈ L²(U)`, `f ∈ H²(U)` and `H(v + f) = λv` weakly on `U`.
Since `Y` is divergence free, the weak form of `L₀ g = h` is `∫ g L₀φ = -∫ h φ` for test
functions `φ` on `U`. The transport unknown `z = -(v + f)/λ` satisfies `Hz = -v` and
`(H - λ)z = f`.

Transport pairs live on the lift. The lift of a periodic function is not in `L²` of an
unbounded set, so in the applications `U` is bounded: a neighbourhood of the closed cell
made of whole orbits, or a compact annulus of orbits.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Complex

/-- `U` is an open union of orbits of the dipole flow. -/
def IsOrbitUnion (U : Set (ℝ × ℝ)) : Prop :=
  IsOpen U ∧ ∀ p ∈ U, ∀ t, dipoleFlow p t ∈ U

/-- `L₀ g = h` weakly on `U`: both are locally integrable on `U` and `∫ g L₀φ = -∫ h φ` for
    every test function `φ` on `U`. -/
def HasWeakL0On (U : Set (ℝ × ℝ)) (g h : ℝ × ℝ → ℂ) : Prop :=
  LocallyIntegrableOn g U ∧ LocallyIntegrableOn h U ∧
    ∀ φ, IsTestFunctionOn U φ → ∫ p, g p * classicalL0 φ p = -∫ p, h p * φ p

open Set Filter in
open scoped ContDiff in
/-- A function with weak partial derivatives has the weak transport derivative
`L₀F = sin y ∂ₓF - sin x ∂_yF`. -/
theorem HasWeakPartialOn.hasWeakL0On {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F d₀ d₁ : ℝ × ℝ → ℂ}
    (h₀ : HasWeakPartialOn U 0 F d₀) (h₁ : HasWeakPartialOn U 1 F d₁) :
    HasWeakL0On U F (fun p ↦ (Real.sin p.2 : ℂ) * d₀ p - (Real.sin p.1 : ℂ) * d₁ p) := by
  have hsy : Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have hsx : Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  refine ⟨h₀.1, (h₀.2.1.continuousOn_mul hsy.continuousOn hU.isLocallyClosed).sub
    (h₁.2.1.continuousOn_mul hsx.continuousOn hU.isLocallyClosed), fun φ hφ ↦ ?_⟩
  have hsyd : Differentiable ℝ (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have hsxd : Differentiable ℝ (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have hφd : Differentiable ℝ φ := hφ.contDiff.differentiable (by simp)
  have ty : IsTestFunctionOn U (fun p ↦ (Real.sin p.2 : ℂ) * φ p) :=
    ⟨(ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)).mul hφ.contDiff,
      hφ.hasCompactSupport.mul_left, (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩
  have tx : IsTestFunctionOn U (fun p ↦ (Real.sin p.1 : ℂ) * φ p) :=
    ⟨(ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_fst)).mul hφ.contDiff,
      hφ.hasCompactSupport.mul_left, (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩
  have ey : coordPartial 0 (fun p ↦ (Real.sin p.2 : ℂ) * φ p) =
      fun p ↦ (Real.sin p.2 : ℂ) * partialX φ p := by
    rw [coordPartial_mul 0 hsyd hφd]
    funext p
    simp [coordPartial, partialX]
  have ex : coordPartial 1 (fun p ↦ (Real.sin p.1 : ℂ) * φ p) =
      fun p ↦ (Real.sin p.1 : ℂ) * partialY φ p := by
    rw [coordPartial_mul 1 hsxd hφd]
    funext p
    simp [coordPartial, partialY]
  have wy := h₀.2.2 _ ty
  have wx := h₁.2.2 _ tx
  rw [ey] at wy
  rw [ex] at wx
  have i1 := integrable_mul_of_tsupport_subset h₀.1 (ty.continuous_coordPartial 0)
    (ty.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 _).trans ty.tsupport_subset)
  have i2 := integrable_mul_of_tsupport_subset h₁.1 (tx.continuous_coordPartial 1)
    (tx.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 _).trans tx.tsupport_subset)
  have i3 := integrable_mul_of_tsupport_subset h₀.2.1 ty.contDiff.continuous
    ty.hasCompactSupport ty.tsupport_subset
  have i4 := integrable_mul_of_tsupport_subset h₁.2.1 tx.contDiff.continuous
    tx.hasCompactSupport tx.tsupport_subset
  rw [ey] at i1
  rw [ex] at i2
  have e1 : (fun p ↦ F p * classicalL0 φ p) = fun p ↦
      F p * ((Real.sin p.2 : ℂ) * partialX φ p) - F p * ((Real.sin p.1 : ℂ) * partialY φ p) := by
    funext p
    simp only [classicalL0, real_smul]
    ring
  have e2 : (fun p ↦ ((Real.sin p.2 : ℂ) * d₀ p - (Real.sin p.1 : ℂ) * d₁ p) * φ p) = fun p ↦
      d₀ p * ((Real.sin p.2 : ℂ) * φ p) - d₁ p * ((Real.sin p.1 : ℂ) * φ p) := by
    funext p
    ring
  rw [e1, e2, integral_sub i1 i2, integral_sub i3 i4, wy, wx]
  ring


/-- A transport pair `(v, f)` on `U` with parameter `λ ≠ 0`: `v ∈ L²(U)`, `f ∈ H²(U)` and
    `H(v + f) = λv` weakly on `U`, that is `L₀(v + f) = iλv`. -/
structure IsTransportPair (lam : ℝ) (U : Set (ℝ × ℝ)) (v f : ℝ × ℝ → ℂ) : Prop where
  ne_zero : lam ≠ 0
  isOrbitUnion : IsOrbitUnion U
  memLp : MemLp v 2 (volume.restrict U)
  memSobolevOn : MemSobolevOn 2 U f
  hasWeakL0On : HasWeakL0On U (fun p ↦ v p + f p) (fun p ↦ I * (lam * v p))

/-- The transport unknown `z = -(v + f)/λ`. -/
def transportUnknown (lam : ℝ) (v f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p ↦ -(v p + f p) / lam

/-- The weak `L₀` is linear: scalar multiples. -/
theorem HasWeakL0On.const_mul {U : Set (ℝ × ℝ)} {g h : ℝ × ℝ → ℂ} (hd : HasWeakL0On U g h)
    (c : ℂ) : HasWeakL0On U (fun p ↦ c * g p) (fun p ↦ c * h p) := by
  refine ⟨by simpa [Pi.smul_def] using hd.1.smul c, by simpa [Pi.smul_def] using hd.2.1.smul c,
    fun φ hφ ↦ ?_⟩
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hd.2.2 φ hφ]
  ring

/-- Weak transport is unchanged by a global a.e. change of its value representative. -/
theorem HasWeakL0On.congr_value {U : Set (ℝ × ℝ)} {f g d : ℝ × ℝ → ℂ}
    (h : HasWeakL0On U f d) (hfg : f =ᵐ[volume] g) : HasWeakL0On U g d := by
  refine ⟨h.1.congr hfg.restrict, h.2.1, fun φ hφ ↦ ?_⟩
  rw [← h.2.2 φ hφ]
  exact integral_congr_ae (hfg.mono fun p hp ↦ congrArg (· * classicalL0 φ p) hp.symm)

/-- Weak transport is unchanged by a global a.e. change of its derivative representative. -/
theorem HasWeakL0On.congr_deriv {U : Set (ℝ × ℝ)} {f d d' : ℝ × ℝ → ℂ}
    (h : HasWeakL0On U f d) (hd : d =ᵐ[volume] d') : HasWeakL0On U f d' := by
  refine ⟨h.1, h.2.1.congr hd.restrict, fun φ hφ ↦ ?_⟩
  rw [h.2.2 φ hφ]
  exact congrArg Neg.neg (integral_congr_ae (hd.mono fun p hp ↦ congrArg (· * φ p) hp))

/-- Lifts of a torus transport relation `L₀g = h`, tested against the characters, satisfy
    `L₀g = h` weakly on every set (`hasWeakL0On_liftL2`). -/
theorem hasWeakL0On_liftL2 {g h : L2} (hgh : HasL0 g h) (U : Set (ℝ × ℝ)) :
    HasWeakL0On U (liftL2 g) (liftL2 h) :=
  ⟨(locallyIntegrable_liftL2 g).locallyIntegrableOn U,
    (locallyIntegrable_liftL2 h).locallyIntegrableOn U,
    fun _ hφ ↦ integral_liftL2_mul_classicalL0 hgh (hφ.mono (Set.subset_univ U))⟩

/-- `Hz = -v`, that is `L₀ z = -iv`. -/
theorem IsTransportPair.hasWeakL0On_transportUnknown {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f) :
    HasWeakL0On U (transportUnknown lam v f) (fun p ↦ I * -v p) := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne_zero
  convert hp.hasWeakL0On.const_mul (-1 / lam) using 1
  · funext p
    simp only [transportUnknown]
    field_simp
  · funext p
    field_simp

/-- `(H - λ)z = f`, that is `L₀ z = i(λz + f)`. -/
theorem IsTransportPair.hasWeakL0On_transportUnknown_sub {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f) :
    HasWeakL0On U (transportUnknown lam v f)
      (fun p ↦ I * (lam * transportUnknown lam v f p + f p)) := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne_zero
  convert hp.hasWeakL0On_transportUnknown using 1
  funext p
  simp only [transportUnknown]
  field_simp
  ring

/-! ### Eigenfunctions (`lem:transport-pair-eigen`) -/

/-- The lifts of an eigenfunction and its stream function form a transport pair on every
    bounded open union of orbits. -/
theorem isTransportPair_of_isEigenSolution {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U)
    (hb : Bornology.IsBounded U) :
    IsTransportPair lam U (liftL2 ω) (liftL2 (invLap ω)) := by
  refine ⟨hlam, hU, memSobolevOn_liftL2 (k := 0) (by exact_mod_cast memSobolev_zero ω) hb,
    memSobolevOn_liftL2 (memSobolev_two_invLap ω) hb, ?_⟩
  refine ((hasWeakL0On_liftL2 hω.2 U).congr_value (liftL2_add_ae ω (invLap ω))).congr_deriv ?_
  filter_upwards [liftL2_smul_ae (I * lam) ω] with p hp
  rw [hp, mul_assoc]

/-! ### Good windows (`lem:good-windows`) -/

open Filter Topology in
/-- The good windows `|λS(h) - 2π(j + ½)| < π/3` have positive measure near `h = 0`. -/
theorem volume_goodWindows_pos {lam : ℝ} (hlam : lam ≠ 0) {η : ℝ} (hη : 0 < η) :
    0 < volume {h ∈ Set.Ioo 0 η |
      ∃ j : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3} := by
  have hpi := Real.pi_pos
  set η' := min η (1 / 2)
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hη'1 : η' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcont : ContinuousOn orbitPeriod (Set.Ioo 0 1) := continuousOn_orbitPeriod
  -- A level `hs ∈ (0, η')` where `λS` is exactly a phase centre.
  obtain ⟨hs, hs0, hsη, j, hj⟩ : ∃ hs, 0 < hs ∧ hs < η' ∧ ∃ j : ℤ,
      lam * orbitPeriod hs = 2 * Real.pi * (j + 1 / 2) := by
    set μ := |lam|
    have hμ : 0 < μ := abs_pos.2 hlam
    set h₀ := η' / 2
    have h₀0 : 0 < h₀ := by positivity
    have h₀η : h₀ < η' := half_lt_self hη'
    set j₀ : ℤ := ⌈μ * orbitPeriod h₀ / (2 * Real.pi)⌉
    set c := 2 * Real.pi * (j₀ + 1 / 2)
    have hc₀ : μ * orbitPeriod h₀ ≤ c := by
      have h1 : μ * orbitPeriod h₀ / (2 * Real.pi) ≤ j₀ := Int.le_ceil _
      have h2 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 h1
      simp only [c]
      linarith
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), c ≤ μ * orbitPeriod h ∧ h < h₀ :=
      ((tendsto_orbitPeriod_atTop.const_mul_atTop hμ).eventually_ge_atTop c).and
        (Filter.eventually_of_mem (Ioo_mem_nhdsGT h₀0) fun h hh ↦ hh.2)
    obtain ⟨h₁, ⟨hc₁, h₁h₀⟩, h₁0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hsub : Set.Icc h₁ h₀ ⊆ Set.Ioo 0 1 :=
      fun h hh ↦ ⟨(show (0 : ℝ) < h₁ from h₁0).trans_le hh.1, by linarith [hh.2]⟩
    obtain ⟨hs, hsI, hsc⟩ := intermediate_value_Icc' h₁h₀.le
      ((hcont.mono hsub).const_smul μ) ⟨hc₀, hc₁⟩
    refine ⟨hs, (show (0 : ℝ) < h₁ from h₁0).trans_le hsI.1, hsI.2.trans_lt h₀η, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul] at hsc
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · refine ⟨-j₀ - 1, ?_⟩
      have : lam = -μ := by simp only [μ, abs_of_neg hneg, neg_neg]
      rw [this, neg_mul, hsc]
      push_cast
      ring
    · refine ⟨j₀, ?_⟩
      have : lam = μ := by simp only [μ, abs_of_pos hpos]
      rw [this, hsc]
  -- A neighbourhood of `hs` lies in the good windows.
  have hca : ContinuousAt (fun h ↦ lam * orbitPeriod h) hs :=
    continuousAt_const.mul (hcont.continuousAt (Ioo_mem_nhds hs0 (hsη.trans hη'1)))
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hca (Real.pi / 3) (by positivity)
  set ε := min δ (min hs (η - hs))
  have hε : 0 < ε := lt_min hδ (lt_min hs0 (by linarith [min_le_left η (1 / 2)]))
  have hsubset : Set.Ioo (hs - ε) (hs + ε) ⊆ {h ∈ Set.Ioo 0 η |
      ∃ j : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3} := by
    intro h hh
    have e1 : ε ≤ δ := min_le_left _ _
    have e2 : ε ≤ hs := (min_le_right _ _).trans (min_le_left _ _)
    have e3 : ε ≤ η - hs := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨⟨by linarith [hh.1], by linarith [hh.2]⟩, j, ?_⟩
    have hd : dist h hs < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hh.1, hh.2]
    have := hδc hd
    rwa [Real.dist_eq, hj] at this
  refine lt_of_lt_of_le ?_ (measure_mono hsubset)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

open Filter Topology in
/-- Good levels approaching zero can avoid any null set and satisfy an arbitrary
    almost-everywhere level property. No measurability of that property is required. -/
theorem exists_goodLevels_avoiding {lam : ℝ} (hlam : lam ≠ 0) {P : ℝ → Prop}
    (hP : ∀ᵐ h ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), P h)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j < 1 / ((j : ℝ) + 1) ∧
        hs j ∉ N ∧ P (hs j) ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) := by
  have hbad : volume {h | h ∈ Set.Ioo (0 : ℝ) 1 ∧ ¬P h} = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' measurableSet_Ioo).1 hP
  let B := N ∪ {h | h ∈ Set.Ioo (0 : ℝ) 1 ∧ ¬P h}
  have hB : volume B = 0 := measure_union_null hN hbad
  have heach (j : ℕ) : ∃ h : ℝ, h ∈ Set.Ioo 0 1 ∧ h < 1 / ((j : ℝ) + 1) ∧
      h ∉ N ∧ P h ∧
      ∃ m : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3 := by
    let η : ℝ := min (1 / ((j : ℝ) + 1)) 1
    have hη : 0 < η := lt_min (by positivity) zero_lt_one
    have hpos : 0 < volume ({h ∈ Set.Ioo 0 η |
        ∃ m : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3} \ B) := by
      rw [measure_sdiff_null hB]
      exact volume_goodWindows_pos hlam hη
    obtain ⟨h, ⟨hh, hw⟩, hnB⟩ := nonempty_of_measure_ne_zero hpos.ne'
    have h1 : h < 1 := hh.2.trans_le (min_le_right _ _)
    refine ⟨h, ⟨hh.1, h1⟩, hh.2.trans_le (min_le_left _ _),
      fun hn ↦ hnB (Or.inl hn), ?_, hw⟩
    by_contra hnP
    exact hnB (Or.inr ⟨⟨hh.1, h1⟩, hnP⟩)
  choose hs hhs using heach
  refine ⟨hs, hhs, squeeze_zero (fun j ↦ (hhs j).1.1.le)
    (fun j ↦ (hhs j).2.1.le) tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- On a good window `e^{iλS(h)/4}` stays at distance at least `2 sin(π/12)` from `κ = ±1`. -/
theorem norm_exp_sub_ge_of_goodWindow {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3) {κ : ℂ}
    (hκ : κ = 1 ∨ κ = -1) :
    2 * Real.sin (Real.pi / 12) ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ := by
  set θ : ℝ := lam * orbitPeriod h / 4
  set ε := lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)
  have hpi := Real.pi_pos
  -- `cos 2θ = ∓ sin(ε/2)` is at most `1/2` in absolute value.
  have h2θ : 2 * θ = (j : ℝ) * Real.pi + Real.pi / 2 + ε / 2 := by simp only [θ, ε]; ring
  have hsin : |Real.sin (ε / 2)| ≤ 1 / 2 := by
    rw [abs_lt] at hj
    have hb : |ε / 2| ≤ Real.pi / 6 := by rw [abs_le]; constructor <;> linarith
    rw [← Real.sin_pi_div_six, abs_le]
    constructor
    · rw [← neg_le_neg_iff, neg_neg, ← Real.sin_neg]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [(abs_le.1 hb).2])
        (by linarith) (by linarith [(abs_le.1 hb).2])
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [(abs_le.1 hb).1])
        (by linarith) (by linarith [(abs_le.1 hb).2])
  have hcos2 : |Real.cos (2 * θ)| ≤ 1 / 2 := by
    rw [h2θ, Real.cos_add, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.sin_int_mul_pi]
    simp only [neg_zero, zero_mul, zero_sub, abs_neg, abs_mul, Real.abs_cos_int_mul_pi,
      one_mul]
    exact hsin
  have hcos : Real.cos θ ^ 2 ≤ 3 / 4 := by
    have := Real.cos_sq θ
    rw [abs_le] at hcos2
    linarith [hcos2.2]
  -- `|e^{iθ} - κ|² = 2 - 2κ cos θ ≥ 2 - √3 = 4 sin²(π/12)`.
  have hκc : κ = ((κ.re : ℝ) : ℂ) := by rcases hκ with rfl | rfl <;> simp
  have hκ2 : κ.re ^ 2 = 1 := by rcases hκ with rfl | rfl <;> simp
  have hexp : exp (I * (lam * orbitPeriod h / 4)) = exp ((θ : ℂ) * I) := by
    simp only [θ]; push_cast; ring_nf
  have hnorm : ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ ^ 2 = 2 - 2 * κ.re * Real.cos θ := by
    rw [hexp, Complex.sq_norm, Complex.normSq_apply, hκc]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs3 : (2 * Real.sin (Real.pi / 12)) ^ 2 = 2 - √3 := by
    have h2 := Real.cos_two_mul (Real.pi / 12)
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at h2
    rw [mul_pow, Real.sin_sq]
    linarith
  have hkc : κ.re * Real.cos θ ≤ √3 / 2 := by
    have h3 : (κ.re * Real.cos θ) ^ 2 ≤ (√3 / 2) ^ 2 := by
      rw [mul_pow, hκ2, one_mul, div_pow, Real.sq_sqrt (by norm_num)]
      linarith
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
  have hsq : (2 * Real.sin (Real.pi / 12)) ^ 2 ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ ^ 2 := by
    rw [hs3, hnorm]
    linarith
  exact (abs_le_of_sq_le_sq' hsq (norm_nonneg _)).2

open Filter Topology in
/-- A good window is also nonresonant for the full period. -/
theorem exp_orbitPeriod_ne_one_of_goodWindow {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3) :
    exp (I * lam * orbitPeriod h) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
  have ht : lam * orbitPeriod h = (n : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hn
  rw [ht, abs_lt] at hj
  rcases le_or_gt n j with hle | hgt
  · have hle' : (n : ℝ) ≤ j := by exact_mod_cast hle
    nlinarith [mul_le_mul_of_nonneg_left hle' Real.pi_pos.le]
  · have hle' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hgt
    nlinarith [mul_le_mul_of_nonneg_left hle' Real.pi_pos.le]

end NoEmbeddedEigenvalues
