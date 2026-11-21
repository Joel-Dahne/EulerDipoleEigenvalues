module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal
public import NoEmbeddedEigenvalues.Analysis.TorusSobolev.LiftPeriodization
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.PeriodicOrbits
public import NoEmbeddedEigenvalues.Transport.CanonicalProfile.CanonicalProfile
public import NoEmbeddedEigenvalues.Geometry.SeparatrixArcs.SeparatrixArc
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.OrbitCoordinates

/-! # Weak transport pairs -/

@[expose] public section

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

end NoEmbeddedEigenvalues
