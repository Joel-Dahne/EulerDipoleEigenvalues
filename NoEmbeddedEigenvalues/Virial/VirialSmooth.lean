module

public import NoEmbeddedEigenvalues.Geometry.Cells.LiftIntegration

/-!
# The virial identity for smooth eigenfunctions

Blueprint: `lem:virial-smooth` (first form).

If `W` is adapted with coefficient `f`, `a = ω + ψ` and `L₀ a = iλ ω` with `λ ≠ 0`,
then `Re ⟨f ω, ω + ψ⟩ = 2 Re ⟨D ψ, ω⟩`, for smooth periodic data on the lift.
The relation `ψ = Δ⁻¹ ω` is not used. The proof pairs `[L₀, D] a = ½(f L₀ + L₀ f) a`
with `a`, moves `L₀` and `D` across the pairing by skew-symmetry, and uses
`Re ⟨D ω, ω⟩ = 0`.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex ComplexConjugate

variable {W₁ W₂ f : ℝ × ℝ → ℝ}

theorem contDiff_classicalL0 {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (classicalL0 u) := by
  have hx := contDiff_partialX (n := 1) hu
  have hy := contDiff_partialY (n := 1) hu
  rw [classicalL0_eq]
  fun_prop

theorem contDiff_halfDensityGen (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (halfDensityGen W₁ W₂ u) := by
  have hx := contDiff_partialX (n := 1) hu
  have hy := contDiff_partialY (n := 1) hu
  have h1 := contDiff_partialX (n := 1) hW₁
  have h2 := contDiff_partialY (n := 1) hW₂
  have hW₁' : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂' : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hu' : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  unfold halfDensityGen fieldDeriv divergence
  fun_prop

theorem IsPeriodicLift.classicalL0 {u : ℝ × ℝ → ℂ} (h : IsPeriodicLift u) :
    IsPeriodicLift (classicalL0 u) := fun p ↦ by
  simp only [NoEmbeddedEigenvalues.classicalL0, (h.partialX p).1, (h.partialX p).2,
    (h.partialY p).1, (h.partialY p).2, Real.sin_add_two_pi, and_self]

theorem IsPeriodicLift.halfDensityGen (hp₁ : IsPeriodicLift W₁) (hp₂ : IsPeriodicLift W₂)
    {u : ℝ × ℝ → ℂ} (h : IsPeriodicLift u) :
    IsPeriodicLift (NoEmbeddedEigenvalues.halfDensityGen W₁ W₂ u) := fun p ↦ by
  simp only [NoEmbeddedEigenvalues.halfDensityGen, fieldDeriv, divergence, (hp₁ p).1,
    (hp₁ p).2, (hp₂ p).1, (hp₂ p).2, (h p).1, (h p).2, (h.partialX p).1, (h.partialX p).2,
    (h.partialY p).1, (h.partialY p).2, (hp₁.partialX p).1, (hp₁.partialX p).2,
    (hp₂.partialY p).1, (hp₂.partialY p).2, and_self]

theorem halfDensityGen_add {u v : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (p : ℝ × ℝ) :
    halfDensityGen W₁ W₂ (fun q ↦ u q + v q) p =
      halfDensityGen W₁ W₂ u p + halfDensityGen W₁ W₂ v p := by
  simp only [halfDensityGen, fieldDeriv, partialX_add (hu p) (hv p), partialY_add (hu p) (hv p)]
  module

/-- The virial identity for smooth eigenfunctions:
    `Re ⟨f ω, ω + ψ⟩ = 2 Re ⟨D ψ, ω⟩`. -/
theorem virial_smooth (had : IsAdaptedOn W₁ W₂ f Set.univ) (hW₁ : ContDiff ℝ 2 W₁)
    (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f) (hpW₁ : IsPeriodicLift W₁)
    (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f) {ω ψ : ℝ × ℝ → ℂ}
    (hω : ContDiff ℝ 2 ω) (hψ : ContDiff ℝ 2 ψ) (hpω : IsPeriodicLift ω)
    (hpψ : IsPeriodicLift ψ) {lam : ℝ} (hlam : lam ≠ 0)
    (heq : ∀ p, classicalL0 (fun q ↦ ω q + ψ q) p = I * lam * ω p) :
    (squarePairing (fun p ↦ f p • ω p) (fun p ↦ ω p + ψ p)).re =
      2 * (squarePairing (halfDensityGen W₁ W₂ ψ) ω).re := by
  set a : ℝ × ℝ → ℂ := fun q ↦ ω q + ψ q with ha_def
  have ha : ContDiff ℝ 2 a := hω.add hψ
  have hpa : IsPeriodicLift a := fun q ↦ by simp [a, (hpω q).1, (hpω q).2, (hpψ q).1, (hpψ q).2]
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hLa : classicalL0 a = fun p ↦ I * lam * ω p := funext heq
  -- Regularity and periodicity of the functions paired below.
  have hDa := contDiff_halfDensityGen hW₁ hW₂ ha
  have hpDa := IsPeriodicLift.halfDensityGen hpW₁ hpW₂ hpa
  have hLa1 := contDiff_classicalL0 ha
  have hpLa := hpa.classicalL0
  have hfa : ContDiff ℝ 1 (fun q ↦ f q • a q) := hf.smul ha1
  have hpfa : IsPeriodicLift (fun q ↦ f q • a q) := fun q ↦ by
    simp [(hpf q).1, (hpf q).2, (hpa q).1, (hpa q).2]
  have hDL := contDiff_halfDensityGen hW₁ hW₂ (u := classicalL0 a) (by
    rw [hLa]; exact contDiff_const.mul hω)
  have hLD : Continuous (classicalL0 (halfDensityGen W₁ W₂ a)) := by
    have hx := (contDiff_partialX (n := 0) (by simpa using hDa)).continuous
    have hy := (contDiff_partialY (n := 0) (by simpa using hDa)).continuous
    rw [classicalL0_eq]
    fun_prop
  have hLfa : Continuous (classicalL0 (fun q ↦ f q • a q)) := by
    have hx := (contDiff_partialX (n := 0) (by simpa using hfa)).continuous
    have hy := (contDiff_partialY (n := 0) (by simpa using hfa)).continuous
    rw [classicalL0_eq]
    fun_prop
  -- The commutator identity `[L₀, D] a = ½ (f L₀ a + L₀ (f a))`, paired with `a`.
  have hcomm : squarePairing (classicalL0 (halfDensityGen W₁ W₂ a)) a -
      squarePairing (halfDensityGen W₁ W₂ (classicalL0 a)) a =
      (1 / 2 : ℂ) * (squarePairing (fun p ↦ f p • classicalL0 a p) a +
        squarePairing (classicalL0 (fun q ↦ f q • a q)) a) := by
    rw [← squarePairing_sub_left hLD hDL.continuous ha.continuous,
      ← squarePairing_add_left (by fun_prop) hLfa ha.continuous,
      ← squarePairing_const_mul_left]
    congr 1
    funext p
    rw [had.classicalL0_halfDensityGen isOpen_univ hW₁ hW₂ (hf.differentiable one_ne_zero) ha
      (Set.mem_univ p), Complex.real_smul]
    push_cast
    ring
  -- Move `L₀` and `D` across the pairing and use `L₀ a = iλ ω`.
  rw [squarePairing_classicalL0 hDa ha1 hpDa hpa,
    squarePairing_halfDensityGen hW₁1 hW₂1 hpW₁ hpW₂ hLa1 ha1 hpLa hpa,
    squarePairing_classicalL0 hfa ha1 hpfa hpa, hLa] at hcomm
  have e1 : squarePairing (halfDensityGen W₁ W₂ a) (fun p ↦ I * lam * ω p) =
      conj (I * lam) * squarePairing (halfDensityGen W₁ W₂ a) ω :=
    squarePairing_const_mul_right _ _
  have e2 : squarePairing (fun p ↦ I * lam * ω p) (halfDensityGen W₁ W₂ a) =
      I * lam * conj (squarePairing (halfDensityGen W₁ W₂ a) ω) := by
    rw [squarePairing_const_mul_left, squarePairing_comm]
  have e3 : squarePairing (fun p ↦ f p • (I * lam * ω p)) a =
      I * lam * squarePairing (fun p ↦ f p • ω p) a := by
    rw [← squarePairing_const_mul_left]
    congr 1
    funext p
    simp only [Complex.real_smul]
    ring
  have e4 : squarePairing (fun q ↦ f q • a q) (fun p ↦ I * lam * ω p) =
      conj (I * lam) * conj (squarePairing (fun p ↦ f p • ω p) a) := by
    rw [squarePairing_const_mul_right, squarePairing_real_smul, squarePairing_comm]
  rw [e1, e2, e3, e4] at hcomm
  set X := squarePairing (halfDensityGen W₁ W₂ a) ω
  set Y := squarePairing (fun p ↦ f p • ω p) a
  have hconj : conj (I * (lam : ℂ)) = -(I * lam) := by simp
  rw [hconj] at hcomm
  have hIl : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hlam)
  have hXY : X + conj X = (1 / 2) * (Y + conj Y) := by
    apply mul_left_cancel₀ hIl
    linear_combination hcomm
  have hre : 2 * X.re = Y.re := by
    have := congrArg Complex.re hXY
    simp only [Complex.add_re, Complex.conj_re, Complex.mul_re] at this
    norm_num at this
    linarith
  -- `X = ⟨D ω, ω⟩ + ⟨D ψ, ω⟩` and `Re ⟨D ω, ω⟩ = 0` by skew-symmetry.
  have hX : X = squarePairing (halfDensityGen W₁ W₂ ω) ω +
      squarePairing (halfDensityGen W₁ W₂ ψ) ω := by
    change squarePairing (halfDensityGen W₁ W₂ a) ω = _
    rw [← squarePairing_add_left (contDiff_halfDensityGen hW₁ hW₂ hω).continuous
      (contDiff_halfDensityGen hW₁ hW₂ hψ).continuous hω.continuous]
    congr 1
    funext p
    exact halfDensityGen_add (hω.differentiable two_ne_zero) (hψ.differentiable two_ne_zero) p
  have hskew : (squarePairing (halfDensityGen W₁ W₂ ω) ω).re = 0 := by
    have h := squarePairing_halfDensityGen hW₁1 hW₂1 hpW₁ hpW₂ hω1 hω1 hpω hpω
    rw [squarePairing_comm (halfDensityGen W₁ W₂ ω) ω] at h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  rw [← hre, hX, Complex.add_re, hskew, zero_add]

end NoEmbeddedEigenvalues
