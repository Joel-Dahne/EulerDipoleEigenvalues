import NoEmbeddedEigenvalues

/-!
# Solution: proof of the challenge statements

Proves the theorems of `Challenge.lean` from the development in `NoEmbeddedEigenvalues/`.

The definitions of `Challenge.lean` are repeated here verbatim, between the markers below. The
comparator checks that they elaborate to the same constants as in `Challenge.lean`, and that the
theorems have the same statements and use only the permitted axioms (`comparator.json`).

The bridge lemmas identify the challenge definitions with those of the library: the two `L²`
spaces are definitionally equal (`Real.Angle` is `AddCircle (2 * π)`), `coeff` is
`fourierCoeff`, `IsInvLap ω ψ` says `MeanZero ω ∧ ψ = invLap ω`, and `HasL0` is the library's
`HasL0`.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real ComplexConjugate InnerProductSpace

namespace EulerDipole

-- BEGIN CHALLENGE DEFINITIONS (verbatim copy of `Challenge.lean`)

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The torus `𝕋² = (ℝ/2πℤ)²`. Its measure `volume` is the product of Mathlib's Haar measures of
total mass `2π` on `ℝ/2πℤ`, that is, Lebesgue measure `dx dy`. -/
abbrev Torus := AddCircle (2 * π) × AddCircle (2 * π)

/-- `L²(𝕋²; ℂ)` with respect to `dx dy`. -/
abbrev L2 := Lp ℂ 2 (volume : Measure Torus)

/-- The character `e_k(x, y) = exp(i(k₁x + k₂y))`, see `char_coe`. Mathlib's `fourier n` is
`x ↦ exp(2πinx/T)` on `ℝ/Tℤ`, here with `T = 2π`. -/
def char (k : ℤ × ℤ) (p : Torus) : ℂ := fourier k.1 p.1 * fourier k.2 p.2

/-- The Fourier coefficient `ĝ(k) = (2π)⁻² ∫_{𝕋²} conj(e_k) g dx dy`. In particular `ĝ(0)` is the
mean of `g`. -/
def coeff (g : L2) (k : ℤ × ℤ) : ℂ := ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, conj (char k p) * g p

/-- `ψ = Δ⁻¹ω`: `ψ` has mean zero and solves `Δψ = ω` weakly. Testing `∫ ψ Δφ = ∫ ω φ` with
`φ = conj(e_k)`, for which `Δφ = -(k₁² + k₂²) φ`, gives the coefficient equations below. For
`k = 0` the equation says that `ω` has mean zero. -/
def IsInvLap (ω ψ : L2) : Prop :=
  coeff ψ 0 = 0 ∧ ∀ k : ℤ × ℤ, -((k.1 : ℂ) ^ 2 + (k.2 : ℂ) ^ 2) * coeff ψ k = coeff ω k

/-- `L₀ e_k = i(k₁ sin y - k₂ sin x) e_k`, where `L₀ = sin y ∂ₓ - sin x ∂_y`, see `L0char_coe`. -/
def L0char (k : ℤ × ℤ) (p : Torus) : ℂ :=
  I * (k.1 * Real.Angle.sin p.2 - k.2 * Real.Angle.sin p.1) * char k p

/-- `L₀g = h` weakly. The vector field `L₀` is real and divergence free, so
`∫ (L₀g) φ = -∫ g L₀φ`; testing with `φ = conj(e_k)`, for which `L₀φ = conj(L₀e_k)`, gives the
equations below. -/
def HasL0 (g h : L2) : Prop :=
  ∀ k : ℤ × ℤ, ∫ p, conj (char k p) * h p = -∫ p, conj (L0char k p) * g p

-- END CHALLENGE DEFINITIONS

/-! ### Bridge to the library -/

/-- The challenge `L²` space is the library's. -/
theorem L2_eq : L2 = NoEmbeddedEigenvalues.L2 := rfl

theorem char_eq (k : ℤ × ℤ) (p : Torus) : char k p = NoEmbeddedEigenvalues.char k p := rfl

theorem L0char_eq (k : ℤ × ℤ) (p : Torus) :
    L0char k p = NoEmbeddedEigenvalues.L0char k p := rfl

theorem coeff_eq (g : NoEmbeddedEigenvalues.L2) (k : ℤ × ℤ) :
    coeff g k = NoEmbeddedEigenvalues.fourierCoeff g k := by
  exact (NoEmbeddedEigenvalues.fourierCoeff_eq_integral g k).symm

/-- Pairing a continuous function with an `L²` function is the Lebesgue integral. -/
theorem inner_toLp (φ : C(NoEmbeddedEigenvalues.Torus, ℂ)) (f : NoEmbeddedEigenvalues.L2) :
    ⟪ContinuousMap.toLp 2 volume ℂ φ, f⟫_ℂ = ∫ p, conj (φ p) * f p := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) φ] with p hp
  simp only [hp, RCLike.inner_apply, mul_comm]

theorem hasL0_iff (g h : NoEmbeddedEigenvalues.L2) :
    HasL0 g h ↔ NoEmbeddedEigenvalues.HasL0 g h := by
  refine forall_congr' fun k => ?_
  have e1 := inner_toLp (NoEmbeddedEigenvalues.char k) h
  have e2 := inner_toLp (NoEmbeddedEigenvalues.L0char k) g
  change _ ↔ ⟪NoEmbeddedEigenvalues.charLp k, h⟫_ℂ = -⟪NoEmbeddedEigenvalues.L0charLp k, g⟫_ℂ
  unfold NoEmbeddedEigenvalues.charLp NoEmbeddedEigenvalues.L0charLp
  rw [e1, e2]
  rfl

theorem isInvLap_iff (ω ψ : NoEmbeddedEigenvalues.L2) :
    IsInvLap ω ψ ↔ NoEmbeddedEigenvalues.MeanZero ω ∧ ψ = NoEmbeddedEigenvalues.invLap ω := by
  simp only [IsInvLap, coeff_eq]
  constructor
  · rintro ⟨h0, hk⟩
    have hmean : NoEmbeddedEigenvalues.MeanZero ω := by
      simpa [NoEmbeddedEigenvalues.MeanZero] using (hk 0).symm
    refine ⟨hmean, NoEmbeddedEigenvalues.fourierCoeff_ext fun k => ?_⟩
    rw [NoEmbeddedEigenvalues.fourierCoeff_invLap]
    split_ifs with hk0
    · subst hk0
      exact h0
    · have hn : (NoEmbeddedEigenvalues.normSq k : ℂ) ≠ 0 := by
        exact_mod_cast (NoEmbeddedEigenvalues.normSq_pos k hk0).ne'
      rw [← hk k]
      field_simp
      push_cast [NoEmbeddedEigenvalues.normSq]
      ring
  · rintro ⟨hmean, rfl⟩
    refine ⟨NoEmbeddedEigenvalues.meanZero_invLap ω, fun k => ?_⟩
    rw [NoEmbeddedEigenvalues.fourierCoeff_invLap]
    split_ifs with hk0
    · subst hk0
      simpa using hmean.symm
    · have hn : (NoEmbeddedEigenvalues.normSq k : ℂ) ≠ 0 := by
        exact_mod_cast (NoEmbeddedEigenvalues.normSq_pos k hk0).ne'
      field_simp
      push_cast [NoEmbeddedEigenvalues.normSq]
      ring

/-- Fourier coefficients of a character. -/
theorem fourierCoeff_charLp (k j : ℤ × ℤ) :
    NoEmbeddedEigenvalues.fourierCoeff (NoEmbeddedEigenvalues.charLp k) j =
      if j = k then 1 else 0 := by
  rw [NoEmbeddedEigenvalues.fourierCoeff, NoEmbeddedEigenvalues.inner_charLp]
  split_ifs
  · exact inv_mul_cancel₀ (pow_ne_zero 2 NoEmbeddedEigenvalues.two_pi_ne_zero_complex)
  · simp

/-- `L₀ e_k = L0char k` in the weak sense of the library. -/
theorem hasL0_charLp (k : ℤ × ℤ) :
    NoEmbeddedEigenvalues.HasL0 (NoEmbeddedEigenvalues.charLp k)
      (NoEmbeddedEigenvalues.L0charLp k) := by
  rw [NoEmbeddedEigenvalues.hasL0_iff_fourierCoeff]
  intro j
  rw [NoEmbeddedEigenvalues.L0charLp_fourier]
  simp only [NoEmbeddedEigenvalues.fourierCoeff_sub, NoEmbeddedEigenvalues.fourierCoeff_smul,
    NoEmbeddedEigenvalues.transportCoeff, fourierCoeff_charLp]
  obtain ⟨j1, j2⟩ := j
  obtain ⟨k1, k2⟩ := k
  simp only [Prod.ext_iff, Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero]
  have c1 : (j1 = k1 ∧ j2 - 1 = k2) ↔ (j1 = k1 ∧ j2 = k2 + 1) := by omega
  have c2 : (j1 = k1 ∧ j2 + 1 = k2) ↔ (j1 = k1 ∧ j2 = k2 - 1) := by omega
  have c3 : (j1 - 1 = k1 ∧ j2 = k2) ↔ (j1 = k1 + 1 ∧ j2 = k2) := by omega
  have c4 : (j1 + 1 = k1 ∧ j2 = k2) ↔ (j1 = k1 - 1 ∧ j2 = k2) := by omega
  simp only [c1, c2, c3, c4]
  split_ifs <;> first | (exfalso; omega) | skip
  all_goals
    try obtain ⟨rfl, rfl⟩ := ‹(_ : ℤ) = _ ∧ (_ : ℤ) = _›
    push_cast
    ring

/-! ### Main theorem -/

theorem no_embedded_eigenvalues (lam : ℝ) (hlam : lam ≠ 0) (ω ψ : L2) (hψ : IsInvLap ω ψ)
    (h : HasL0 (ω + ψ) ((I * lam) • ω)) : ω = 0 := by
  obtain ⟨hmean, rfl⟩ := (isInvLap_iff ω ψ).mp hψ
  exact NoEmbeddedEigenvalues.main lam hlam ω
    ((NoEmbeddedEigenvalues.hasL_iff_isEigenSolution lam ω).mpr ⟨hmean, (hasL0_iff _ _).mp h⟩)

/-! ### Sanity checks of the definitions -/

theorem char_coe (k : ℤ × ℤ) (x y : ℝ) :
    char k ((x : AddCircle (2 * π)), (y : AddCircle (2 * π))) =
      exp (I * (k.1 * x + k.2 * y)) :=
  NoEmbeddedEigenvalues.char_coe k x y

theorem L0char_coe (k : ℤ × ℤ) (x y : ℝ) :
    L0char k ((x : AddCircle (2 * π)), (y : AddCircle (2 * π))) =
      Real.sin y * deriv (fun s : ℝ => exp (I * (k.1 * s + k.2 * y))) x -
        Real.sin x * deriv (fun t : ℝ => exp (I * (k.1 * x + k.2 * t))) y :=
  NoEmbeddedEigenvalues.L0char_coe k x y

theorem existsUnique_isInvLap (ω : L2) (hω : coeff ω 0 = 0) : ∃! ψ, IsInvLap ω ψ := by
  have hmean : NoEmbeddedEigenvalues.MeanZero ω := (coeff_eq ω 0).symm.trans hω
  exact ⟨NoEmbeddedEigenvalues.invLap ω, (isInvLap_iff _ _).mpr ⟨hmean, rfl⟩,
    fun ψ hψ => ((isInvLap_iff _ _).mp hψ).2⟩

theorem hasL0_char (k : ℤ × ℤ) (g h : L2) (hg : g =ᵐ[volume] char k)
    (hh : h =ᵐ[volume] L0char k) : HasL0 g h := by
  have hg' : g = NoEmbeddedEigenvalues.charLp k :=
    Lp.ext (hg.trans (NoEmbeddedEigenvalues.charLp_ae_eq k).symm)
  have hh' : h = NoEmbeddedEigenvalues.L0charLp k :=
    Lp.ext (hh.trans (ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (NoEmbeddedEigenvalues.L0char k)).symm)
  subst hg' hh'
  exact (hasL0_iff _ _).mpr (hasL0_charLp k)

theorem zero_eigenvalue :
    ∃ ω ψ : L2, ω ≠ 0 ∧ IsInvLap ω ψ ∧ HasL0 (ω + ψ) ((I * (0 : ℝ)) • ω) := by
  let e : NoEmbeddedEigenvalues.L2 := NoEmbeddedEigenvalues.charLp (1, 0)
  have he : e ≠ 0 := by
    intro h0
    have := fourierCoeff_charLp (1, 0) (1, 0)
    rw [show NoEmbeddedEigenvalues.charLp (1, 0) = 0 from h0] at this
    simp [NoEmbeddedEigenvalues.fourierCoeff] at this
  have hinv : -e = NoEmbeddedEigenvalues.invLap e := by
    refine NoEmbeddedEigenvalues.fourierCoeff_ext fun j => ?_
    rw [NoEmbeddedEigenvalues.fourierCoeff_invLap, ← neg_one_smul ℂ e,
      NoEmbeddedEigenvalues.fourierCoeff_smul, fourierCoeff_charLp]
    split_ifs with h1 h2 <;> simp_all [NoEmbeddedEigenvalues.normSq, Prod.ext_iff]
  have hmean : NoEmbeddedEigenvalues.MeanZero e := by
    simp [e, NoEmbeddedEigenvalues.MeanZero, fourierCoeff_charLp, Prod.ext_iff]
  have hL0 : NoEmbeddedEigenvalues.HasL0 (e + -e) ((I * (0 : ℝ)) • e) := by
    simpa using NoEmbeddedEigenvalues.HasL0.zero
  exact ⟨e, -e, he, (isInvLap_iff _ _).mpr ⟨hmean, hinv⟩, (hasL0_iff _ _).mpr hL0⟩

end EulerDipole
