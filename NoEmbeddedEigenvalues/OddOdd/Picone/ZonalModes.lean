module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic

/-!
# Zonal modes and the weak spectral-gap step

The modes `Uₙ(sin a)` are smooth up to the endpoints of `(-π/2, π/2)`.
Their weighted flux satisfies the Sturm–Liouville equation with weight `cos² a`.
The two-dimensional eigenvalue includes the factor `1/2` converting diagonal
derivatives to Cartesian energy.

`poincare_of_weak_modes` uses only Parseval for the value, orthonormality of
normalized mode gradients, and weak pairings with those gradients. It requires
neither an energy expansion nor smooth approximation in the weighted H¹ norm.
The companion `ZonalBasis.lean` constructs the concrete weighted Hilbert basis.
Application to `zonal_poincare` also needs weak pairings with the supplied
weighted derivatives; the algebraic mode identities here do not supply them.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open scoped ContDiff

/-- The smooth one-dimensional zonal mode for the weight `cos² a`. -/
def zonalMode (n : ℕ) (a : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.sin a)

/-- Product-mode eigenvalue for Cartesian, rather than diagonal, energy. -/
def zonalEigenvalue (n m : ℕ) : ℝ :=
  ((n : ℝ) * (n + 2) + (m : ℝ) * (m + 2)) / 2

@[simp] theorem zonalMode_zero (a : ℝ) : zonalMode 0 a = 1 := by
  simp [zonalMode]

@[simp] theorem zonalMode_one (a : ℝ) : zonalMode 1 a = 2 * Real.sin a := by
  simp [zonalMode]

theorem contDiff_zonalMode (n : ℕ) : ContDiff ℝ ∞ (zonalMode n) := by
  convert ((Polynomial.Chebyshev.U ℝ (n : ℤ)).contDiff_aeval ∞).comp
    Real.contDiff_sin using 1
  funext a
  simp [zonalMode]

theorem zonalMode_neg (n : ℕ) (a : ℝ) :
    zonalMode n (-a) = (-1 : ℝ) ^ n * zonalMode n a := by
  simp [zonalMode, Polynomial.Chebyshev.U_eval_neg]

/-- Multiplication by the ground state identifies the zonal modes with sine
modes on `(0,π)`, which explains their weighted orthogonality and completeness. -/
theorem zonalMode_mul_cos (n : ℕ) (a : ℝ) :
    zonalMode n a * Real.cos a =
      Real.sin (((n : ℝ) + 1) * (Real.pi / 2 - a)) := by
  have h := Polynomial.Chebyshev.U_real_cos (Real.pi / 2 - a) (n : ℤ)
  simpa [zonalMode, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] using h

theorem hasDerivAt_zonalMode (n : ℕ) (a : ℝ) :
    HasDerivAt (zonalMode n)
      ((Polynomial.Chebyshev.U ℝ (n : ℤ)).derivative.eval (Real.sin a) * Real.cos a) a := by
  exact ((Polynomial.Chebyshev.U ℝ (n : ℤ)).hasDerivAt (Real.sin a)).comp a
    (Real.hasDerivAt_sin a)

theorem deriv_zonalMode (n : ℕ) (a : ℝ) :
    deriv (zonalMode n) a =
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).derivative.eval (Real.sin a) * Real.cos a :=
  (hasDerivAt_zonalMode n a).deriv

/-- The mode derivative vanishes linearly at each weighted endpoint, uniformly
in `a` for a fixed degree. This gives the cubic vanishing of weighted flux. -/
theorem zonalMode_deriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, |deriv (zonalMode n) a| ≤ C * |Real.cos a| := by
  let p := (Polynomial.Chebyshev.U ℝ (n : ℤ)).derivative
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun a ↦ ?_⟩
  have hb := hC (Real.sin a) ⟨Real.neg_one_le_sin a, Real.sin_le_one a⟩
  rw [deriv_zonalMode, abs_mul]
  exact mul_le_mul_of_nonneg_right
    ((show |p.eval (Real.sin a)| ≤ C by simpa only [Real.norm_eq_abs] using hb).trans
      (le_max_left _ _)) (abs_nonneg _)

/-- The weighted divergence identity, with no division by `cos a`; it also holds
at the endpoints. -/
theorem hasDerivAt_zonalMode_flux (n : ℕ) (a : ℝ) :
    HasDerivAt (fun t ↦ Real.cos t ^ 2 * deriv (zonalMode n) t)
      (-((n : ℝ) * (n + 2)) * Real.cos a ^ 2 * zonalMode n a) a := by
  let p := Polynomial.Chebyshev.U ℝ (n : ℤ)
  have hp := congrArg (Polynomial.eval (Real.sin a))
    (Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
      (R := ℝ) (n : ℤ))
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_add,
    Polynomial.eval_intCast] at hp
  have hc := Real.sin_sq_add_cos_sq a
  have hd := ((Real.hasDerivAt_cos a).pow 3).mul
    ((p.derivative.hasDerivAt (Real.sin a)).comp a (Real.hasDerivAt_sin a))
  have heq : (fun t ↦ Real.cos t ^ 2 * deriv (zonalMode n) t) =
      (fun t ↦ Real.cos t ^ 3 * p.derivative.eval (Real.sin t)) := by
    funext t
    rw [deriv_zonalMode]
    dsimp [p]
    ring
  rw [heq]
  convert hd using 1
  · rfl
  · dsimp [p, zonalMode]
    push_cast at hp
    rw [show 1 - Real.sin a ^ 2 = Real.cos a ^ 2 by nlinarith only [hc]] at hp
    linear_combination -(Real.cos a ^ 2) * hp

/-- Central parity removes total degree one; the lowest remaining nonconstant
Cartesian eigenvalue is attained by degrees `(1,1)`. -/
theorem zonalEigenvalue_gap {n m : ℕ} (hne : (n, m) ≠ (0, 0))
    (heven : Even (n + m)) : 3 ≤ zonalEigenvalue n m := by
  obtain ⟨k, hk⟩ := heven
  have hsum : 2 ≤ n + m := by
    have : n ≠ 0 ∨ m ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    omega
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
  have hs : (2 : ℝ) ≤ (n : ℝ) + m := by exact_mod_cast hsum
  unfold zonalEigenvalue
  nlinarith

/-- Bessel turns weak mode pairings into a spectral-gap estimate. `N` is the
squared norm after removing the constant mode. The index set can omit all
symmetry-forbidden modes. No completeness of the gradient family is assumed. -/
theorem poincare_of_weak_modes {ι F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {v : ι → F} (hv : Orthonormal ℂ v) {c : ι → ℂ} {eigenvalue : ι → ℝ}
    {N γ : ℝ} {D : F}
    (hparseval : HasSum (fun i ↦ ‖c i‖ ^ 2) N)
    (hpair : ∀ i, ‖inner ℂ (v i) D‖ ^ 2 = eigenvalue i * ‖c i‖ ^ 2)
    (hgap : ∀ i, c i ≠ 0 → γ ≤ eigenvalue i) : γ * N ≤ ‖D‖ ^ 2 := by
  have hle : γ * N ≤ ∑' i, ‖inner ℂ (v i) D‖ ^ 2 := by
    apply hasSum_le _ (hparseval.mul_left γ) (hv.inner_products_summable D).hasSum
    intro i
    rw [hpair i]
    by_cases hi : c i = 0
    · simp [hi]
    · exact mul_le_mul_of_nonneg_right (hgap i hi) (sq_nonneg _)
  exact hle.trans (hv.tsum_inner_products_le D)

end NoEmbeddedEigenvalues
