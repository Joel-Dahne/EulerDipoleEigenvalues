module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SaddleChartPullback
public import EulerDipoleEigenvalues.Geometry.OrbitCoordinates.PeriodicOrbits

/-! # The linearized Hamiltonian at a saddle -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues

/-- The Jacobian of the dipole velocity in the orthonormal saddle chart, applied to `q`. -/
def saddleLinearVelocity (P q : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (fun z ↦ fderiv ℝ (saddleOrthoCoord P) P
    (dipoleVelocity (saddleOrthoChart P z))) 0 q

/-- The first-order operator `-i L_s` obtained by retaining the linear part of the flow. -/
def saddleLinearHamiltonian (P : ℝ × ℝ) (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  -Complex.I * ((saddleLinearVelocity P q).1 • coordPartial 0 f q +
    (saddleLinearVelocity P q).2 • coordPartial 1 f q)

/-- The two Cartesian cosine values at a saddle have opposite signs. -/
theorem cos_saddle_snd {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    Real.cos P.2 = -Real.cos P.1 := by
  have hs : Real.cos P.1 ^ 2 = 1 := (sq_abs _).symm.trans (by rw [abs_cos_saddle hP]; norm_num)
  obtain ⟨m, n, hmn, rfl⟩ := hP
  have he : Real.cos ((m : ℝ) * Real.pi + n * Real.pi) = -1 := by
    rw [← add_mul, ← Int.cast_add, Real.cos_int_mul_pi, hmn.neg_one_zpow]
  rw [Real.cos_add, Real.sin_int_mul_pi, Real.sin_int_mul_pi, mul_zero, sub_zero] at he
  change Real.cos (n * Real.pi) = -Real.cos (m * Real.pi)
  change Real.cos (m * Real.pi) ^ 2 = 1 at hs
  have hn : Real.cos (m * Real.pi) ≠ 0 := by intro h; simp [h] at hs
  apply mul_left_cancel₀ hn
  rw [he]
  nlinarith only [hs]

/-- The normalized axes diagonalize the saddle Jacobian and give the two eigenvalues
of the linearized Hamiltonian on homogeneous linear polynomials. -/
theorem saddle_linearization {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    let s := Real.cos P.1
    (∀ q, saddleLinearVelocity P q = (-s * q.1, s * q.2)) ∧
    (∀ q, saddleLinearHamiltonian P (fun z ↦ (z.1 : ℂ)) q = Complex.I * s * q.1) ∧
    (∀ q, saddleLinearHamiltonian P (fun z ↦ (z.2 : ℂ)) q = -Complex.I * s * q.2) := by
  let A := (saddleLinear P hP).toContinuousLinearMap
  let B := (saddleLinear P hP).symm.toContinuousLinearMap
  have hchart : HasFDerivAt (saddleOrthoChart P) A 0 := by
    rw [← planeAffine_saddleLinear P hP]
    exact A.hasFDerivAt.add_const P
  have hcoord : ∀ p, saddleOrthoCoord P p = B (p - P) := by
    intro p
    have he := (saddleOrthoChart_orthogonal hP).1 (B (p - P))
    rw [← planeAffine_saddleLinear P hP] at he
    have hp : planeAffine (saddleLinear P hP) P (B (p - P)) = p := by
      change (saddleLinear P hP) ((saddleLinear P hP).symm (p - P)) + P = p
      rw [ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
    rwa [hp] at he
  have hB : fderiv ℝ (saddleOrthoCoord P) P = B := by
    have h : saddleOrthoCoord P = fun p ↦ B p - B P := by
      funext p
      rw [hcoord, map_sub]
    rw [h]
    exact (B.hasFDerivAt.sub_const (B P)).fderiv
  have hvel := (Real.hasDerivAt_sin P.2).comp_hasFDerivAt P
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt |>.prodMk
    (((Real.hasDerivAt_sin P.1).comp_hasFDerivAt P
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).neg)
  have hz : saddleOrthoChart P 0 = P := by simp [saddleOrthoChart]
  have hV (q : ℝ × ℝ) : saddleLinearVelocity P q = (-Real.cos P.1 * q.1, Real.cos P.1 * q.2) := by
    unfold saddleLinearVelocity
    rw [hB]
    have hv : HasFDerivAt dipoleVelocity
        ((Real.cos P.2 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
          (-(Real.cos P.1 • ContinuousLinearMap.fst ℝ ℝ ℝ))) (saddleOrthoChart P 0) := by
      rw [hz]
      exact hvel
    change fderiv ℝ (B ∘ dipoleVelocity ∘ saddleOrthoChart P) 0 q = _
    rw [(B.hasFDerivAt.comp 0 (hv.comp 0 hchart)).fderiv]
    let w := (Real.cos P.2 * (A q).2, -(Real.cos P.1 * (A q).1))
    change B w = _
    have hh := hcoord (w + P)
    rw [add_sub_cancel_right] at hh
    rw [← hh]
    have hs : Real.cos P.1 ^ 2 = 1 := (sq_abs _).symm.trans
      (by rw [abs_cos_saddle hP]; norm_num)
    have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs3 : Real.cos P.1 ^ 3 = Real.cos P.1 := by rw [pow_succ, hs, one_mul]
    subst w
    ext <;> simp [saddleOrthoCoord, A, cos_saddle_snd hP] <;> field_simp <;> ring_nf <;>
      simp [ht, hs3]
  refine ⟨hV, ?_, ?_⟩
  · intro q
    have hx : ∀ p : ℝ × ℝ, partialX (fun z : ℝ × ℝ ↦ (z.1 : ℂ)) p = 1 := fun p ↦
      (hasDerivAt_id p.1).ofReal_comp.deriv
    simp [saddleLinearHamiltonian, hV, coordPartial, hx, partialY, Complex.real_smul]
    ring
  · intro q
    have hy : ∀ p : ℝ × ℝ, partialY (fun z : ℝ × ℝ ↦ (z.2 : ℂ)) p = 1 := fun p ↦
      (hasDerivAt_id p.2).ofReal_comp.deriv
    simp [saddleLinearHamiltonian, hV, coordPartial, hy, partialX, Complex.real_smul]
    ring

end EulerDipoleEigenvalues
