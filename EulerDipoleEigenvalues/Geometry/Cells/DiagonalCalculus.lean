module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import EulerDipoleEigenvalues.Geometry.Cells.Cells

/-!
# Calculus in diagonal coordinates

Blueprint: `lem:diagonal-calculus`.

The diagonal coordinates `a = (x + y)/2`, `b = (x - y)/2` have inverse
`(a, b) ↦ (a + b, a - b)`, a linear map of determinant `-2`. Hence `dx dy = 2 da db`, and
since `∂_a = ∂ₓ + ∂_y`, `∂_b = ∂ₓ - ∂_y`, the Laplacian is `Δ = ½(∂_a² + ∂_b²)`. In the
latter the mixed terms cancel directly, without symmetry of second derivatives.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory

/-- `(a, b) ↦ (a + b, a - b)`, the inverse of the diagonal coordinates, as a linear
    equivalence. -/
def diagInvLinear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun q := (q.1 + q.2, q.1 - q.2)
  invFun := diagCoord
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  left_inv q := by ext <;> simp [diagCoord]
  right_inv p := by ext <;> simp [diagCoord] <;> ring

/-- `(a, b) ↦ (a + b, a - b)` as a continuous linear equivalence. -/
def diagInv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := diagInvLinear.toContinuousLinearEquiv

@[simp] theorem diagInv_apply (q : ℝ × ℝ) : diagInv q = (q.1 + q.2, q.1 - q.2) := rfl

theorem diagCoord_diagInv (q : ℝ × ℝ) : diagCoord (diagInv q) = q := diagInvLinear.left_inv q

theorem diagInv_diagCoord (p : ℝ × ℝ) : diagInv (diagCoord p) = p := diagInvLinear.right_inv p

theorem det_diagInvLinear : LinearMap.det (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, diagInvLinear]
  norm_num

/-- `dx dy = 2 da db`. -/
theorem integral_eq_two_smul_integral_diagInv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) :
    ∫ p, f p = (2 : ℝ) • ∫ q, f (diagInv q) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hmap : Measure.map (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) volume =
      ENNReal.ofReal |(LinearMap.det (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_diagInvLinear]; norm_num)
  have key : ∫ q, f (diagInv q) =
      ∫ y, f y ∂Measure.map (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) volume :=
    (diagInv.toHomeomorph.measurableEmbedding.integral_map f).symm
  rw [key, hmap, integral_smul_measure, det_diagInvLinear, smul_smul]
  norm_num

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ × ℝ → E}

/-- `∂_a = ∂ₓ + ∂_y`. -/
theorem partialX_comp_diagInv (hu : Differentiable ℝ u) :
    partialX (u ∘ diagInv) = (fun p ↦ partialX u p + partialY u p) ∘ diagInv := by
  funext q
  have hd : DifferentiableAt ℝ (u ∘ diagInv) q := (hu _).comp q diagInv.differentiableAt
  rw [partialX_eq_fderiv hd, fderiv_comp q (hu _) diagInv.differentiableAt, diagInv.fderiv,
    Function.comp_apply, partialX_eq_fderiv (hu _), partialY_eq_fderiv (hu _), ← map_add,
    ContinuousLinearMap.comp_apply]
  congr 1
  ext <;> simp

/-- `∂_b = ∂ₓ - ∂_y`. -/
theorem partialY_comp_diagInv (hu : Differentiable ℝ u) :
    partialY (u ∘ diagInv) = (fun p ↦ partialX u p - partialY u p) ∘ diagInv := by
  funext q
  have hd : DifferentiableAt ℝ (u ∘ diagInv) q := (hu _).comp q diagInv.differentiableAt
  rw [partialY_eq_fderiv hd, fderiv_comp q (hu _) diagInv.differentiableAt, diagInv.fderiv,
    Function.comp_apply, partialX_eq_fderiv (hu _), partialY_eq_fderiv (hu _), ← map_sub,
    ContinuousLinearMap.comp_apply]
  congr 1
  ext <;> simp

/-- `Δ = ½(∂_a² + ∂_b²)`, in the form `(∂_a² + ∂_b²)(u ∘ T) = 2 (Δu) ∘ T`. -/
theorem laplacian_comp_diagInv (hu : ContDiff ℝ 2 u) (q : ℝ × ℝ) :
    laplacian (u ∘ diagInv) q = (2 : ℝ) • laplacian u (diagInv q) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hx : Differentiable ℝ (partialX u) :=
    (contDiff_partialX (n := 1) (hu.of_le (by norm_num))).differentiable (by norm_num)
  have hy : Differentiable ℝ (partialY u) :=
    (contDiff_partialY (n := 1) (hu.of_le (by norm_num))).differentiable (by norm_num)
  have hadd : Differentiable ℝ (fun p ↦ partialX u p + partialY u p) := hx.add hy
  have hsub : Differentiable ℝ (fun p ↦ partialX u p - partialY u p) := hx.sub hy
  rw [laplacian, partialX_comp_diagInv hd, partialY_comp_diagInv hd,
    partialX_comp_diagInv hadd, partialY_comp_diagInv hsub]
  simp only [Function.comp_apply]
  rw [partialX_add (hx _) (hy _), partialY_add (hx _) (hy _), partialX_sub (hx _) (hy _),
    partialY_sub (hx _) (hy _), laplacian, two_smul]
  abel

end Laplacian

end EulerDipoleEigenvalues
