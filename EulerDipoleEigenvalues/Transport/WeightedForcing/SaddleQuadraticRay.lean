module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterRayRadialTrace
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SaddleLogarithmicMass

/-!
# Explicit logarithmic quadratic ray bounds

Blueprint: `lem:saddle-quadratic-ray`, `lem:saddle-quadratic-first-jet`.

Along each Cartesian ray the quadratic is homogeneous of degree two, and its
classical gradient is homogeneous of degree one. A positive residual radius
power absorbs the logarithm, without polar trace estimates.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

theorem continuous_saddleQuadratic (c : ℝ × ℝ) (a : ℂ) :
    Continuous (saddleQuadratic c a) := by
  unfold saddleQuadratic
  fun_prop

theorem continuous_first_saddleQuadratic (c : ℝ × ℝ) (a : ℂ) (j : Fin 2) :
    Continuous (classicalComplexJet [j] (saddleQuadratic c a)) := by
  change Continuous (fun p ↦ classicalComplexJet [j] (saddleQuadratic c a) p)
  simp_rw [first_saddleQuadratic]
  fin_cases j <;> dsimp [axisCoord] <;> fun_prop

theorem saddleQuadratic_quarterRay (k : Fin 4) (side : Bool) (a : ℂ) (r : ℝ) :
    saddleQuadratic (rotatedQuarterEndpointRay k side 0) a
      (rotatedQuarterEndpointRay k side r) = (r : ℂ) ^ 2 *
        saddleQuadratic (rotatedQuarterEndpointRay k side 0) a
          (rotatedQuarterEndpointRay k side 1) := by
  fin_cases k <;> cases side <;>
    simp [saddleQuadratic, rotatedQuarterEndpointRay, quarterEndpointRay,
      Function.iterate_succ_apply', rotLift] <;> ring

theorem first_saddleQuadratic_quarterRay (k : Fin 4) (side : Bool) (a : ℂ)
    (j : Fin 2) (r : ℝ) :
    classicalComplexJet [j] (saddleQuadratic (rotatedQuarterEndpointRay k side 0) a)
      (rotatedQuarterEndpointRay k side r) = (r : ℂ) *
        classicalComplexJet [j] (saddleQuadratic (rotatedQuarterEndpointRay k side 0) a)
          (rotatedQuarterEndpointRay k side 1) := by
  simp only [first_saddleQuadratic]
  fin_cases k <;> cases side <;> fin_cases j <;>
    simp [rotatedQuarterEndpointRay, quarterEndpointRay, Function.iterate_succ_apply',
      rotLift, axisCoord] <;> ring

theorem saddleQuadratic_log_quarterRay_value {ρ : ℝ} (hρ : ρ ≤ 1)
    (k : Fin 4) (side : Bool) (a : ℂ) :
    MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      saddleQuadratic (rotatedQuarterEndpointRay k side 0) a
        (rotatedQuarterEndpointRay k side r) / (Real.rpow r (3 / 2) : ℂ)) 2
      (volume.restrict (Ioo 0 ρ)) := by
  have h := memLp_logRadius_nat_mul_div hρ (n := 2) (t := 3 / 2) (by norm_num)
    (memLp_const (saddleQuadratic (rotatedQuarterEndpointRay k side 0) a
      (rotatedQuarterEndpointRay k side 1)))
  apply h.ae_eq
  exact Eventually.of_forall fun r ↦ by
    dsimp only
    rw [saddleQuadratic_quarterRay k side a r]
    ring

theorem saddleQuadratic_log_quarterRay_gradient {ρ : ℝ} (hρ : ρ ≤ 1)
    (k : Fin 4) (side : Bool) (a : ℂ) (j : Fin 2) :
    MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) *
      classicalComplexJet [j] (saddleQuadratic (rotatedQuarterEndpointRay k side 0) a)
        (rotatedQuarterEndpointRay k side r) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 ρ)) := by
  have h := memLp_logRadius_nat_mul_div hρ (n := 1) (t := 1 / 2) (by norm_num)
    (memLp_const (classicalComplexJet [j]
      (saddleQuadratic (rotatedQuarterEndpointRay k side 0) a)
      (rotatedQuarterEndpointRay k side 1)))
  apply h.ae_eq
  exact Eventually.of_forall fun r ↦ by
    dsimp only
    rw [first_saddleQuadratic_quarterRay k side a j r, Real.sqrt_eq_rpow r]
    simp only [pow_one, Real.rpow_eq_pow]
    ring

end EulerDipoleEigenvalues
