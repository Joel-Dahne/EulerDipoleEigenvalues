module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.LogPolarInverse

/-!
# The pointwise physical cylinder reconstruction

Use the continuous circle-valued inverse coordinates, not a real-angle branch.
For positive exponent, a uniform cylinder bound gives continuity through the
origin with value zero. These are value statements; no weak jet is inferred
from a growth bound or from pointwise parity.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Physical value reconstructed from the same cylinder function. -/
def cylinderPhysicalValue (a : ℝ) (S : ℝ × AddCircle (2 * Real.pi) → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  (Real.rpow (localRadius 0 p) a : ℂ) * S (logCylinderCoordinates p)

/-- Pointwise recovery of the actual input on the entire cylinder. -/
theorem cylinderPhysicalValue_plane (a : ℝ) (S : ℝ × AddCircle (2 * Real.pi) → ℂ)
    (q : ℝ × AddCircle (2 * Real.pi)) :
    cylinderPhysicalValue a S (logCylinderPlane q) = (Real.exp (-a * q.1) : ℂ) * S q := by
  simp only [cylinderPhysicalValue, logCylinderCoordinates_plane, localRadius_logCylinderPlane]
  congr 2
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

theorem cylinderPhysicalValue_zero {a : ℝ} (ha : 0 < a)
    (S : ℝ × AddCircle (2 * Real.pi) → ℂ) : cylinderPhysicalValue a S 0 = 0 := by
  simp [cylinderPhysicalValue, localRadius, Real.zero_rpow ha.ne']

/-- The original uniform bound is retained, with no enlargement of C. -/
theorem norm_cylinderPhysicalValue_le {a C : ℝ} {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : ∀ q, ‖S q‖ ≤ C) (p : ℝ × ℝ) :
    ‖cylinderPhysicalValue a S p‖ ≤ C * Real.rpow (localRadius 0 p) a := by
  have hr : 0 ≤ localRadius 0 p := Real.sqrt_nonneg _
  simp only [cylinderPhysicalValue, Real.rpow_eq_pow]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr a), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hS _) (Real.rpow_nonneg hr a)

/-- Continuity away from zero holds across every real-angle seam. -/
theorem continuousAt_cylinderPhysicalValue {a : ℝ}
    {S : ℝ × AddCircle (2 * Real.pi) → ℂ} (hS : Continuous S)
    {p : ℝ × ℝ} (hp : p ≠ 0) : ContinuousAt (cylinderPhysicalValue a S) p := by
  have hr : ContinuousAt (localRadius 0) p := by unfold localRadius; fun_prop
  exact (Complex.continuous_ofReal.continuousAt.comp
    (hr.rpow_const (.inl (localRadius_pos_of_ne_zero hp).ne'))).mul
      (hS.continuousAt.comp (continuousAt_logCylinderCoordinates hp))

/-- Bounded continuous cylinder data give a continuous physical value at zero
as well, without asserting any differentiability there. -/
theorem continuous_cylinderPhysicalValue {a C : ℝ} (ha : 0 < a)
    {S : ℝ × AddCircle (2 * Real.pi) → ℂ} (hS : Continuous S)
    (hbound : ∀ q, ‖S q‖ ≤ C) : Continuous (cylinderPhysicalValue a S) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    change Tendsto _ (𝓝 0) (𝓝 (cylinderPhysicalValue a S 0))
    rw [cylinderPhysicalValue_zero ha]
    have hr : Tendsto (localRadius 0) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (localRadius 0) := by unfold localRadius; fun_prop
      simpa [localRadius] using hc.tendsto 0
    have hl := (hr.rpow_const_nhds_zero ha).const_mul C
    exact squeeze_zero_norm (norm_cylinderPhysicalValue_le hbound)
      (by simpa only [Real.rpow_eq_pow, mul_zero] using hl)
  · exact continuousAt_cylinderPhysicalValue hS hp

/-- Both cylinder reflection signs give pointwise Cartesian parity. The center
is handled by its actual zero value, not by evaluating an a.e. identity there. -/
theorem cylinderPhysicalValue_axis_parity {a : ℝ} (ha : 0 < a)
    {ε : Fin 2 → Bool} {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hp : ∀ t : ℝ, ∀ θ : AddCircle (2 * Real.pi),
      S (t, (Real.pi : AddCircle (2 * Real.pi)) - θ) = paritySign (ε 0) * S (t, θ) ∧
      S (t, -θ) = paritySign (ε 1) * S (t, θ)) :
    ∀ j p, cylinderPhysicalValue a S (axisReflect j p) =
      paritySign (ε j) * cylinderPhysicalValue a S p := by
  have hq (j : Fin 2) (q : ℝ × AddCircle (2 * Real.pi)) :
      cylinderPhysicalValue a S (axisReflect j (logCylinderPlane q)) =
        paritySign (ε j) * cylinderPhysicalValue a S (logCylinderPlane q) := by
    rcases q with ⟨t, θ⟩
    fin_cases j
    · change cylinderPhysicalValue a S (axisReflect 0 (logCylinderPlane (t, θ))) =
        paritySign (ε 0) * cylinderPhysicalValue a S (logCylinderPlane (t, θ))
      rw [← logCylinderPlane_reflect_fst, cylinderPhysicalValue_plane,
        cylinderPhysicalValue_plane, (hp t θ).1]
      ring
    · change cylinderPhysicalValue a S (axisReflect 1 (logCylinderPlane (t, θ))) =
        paritySign (ε 1) * cylinderPhysicalValue a S (logCylinderPlane (t, θ))
      rw [← logCylinderPlane_reflect_snd, cylinderPhysicalValue_plane,
        cylinderPhysicalValue_plane, (hp t θ).2]
      ring
  intro j p
  by_cases hzero : p = 0
  · subst p
    have hr : axisReflect j 0 = 0 := by fin_cases j <;> simp [axisReflect]
    rw [hr, cylinderPhysicalValue_zero ha, mul_zero]
  · calc
      _ = cylinderPhysicalValue a S
          (axisReflect j (logCylinderPlane (logCylinderCoordinates p))) := by
        rw [logCylinderPlane_coordinates hzero]
      _ = _ := (hq j (logCylinderCoordinates p)).trans
        (by rw [logCylinderPlane_coordinates hzero])

end NoEmbeddedEigenvalues
