module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderPhysicalValue
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderLift

/-!
# Genuine physical weighted L² from joint cylinder L²

The inverse square-root-Jacobian reconstruction is S(t,θ)/r. Its finite planar
mass is proved before using the exact factor 2π. All identities and null sets
are transported jointly, never by restricting a raw representative to a ray.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Measure Set

/-- Inverse of the square-root-area-Jacobian pullback. -/
def cylinderPhysicalL2Inverse (S : ℝ × AddCircle (2 * Real.pi) → ℂ)
    (p : ℝ × ℝ) : ℂ := S (logCylinderCoordinates p) / (localRadius 0 p : ℂ)

theorem logCylinderL2Pullback_physicalInverse (S : ℝ × AddCircle (2 * Real.pi) → ℂ) :
    logCylinderL2Pullback (cylinderPhysicalL2Inverse S) = S := by
  funext q
  simp only [logCylinderL2Pullback, cylinderPhysicalL2Inverse,
    logCylinderCoordinates_plane, localRadius_logCylinderPlane]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

/-- Finiteness of the planar norm, including a.e. strong measurability. -/
theorem memLp_cylinderPhysicalL2Inverse {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : MemLp S 2 logCylinderMeasure) :
    MemLp (cylinderPhysicalL2Inverse S) 2 volume := by
  have hr : Measurable (fun p : ℝ × ℝ ↦ (localRadius 0 p : ℂ)) := by
    unfold localRadius
    fun_prop
  have hm : AEStronglyMeasurable (cylinderPhysicalL2Inverse S) volume :=
    (hS.aestronglyMeasurable.comp_quasiMeasurePreserving
      quasiMeasurePreserving_logCylinderCoordinates).div₀ hr.aestronglyMeasurable
  have hl : MemLp (S ∘ logCylinderProjection) 2 (volume.restrict logPolarStrip) := by
    have h := memLp_logCylinderProjection_strip hS (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
    exact h.mono_measure (Measure.restrict_mono
      (prod_mono Subset.rfl Ioo_subset_Ioc_self) le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  have hj : Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-q.1) ^ 2)) := by
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (measurePreserving_logPolarPlane.integrable_comp (hm.norm.pow 2)).mp
  apply (integrable_withDensity_iff_integrable_smul' hj
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  apply hi.congr
  filter_upwards [] with q
  have he : Real.exp (-q.1) ≠ 0 := (Real.exp_pos _).ne'
  have hc : logCylinderCoordinates (logPolarPlane q) = logCylinderProjection q := by
    rw [← logCylinderPlane_coe q.1 q.2]
    exact logCylinderCoordinates_plane _
  have hrq : localRadius 0 (logPolarPlane q) = Real.exp (-q.1) := by
    rw [← logCylinderPlane_coe q.1 q.2]
    exact localRadius_logCylinderPlane _
  simp only [Function.comp_apply, Pi.pow_apply, cylinderPhysicalL2Inverse, hc, hrq,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_pow]
  field_simp

/-- Exact physical mass, only after genuine finiteness has been proved. -/
theorem integral_sq_cylinderPhysicalL2Inverse {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : MemLp S 2 logCylinderMeasure) :
    (∫ p, ‖cylinderPhysicalL2Inverse S p‖ ^ 2) =
      (2 * Real.pi) * ∫ q, ‖S q‖ ^ 2 ∂logCylinderMeasure := by
  have h := integral_sq_logCylinderL2Pullback (memLp_cylinderPhysicalL2Inverse hS)
  rw [logCylinderL2Pullback_physicalInverse] at h
  calc
    _ = (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
        ∫ p, ‖cylinderPhysicalL2Inverse S p‖ ^ 2) := by field_simp
    _ = _ := by rw [← h]

/-- Every real homogeneity has the same genuine inverse-Jacobian weighted norm.
The equality is joint a.e.; no derivative representative is evaluated at zero. -/
theorem cylinderPhysicalValue_weighted_ae (a : ℝ)
    (S : ℝ × AddCircle (2 * Real.pi) → ℂ) :
    (fun p ↦ cylinderPhysicalValue a S p / (Real.rpow (localRadius 0 p) (a + 1) : ℂ))
      =ᵐ[volume] cylinderPhysicalL2Inverse S := by
  have hn : ∀ᵐ p : ℝ × ℝ, p ≠ 0 := by
    rw [ae_iff]
    simp [Measure.volume_eq_prod]
  filter_upwards [hn] with p hp
  have hr := localRadius_pos_of_ne_zero hp
  have he : Real.rpow (localRadius 0 p) (a + 1) =
      Real.rpow (localRadius 0 p) a * localRadius 0 p := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_add hr, Real.rpow_one]
  have hne : (Real.rpow (localRadius 0 p) a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hr a).ne'
  simp only [cylinderPhysicalValue, cylinderPhysicalL2Inverse, he, Complex.ofReal_mul]
  exact mul_div_mul_left _ _ hne

theorem memLp_cylinderPhysicalValue_weighted (a : ℝ)
    {S : ℝ × AddCircle (2 * Real.pi) → ℂ} (hS : MemLp S 2 logCylinderMeasure) :
    MemLp (fun p ↦ cylinderPhysicalValue a S p / (Real.rpow (localRadius 0 p) (a + 1) : ℂ))
      2 volume :=
  (memLp_cylinderPhysicalL2Inverse hS).ae_eq (cylinderPhysicalValue_weighted_ae a S).symm

/-- On a bounded disk, a nonnegative radial weight can be restored without
losing finiteness. Values assigned at the center are irrelevant to this norm. -/
theorem memLp_of_div_localRadius_rpow {F : ℝ × ℝ → ℂ} {ρ s : ℝ}
    (hs : 0 ≤ s)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) s : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    MemLp F 2 (volume.restrict (localDisk 0 ρ)) := by
  have hU : MeasurableSet (localDisk 0 ρ) := by
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hb : MemLp (fun p : ℝ × ℝ ↦ (Real.rpow (localRadius 0 p) s : ℂ)) ⊤
      (volume.restrict (localDisk 0 ρ)) := by
    apply memLp_top_of_bound (by
      simp only [Real.rpow_eq_pow]
      unfold localRadius
      fun_prop) (Real.rpow ρ s)
    filter_upwards [ae_restrict_mem hU] with p hp
    have hr : 0 ≤ localRadius 0 p := Real.sqrt_nonneg _
    simpa only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_eq_pow,
      abs_of_nonneg (Real.rpow_nonneg hr s)] using
        Real.rpow_le_rpow hr (le_of_lt hp) hs
  apply (hb.mul hF).ae_eq
  have hn : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), p ≠ 0 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp [Measure.volume_eq_prod])
  filter_upwards [hn] with p hp
  have he : (Real.rpow (localRadius 0 p) s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (localRadius_pos_of_ne_zero hp) s).ne'
  exact mul_div_cancel₀ _ he

end NoEmbeddedEigenvalues
