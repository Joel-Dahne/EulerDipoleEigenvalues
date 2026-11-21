module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderAngularSpectrum
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderAngularTransform
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.LogPolarL2
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderParity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Physical Poisson data on the logarithmic cylinder

Extend the weighted forcing by zero from the original disk, then apply the
square-root-Jacobian pullback. Parity is transported jointly before slicing;
no arbitrary planar representative is restricted to a chosen circle.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Measure Set

private theorem measurable_disk (ρ : ℝ) : MeasurableSet (localDisk 0 ρ) := by
  apply IsOpen.measurableSet
  apply isOpen_lt _ continuous_const
  unfold localRadius
  fun_prop

theorem localRadius_logCylinderPlane (q : ℝ × AddCircle (2 * Real.pi)) :
    localRadius 0 (logCylinderPlane q) = Real.exp (-q.1) := by
  rcases q with ⟨t, θ⟩
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [logCylinderPlane_coe]
  simp only [localRadius, logPolarPlane, Prod.fst_zero, Prod.snd_zero, sub_zero]
  have he : (Real.exp (-t) * Real.cos θ) ^ 2 + (Real.exp (-t) * Real.sin θ) ^ 2 =
      Real.exp (-t) ^ 2 := by
    calc
      _ = Real.exp (-t) ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [he, Real.sqrt_sq (Real.exp_pos _).le]

theorem logCylinderPlane_reflect_fst (t : ℝ) (θ : AddCircle (2 * Real.pi)) :
    logCylinderPlane (t, (Real.pi : AddCircle (2 * Real.pi)) - θ) =
      axisReflect 0 (logCylinderPlane (t, θ)) := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← AddCircle.coe_sub, logCylinderPlane_coe, logCylinderPlane_coe]
  simp [logPolarPlane, axisReflect, Real.cos_pi_sub, Real.sin_pi_sub]

theorem logCylinderPlane_reflect_snd (t : ℝ) (θ : AddCircle (2 * Real.pi)) :
    logCylinderPlane (t, -θ) = axisReflect 1 (logCylinderPlane (t, θ)) := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← AddCircle.coe_neg, logCylinderPlane_coe, logCylinderPlane_coe]
  simp [logPolarPlane, axisReflect]

/-- The globally defined weighted forcing; outside the input disk it is zero. -/
def cylinderWeightedExtension (a ρ : ℝ) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  (localDisk 0 ρ).indicator (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ))

/-- Physical weighted forcing transported with the square-root area Jacobian. -/
def cylinderForcing (a ρ : ℝ) (F : ℝ × ℝ → ℂ) : ℝ × AddCircle (2 * Real.pi) → ℂ :=
  logCylinderL2Pullback (cylinderWeightedExtension a ρ F)

/-- The pulled-back source is exactly r^(2-a) F inside the input disk and zero outside. -/
theorem cylinderForcing_apply (a ρ : ℝ) (F : ℝ × ℝ → ℂ)
    (q : ℝ × AddCircle (2 * Real.pi)) :
    cylinderForcing a ρ F q = if Real.exp (-q.1) < ρ then
      (Real.exp ((a - 2) * q.1) : ℂ) * F (logCylinderPlane q) else 0 := by
  have hm : logCylinderPlane q ∈ localDisk 0 ρ ↔ Real.exp (-q.1) < ρ := by
    change localRadius 0 (logCylinderPlane q) < ρ ↔ _
    rw [localRadius_logCylinderPlane]
  unfold cylinderForcing logCylinderL2Pullback cylinderWeightedExtension
  split_ifs with hq
  · rw [indicator_of_mem (hm.mpr hq), localRadius_logCylinderPlane]
    have he : -q.1 - (-q.1) * (a - 1) = (a - 2) * q.1 := by ring
    have hc : (Real.exp (-q.1) : ℂ) / (Real.rpow (Real.exp (-q.1)) (a - 1) : ℂ) =
        (Real.exp ((a - 2) * q.1) : ℂ) := by
      rw [← Complex.ofReal_div, Real.rpow_eq_pow,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        ← Real.exp_sub, he]
    calc
      _ = ((Real.exp (-q.1) : ℂ) / (Real.rpow (Real.exp (-q.1)) (a - 1) : ℂ)) *
          F (logCylinderPlane q) := by ring
      _ = _ := by rw [hc]
  · rw [indicator_of_notMem (not_congr hm |>.mpr hq), mul_zero]

/-- The original radial forcing norm supplies an actual finite cylinder norm. -/
theorem cylinderForcing_memLp {a ρ : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    MemLp (cylinderForcing a ρ F) 2 logCylinderMeasure := by
  apply memLp_logCylinderL2Pullback
  exact (memLp_indicator_iff_restrict (measurable_disk ρ).nullMeasurableSet).mpr hF

/-- The physical forcing weight and the probability-Haar normalization agree exactly. -/
theorem cylinderForcing_sq_mass {a ρ : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    (∫ q, ‖cylinderForcing a ρ F q‖ ^ 2 ∂logCylinderMeasure) =
      (2 * Real.pi)⁻¹ * ∫ p in localDisk 0 ρ,
        ‖F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)‖ ^ 2 := by
  have hw : MemLp (cylinderWeightedExtension a ρ F) 2 volume :=
    (memLp_indicator_iff_restrict (measurable_disk ρ).nullMeasurableSet).mpr hF
  rw [cylinderForcing, integral_sq_logCylinderL2Pullback hw]
  congr 1
  have he : (fun p ↦ ‖cylinderWeightedExtension a ρ F p‖ ^ 2) =
      (localDisk 0 ρ).indicator
        (fun p ↦ ‖F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)‖ ^ 2) := by
    funext p
    by_cases hp : p ∈ localDisk 0 ρ <;> simp [cylinderWeightedExtension, hp]
  rw [he, integral_indicator (measurable_disk ρ)]

/-- Radial division and zero extension preserve the given a.e. disk parity. -/
theorem HasAxisParityOn.cylinderWeightedExtension {a ρ : ℝ} {ε : Fin 2 → Bool}
    {F : ℝ × ℝ → ℂ} (hp : HasAxisParityOn ε (localDisk 0 ρ) F) :
    HasAxisParityOn ε univ (cylinderWeightedExtension a ρ F) := by
  intro j
  rw [Measure.restrict_univ]
  have hj := (ae_restrict_iff' (measurable_disk ρ)).mp (hp j)
  filter_upwards [hj] with p hp
  have hm : axisReflect j p ∈ localDisk 0 ρ ↔ p ∈ localDisk 0 ρ := by
    change localRadius 0 (axisReflect j p) < ρ ↔ localRadius 0 p < ρ
    rw [localRadius_axisReflect]
  by_cases hmem : p ∈ localDisk 0 ρ
  · simp only [NoEmbeddedEigenvalues.cylinderWeightedExtension, indicator_of_mem hmem,
      indicator_of_mem (hm.mpr hmem), localRadius_axisReflect, hp hmem]
    ring
  · simp only [NoEmbeddedEigenvalues.cylinderWeightedExtension, indicator_of_notMem hmem,
      indicator_of_notMem (not_congr hm |>.mpr hmem), mul_zero]

/-- Global a.e. planar parity pulls back jointly and then holds on a.e. angular slice. -/
theorem HasAxisParityOn.logCylinder_slices {ε : Fin 2 → Bool} {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε univ f) :
    ∀ᵐ t : ℝ, HasCircleAxisParity ε (fun θ ↦ logCylinderL2Pullback f (t, θ)) := by
  have hx := quasiMeasurePreserving_logCylinderPlane.ae
    (show ∀ᵐ p, f (axisReflect 0 p) = paritySign (ε 0) * f p by
      simpa only [Measure.restrict_univ] using hp 0)
  have hy := quasiMeasurePreserving_logCylinderPlane.ae
    (show ∀ᵐ p, f (axisReflect 1 p) = paritySign (ε 1) * f p by
      simpa only [Measure.restrict_univ] using hp 1)
  have hx' : ∀ᵐ q ∂logCylinderMeasure,
      logCylinderL2Pullback f (q.1, (Real.pi : AddCircle (2 * Real.pi)) - q.2) =
        paritySign (ε 0) * logCylinderL2Pullback f q := by
    filter_upwards [hx] with q hq
    simp only [logCylinderL2Pullback, logCylinderPlane_reflect_fst, hq]
    ring
  have hy' : ∀ᵐ q ∂logCylinderMeasure,
      logCylinderL2Pullback f (q.1, -q.2) =
        paritySign (ε 1) * logCylinderL2Pullback f q := by
    filter_upwards [hy] with q hq
    simp only [logCylinderL2Pullback, logCylinderPlane_reflect_snd, hq]
    ring
  filter_upwards [ae_ae_of_ae_prod hx', ae_ae_of_ae_prod hy'] with t hx_t hy_t
  exact ⟨hx_t, hy_t⟩

/-- Allowed support is produced from the solution's parity and its specified weak
Poisson equation, not postulated for the forcing. All coefficient integrals exist. -/
theorem cylinder_forcing_data {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    MemLp (cylinderForcing a ρ F) 2 logCylinderMeasure ∧
      ∀ᵐ t : ℝ,
        HasCircleAxisParity ε (fun θ ↦ cylinderForcing a ρ F (t, θ)) ∧
        MemLp (fun θ ↦ cylinderForcing a ρ F (t, θ)) 2 AddCircle.haarAddCircle ∧
        (∀ n : ℤ, Integrable (fun θ ↦ _root_.fourier (-n) θ * cylinderForcing a ρ F (t, θ))
          AddCircle.haarAddCircle) ∧
        ∀ n : ℤ, ¬AllowedSaddleDegree ε n.natAbs →
          _root_.fourierCoeff (fun θ ↦ cylinderForcing a ρ F (t, θ)) n = 0 := by
  have hG := cylinderForcing_memLp hF
  refine ⟨hG, ?_⟩
  have hpar := ((hp.weak_laplacian hD hΔ).cylinderWeightedExtension (a := a)).logCylinder_slices
  filter_upwards [hpar, memLp_logCylinder_slices hG] with t ht hnorm
  exact ⟨ht, hnorm, ht.fourierCoeff_support (hnorm.integrable (by norm_num))⟩

/-- The actual forcing modes lie in real-line L² and forbidden modes vanish a.e.
These are the inputs for L² Fourier analysis in the logarithmic-radius variable. -/
theorem cylinder_forcing_modes {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) (n : ℤ) :
    MemLp (cylinderAngularCoeff (cylinderForcing a ρ F) n) 2 volume ∧
      (¬AllowedSaddleDegree ε n.natAbs →
        cylinderAngularCoeff (cylinderForcing a ρ F) n =ᵐ[volume] 0) := by
  refine ⟨cylinderAngularCoeff_memLp (cylinderForcing_memLp hF) n, ?_⟩
  intro hn
  filter_upwards [(cylinder_forcing_data hp hD hΔ hF).2] with t ht
  exact ht.2.2.2 n hn

end NoEmbeddedEigenvalues
