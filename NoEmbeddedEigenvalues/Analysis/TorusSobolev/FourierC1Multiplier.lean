module

public import NoEmbeddedEigenvalues.Analysis.TorusSobolev.LiftPeriodization

/-!
# C¹ multipliers for specified Fourier derivatives

Compact C¹ plane tests can be periodized and paired directly with Fourier
derivatives. Thus multiplying a lifted Fourier H¹ function by a C¹ coefficient
needs neither smooth density nor uniform bounds on the coefficient at infinity.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- Fourier integration by parts extends directly to compact C¹ tests. -/
theorem integral_liftL2_mul_coordPartial_of_contDiff {j : Fin 2} {g h : L2}
    (hgh : HasFourierPartial j g h) {φ : ℝ × ℝ → ℂ}
    (hφc : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    ∫ p, liftL2 g p * coordPartial j φ p = -∫ p, liftL2 h p * φ p := by
  have hφ1 : ContDiff ℝ 1 φ := hφc
  have hP1 : ContDiff ℝ 1 (liftPeriodize φ) :=
    (contDiff_liftPeriodize hφc hφs).of_le (by simp)
  have hpP := isPeriodicLift_liftPeriodize φ
  rw [integral_liftL2_mul_eq h hφc.continuous hφs,
    integral_liftL2_mul_eq g ((contDiff_coordPartial (n := 0) j hφc).continuous)
      (hφs.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j φ))]
  by_cases hj : j = 0
  · subst j
    rw [hgh.hasWeakPartial _ _ (hasClassicalPartial_torusFun_x hP1 hpP), neg_neg]
    congr 1
    funext t
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    congr 1
    rw [torusFun_torusProj, torusFun_torusProj, partialX_liftPeriodize hφ1 hφs]
    simp [coordPartial]
  · have hj1 : j = 1 := by omega
    subst j
    rw [hgh.hasWeakPartial _ _ (hasClassicalPartial_torusFun_y hP1 hpP), neg_neg]
    congr 1
    funext t
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    congr 1
    rw [torusFun_torusProj, torusFun_torusProj, partialY_liftPeriodize hφ1 hφs]
    simp [coordPartial]


/-- A C¹ coefficient times a lifted Fourier function has the specified weak derivative. -/
theorem HasFourierPartial.weak_mul_contDiff {g dg : L2} {j : Fin 2}
    (hd : HasFourierPartial j g dg) {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ 1 χ)
    (U : Set (ℝ × ℝ)) :
    HasWeakPartialOn U j (fun p ↦ χ p * liftL2 g p)
      (fun p ↦ coordPartial j χ p * liftL2 g p + χ p * liftL2 dg p) := by
  have hχj := (contDiff_coordPartial (n := 0) j hχ).continuous
  have hlocg := locallyIntegrable_liftL2 g
  have hlocd := locallyIntegrable_liftL2 dg
  refine ⟨(hlocg.continuous_mul hχ.continuous).locallyIntegrableOn U,
    ((hlocg.continuous_mul hχj).add
      (hlocd.continuous_mul hχ.continuous)).locallyIntegrableOn U, fun φ hφ ↦ ?_⟩
  have hφc := hφ.contDiff.continuous
  have hφj := hφ.continuous_coordPartial j
  have hw := integral_liftL2_mul_coordPartial_of_contDiff hd
    (hχ.mul (hφ.contDiff.of_le (by simp))) (hφ.hasCompactSupport.mul_left)
  rw [coordPartial_mul j (hχ.differentiable (by simp))
    (hφ.contDiff.differentiable (by simp))] at hw
  have a1 : Integrable (fun p ↦ liftL2 g p * (coordPartial j χ p * φ p)) :=
    integrable_mul_of_tsupport_subset (hlocg.locallyIntegrableOn univ)
      (hχj.mul hφc) hφ.hasCompactSupport.mul_left (subset_univ _)
  have a2 : Integrable (fun p ↦ liftL2 g p * (χ p * coordPartial j φ p)) :=
    integrable_mul_of_tsupport_subset (hlocg.locallyIntegrableOn univ)
      (hχ.continuous.mul hφj) (hφ.hasCompactSupport_coordPartial j).mul_left (subset_univ _)
  have a3 : Integrable (fun p ↦ liftL2 dg p * (χ p * φ p)) :=
    integrable_mul_of_tsupport_subset (hlocd.locallyIntegrableOn univ)
      (hχ.continuous.mul hφc) hφ.hasCompactSupport.mul_left (subset_univ _)
  simp only [mul_add] at hw
  rw [integral_add a1 a2] at hw
  have e1 : (∫ p, χ p * liftL2 g p * coordPartial j φ p) =
      ∫ p, liftL2 g p * (χ p * coordPartial j φ p) := by
    congr 1; funext p; ring
  have e2 : (∫ p, (coordPartial j χ p * liftL2 g p + χ p * liftL2 dg p) * φ p) =
      (∫ p, liftL2 g p * (coordPartial j χ p * φ p)) +
        ∫ p, liftL2 dg p * (χ p * φ p) := by
    rw [← integral_add a1 a3]
    congr 1; funext p; ring
  rw [e1, e2]
  linear_combination hw

end NoEmbeddedEigenvalues
