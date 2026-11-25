module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalJets
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A genuinely Euclidean radial smoothing kernel

The generic chosen bump base on a normed space need not be radial. This kernel
uses the explicit inner-product bump base on the complex plane and pulls it
back through the real coordinate equivalence. Its support is an actual
Euclidean disk, not a ball for the product maximum norm.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Metric
open scoped ContDiff Topology

/-- Explicit radial bump equal to one near the origin. -/
def radialPlaneBump (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2
    ((2 / R) • Complex.equivRealProdCLM.symm p)

/-- Normalize by the genuine positive planar mass. -/
def radialPlaneKernel (R : ℝ) (p : ℝ × ℝ) : ℂ :=
  (radialPlaneBump R p / ∫ q, radialPlaneBump R q : ℝ)

/-- Smoothness includes the actual value at zero. -/
theorem contDiff_radialPlaneBump (R : ℝ) : ContDiff ℝ ∞ (radialPlaneBump R) := by
  have hb : ContDiff ℝ ∞ ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) :=
    (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun _ ↦ ⟨by norm_num, mem_univ _⟩)
  exact hb.comp (ContDiff.const_smul (2 / R : ℝ) Complex.equivRealProdCLM.symm.contDiff)

/-- The unnormalized kernel has the required strict radial support bound. -/
theorem radialPlaneBump_support {R : ℝ} (hR : 0 < R) {p : ℝ × ℝ}
    (hp : radialPlaneBump R p ≠ 0) : ‖Complex.equivRealProdCLM.symm p‖ < R := by
  have hm : (2 / R) • Complex.equivRealProdCLM.symm p ∈
      Function.support ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) := hp
  rw [(ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)] at hm
  have hpos : 0 < (2 / R : ℝ) := div_pos (by norm_num) hR
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hm
  rw [div_mul_eq_mul_div, div_lt_iff₀ hR] at hm
  linarith

/-- Compactness is in physical Cartesian coordinates. -/
theorem hasCompactSupport_radialPlaneBump {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialPlaneBump R) := by
  apply HasCompactSupport.intro
    (Complex.equivRealProdCLM.symm.toHomeomorph.isProperMap.isCompact_preimage
      (isCompact_closedBall (0 : ℂ) R))
  intro p hp
  by_contra hn
  exact hp (by simpa using (radialPlaneBump_support hR hn).le)

/-- The normalization divides by a finite, strictly positive actual integral. -/
theorem integral_radialPlaneBump_pos {R : ℝ} (hR : 0 < R) :
    0 < ∫ p, radialPlaneBump R p := by
  have hc := contDiff_radialPlaneBump R |>.continuous
  apply integral_pos_of_integrable_nonneg_ne_zero hc
    (hc.integrable_of_hasCompactSupport (hasCompactSupport_radialPlaneBump hR))
  · intro p
    exact (ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _ |>.1
  · have h0 : radialPlaneBump R 0 = 1 := by
      apply (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num)
      simp
    rw [h0]
    norm_num

/-- The normalized kernel is smooth on the whole plane. -/
theorem contDiff_radialPlaneKernel (R : ℝ) : ContDiff ℝ ∞ (radialPlaneKernel R) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_radialPlaneBump R).div_const _)

/-- Normalization preserves compact support. -/
theorem hasCompactSupport_radialPlaneKernel {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialPlaneKernel R) := by
  change HasCompactSupport
    ((fun t : ℝ ↦ ((t / ∫ q, radialPlaneBump R q : ℝ) : ℂ)) ∘ radialPlaneBump R)
  exact (hasCompactSupport_radialPlaneBump hR).comp_left (g :=
    fun t : ℝ ↦ ((t / ∫ q, radialPlaneBump R q : ℝ) : ℂ)) (by simp)

/-- The kernel's genuine mass is one, before any mean-value identity is used. -/
theorem integral_radialPlaneKernel {R : ℝ} (hR : 0 < R) :
    (∫ p, radialPlaneKernel R p) = 1 := by
  simp only [radialPlaneKernel, integral_complex_ofReal, integral_div]
  rw [div_self (integral_radialPlaneBump_pos hR).ne', Complex.ofReal_one]

/-- Radiality follows from the explicit base, not from a chosen bump instance. -/
theorem radialPlaneKernel_norm_eq (R : ℝ) {p q : ℝ × ℝ}
    (hpq : ‖Complex.equivRealProdCLM.symm p‖ = ‖Complex.equivRealProdCLM.symm q‖) :
    radialPlaneKernel R p = radialPlaneKernel R q := by
  simp only [radialPlaneKernel, radialPlaneBump, ContDiffBumpBase.ofInnerProductSpace,
    norm_smul, hpq]

/-- The closed support fits the same Euclidean radius, including its boundary. -/
theorem tsupport_radialPlaneKernel {R : ℝ} (hR : 0 < R) :
    tsupport (radialPlaneKernel R) ⊆
      {p | ‖Complex.equivRealProdCLM.symm p‖ ≤ R} := by
  apply closure_minimal ?_ (isClosed_le (by fun_prop) continuous_const)
  intro p hp
  have hn : radialPlaneBump R p ≠ 0 := by
    intro hz
    exact hp (by simp [radialPlaneKernel, hz])
  exact (radialPlaneBump_support hR hn).le

end EulerDipoleEigenvalues
