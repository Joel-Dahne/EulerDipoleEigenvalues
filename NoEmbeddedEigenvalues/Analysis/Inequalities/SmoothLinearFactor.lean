module

public import NoEmbeddedEigenvalues.Analysis.Inequalities.SmoothIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Convex.Basic

/-!
# Smooth division by a linear factor

Blueprint: `lem:smooth-linear-factor`.

A smooth function vanishing at `z` factors through the segment average of its
first derivative. A uniform second-derivative bound controls the derivative of
the factor, including at the removable singularity.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology
open scoped ContDiff

private theorem affine_segment_mem {s : Set ℝ} (hs : Convex ℝ s) {x z t : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x + (1 - t) * z ∈ s := by
  simpa only [AffineMap.lineMap_apply_ring, add_comm] using hs.lineMap_mem hz hx ht

/-- Smooth linear division with a quantitative derivative bound. -/
theorem smooth_linear_factor {l r a b z M : ℝ} {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r)) (hz : z ∈ Icc a b)
    (hsub : Icc a b ⊆ Ioo l r) (hfz : f z = 0) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc a b, ‖deriv (deriv f) x‖ ≤ M) :
    ∃ g g₁ : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioo l r) ∧
      (∀ x ∈ Ioo l r, HasDerivAt g (g₁ x) x) ∧ g z = deriv f z ∧
      (∀ x ∈ Ioo l r, f x = (x - z) • g x) ∧
      (∀ x ∈ Icc a b, ‖g₁ x‖ ≤ M) := by
  let A : ℝ × ℝ → ℝ := fun p ↦ p.2 * p.1 + (1 - p.2) * z
  let U := A ⁻¹' Ioo l r
  have hU : IsOpen U := isOpen_Ioo.preimage (by fun_prop)
  have hf₁ : ContDiffOn ℝ ∞ (deriv f) (Ioo l r) :=
    hf.deriv_of_isOpen isOpen_Ioo (by simp)
  let F : ℝ × ℝ → ℂ := fun p ↦ deriv f (A p)
  have hF : ContDiffOn ℝ ∞ F U := hf₁.comp (by fun_prop) (fun _ hx ↦ hx)
  have hseg (x : ℝ) (hx : x ∈ Ioo l r) : {x} ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    rcases mem_singleton_iff.1 hy with rfl
    exact affine_segment_mem (convex_Ioo l r) hx (hsub hz) ht
  let g := fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t)
  let g₁ := fun x ↦ ∫ t in (0 : ℝ)..1, t • deriv (deriv f) (A (x, t))
  have hg : ContDiffOn ℝ ∞ g (Ioo l r) :=
    contDiffOn_integral_unitInterval hU isOpen_Ioo (fun p hp ↦ hseg p.1 hp.1 ⟨rfl, hp.2⟩) hF
  have hd (x : ℝ) (hx : x ∈ Ioo l r) : HasDerivAt g (g₁ x) x := by
    have hi := hasDerivAt_integral_smooth hU hF (hseg x hx)
    convert hi using 1
    apply intervalIntegral.integral_congr
    intro t ht
    have hxt : (x, t) ∈ U := hseg x hx ⟨rfl, by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht⟩
    have hp := ((hF.contDiffAt (hU.mem_nhds hxt)).differentiableAt (by simp)).hasFDerivAt
    have hpart := hp.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
    have hexp := ((hf₁.contDiffAt (isOpen_Ioo.mem_nhds hxt)).differentiableAt
      (by simp)).hasDerivAt.scomp x (((hasDerivAt_id x).const_mul t).add_const ((1 - t) * z))
    simpa only [mul_one] using (hpart.unique hexp).symm
  refine ⟨g, g₁, hg, hd, ?_, ?_, ?_⟩
  · have he : ∀ t, A (z, t) = z := by intro t; dsimp [A]; ring
    simp [g, F, he]
  · intro x hx
    have hC : ContinuousOn (deriv f) (uIcc z x) := hf₁.continuousOn.mono
      ((convex_Ioo l r).ordConnected.uIcc_subset (hsub hz) hx)
    have hi : IntervalIntegrable (deriv f) volume z x :=
      hC.intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy ↦ ((hf.contDiffAt (isOpen_Ioo.mem_nhds
        ((convex_Ioo l r).ordConnected.uIcc_subset (hsub hz) hx hy))).differentiableAt
          (by simp)).hasDerivAt) hi
    rw [hfz, sub_zero] at hFTC
    rw [← hFTC]
    dsimp only [g, F]
    have he : ∀ t, A (x, t) = (x - z) * t + z := by intro t; dsimp [A]; ring
    simp_rw [he]
    simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add (deriv f) (x - z) z
        (a := 0) (b := 1)).symm
  · intro x hx
    have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖t • deriv (deriv f) (A (x, t))‖ ≤ M := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact (mul_le_mul_of_nonneg_left
        (hbound _ (affine_segment_mem (convex_Icc a b) hx hz ht')) ht'.1).trans
          (mul_le_of_le_one_left hM ht'.2)
    simpa only [g₁, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb

end NoEmbeddedEigenvalues
