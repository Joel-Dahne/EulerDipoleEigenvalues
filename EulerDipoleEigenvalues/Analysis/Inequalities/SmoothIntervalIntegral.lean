module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth parameter integrals over a compact interval

A jointly smooth integrand on an open neighbourhood of `s × [0, 1]` has a smooth
parameter integral on the open set `s`. Compactness supplies a uniform local bound
for each derivative; the proof iterates dominated differentiation under the integral.
Used by the regular period quadrature and the incomplete orbit-time quadrature.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Filter Topology Set Metric MeasureTheory
open scoped ContDiff

universe u

private theorem bounded_integral_tube {P E : Type u} [NormedAddCommGroup P]
    [NormedAddCommGroup E] {F : P × ℝ → E} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hF : ContinuousOn F U) {p : P}
    (hp : {p} ×ˢ Icc (0 : ℝ) 1 ⊆ U) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ x ∈ ball p ε, ∀ t ∈ Icc (0 : ℝ) 1,
      (x, t) ∈ U ∧ ‖F (x, t)‖ ≤ C := by
  have hK : IsCompact ({p} ×ˢ Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  obtain ⟨V, hKV, hV, hb⟩ :=
    exists_isOpen_isBounded_image_of_isCompact_of_continuousOn hK hU hp hF
  obtain ⟨ε, hε, htube⟩ := hK.exists_thickening_subset_open (hV.inter hU)
    (subset_inter hKV hp)
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨ε, C, hε, fun x hx t ht ↦ ?_⟩
  have hxt : (x, t) ∈ V ∩ U := by
    apply htube
    refine mem_thickening_iff.2 ⟨(p, t), ⟨by simp, ht⟩, ?_⟩
    simpa [Prod.dist_eq, hε] using hx
  exact ⟨hxt.2, hC _ (mem_image_of_mem F hxt.1)⟩

/-- Dominated differentiation for a smooth integrand near a compact vertical segment. -/
theorem hasFDerivAt_integral_unitInterval {P E : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × ℝ → E} {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {p : P} (hp : {p} ×ˢ Icc (0 : ℝ) 1 ⊆ U) :
    HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, (fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)) p := by
  let G : P × ℝ → P →L[ℝ] E :=
    fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ P ℝ)
  have hG : ContDiffOn ℝ ∞ G U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
  obtain ⟨ε, C, hε, hb⟩ := bounded_integral_tube hU hG.continuousOn hp
  have hslice (x : P) (hx : x ∈ ball p ε) :
      ContinuousOn (fun t ↦ F (x, t)) (Icc 0 1) :=
    hF.continuousOn.comp (by fun_prop) (fun t ht ↦ (hb x hx t ht).1)
  have hsliceG : ContinuousOn (fun t ↦ G (p, t)) (Icc 0 1) :=
    hG.continuousOn.comp (by fun_prop) (fun t ht ↦ hp ⟨by simp, ht⟩)
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t ↦ F (x, t)) (F' := fun x t ↦ G (x, t))
    (bound := fun _ ↦ C) (ball_mem_nhds p hε) ?_
    ((hslice p (mem_ball_self hε)).intervalIntegrable_of_Icc zero_le_one)
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds p hε] with x hx
    exact ((hslice x hx).aestronglyMeasurable measurableSet_Icc).mono_set (by
      rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
  · exact (hsliceG.aestronglyMeasurable measurableSet_Icc).mono_set (by
      rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact (hb x hx t (Ioc_subset_Icc_self ht)).2
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hxt := (hb x hx t (Ioc_subset_Icc_self ht)).1
    have hd : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
      ((hF.contDiffAt (hU.mem_nhds hxt)).differentiableAt (by simp)).hasFDerivAt
    exact hd.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

/-- A jointly smooth integrand has a smooth fixed-interval parameter integral. -/
theorem contDiffOn_integral_unitInterval {P E : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × ℝ → E} {U : Set (P × ℝ)} {s : Set P} (hU : IsOpen U) (hs : IsOpen s)
    (hsub : s ×ˢ Icc (0 : ℝ) 1 ⊆ U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t)) s := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing E with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    intro p hp
    exact (hasFDerivAt_integral_unitInterval hU hF (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩; rcases mem_singleton_iff.1 hx with rfl
      exact hsub ⟨hp, ht⟩)).continuousAt.continuousWithinAt
  | succ n ih =>
    let G : P × ℝ → P →L[ℝ] E :=
      fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ P ℝ)
    have hG : ContDiffOn ℝ ∞ G U :=
      (hF.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
    have hd : ∀ p ∈ s, HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
        (∫ t in (0 : ℝ)..1, G (p, t)) p := by
      intro p hp
      apply hasFDerivAt_integral_unitInterval hU hF
      rintro ⟨x, t⟩ ⟨hx, ht⟩; rcases mem_singleton_iff.1 hx with rfl
      exact hsub ⟨hp, ht⟩
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    exact ⟨fun p hp ↦ (hd p hp).differentiableAt.differentiableWithinAt,
      by simp, (ih hG).congr (fun p hp ↦ (hd p hp).fderiv)⟩

/-- Local version: the integrand need only be smooth near the vertical segment at `p`. -/
theorem contDiffAt_integral_unitInterval {P E : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × ℝ → E} {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {p : P} (hp : {p} ×ˢ Icc (0 : ℝ) 1 ⊆ U) :
    ContDiffAt ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t)) p := by
  obtain ⟨ε, C, hε, hb⟩ := bounded_integral_tube hU hF.continuousOn hp
  exact (contDiffOn_integral_unitInterval hU isOpen_ball
    (fun q hq ↦ (hb q.1 hq.1 q.2 hq.2).1) hF).contDiffAt (ball_mem_nhds p hε)

/-- One-dimensional parameter version of the shared differentiation rule. -/
theorem hasDerivAt_integral_smooth {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × ℝ → E} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {h : ℝ}
    (hh : {h} ×ˢ Icc (0 : ℝ) 1 ⊆ U) :
    HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, fderiv ℝ F (h, t) (1, 0)) h := by
  let G : ℝ × ℝ → ℝ →L[ℝ] E :=
    fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hG : ContDiffOn ℝ ∞ G U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
  have hi : IntervalIntegrable (fun t ↦ G (h, t)) MeasureTheory.volume 0 1 :=
    (hG.continuousOn.comp (by fun_prop)
      (fun t ht ↦ hh ⟨by simp, ht⟩)).intervalIntegrable_of_Icc zero_le_one
  have hd := (hasFDerivAt_integral_unitInterval hU hF hh).hasDerivAt
  rw [ContinuousLinearMap.intervalIntegral_apply hi] at hd
  exact hd

end EulerDipoleEigenvalues
