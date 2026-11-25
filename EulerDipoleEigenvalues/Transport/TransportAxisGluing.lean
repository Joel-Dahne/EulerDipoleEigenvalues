module

public import EulerDipoleEigenvalues.Transport.WeightedGains.TransportRotations
public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier

/-!
# Distributional no-jump gluing at transverse Cartesian axes

A tangential weak partial extends through a transverse null line by cutoffs.
The global transport equation then determines the missing normal partial where
its velocity coefficient is nonzero. No raw trace on an axis is evaluated.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology

private def velocityCoefficient (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  if j = 0 then (Real.sin p.2 : ℂ) else -(Real.sin p.1 : ℂ)

private theorem coefficient_smooth (j : Fin 2) :
    ContDiff ℝ ∞ (velocityCoefficient j) := by
  unfold velocityCoefficient
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)
  · exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_fst)).neg

private theorem coefficient_partial (j : Fin 2) :
    coordPartial j (velocityCoefficient j) = 0 := by
  funext p
  fin_cases j <;> simp [coordPartial, partialX, partialY, velocityCoefficient]

/-- The other specified partial and global weak transport determine a missing
partial on any open set where its velocity coefficient is nonzero. -/
theorem HasWeakL0On.partial_of_transverse
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F : ℝ × ℝ → ℂ}
    {D : Fin 2 → ℝ × ℝ → ℂ}
    (h : HasWeakL0On U F (fun p ↦
      (Real.sin p.2 : ℂ) * D 0 p - (Real.sin p.1 : ℂ) * D 1 p))
    (hD : ∀ i, LocallyIntegrableOn (D i) U) (j : Fin 2)
    (ho : HasWeakPartialOn U j.rev F (D j.rev))
    (hn : ∀ p ∈ U,
      (if j = 0 then (Real.sin p.2 : ℂ) else -(Real.sin p.1 : ℂ)) ≠ 0) :
    HasWeakPartialOn U j F (D j) := by
  let c := velocityCoefficient
  change ∀ p ∈ U, c j p ≠ 0 at hn
  have hc (i : Fin 2) : Continuous (c i) := (coefficient_smooth i).continuous
  have hweighted : HasWeakPartialOn U j (fun p ↦ c j p * F p)
      (fun p ↦ c j p * D j p) := by
    refine ⟨h.1.continuousOn_mul (hc j).continuousOn hU.isLocallyClosed,
      (hD j).continuousOn_mul (hc j).continuousOn hU.isLocallyClosed, ?_⟩
    intro φ hφ
    let ψ := fun p ↦ c j.rev p * φ p
    have hψ : IsTestFunctionOn U ψ :=
      ⟨(coefficient_smooth j.rev).mul hφ.contDiff,
        hφ.hasCompactSupport.mul_left,
        tsupport_mul_subset_right.trans hφ.tsupport_subset⟩
    have hdψ : coordPartial j.rev ψ = fun p ↦ c j.rev p * coordPartial j.rev φ p := by
      rw [coordPartial_mul j.rev ((coefficient_smooth j.rev).differentiable (by simp))
        (hφ.contDiff.differentiable (by simp)), coefficient_partial]
      simp [c]
    have hoφ := ho.2.2 ψ hψ
    rw [hdψ] at hoφ
    have htest (i : Fin 2) : IsTestFunctionOn U (fun p ↦ c i p * φ p) :=
      ⟨(coefficient_smooth i).mul hφ.contDiff,
        hφ.hasCompactSupport.mul_left,
        tsupport_mul_subset_right.trans hφ.tsupport_subset⟩
    have hterm (i : Fin 2) : Integrable (fun p ↦ F p * (c i p * coordPartial i φ p)) := by
      have hi := integrable_mul_of_tsupport_subset h.1
        ((htest i).continuous_coordPartial i) ((htest i).hasCompactSupport_coordPartial i)
        ((tsupport_coordPartial_subset i _).trans (htest i).tsupport_subset)
      have he : coordPartial i (fun p ↦ c i p * φ p) =
          fun p ↦ c i p * coordPartial i φ p := by
        rw [coordPartial_mul i ((coefficient_smooth i).differentiable (by simp))
          (hφ.contDiff.differentiable (by simp)), coefficient_partial]
        simp [c]
      simpa only [he] using hi
    have hder (i : Fin 2) : Integrable (fun p ↦ D i p * (c i p * φ p)) :=
      integrable_mul_of_tsupport_subset (hD i) (htest i).contDiff.continuous
        (htest i).hasCompactSupport (htest i).tsupport_subset
    have eF : (fun p ↦ F p * classicalL0 φ p) = fun p ↦
        F p * (c j p * coordPartial j φ p) +
          F p * (c j.rev p * coordPartial j.rev φ p) := by
      funext p
      fin_cases j <;>
        simp [classicalL0, coordPartial, c, velocityCoefficient, Complex.real_smul] <;> ring
    have eD : (fun p ↦ ((Real.sin p.2 : ℂ) * D 0 p -
        (Real.sin p.1 : ℂ) * D 1 p) * φ p) = fun p ↦
          D j p * (c j p * φ p) + D j.rev p * (c j.rev p * φ p) := by
      funext p
      fin_cases j <;> simp [c, velocityCoefficient] <;> ring
    have hw := h.2.2 φ hφ
    rw [eF, eD, integral_add (hterm j) (hterm j.rev),
      integral_add (hder j) (hder j.rev), hoφ] at hw
    have ej : (fun p ↦ c j p * F p * coordPartial j φ p) =
        (fun p ↦ F p * (c j p * coordPartial j φ p)) := by funext p; ring
    have ed : (fun p ↦ c j p * D j p * φ p) =
        (fun p ↦ D j p * (c j p * φ p)) := by funext p; ring
    rw [ej, ed]
    linear_combination hw
  have hinv : ContDiffOn ℝ ∞ (fun p ↦ (c j p)⁻¹) U :=
    (coefficient_smooth j).contDiffOn.inv hn
  have hdinv : coordPartial j (fun p ↦ (c j p)⁻¹) = 0 := by
    funext p
    fin_cases j <;> simp [coordPartial, partialX, partialY, c, velocityCoefficient]
  apply (hweighted.mul_contDiffOn hU hinv).congr_ae_on hU.measurableSet
  · exact Eventually.of_forall fun p hp ↦ by
      rw [← mul_assoc, inv_mul_cancel₀ (hn p hp), one_mul]
  · exact Eventually.of_forall fun p hp ↦ by
      simp only [hdinv, Pi.zero_apply, zero_mul, zero_add]
      rw [← mul_assoc, inv_mul_cancel₀ (hn p hp), one_mul]

/-- Finite full-domain norms and the global weak transport equation remove the
axis jumps of specified off-axis derivatives. The origin is excluded; each
nonzero coordinate must have nonzero sine on the domain. -/
theorem HasWeakL0On.h1_of_off_axes
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F R : ℝ × ℝ → ℂ}
    (h : HasWeakL0On U F R) (hF : MemLp F 2 (volume.restrict U))
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, MemLp (D j) 2 (volume.restrict U))
    (hoff : ∀ j, HasWeakPartialOn (U \ {p | p.1 = 0 ∨ p.2 = 0}) j F (D j))
    (hzero : (0 : ℝ × ℝ) ∉ U)
    (hsin : ∀ p ∈ U, ∀ j : Fin 2,
      (if j = 0 then p.1 else p.2) ≠ 0 →
        Real.sin (if j = 0 then p.1 else p.2) ≠ 0) :
    MemSobolevOn 1 U F := by
  let O := U \ {p | p.1 = 0 ∨ p.2 = 0}
  let X := U \ {p | p.1 = 0}
  let Y := U \ {p | p.2 = 0}
  have hxClosed : IsClosed {p : ℝ × ℝ | p.1 = 0} := isClosed_eq continuous_fst continuous_const
  have hyClosed : IsClosed {p : ℝ × ℝ | p.2 = 0} := isClosed_eq continuous_snd continuous_const
  have hO : IsOpen O := hU.sdiff (hxClosed.union hyClosed)
  have hX : IsOpen X := hU.sdiff hxClosed
  have hY : IsOpen Y := hU.sdiff hyClosed
  have hFl : LocallyIntegrableOn F U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have hDl (j : Fin 2) : LocallyIntegrableOn (D j) U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hD j).locallyIntegrable (by norm_num))
  have hne : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    have hn : ∀ᵐ x : ℝ, x ≠ 0 := by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hn,
      Measure.quasiMeasurePreserving_snd.ae hn] with p hx hy
    exact ⟨hx, hy⟩
  let C := fun p ↦ (Real.sin p.2 : ℂ) * D 0 p - (Real.sin p.1 : ℂ) * D 1 p
  have hCl : LocallyIntegrableOn C U :=
    ((hDl 0).continuousOn_mul
      (show Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) by fun_prop).continuousOn
      hU.isLocallyClosed).sub
      ((hDl 1).continuousOn_mul
        (show Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) by fun_prop).continuousOn
        hU.isLocallyClosed)
  have heO := (h.mono sdiff_subset).ae_eq hO
    ((hoff 0).hasWeakL0On hO (hoff 1))
  have he : ∀ᵐ p, p ∈ U → R p = C p := by
    filter_upwards [hne, heO] with p hp he hpU
    exact he ⟨hpU, fun hh ↦ hh.elim hp.1 hp.2⟩
  have hC : HasWeakL0On U F C := by
    refine ⟨h.1, hCl, fun φ hφ ↦ ?_⟩
    rw [h.2.2 φ hφ]
    congr 1
    apply integral_congr_ae
    filter_upwards [he] with p he
    by_cases hp : p ∈ U
    · rw [he hp]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφ.tsupport_subset ht))]
      simp only [mul_zero]
  have hx : HasWeakPartialOn X 0 F (D 0) := by
    apply HasWeakPartialOn.remove_transverse_line (t := 0)
      (hF := hFl.mono_set sdiff_subset) (hD := (hDl 0).mono_set sdiff_subset)
    apply (hoff 0).mono
    rintro p ⟨⟨hp, hx⟩, hy⟩
    exact ⟨hp, fun hh ↦ hh.elim hx hy⟩
  have hy : HasWeakPartialOn Y 1 F (D 1) := by
    apply HasWeakPartialOn.remove_transverse_line (t := 0)
      (hF := hFl.mono_set sdiff_subset) (hD := (hDl 1).mono_set sdiff_subset)
    apply (hoff 1).mono
    rintro p ⟨⟨hp, hy⟩, hx⟩
    exact ⟨hp, fun hh ↦ hh.elim hx hy⟩
  have hxy : HasWeakPartialOn X 1 F (D 1) := by
    apply (hC.mono sdiff_subset).partial_of_transverse hX
      (fun j ↦ (hDl j).mono_set sdiff_subset) 1 (by simpa using hx)
    intro p hp
    simpa using neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hsin p hp.1 0 hp.2))
  have hyx : HasWeakPartialOn Y 0 F (D 0) := by
    apply (hC.mono sdiff_subset).partial_of_transverse hY
      (fun j ↦ (hDl j).mono_set sdiff_subset) 0 (by simpa using hy)
    intro p hp
    simpa using Complex.ofReal_ne_zero.mpr (hsin p hp.1 1 hp.2)
  have hXj (j : Fin 2) : HasWeakPartialOn X j F (D j) := by
    fin_cases j
    · exact hx
    · exact hxy
  have hYj (j : Fin 2) : HasWeakPartialOn Y j F (D j) := by
    fin_cases j
    · exact hyx
    · exact hy
  refine ⟨hF, fun j ↦ ⟨D j, hasWeakPartialOn_of_locally ?_, hD j⟩⟩
  intro p hp
  by_cases hx : p.1 = 0
  · have hy : p.2 ≠ 0 := fun hy ↦ hzero ((show p = (0 : ℝ × ℝ) from Prod.ext hx hy) ▸ hp)
    exact ⟨Y, hY, ⟨hp, hy⟩, hYj j⟩
  · exact ⟨X, hX, ⟨hp, hx⟩, hXj j⟩

end EulerDipoleEigenvalues
