module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.BoundaryTraceContinuity
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWeakGluing
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceH2
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Convergence of transverse trace pairings -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Trace pairings against a fixed L² test converge, including at the boundary. -/
theorem HasACLSectionsOn.tendsto_trace_pairing {I : Set ℝ} {a b t : ℝ}
    {G D : ℝ × ℝ → ℂ} (h : HasACLSectionsOn I (Ioo a b) G D)
    (hab : a < b) (ht : t ∈ Icc a b) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo a b)))
    {β : ℝ → ℂ} (hβ : MemLp β 2 (volume.restrict I)) :
    Tendsto (fun u ↦ ∫ s in I, aclTrace a b G D u s * β s)
      (𝓝[Icc a b] t) (𝓝 (∫ s in I, aclTrace a b G D t s * β s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsmall := ((h.tendsto_trace_sq hab ht hGm hG hD).sqrt).mul_const
    (Real.sqrt (∫ s in I, ‖β s‖ ^ 2))
  simp only [Real.sqrt_zero, zero_mul] at hsmall
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hsmall
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hU := (h.l2_trace hab hGm hG hD u hu).1
  have hT := (h.l2_trace hab hGm hG hD t ht).1
  have iU : Integrable (fun s ↦ aclTrace a b G D u s * β s) (volume.restrict I) :=
    hU.integrable_mul hβ
  have iT : Integrable (fun s ↦ aclTrace a b G D t s * β s) (volume.restrict I) :=
    hT.integrable_mul hβ
  rw [← integral_sub iU iT]
  have he : (fun s ↦ aclTrace a b G D u s * β s - aclTrace a b G D t s * β s) =
      fun s ↦ (aclTrace a b G D u s - aclTrace a b G D t s) * β s := by
    funext s; rw [sub_mul]
  rw [he]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [norm_mul]
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp _ (ENNReal.ofReal 2) _ by simpa using hU.sub hT)
    (show MemLp _ (ENNReal.ofReal 2) _ by simpa using hβ)
  simpa only [Pi.sub_apply, Real.rpow_two, ← Real.sqrt_eq_rpow] using hh

end EulerDipoleEigenvalues
