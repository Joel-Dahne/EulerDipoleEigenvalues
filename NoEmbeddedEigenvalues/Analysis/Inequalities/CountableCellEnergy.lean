module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Summing uniform L² estimates over disjoint measurable cells

Blueprint: `lem:countable-cell-energy`.

Finite global energy follows from a uniform cell bound. Finiteness is proved
with nonnegative integrals, before returning to Bochner integrals.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open Set MeasureTheory
open scoped ENNReal

/-- A common energy controls the L² norm over a countable disjoint family. -/
theorem memLp_two_of_cell_energy {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hdis : Pairwise fun i j ↦ Disjoint (s i) (s j)) {F : α → ℂ} {G : α → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hG : IntegrableOn G (⋃ n, s n) μ)
    (hGpos : ∀ x ∈ ⋃ n, s n, 0 ≤ G x)
    (hF : ∀ n, MemLp F 2 (μ.restrict (s n)))
    (hbound : ∀ n, (∫ x in s n, ‖F x‖ ^ 2 ∂μ) ≤ K * ∫ x in s n, G x ∂μ) :
    MemLp F 2 (μ.restrict (⋃ n, s n)) := by
  have hFm : AEStronglyMeasurable F (μ.restrict (⋃ n, s n)) :=
    AEStronglyMeasurable.iUnion fun n ↦ (hF n).aestronglyMeasurable
  have hGn (n : ℕ) : IntegrableOn G (s n) μ := hG.mono_set (subset_iUnion s n)
  have hGp (n : ℕ) : 0 ≤ᵐ[μ.restrict (s n)] G := by
    filter_upwards [ae_restrict_mem (hs n)] with x hx
    exact hGpos x (mem_iUnion.2 ⟨n, hx⟩)
  have hbe (n : ℕ) : (∫⁻ x in s n, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal K * ∫⁻ x in s n, ENNReal.ofReal (G x) ∂μ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hF n).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal (hGn n) (hGp n), ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  apply (memLp_two_iff_integrable_sq_norm hFm).2
  refine ⟨hFm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  have hsum := ENNReal.tsum_le_tsum hbe
  rw [ENNReal.tsum_mul_left,
    ← lintegral_iUnion hs hdis (fun x ↦ ENNReal.ofReal (G x))] at hsum
  rw [lintegral_iUnion hs hdis]
  apply hsum.trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hasFiniteIntegral_iff_ofReal (by
      filter_upwards [ae_restrict_mem (MeasurableSet.iUnion hs)] with x hx
      exact hGpos x hx)).1 hG.2)

end NoEmbeddedEigenvalues
