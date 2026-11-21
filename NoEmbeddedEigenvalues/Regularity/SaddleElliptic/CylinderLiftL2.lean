import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderLift
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderL2Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Joint L² convergence and null-set transport on real-angle lifts

Exact strip mass gives a uniform bound for the lift, hence transports strong
joint L² convergence to every translated angular strip. Countable strip covers
also transport joint a.e. identities to the whole plane. Neither assertion
provides weak derivative gluing.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem integral_sq_logCylinderProjection_strip {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : MemLp S 2 logCylinderMeasure) (a : ℝ) :
    (∫ q in univ ×ˢ Ioc a (a + 2 * Real.pi), ‖S (logCylinderProjection q)‖ ^ 2) =
      (2 * Real.pi) * ∫ q, ‖S q‖ ^ 2 ∂logCylinderMeasure := by
  have hl := hS.smul_measure (c := ENNReal.ofReal (2 * Real.pi)) ENNReal.ofReal_ne_top
  rw [← logCylinderLengthMeasure_eq] at hl
  calc
    _ = ∫ q, ‖S q‖ ^ 2
        ∂((volume : Measure ℝ).prod (volume : Measure (AddCircle (2 * Real.pi)))) :=
      by
        have hp := measurePreserving_logCylinderProjection_strip a
        have hm : AEStronglyMeasurable (fun q ↦ ‖S q‖ ^ 2)
            (Measure.map logCylinderProjection
              (volume.restrict (univ ×ˢ Ioc a (a + 2 * Real.pi)))) := by
          rw [hp.map_eq]
          exact hl.aestronglyMeasurable.norm.pow 2
        simpa only [hp.map_eq] using
          (integral_map hp.measurable.aemeasurable hm).symm
    _ = _ := by
      rw [logCylinderLengthMeasure_eq, integral_smul_measure]
      simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]

private theorem norm_toLp_sub_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ q, ‖f q - g q‖ ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub hf hg, cylinderL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(hf.sub hg).coeFn_toLp] with q hq
  rw [hq, Pi.sub_apply]

/-- The same finite factor works for every approximant and every translated period. -/
theorem tendsto_L2_logCylinderProjection_strip {ι : Type*} {l : Filter ι}
    {S : ι → ℝ × AddCircle (2 * Real.pi) → ℂ}
    {T : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : ∀ i, MemLp (S i) 2 logCylinderMeasure) (hT : MemLp T 2 logCylinderMeasure)
    (hlim : Tendsto (fun i ↦ (hS i).toLp (S i)) l (𝓝 (hT.toLp T))) (a : ℝ) :
    Tendsto (fun i ↦ (memLp_logCylinderProjection_strip (hS i) a).toLp
      (S i ∘ logCylinderProjection)) l
      (𝓝 ((memLp_logCylinderProjection_strip hT a).toLp (T ∘ logCylinderProjection))) := by
  have hn : Tendsto (fun i ↦ ‖(hS i).toLp (S i) - hT.toLp T‖ ^ 2) l (𝓝 0) := by
    have hc : Tendsto (fun _ : ι ↦ hT.toLp T) l (𝓝 (hT.toLp T)) := tendsto_const_nhds
    simpa using (hlim.sub hc).norm.pow 2
  have he (i : ι) :
      ‖(memLp_logCylinderProjection_strip (hS i) a).toLp (S i ∘ logCylinderProjection) -
        (memLp_logCylinderProjection_strip hT a).toLp (T ∘ logCylinderProjection)‖ ^ 2 =
      (2 * Real.pi) * ‖(hS i).toLp (S i) - hT.toLp T‖ ^ 2 := by
    rw [norm_toLp_sub_sq, norm_toLp_sub_sq]
    exact integral_sq_logCylinderProjection_strip ((hS i).sub hT) a
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := (hn.const_mul (2 * Real.pi)).sqrt
  simpa only [← he, Real.sqrt_sq (norm_nonneg _), mul_zero, Real.sqrt_zero] using ht

/-- A joint cylinder a.e. assertion pulls back jointly to the entire real-angle plane. -/
theorem ae_logCylinderProjection {P : ℝ × AddCircle (2 * Real.pi) → Prop}
    (hP : ∀ᵐ q ∂logCylinderMeasure, P q) :
    ∀ᵐ q : ℝ × ℝ, P (logCylinderProjection q) := by
  have hl : ∀ᵐ q ∂((volume : Measure ℝ).prod
      (volume : Measure (AddCircle (2 * Real.pi)))), P q := by
    rw [logCylinderLengthMeasure_eq]
    exact Measure.ae_smul_measure hP _
  let s (n : ℤ) : Set (ℝ × ℝ) :=
    univ ×ˢ Ioc ((n : ℝ) - 1) ((n : ℝ) - 1 + 2 * Real.pi)
  have hcover : ⋃ n, s n = univ := by
    apply eq_univ_of_forall
    intro q
    apply mem_iUnion_of_mem (⌊q.2⌋ : ℤ)
    refine ⟨mem_univ _, ?_, ?_⟩ <;>
      linarith [Int.floor_le q.2, Int.lt_floor_add_one q.2, Real.pi_gt_three]
  rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ × ℝ))), ← hcover]
  apply (ae_restrict_iUnion_iff s _).mpr
  intro n
  exact (measurePreserving_logCylinderProjection_strip ((n : ℝ) - 1)).quasiMeasurePreserving.ae hl

end NoEmbeddedEigenvalues
