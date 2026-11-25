module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterMeasureTransport

/-!
# Actual integrals and L² sections on a moving quarter strip

Blueprint: `lem:quarter-gradient-energy`.

The constant-Jacobian area bridge applies to raw L² representatives on the
cell. Zero extension of a moving strip then permits ordinary product-measure
Fubini. In particular, no global measurability of the original representative
and no unproved fiber integrability are needed.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

private theorem quarterStrip_indicator_section {E : Type*} [Zero E]
    {b : ℝ} {F : ℝ × ℝ → E}
    {h : ℝ} (hh : h ∈ Ioo 0 b) :
    (fun t ↦ (quarterOrbitStrip b).indicator F (h, t)) =
      (Ioo (-eighthPeriod h) (eighthPeriod h)).indicator (fun t ↦ F (h, t)) := by
  funext t
  simp only [indicator_apply, quarterOrbitStrip, mem_ofPred_eq, hh.1, hh.2,
    true_and, mem_Ioo]

/-- A raw spatial L² representative pulls back to L² without a global
measurability assumption on its chosen values outside the cell. -/
theorem memLp_comp_quarterOrbitStrip_of_memLp {b : ℝ} (hb : b ≤ 1)
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict cellSquare)) :
    MemLp (fun q ↦ F (dipoleOrbit q.1 q.2)) 2 (volume.restrict (quarterOrbitStrip b)) := by
  have hc := (isBounded_cellNeighbourhood.subset
    (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)).isCompact_closure
  have : IsFiniteMeasure (volume.restrict cellSquare) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  have hi := (integrableOn_comp_orbitMap (hF.integrable (by norm_num))).mono_set
    (quarterOrbitStrip_subset_orbitDomain hb)
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
  exact (integrableOn_comp_orbitMap (hF.integrable_norm_pow (by norm_num))).mono_set
    (quarterOrbitStrip_subset_orbitDomain hb)

/-- L² on the joint moving strip gives L² on almost every actual time interval. -/
theorem memLp_quarterStrip_sections {b : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (quarterOrbitStrip b))) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      MemLp (fun t ↦ F (h, t)) 2
        (volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))) := by
  have hI :=
    (memLp_indicator_iff_restrict (measurableSet_quarterOrbitStrip b).nullMeasurableSet).2 hF
  have hR := hI.mono_measure
    (Measure.restrict_le_self (s := Ioo 0 b ×ˢ (univ : Set ℝ)))
  filter_upwards [ae_memLp_sections hR, ae_restrict_mem measurableSet_Ioo] with h hh hhI
  rw [Measure.restrict_univ, quarterStrip_indicator_section hhI] at hh
  exact (memLp_indicator_iff_restrict (measurableSet_Ioo.nullMeasurableSet (μ := volume))).1 hh

/-- Fubini on a zero-extended moving strip supplies an integrable level mass
and genuine integrability on almost every time fiber. -/
theorem integrable_quarterStrip_sections {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {b : ℝ} {F : ℝ × ℝ → E}
    (hF : IntegrableOn F (quarterOrbitStrip b)) :
    IntegrableOn (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), F (h, t)) (Ioo 0 b) ∧
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      IntegrableOn (fun t ↦ F (h, t)) (Ioo (-eighthPeriod h) (eighthPeriod h)) := by
  have hI := (integrable_indicator_iff (measurableSet_quarterOrbitStrip b)).2 hF
  have hP : Integrable ((quarterOrbitStrip b).indicator F)
      ((volume : Measure ℝ).prod volume) := by rwa [← Measure.volume_eq_prod]
  have he (h : ℝ) (hh : h ∈ Ioo 0 b) := quarterStrip_indicator_section (F := F) hh
  constructor
  · apply hP.integral_prod_left.restrict.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [he h hh, integral_indicator measurableSet_Ioo]
  · filter_upwards [ae_restrict_of_ae hP.prod_right_ae, ae_restrict_mem measurableSet_Ioo]
      with h hh hhI
    rw [he h hhI] at hh
    exact (integrable_indicator_iff measurableSet_Ioo).1 hh

end EulerDipoleEigenvalues
