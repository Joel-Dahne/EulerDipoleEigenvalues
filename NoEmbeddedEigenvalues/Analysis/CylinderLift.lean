import NoEmbeddedEigenvalues.Analysis.LogPolarL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite local mass on the full real-angle cylinder lift

Every translated fundamental angular strip transports joint L² to angular
length measure. Its open interior gives local integrability near every real
angle, including every seam of any previously selected strip. The full periodic
lift is not asserted to have finite global planar L² mass.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Angular length measure is exactly the finite multiple of probability Haar. -/
theorem logCylinderLengthMeasure_eq :
    (volume : Measure ℝ).prod (volume : Measure (AddCircle (2 * Real.pi))) =
      ENNReal.ofReal (2 * Real.pi) • logCylinderMeasure := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.prod_smul_right]
  rfl

/-- Every translated real-angle fundamental strip transports angular length measure. -/
theorem measurePreserving_logCylinderProjection_strip (a : ℝ) :
    MeasurePreserving logCylinderProjection
      (volume.restrict (univ ×ˢ Ioc a (a + 2 * Real.pi)))
      ((volume : Measure ℝ).prod (volume : Measure (AddCircle (2 * Real.pi)))) := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (AddCircle.measurePreserving_mk (2 * Real.pi) a)
  have hm : volume.restrict (univ ×ˢ Ioc a (a + 2 * Real.pi)) =
      (volume : Measure ℝ).prod (volume.restrict (Ioc a (a + 2 * Real.pi))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm]
  exact hp

/-- Genuine finite mass on any full real-angle period, with the time variable joint. -/
theorem memLp_logCylinderProjection_strip {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : MemLp S 2 logCylinderMeasure) (a : ℝ) :
    MemLp (S ∘ logCylinderProjection) 2
      (volume.restrict (univ ×ˢ Ioc a (a + 2 * Real.pi))) := by
  have hl : MemLp S 2
      ((volume : Measure ℝ).prod (volume : Measure (AddCircle (2 * Real.pi)))) := by
    have h := hS.smul_measure (c := ENNReal.ofReal (2 * Real.pi)) ENNReal.ofReal_ne_top
    rwa [logCylinderMeasure_eq_smul_length, smul_smul,
      ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul] at h
  exact hl.comp_measurePreserving (measurePreserving_logCylinderProjection_strip a)

/-- Every point of the full real-angle plane has a finite-mass neighbourhood. -/
theorem locallyIntegrableOn_logCylinderProjection {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hS : MemLp S 2 logCylinderMeasure) :
    LocallyIntegrableOn (S ∘ logCylinderProjection) univ := by
  intro q _
  let a := q.2 - Real.pi
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioo a (a + 2 * Real.pi)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hq : q ∈ U := by
    refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp only [a] <;> linarith [Real.pi_pos]
  have hm : MemLp (S ∘ logCylinderProjection) 2 (volume.restrict U) :=
    (memLp_logCylinderProjection_strip hS a).mono_measure
      (Measure.restrict_mono (prod_mono Subset.rfl Ioo_subset_Ioc_self) le_rfl)
  have hi : LocallyIntegrableOn (S ∘ logCylinderProjection) U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hm.locallyIntegrable (by norm_num))
  rw [nhdsWithin_univ]
  simpa only [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hq)] using hi q hq

end NoEmbeddedEigenvalues
