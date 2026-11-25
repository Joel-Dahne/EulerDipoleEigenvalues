module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterReconstruction
public import EulerDipoleEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport

/-!
# Square integrability in recentered quarter coordinates

Blueprint: `lem:quarter-l2-pullback`.

The quarter strip is a subset of the full flow-time coordinate domain.
The constant-Jacobian integrability bridge transports actual squared norms;
no measure-preservation property is asserted for the level projection.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

theorem quarterOrbitStrip_subset_orbitDomain {b : ℝ} (hb : b ≤ 1) :
    quarterOrbitStrip b ⊆ orbitDomain := by
  intro q hq
  have hq1 : q.1 ∈ Ioo (0 : ℝ) 1 := ⟨hq.1, hq.2.1.trans_le hb⟩
  have hL := eighthPeriod_pos hq1.1 hq1.2
  exact ⟨hq1, by constructor <;> linarith [hq.2.2.1, hq.2.2.2]⟩

/-- A measurable spatial L² representative pulls back to L² on the base quarter. -/
theorem memLp_comp_quarterOrbitStrip {b : ℝ} (hb : b ≤ 1) {F : ℝ × ℝ → ℂ}
    (hm : Measurable F) (hF : MemLp F 2 (volume.restrict cellSquare)) :
    MemLp (fun q ↦ F (dipoleOrbit q.1 q.2)) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have hp := (integrableOn_comp_orbitMap hi).mono_set
    (quarterOrbitStrip_subset_orbitDomain hb)
  exact (memLp_two_iff_integrable_sq_norm
    (hm.comp continuous_dipoleOrbit.measurable).aestronglyMeasurable).2 hp

end EulerDipoleEigenvalues
