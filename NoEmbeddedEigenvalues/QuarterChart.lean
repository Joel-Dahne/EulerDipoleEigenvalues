import NoEmbeddedEigenvalues.QuarterMeasureTransport
import NoEmbeddedEigenvalues.CellPeriodization
import NoEmbeddedEigenvalues.WeakQuarterReconstruction

/-!
# The open base-quarter orbit chart

Blueprint: `def:quarter-image`, `lem:quarter-open-chart`.

The image is described by ordinary orbit coordinates on the upper regular
patch. Thus its inverse is smooth without crossing the time cut. The strip
and the image are both open; the actual flow map is the chart's forward map.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped Topology ContDiff

/-- The actual spatial image of the open base-quarter strip. -/
def quarterImage (b : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ puncturedCell ∧ 0 < (diagCoord p).2} ∩
    {p | (levelCoord p, timeCoord p) ∈ quarterOrbitStrip b}

lemma contDiffOn_quarterCoordinates {b : ℝ} :
    ContDiffOn ℝ ∞ (fun p ↦ (levelCoord p, timeCoord p)) (quarterImage b) := by
  intro p hp
  exact (contDiffAt_orbitCoordinates hp.1.1
    (fun h ↦ (ne_of_gt hp.1.2) h.1)).contDiffWithinAt

lemma continuousOn_quarterCoordinates {b : ℝ} :
    ContinuousOn (fun p ↦ (levelCoord p, timeCoord p)) (quarterImage b) :=
  contDiffOn_quarterCoordinates.continuousOn

lemma isOpen_quarterImage {b : ℝ} (hb : b ≤ 1) : IsOpen (quarterImage b) := by
  let V := {p : ℝ × ℝ | p ∈ puncturedCell ∧ 0 < (diagCoord p).2}
  have hpc : IsOpen puncturedCell := isOpen_cellSquare.sdiff isClosed_singleton
  have hV : IsOpen V := hpc.inter
    (isOpen_lt continuous_const (show Continuous (fun p : ℝ × ℝ ↦ (diagCoord p).2) by
      unfold diagCoord; fun_prop))
  have hC : ContinuousOn (fun p ↦ (levelCoord p, timeCoord p)) V := by
    intro p hp
    exact (contDiffAt_orbitCoordinates hp.1
      (fun h ↦ (ne_of_gt hp.2) h.1)).continuousAt.continuousWithinAt
  exact hC.isOpen_inter_preimage hV (isOpen_quarterOrbitStrip hb)

lemma quarterCoordinates_dipoleOrbit {b : ℝ} (hb : b ≤ 1) {q : ℝ × ℝ}
    (hq : q ∈ quarterOrbitStrip b) :
    (levelCoord (dipoleOrbit q.1 q.2), timeCoord (dipoleOrbit q.1 q.2)) = q := by
  have hh := (quarterOrbitStrip_subset_orbitDomain hb hq).1
  exact Prod.ext (levelCoord_dipoleOrbit hh.1 hh.2 q.2)
    (timeCoord_dipoleOrbit (quarterOrbitStrip_subset_orbitDomain hb hq))

lemma dipoleOrbit_mem_quarterImage {b : ℝ} (hb : b ≤ 1) {q : ℝ × ℝ}
    (hq : q ∈ quarterOrbitStrip b) : dipoleOrbit q.1 q.2 ∈ quarterImage b := by
  have hh := (quarterOrbitStrip_subset_orbitDomain hb hq).1
  have hp : dipoleOrbit q.1 q.2 ∈ puncturedCell := by
    refine ⟨dipoleOrbit_mem_cellSquare hh.1 hh.2 _, ?_⟩
    intro hz
    have he : dipoleOrbit q.1 q.2 = 0 := hz
    have hl := levelCoord_dipoleOrbit hh.1 hh.2 q.2
    rw [he] at hl
    norm_num [levelCoord, dipoleLift] at hl
    linarith [hh.2]
  have hL := eighthPeriod_pos hh.1 hh.2
  have hB : 0 < orbitB q.1 q.2 := by
    by_cases ht : 0 ≤ q.2
    · exact orbitB_pos_of_mem hh.1 hh.2 ⟨ht, by linarith [hq.2.2.2]⟩
    · have ht' : 0 < orbitB q.1 (-q.2) :=
        orbitB_pos_of_mem hh.1 hh.2 ⟨by linarith, by linarith [hq.2.2.1]⟩
      simpa only [orbitB_neg'] using ht'
  refine ⟨⟨hp, hB⟩, ?_⟩
  change (levelCoord (dipoleOrbit q.1 q.2), timeCoord (dipoleOrbit q.1 q.2)) ∈ quarterOrbitStrip b
  rwa [quarterCoordinates_dipoleOrbit hb hq]

/-- The actual flow-time map, with its canonical smooth inverse on the quarter. -/
def quarterChart {b : ℝ} (hb : b ≤ 1) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun q := dipoleOrbit q.1 q.2
  invFun p := (levelCoord p, timeCoord p)
  source := quarterOrbitStrip b
  target := quarterImage b
  map_source' := fun {_} hq ↦ dipoleOrbit_mem_quarterImage hb hq
  map_target' := fun {_} hp ↦ hp.2
  left_inv' := fun {_} hq ↦ quarterCoordinates_dipoleOrbit hb hq
  right_inv' := fun {_} hp ↦ dipoleOrbit_levelCoord_timeCoord hp.1.1
  continuousOn_toFun := continuous_dipoleOrbit.continuousOn
  continuousOn_invFun := continuousOn_quarterCoordinates
  open_source := isOpen_quarterOrbitStrip hb
  open_target := isOpen_quarterImage hb

lemma contDiffOn_quarterChart {b : ℝ} (hb : b ≤ 1) :
    ContDiffOn ℝ ∞ (quarterChart hb) (quarterOrbitStrip b) := by
  intro q hq
  convert! (contDiffAt_orbitMap (t := q.2)
    (quarterOrbitStrip_subset_orbitDomain hb hq).1).contDiffWithinAt using 1

lemma det_fderiv_quarterChart {b : ℝ} (hb : b ≤ 1) {q : ℝ × ℝ}
    (hq : q ∈ quarterOrbitStrip b) : (fderiv ℝ (quarterChart hb) q).det = 2 := by
  convert! det_fderiv_orbitMap (t := q.2)
    (quarterOrbitStrip_subset_orbitDomain hb hq).1 using 1

end NoEmbeddedEigenvalues
