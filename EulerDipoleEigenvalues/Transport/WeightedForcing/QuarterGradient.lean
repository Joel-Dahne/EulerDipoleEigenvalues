module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterChart
public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterInverseFrame
public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.WeakChartTransport

/-!
# Cartesian weak derivatives on the actual quarter image

Blueprint: `lem:quarter-spatial-reconstruction`, `lem:quarter-gradient-identification`.

The generic cofactor chain rule reconstructs a spatial derivative from the
specified derivatives of the same raw pullback. Its source-coordinate formula
is exactly the weighted inverse frame. Constant-Jacobian L² transport then
supplies the spatial weighted bound, without assuming an ordinary spatial
gradient in advance.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The generic cofactor formula is the actual orbit's inverse frame. -/
theorem chartGradient_quarterChart {b : ℝ} (hb : b ≤ 1)
    (H T : ℝ × ℝ → ℂ) (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ quarterOrbitStrip b) :
    chartGradient (quarterChart hb) (fun i ↦ if i = 0 then H else T) j q =
      quarterInverseGradient H T j q := by
  have hd := ((contDiffOn_quarterChart hb).contDiffAt
    ((isOpen_quarterOrbitStrip hb).mem_nhds hq)).differentiableAt (by simp)
  have hx : HasDerivAt (fun h ↦ dipoleOrbit h q.2)
      (fderiv ℝ (quarterChart hb) q (1, 0)) q.1 := by
    convert! hd.hasFDerivAt.comp_hasDerivAt q.1
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)) using 1
  have ht : HasDerivAt (fun t ↦ dipoleOrbit q.1 t)
      (fderiv ℝ (quarterChart hb) q (0, 1)) q.2 := by
    convert! hd.hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)) using 1
  have htime : fderiv ℝ (quarterChart hb) q (0, 1) =
      dipoleVelocity (dipoleOrbit q.1 q.2) :=
    ht.unique (hasDerivAt_dipoleFlow (Real.arccos q.1, -Real.arccos q.1) q.2)
  have hc := chartCofactor_values (contDiffOn_quarterChart hb) j hq
  change (chartCofactor (quarterChart hb) j 0 q * H q +
    chartCofactor (quarterChart hb) j 1 q * T q) / 2 = _
  rw [hc.1, hc.2, htime, ← hx.deriv]
  unfold quarterInverseGradient quarterLevelDual quarterTimeDual
  dsimp only [dipoleVelocity]
  split_ifs <;> push_cast <;> ring

/-- The inverse-frame candidate, evaluated in canonical spatial coordinates. -/
def quarterSpatialGradient (H T : ℝ × ℝ → ℂ) (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  quarterInverseGradient H T j (levelCoord p, timeCoord p)

/-- Both specified raw quarter derivatives reconstruct a weak spatial partial. -/
theorem quarterSpatialGradient_weak {b : ℝ} (hb : b ≤ 1)
    {F H T : ℝ × ℝ → ℂ}
    (hH : HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ F (dipoleOrbit q.1 q.2)) H)
    (hT : HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ F (dipoleOrbit q.1 q.2)) T) (j : Fin 2) :
    HasWeakPartialOn (quarterImage b) j F (quarterSpatialGradient H T j) := by
  have hg (i : Fin 2) : HasWeakPartialOn (quarterOrbitStrip b) i
      (fun q ↦ F (dipoleOrbit q.1 q.2)) ((fun i ↦ if i = 0 then H else T) i) := by
    fin_cases i
    · exact hH
    · exact hT
  have hw := HasWeakPartialOn.comp_chart_symm (contDiffOn_quarterChart hb)
    (fun _ hq ↦ det_fderiv_quarterChart hb hq) hg j
  apply hw.congr_ae_on (isOpen_quarterImage hb).measurableSet
  · exact Eventually.of_forall fun p hp ↦ by
      change F (dipoleOrbit (levelCoord p) (timeCoord p)) = F p
      rw [dipoleOrbit_levelCoord_timeCoord hp.1.1]
  · exact Eventually.of_forall fun p hp ↦ chartGradient_quarterChart hb H T j hp.2

/-- The genuine weighted L² candidate bound becomes a spatial L² bound. -/
theorem memLp_quarterSpatialGradient {b : ℝ} (hb : b ≤ 1)
    {H T : ℝ × ℝ → ℂ} (j : Fin 2)
    (hL : MemLp (fun q ↦ quarterInverseGradient H T j q /
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b))) :
    MemLp (fun p ↦ quarterSpatialGradient H T j p / (saddleDist p : ℂ)) 2
      (volume.restrict (quarterImage b)) := by
  have hw := memLp_two_comp_chart_symm (contDiffOn_quarterChart hb)
    (fun _ hq ↦ det_fderiv_quarterChart hb hq) hL
  apply hw.ae_eq
  filter_upwards [ae_restrict_mem (isOpen_quarterImage hb).measurableSet] with p hp
  change quarterInverseGradient H T j (levelCoord p, timeCoord p) /
    (saddleDist (dipoleOrbit (levelCoord p) (timeCoord p)) : ℂ) = _
  rw [dipoleOrbit_levelCoord_timeCoord hp.1.1]
  rfl

/-- Uniqueness identifies the reconstructed gradient with any given spatial weak
gradient on the overlap, even when the whole quarter image is not in its domain. -/
theorem quarterSpatialGradient_identification {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F H T D : ℝ × ℝ → ℂ} {j : Fin 2}
    (hD : HasWeakPartialOn U j F D)
    (hH : HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ F (dipoleOrbit q.1 q.2)) H)
    (hT : HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ F (dipoleOrbit q.1 q.2)) T) :
    ∀ᵐ p, p ∈ U ∩ quarterImage b → D p = quarterSpatialGradient H T j p :=
  (hD.mono inter_subset_left).ae_eq (hU.inter (isOpen_quarterImage hb))
    ((quarterSpatialGradient_weak hb hH hT j).mono inter_subset_right)

/-- Transfer the weighted bound to that same specified spatial derivative. -/
theorem memLp_div_saddleDist_of_quarter {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F H T D : ℝ × ℝ → ℂ} {j : Fin 2}
    (hD : HasWeakPartialOn U j F D)
    (hH : HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ F (dipoleOrbit q.1 q.2)) H)
    (hT : HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ F (dipoleOrbit q.1 q.2)) T)
    (hL : MemLp (fun q ↦ quarterInverseGradient H T j q /
      (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b))) :
    MemLp (fun p ↦ D p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ quarterImage b)) := by
  have hi : MemLp (fun p ↦ quarterSpatialGradient H T j p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ quarterImage b)) :=
    (memLp_quarterSpatialGradient hb j hL).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)
  apply hi.ae_eq
  have he := quarterSpatialGradient_identification hb hU hD hH hT
  filter_upwards [ae_restrict_mem (hU.inter (isOpen_quarterImage hb)).measurableSet,
    ae_restrict_of_ae he] with p hp heq
  rw [heq hp]

/-- The source-coordinate identification on a quarter wholly contained in a
spatial weak-gradient domain. This also controls exceptional representatives. -/
theorem quarterInverseGradient_identification {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F H T D : ℝ × ℝ → ℂ} {j : Fin 2}
    (hD : HasWeakPartialOn U j F D)
    (hH : HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ F (dipoleOrbit q.1 q.2)) H)
    (hT : HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ F (dipoleOrbit q.1 q.2)) T)
    (hsub : (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) '' quarterOrbitStrip b ⊆ U) :
    (fun q ↦ quarterInverseGradient H T j q) =ᵐ[volume.restrict (quarterOrbitStrip b)]
      (fun q ↦ D (dipoleOrbit q.1 q.2)) := by
  have hVU : quarterImage b ⊆ U := by
    change (quarterChart hb).target ⊆ U
    rw [← (quarterChart hb).image_source_eq_target]
    exact hsub
  have he := quarterSpatialGradient_identification hb hU hD hH hT
  have he' : D =ᵐ[volume.restrict (quarterImage b)] quarterSpatialGradient H T j := by
    filter_upwards [ae_restrict_of_ae he,
      ae_restrict_mem (isOpen_quarterImage hb).measurableSet] with p hp hpV
    exact hp ⟨hVU hpV, hpV⟩
  have hc := ae_eq_comp_chart (contDiffOn_quarterChart hb)
    (fun _ hq ↦ det_fderiv_quarterChart hb hq) he'
  filter_upwards [hc, ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq hqQ
  change D (dipoleOrbit q.1 q.2) =
    quarterInverseGradient H T j (levelCoord (dipoleOrbit q.1 q.2),
      timeCoord (dipoleOrbit q.1 q.2)) at hq
  rw [quarterCoordinates_dipoleOrbit hb hqQ] at hq
  exact hq.symm

end EulerDipoleEigenvalues
