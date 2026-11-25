module

public import EulerDipoleEigenvalues.Regularity.SaddleEstimates.OddOddSaddle
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.StreamJet

/-!
# Cellwise ordinary H¹ and zero edge traces

Blueprint: `lem:dd-cell-separatrix-h1`.

The weighted forcing input supplies the weak transport theorem with the actual
continuous stream and its Fourier first derivatives. Its second mass gain also
implies the first mass gain on the bounded cell. Zero stream values on a whole
edge then give the canonical one-sided zero trace of the same raw vorticity.
No logarithmic forcing, rotation character or across-edge H¹ is used.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

private theorem dipole_diagonal_trace (j : Fin 2) (s t : ℝ) :
    dipoleLift (diagonalTraceChart j (s, t)) = 2 * Real.cos s * Real.cos t := by
  have he : diagCoord (diagonalTraceChart j (s, t)) =
      if j = 0 then (t, s) else (s, t) := by
    fin_cases j <;> ext <;> simp [diagonalTraceChart, diagCoord]
  rw [dipoleLift_eq_diag, he]
  split_ifs <;> simp only [mul_right_comm]

/-- The positive cell has one ordinary H¹ strip and zero canonical traces on all
four edges, with the second vorticity mass gain on the whole cell. -/
theorem dd_cell_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    MemLp (fun p ↦ liftL2 ω p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω) ∧
      ∀ (j : Fin 2) (positive : Bool),
        HasCellEdgeTrace (cellSeparatrixStrip ε) j positive (liftL2 ω) (fun _ ↦ 0) := by
  have hp := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hf := dd_weighted_forcing hlam hω hs
  have hcell : cellSquare ⊆ cellNeighbourhood :=
    subset_closure.trans closure_cellSquare_subset_cellNeighbourhood
  have hD (j : Fin 2) : HasWeakPartialOn cellNeighbourhood j (contStream ω)
      (liftL2 (streamPartial j ω)) :=
    (streamJet2_weak ω cellNeighbourhood).2 [] (by simp) j
  obtain ⟨hmass, r, hr, hrhalf, hH1, _⟩ := weighted_transport_h1 hp
    isBounded_cellNeighbourhood closure_cellSquare_subset_cellNeighbourhood hD
    (hf.1.mono_measure (Measure.restrict_mono hcell le_rfl))
    (fun j ↦ (hf.2.1 j).mono_measure (Measure.restrict_mono hcell le_rfl))
  have ho : IsOpen cellSquare := by
    exact (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) by
      unfold diagCoord; fun_prop) continuous_const).inter
      (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) by
        unfold diagCoord; fun_prop) continuous_const)
  have hcompact : IsCompact (closure cellSquare) :=
    (isBounded_cellNeighbourhood.subset hcell).isCompact_closure
  have hd : Continuous (fun p : ℝ × ℝ ↦ (saddleDist p : ℂ)) :=
    Complex.continuous_ofReal.comp (Metric.continuous_infDist_pt saddleSet)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hd.continuousOn
  have hdtop : MemLp (fun p ↦ (saddleDist p : ℂ)) ⊤ (volume.restrict cellSquare) := by
    apply memLp_top_of_bound hd.measurable.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem ho.measurableSet] with p hp
    exact hC p (subset_closure hp)
  have hfirst : MemLp (fun p ↦ liftL2 ω p / (saddleDist p : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply (hdtop.mul hmass).ae_eq
    exact Eventually.of_forall fun p ↦ by
      simp only [Pi.mul_apply]
      by_cases hz : (saddleDist p : ℂ) = 0
      · simp [hz]
      · field_simp
  have hε : 0 < 2 * r := mul_pos (by norm_num) hr
  refine ⟨hmass, 2 * r, hε, by linarith, hH1, fun j side ↦ ?_⟩
  have hsub : cellSeparatrixStrip (2 * r) ⊆ cellSquare := fun _ hp ↦ hp.1
  apply transport_zero_edge_trace hp closure_cellSquare_subset_cellNeighbourhood hε hH1
    (hfirst.mono_measure (Measure.restrict_mono hsub le_rfl))
    (continuous_contStream ω).continuousOn (Eventually.of_forall fun _ ↦ rfl) j side
  intro s _
  apply hf.2.2
  rw [dipole_diagonal_trace]
  cases side <;> simp [cellEdgeNormal, neg_div]

end EulerDipoleEigenvalues
