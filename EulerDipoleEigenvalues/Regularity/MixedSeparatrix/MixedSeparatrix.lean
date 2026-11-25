module

public import EulerDipoleEigenvalues.Regularity.MixedSeparatrix.MixedCellH1
public import EulerDipoleEigenvalues.Regularity.OddOddSeparatrix.OddOddRegularSeams
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.StreamElliptic
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.BoundaryTraceCompare

/-! # Mixed Sobolev regularity through the separatrix

Odd sides glue by their zero traces; even sides glue because reflection
preserves the canonical trace. Periodic covering and saddle removability
then give the full collar without any quotient assumptions.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

private theorem mixed_cell_edge_window_h1 {ω : L2} (hs : InSector false true ω)
    {ε : ℝ} (hF : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω))
    (hzero : ∀ side, HasCellEdgeTrace (cellSeparatrixStrip ε) 0 side
      (liftL2 ω) (fun _ ↦ 0))
    (j : Fin 2) (side : Bool) {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    (hI : Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2))
    (hedge : if side then b = cellEdgeNormal side else a = cellEdgeNormal side)
    (hsub : diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ cellSeparatrixStrip ε) :
    let A := if side then a else 2 * cellEdgeNormal side - b
    let B := if side then 2 * cellEdgeNormal side - a else b
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo A B) (liftL2 ω ∘ diagonalTraceChart j) := by
  have hS := (hF.comp_diagonalTraceChart (isOpen_cellSeparatrixStrip ε) j).mono
    (image_subset_iff.mp hsub)
  let t := cellEdgeNormal side
  have ht : t ∈ Icc a b := by
    cases side
    · change a = t at hedge
      exact ⟨hedge.le, hedge.symm.le.trans hab.le⟩
    · change b = t at hedge
      exact ⟨hab.le.trans hedge.le, hedge.symm.le⟩
  have htr : ∃ T : ℝ → ℂ,
      HasTransverseH1Trace l r a b t (diagonalTraceChart j) (liftL2 ω) T ∧
        (fun s ↦ paritySign (if j = 0 then false else true) * T s) = T := by
    by_cases hj : j = 0
    · subst j
      exact ⟨_, hzero side l r a b hlr hab hI hedge hsub, funext fun _ ↦ mul_zero _⟩
    · obtain ⟨D, hd, hD⟩ := hS.2 1
      obtain ⟨T, hT⟩ := hd.exists_transverse_trace hlr hab ht hS.1 hD
      exact ⟨T, hT, by simp [hj, paritySign]⟩
  obtain ⟨T, hST, hT⟩ := htr
  obtain ⟨hR, hRT⟩ := hST.reflected_sector hs hS
  rw [hT] at hRT
  cases side
  · change a = cellEdgeNormal false at hedge
    subst a
    simp only [show 2 * cellEdgeNormal false - cellEdgeNormal false =
      cellEdgeNormal false by ring] at hR hRT
    exact (hR.glue_matching_trace hS hRT hST).1
  · change b = cellEdgeNormal true at hedge
    subst b
    simp only [show 2 * cellEdgeNormal true - cellEdgeNormal true =
      cellEdgeNormal true by ring] at hR hRT
    exact (hS.glue_matching_trace hR hST hRT).1

/-- Mixed vorticity has ordinary H¹ on a full absolute-level collar, and
the same collar has H³ stream and zero inward vorticity traces on odd sides. -/
theorem mixed_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevLocOn 1 {p | |dipoleLift p| < ε} (liftL2 ω) ∧
      MemSobolevLocOn 3 {p | |dipoleLift p| < ε} (contStream ω) ∧
      ∀ side, HasCellEdgeTrace (cellSeparatrixStrip ε) 0 side (liftL2 ω) (fun _ ↦ 0) := by
  obtain ⟨ε, hε, hε1, hF, hzero⟩ := mixed_cell_separatrix_h1 hlam hω hs
  have hV := cell_separatrix_h1_of_regular_edges hs hε hF (by
    intro j side n l r a b hlr hab hI hedge hsub
    let A := if side then a else 2 * cellEdgeNormal side - b
    let B := if side then 2 * cellEdgeNormal side - a else b
    let Q := Ioo l r ×ˢ Ioo A B
    let G := liftL2 ω ∘ liftShift n
    have hQ := mixed_cell_edge_window_h1 hs hF hzero j side hlr hab hI hedge hsub
    have hd : MemSobolevOn 1 Q (G ∘ diagonalTraceChart j) := hQ.congr_ae
      (Eventually.of_forall fun q ↦ (liftL2_liftShift ω n (diagonalTraceChart j q)).symm)
    exact hd.liftShift_diagonalTraceChart_image (isOpen_Ioo.prod isOpen_Ioo) j n)
  have hC : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  exact ⟨ε, hε, hε1, hV, stream_h3_of_vorticity_h1 hω.1 hC hV, hzero⟩

end EulerDipoleEigenvalues
