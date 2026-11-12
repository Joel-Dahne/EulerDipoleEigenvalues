import NoEmbeddedEigenvalues.Regularity.OddOddCellH1
import NoEmbeddedEigenvalues.OddOddEdgeTraces
import NoEmbeddedEigenvalues.RectangleH1Gluing
import NoEmbeddedEigenvalues.DiagonalH1Inverse

/-!
# Canonical trace pairs on reflected-periodic odd–odd cell edges

Blueprint: `lem:dd-cell-edge-trace-pairs`, `lem:dd-cell-edge-h1`.

One ordinary positive-cell strip supplies both sides of every admissible
regular-edge window, with the same zero trace and all periodic translations.
The norms are finite on each bounded window, not on the full periodic lift.
Matching canonical traces give genuine weak gluing in the actual diagonal
coordinates, retaining zero as the full-window trace. Whole-lift spatial
covering and removal of the saddle points are separate from these local patches.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The original cell producer supplies actual matching traces on both sides of
all four regular edges, with one strip and every period index. -/
theorem dd_cell_edge_trace_pairs {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω) ∧
      ∀ (j : Fin 2) (side : Bool) (n : ℤ × ℤ) (l r a b : ℝ), l < r → a < b →
        Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
        (if side then b = cellEdgeNormal side else a = cellEdgeNormal side) →
        diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ cellSeparatrixStrip ε →
        let C := liftShift n ∘ diagonalTraceChart j
        MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) (liftL2 ω ∘ C) ∧
        HasTransverseH1Trace l r a b (cellEdgeNormal side) C (liftL2 ω) (fun _ ↦ 0) ∧
        MemSobolevOn 1
          (Ioo l r ×ˢ Ioo (2 * cellEdgeNormal side - b) (2 * cellEdgeNormal side - a))
          (liftL2 ω ∘ C) ∧
        HasTransverseH1Trace l r (2 * cellEdgeNormal side - b) (2 * cellEdgeNormal side - a)
          (cellEdgeNormal side) C (liftL2 ω) (fun _ ↦ 0) := by
  obtain ⟨_, ε, hε, hε1, hF, hT⟩ := dd_cell_separatrix_h1 hlam hω hs
  refine ⟨ε, hε, hε1, hF, ?_⟩
  intro j side n l r a b hlr hab hI hedge hsub
  have hS := (hF.comp_diagonalTraceChart (isOpen_cellSeparatrixStrip ε) j).mono
    (image_subset_iff.mp hsub)
  have hST := hT j side l r a b hlr hab hI hedge hsub
  obtain ⟨hR, hRT⟩ := (hT j side).oddOdd_reflected hs (isOpen_cellSeparatrixStrip ε)
    hF hlr hab hI hedge hsub
  have he : (liftL2 ω ∘ diagonalTraceChart j) =ᵐ[volume]
      (liftL2 ω ∘ (liftShift n ∘ diagonalTraceChart j)) :=
    Eventually.of_forall fun q ↦ (liftL2_liftShift ω n (diagonalTraceChart j q)).symm
  exact ⟨hS.congr_ae he, hST.liftShift n, hR.congr_ae he, hRT.liftShift n⟩

/-- The actual reflected-periodic cell data give H¹ across every admissible
regular-edge rectangle in diagonal coordinates, with the same zero trace. -/
theorem dd_cell_edge_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω) ∧
      ∀ (j : Fin 2) (side : Bool) (n : ℤ × ℤ) (l r a b : ℝ), l < r → a < b →
        Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
        (if side then b = cellEdgeNormal side else a = cellEdgeNormal side) →
        diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ cellSeparatrixStrip ε →
        let C := liftShift n ∘ diagonalTraceChart j
        let A := if side then a else 2 * cellEdgeNormal side - b
        let B := if side then 2 * cellEdgeNormal side - a else b
        MemSobolevOn 1 (Ioo l r ×ˢ Ioo A B) (liftL2 ω ∘ C) ∧
          HasTransverseH1Trace l r A B (cellEdgeNormal side) C (liftL2 ω) (fun _ ↦ 0) := by
  obtain ⟨ε, hε, hε1, hF, hpairs⟩ := dd_cell_edge_trace_pairs hlam hω hs
  refine ⟨ε, hε, hε1, hF, ?_⟩
  intro j side n l r a b hlr hab hI hedge hsub
  obtain ⟨hS, hST, hR, hRT⟩ := hpairs j side n l r a b hlr hab hI hedge hsub
  cases side
  · change a = cellEdgeNormal false at hedge
    subst a
    simp only [show 2 * cellEdgeNormal false - cellEdgeNormal false =
      cellEdgeNormal false by ring] at hR hRT
    exact hR.glue_matching_trace hS hRT hST
  · change b = cellEdgeNormal true at hedge
    subst b
    simp only [show 2 * cellEdgeNormal true - cellEdgeNormal true =
      cellEdgeNormal true by ring] at hR hRT
    exact hS.glue_matching_trace hR hST hRT

/-- The same glued patches have genuine Cartesian H¹ on their physical images.
The chart inverse transports the whole finite norms and both weak identities. -/
theorem dd_cell_edge_spatial_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω) ∧
      ∀ (j : Fin 2) (side : Bool) (n : ℤ × ℤ) (l r a b : ℝ), l < r → a < b →
        Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
        (if side then b = cellEdgeNormal side else a = cellEdgeNormal side) →
        diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ cellSeparatrixStrip ε →
        let C := liftShift n ∘ diagonalTraceChart j
        let A := if side then a else 2 * cellEdgeNormal side - b
        let B := if side then 2 * cellEdgeNormal side - a else b
        MemSobolevOn 1 (C '' (Ioo l r ×ˢ Ioo A B)) (liftL2 ω) ∧
          HasTransverseH1Trace l r A B (cellEdgeNormal side) C (liftL2 ω) (fun _ ↦ 0) := by
  obtain ⟨ε, hε, hε1, hF, hEdge⟩ := dd_cell_edge_h1 hlam hω hs
  refine ⟨ε, hε, hε1, hF, ?_⟩
  intro j side n l r a b hlr hab hI hedge hsub
  obtain ⟨hQ, hT⟩ := hEdge j side n l r a b hlr hab hI hedge hsub
  let A := if side then a else 2 * cellEdgeNormal side - b
  let B := if side then 2 * cellEdgeNormal side - a else b
  let Q := Ioo l r ×ˢ Ioo A B
  let G := liftL2 ω ∘ liftShift n
  have hd : MemSobolevOn 1 Q (G ∘ diagonalTraceChart j) := hQ
  have hP := hd.diagonalTraceChart_image (isOpen_Ioo.prod isOpen_Ioo)
  have ho := isOpenMap_diagonalTraceChart j Q (isOpen_Ioo.prod isOpen_Ioo)
  let E := cellFold false n
  have hE := hP.comp_planeAffine_symm (cellFoldLinear false) (cellFoldTranslation false n)
    (measurePreserving_cellFold false n) ho
  change MemSobolevOn 1 (E.symm ⁻¹' (diagonalTraceChart j '' Q)) (G ∘ E.symm) at hE
  rw [E.preimage_symm] at hE
  have he : (G ∘ E.symm) =ᵐ[volume] liftL2 ω := Eventually.of_forall fun p ↦ by
    change liftL2 ω (liftShift n (E.symm p)) = liftL2 ω p
    apply congrArg (liftL2 ω)
    simpa only [E, cellFold_apply, Bool.false_eq_true, ite_false] using E.apply_symm_apply p
  refine ⟨?_, hT⟩
  have hh := hE.congr_ae he
  simpa only [image_image, Function.comp_def, E, cellFold_apply, Bool.false_eq_true,
    ite_false] using hh

end NoEmbeddedEigenvalues
