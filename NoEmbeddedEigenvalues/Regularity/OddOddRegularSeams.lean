import NoEmbeddedEigenvalues.Regularity.OddOddEdgeTraces
import NoEmbeddedEigenvalues.Regularity.OddOddPuncturedH1
import NoEmbeddedEigenvalues.RegularEdgeCover
import NoEmbeddedEigenvalues.SaddlePointRemoval

/-!
# Ordinary odd–odd H¹ on the whole lifted collar

Blueprint: `lem:dd-regular-separatrix-h1`, `lem:dd-separatrix-vorticity-h1`.

Actual Cartesian edge patches cover every regular seam. Weak uniqueness off
that null seam identifies their gradients with the specified full-collar
finite-norm candidate. Isolated-point removal uses actual value and gradient
norms on whole punctured neighborhoods. No logarithmic forcing or weighted
vorticity gradient is used. Global canonical trace compatibility is separate.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The finite fold norm cover also applies to the raw vorticity itself. -/
theorem MemSobolevOn.oddOdd_collar_value {ω : L2} (hs : InSector false false ω)
    {ε : ℝ} (hF : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω)) :
    MemSobolevLocOn 0 {p | |dipoleLift p| < ε} (liftL2 ω) := by
  have hm : Measurable (liftL2 ω) :=
    (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have h : MemSobolevLocOn 0 (univ ∩ {p | |dipoleLift p| < ε}) (liftL2 ω) := by
    apply memSobolevLocOn_zero_of_cellFold_cover hm
    intro s n
    simpa only [univ_inter] using
      (hF.oddOdd_cellFold hs (isOpen_cellSeparatrixStrip ε) s n).1
  simpa only [univ_inter] using h

/-- Ordinary H¹ crosses every regular lifted seam, retaining the original
full-collar finite-norm gradient by weak uniqueness. Only saddles are excluded. -/
theorem dd_regular_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevLocOn 0 {p | |dipoleLift p| < ε} (liftL2 ω) ∧
      MemSobolevLocOn 1 ({p | |dipoleLift p| < ε} \ saddleSet) (liftL2 ω) ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        Measurable (D j) ∧
        HasWeakPartialOn ({p | |dipoleLift p| < ε} \ saddleSet) j (liftL2 ω) (D j) ∧
        MemSobolevLocOn 0 {p | |dipoleLift p| < ε} (D j) := by
  obtain ⟨ε, hε, hε1, hF, hEdge⟩ := dd_cell_edge_spatial_h1 hlam hω hs
  have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hC : IsOpen {p | |dipoleLift p| < ε} := isOpen_lt hc.abs continuous_const
  have hR := hC.inter isClosed_saddleSet.isOpen_compl
  have hN : IsOpen {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} :=
    (isClosed_eq hc continuous_const).isOpen_compl.inter hC
  have hSob : MemSobolevLocOn 1 ({p | |dipoleLift p| < ε} \ saddleSet) (liftL2 ω) := by
    apply memSobolevLocOn_of_locally
    intro p hp
    by_cases hz : dipoleLift p = 0
    · obtain ⟨j, side, n, l, r, a, b, hlr, hab, hI, hedge, hsub, hpQ⟩ :=
        exists_regular_edge_window hε hz hp.2
      have hS := (hEdge j side n l r a b hlr hab hI hedge hsub).1
      let A := if side then a else 2 * cellEdgeNormal side - b
      let B := if side then 2 * cellEdgeNormal side - a else b
      let Q := Ioo l r ×ˢ Ioo A B
      have hO : IsOpen ((liftShift n ∘ diagonalTraceChart j) '' Q) := by
        have h := (cellFold false n).isOpenMap _
          (isOpenMap_diagonalTraceChart j Q (isOpen_Ioo.prod isOpen_Ioo))
        simpa only [image_image, Function.comp_def, cellFold_apply, Bool.false_eq_true,
          ite_false] using h
      exact ⟨_, hO, hpQ, hS.memSobolevLocOn⟩
    · exact ⟨_, hN, ⟨hz, hp.1⟩, hF.oddOdd_punctured_collar hs⟩
  obtain ⟨D, hD⟩ := hF.oddOdd_collar_gradient hs
  obtain ⟨E, hE⟩ := hSob.exists_weakGradient hR
  refine ⟨ε, hε, hε1, hF.oddOdd_collar_value hs, hSob, D, fun j ↦
    ⟨(hD j).1, ?_, (hD j).2.2⟩⟩
  have he := ((hE j).1.mono inter_subset_right).ae_eq (hN.inter hR)
    ((hD j).2.1.mono inter_subset_left)
  have heD : ∀ᵐ p, p ∈ ({p | |dipoleLift p| < ε} \ saddleSet) → E j p = D j p := by
    filter_upwards [he, ae_dipoleLift_ne_zero] with p hp hnz hpR
    exact hp ⟨⟨hnz, hpR.1⟩, hpR⟩
  exact (hE j).1.congr_ae_on hR.measurableSet
    (Eventually.of_forall fun _ _ ↦ rfl) heD

/-- Ordinary vorticity H¹ holds on one full absolute-level collar, including
all regular seams and every lifted saddle. No trace conclusion is asserted here. -/
theorem dd_separatrix_vorticity_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevLocOn 1 {p | |dipoleLift p| < ε} (liftL2 ω) := by
  obtain ⟨ε, hε, hε1, hF, _, D, hD⟩ := dd_regular_separatrix_h1 hlam hω hs
  have hC : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  exact ⟨ε, hε, hε1, memSobolevLocOn_of_weakGradient_off_saddleSet hC hF
    (fun j ↦ ⟨(hD j).2.1, (hD j).2.2⟩)⟩

end NoEmbeddedEigenvalues
