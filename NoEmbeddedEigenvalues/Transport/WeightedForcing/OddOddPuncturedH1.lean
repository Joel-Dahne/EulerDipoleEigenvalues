module

public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddCellH1
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.PeriodicWeightedGradient
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SobolevGluing
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakDerivativeGluing

/-!
# Ordinary H¹ on reflected periodic open cell strips

Blueprint: `lem:odd-odd-h1-cell-fold`, `lem:odd-odd-collar-gradient`,
`lem:dd-punctured-separatrix-h1`.

Affine Sobolev pullback and raw a.e. parity give ordinary H¹ on each fold of
one positive-cell strip. These open strips cover every small nonzero level.
Weak uniqueness identifies one measurable gradient on every folded strip.
Finite covers give actual local L² for that gradient through the omitted seams.
The weak identities are asserted only off the separatrix, not across it.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Reflected periodic pullback retains the same raw lift for first-odd sectors. -/
theorem MemSobolevOn.oddOdd_cellFold {ω : L2} {b : Bool}
    (hs : InSector false b ω)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hF : MemSobolevOn 1 V (liftL2 ω))
    (s : Bool) (n : ℤ × ℤ) :
    MemSobolevOn 1 (cellFold s n ⁻¹' V) (liftL2 ω) := by
  have h := hF.comp_planeAffine (cellFoldLinear s) (cellFoldTranslation s n)
    (measurePreserving_cellFold s n) hV
  apply MemSobolevOn.congr_ae (h.const_mul (if s then -1 else 1 : ℂ))
  filter_upwards [liftL2_cellFold_ae hs s n] with p hp
  change (if s then -1 else 1 : ℂ) * liftL2 ω (cellFold s n p) = liftL2 ω p
  change liftL2 ω (cellFold s n p) = (if s then -1 else 1 : ℂ) * liftL2 ω p at hp
  rw [hp]
  cases s <;> simp

/-- An ordinary positive-cell strip covers the small-level lift only away from
its null seams. No assertion of across-seam weak derivatives is made. -/
theorem MemSobolevOn.oddOdd_punctured_collar {ω : L2} {b : Bool}
    (hs : InSector false b ω)
    {ε : ℝ} (hF : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω)) :
    MemSobolevLocOn 1 {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} (liftL2 ω) := by
  apply memSobolevLocOn_of_locally
  intro p hp
  obtain ⟨s, n, hn⟩ := exists_cellFold_mem_collar hp.1 hp.2
  exact ⟨cellFold s n ⁻¹' cellSeparatrixStrip ε,
    (isOpen_cellSeparatrixStrip ε).preimage (cellFold s n).continuous,
    hn, (hF.oddOdd_cellFold hs (isOpen_cellSeparatrixStrip ε) s n).memSobolevLocOn⟩

/-- A single measurable off-separatrix gradient has finite local L² norms on
the full collar. These norm bounds do not assert across-seam weak identities. -/
theorem MemSobolevOn.oddOdd_collar_gradient {ω : L2} {b : Bool}
    (hs : InSector false b ω)
    {ε : ℝ} (hF : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω)) :
    ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      Measurable (D j) ∧
      HasWeakPartialOn {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} j (liftL2 ω) (D j) ∧
      MemSobolevLocOn 0 {p | |dipoleLift p| < ε} (D j) := by
  have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have ho : IsOpen {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} :=
    (isClosed_eq hc continuous_const).isOpen_compl.inter
      (isOpen_lt hc.abs continuous_const)
  obtain ⟨D, hD⟩ := (hF.oddOdd_punctured_collar hs).exists_measurable_weakGradient ho
  refine ⟨D, fun j ↦ ⟨(hD j).1, (hD j).2.1, ?_⟩⟩
  have hL : MemSobolevLocOn 0 (univ ∩ {p | |dipoleLift p| < ε}) (D j) := by
    apply memSobolevLocOn_zero_of_cellFold_cover (hD j).1
    intro s n
    have hV : IsOpen (cellFold s n ⁻¹' cellSeparatrixStrip ε) :=
      (isOpen_cellSeparatrixStrip ε).preimage (cellFold s n).continuous
    obtain ⟨E, hE, hEL⟩ :=
      (hF.oddOdd_cellFold hs (isOpen_cellSeparatrixStrip ε) s n).2 j
    have he := ((hD j).2.1.mono (cellFold_preimage_strip_subset s n ε)).ae_eq hV hE
    have hED : MemLp (D j) 2
        (volume.restrict (cellFold s n ⁻¹' cellSeparatrixStrip ε)) := by
      apply (show MemLp E 2
        (volume.restrict (cellFold s n ⁻¹' cellSeparatrixStrip ε)) from hEL).ae_eq
      filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hV.measurableSet] with p hp hpV
      exact (hp hpV).symm
    exact hED.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  simpa only [univ_inter] using hL

/-- The ordinary small-level gain before crossing the reflected-cell seams,
with a specified gradient whose actual L² norms extend locally through them. -/
theorem dd_punctured_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      MemSobolevLocOn 1 {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} (liftL2 ω) ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        Measurable (D j) ∧
        HasWeakPartialOn {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} j (liftL2 ω) (D j) ∧
        MemSobolevLocOn 0 {p | |dipoleLift p| < ε} (D j) := by
  obtain ⟨_, ε, hε, hε1, hF, _⟩ := dd_cell_separatrix_h1 hlam hω hs
  exact ⟨ε, hε, hε1, hF.oddOdd_punctured_collar hs, hF.oddOdd_collar_gradient hs⟩

end NoEmbeddedEigenvalues
