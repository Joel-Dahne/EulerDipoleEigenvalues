import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterCellCover
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SmoothChartTests
import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitNumerators
import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.LevelTraces

/-!
# Physical-area mass from a quarter character

Blueprint: `lem:quarter-l2-pushforward`, `lem:collar-rotation-character`,
`lem:quarter-character-cell-mass`, `lem:cell-interior-mass`.

Constant-Jacobian transport gives the mass on the actual quarter image.
Restricted measure-preserving rotations propagate a raw character identity
and its norm to the other quarters. Their finite cover omits only null axes.
No global measurability of the original spatial function is assumed.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Raw square integrability descends from the moving quarter to physical area. -/
theorem memLp_of_comp_quarterOrbitStrip {b : ℝ} (hb : b ≤ 1)
    {F : ℝ × ℝ → ℂ}
    (hF : MemLp (fun q ↦ F (dipoleOrbit q.1 q.2)) 2
      (volume.restrict (quarterOrbitStrip b))) :
    MemLp F 2 (volume.restrict (quarterImage b)) := by
  have hi := memLp_two_comp_chart_symm (contDiffOn_quarterChart hb)
    (fun _ hq ↦ det_fderiv_quarterChart hb hq) hF
  apply hi.ae_eq
  filter_upwards [ae_restrict_mem (isOpen_quarterImage hb).measurableSet] with p hp
  change F (dipoleOrbit (levelCoord p) (timeCoord p)) = F p
  rw [dipoleOrbit_levelCoord_timeCoord hp.1.1]

/-- Rotation preserves the entire positive cell collar. -/
theorem preimage_rotLift_cellSeparatrixStrip (ε : ℝ) :
    rotLift ⁻¹' cellSeparatrixStrip ε = cellSeparatrixStrip ε := by
  ext p
  simp only [mem_preimage, cellSeparatrixStrip, mem_ofPred_eq, (rotLift_cell_level p).1]
  have he : dipoleLift (rotLift p) = dipoleLift p := by
    simp [dipoleLift, rotLift, Real.cos_neg, add_comm]
  rw [he]

/-- The physical collar uses stream level Ψ = 2h; below level one it excludes
also the cell center, exactly as the orbit annulus does. -/
theorem cellSeparatrixStrip_eq_orbitAnnulus {b : ℝ} (hb : b ≤ 1) :
    cellSeparatrixStrip (2 * b) = orbitAnnulus 0 b := by
  ext p
  constructor
  · intro hp
    have hn : p ≠ 0 := by
      intro hz
      have ht := hp.2.2
      rw [hz] at ht
      norm_num [dipoleLift] at ht
      linarith
    refine ⟨⟨hp.1, hn⟩, ?_⟩
    change 0 < dipoleLift p / 2 ∧ dipoleLift p / 2 < b
    constructor <;> linarith [hp.2.1, hp.2.2]
  · intro hp
    have hh := hp.2
    change 0 < dipoleLift p / 2 ∧ dipoleLift p / 2 < b at hh
    refine ⟨hp.1.1, ?_⟩
    constructor <;> linarith [hh.1, hh.2]

/-- Iteration of a character on a rotation-invariant collar is an a.e. identity
on that same restricted measure, with no assumptions outside the collar. -/
theorem HasQuarterCharacterOn.iterate_cell_collar {ε : ℝ} {κ : ℂ}
    {F : ℝ × ℝ → ℂ} (hchar : HasQuarterCharacterOn κ (cellSeparatrixStrip ε) F)
    (k : ℕ) :
    ∀ᵐ p ∂(volume.restrict (cellSeparatrixStrip ε)),
      F (rotLift^[k] p) = κ ^ k * F p := by
  have hmp : MeasurePreserving rotLift
      (volume.restrict (cellSeparatrixStrip ε)) (volume.restrict (cellSeparatrixStrip ε)) := by
    simpa only [preimage_rotLift_cellSeparatrixStrip] using
      measurePreserving_rotLift.restrict_preimage (isOpen_cellSeparatrixStrip ε).measurableSet
  induction k with
  | zero => exact Eventually.of_forall fun p ↦ by simp
  | succ k ih =>
    filter_upwards [hmp.quasiMeasurePreserving.ae ih, hchar] with p hp hc
    rw [Function.iterate_succ_apply, hp, hc, pow_succ]
    ring

/-- A raw nonzero quarter character with base-quarter mass has physical-area
mass on the full collar. Only the collar character, not a global one, is used. -/
theorem memLp_cell_collar_of_quarter_character {b : ℝ} (hb : b ≤ 1)
    {κ : ℂ} (hκ : κ ≠ 0) {F : ℝ × ℝ → ℂ}
    (hchar : HasQuarterCharacterOn κ (cellSeparatrixStrip (2 * b)) F)
    (hF : MemLp (fun q ↦ F (dipoleOrbit q.1 q.2)) 2
      (volume.restrict (quarterOrbitStrip b))) :
    MemLp F 2 (volume.restrict (cellSeparatrixStrip (2 * b))) := by
  have hi := memLp_of_comp_quarterOrbitStrip hb hF
  let A := cellSeparatrixStrip (2 * b)
  let V := fun k : Fin 4 ↦ A ∩ (rotLift^[k.val] ⁻¹' quarterImage b)
  have hL (k : Fin 4) : MemLp F 2 (volume.restrict (V k)) := by
    have hm := (measurePreserving_rotLift.iterate k.val).restrict_preimage
      (isOpen_quarterImage hb).measurableSet
    have hr := hi.comp_measurePreserving hm
    have hs : V k ⊆ rotLift^[k.val] ⁻¹' quarterImage b := inter_subset_right
    have hl := (hr.mono_measure (Measure.restrict_mono_set _ hs)).const_mul (κ ^ k.val)⁻¹
    apply hl.ae_eq
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (show V k ⊆ A from inter_subset_left)
      (hchar.iterate_cell_collar k.val)] with p hp
    change (κ ^ k.val)⁻¹ * F (rotLift^[k.val] p) = F p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hκ), one_mul]
  have hm : AEStronglyMeasurable F (volume.restrict (⋃ k, V k)) :=
    AEStronglyMeasurable.iUnion (fun k ↦ (hL k).aestronglyMeasurable)
  have hu : MemLp F 2 (volume.restrict (⋃ k, V k)) :=
    (memLp_two_iff_integrable_sq_norm hm).2
      (integrableOn_finite_iUnion.mpr fun k ↦ (hL k).integrable_norm_pow (by norm_num))
  apply hu.mono_measure (Measure.restrict_mono_ae ?_)
  filter_upwards [ae_cell_collar_covered hb] with p hp hpA
  obtain ⟨k, hk⟩ := hp hpA
  exact mem_iUnion.mpr ⟨k, hpA, hk⟩

/-- The stream level supplies a lower distance bound everywhere inside the cell. -/
theorem levelCoord_le_saddleDist {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    levelCoord p ≤ saddleDist p := by
  have hc : 0 ≤ Real.cos (diagCoord p).1 :=
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1)).le
  have he : levelCoord p = Real.cos (diagCoord p).1 * Real.cos (diagCoord p).2 := by
    rw [levelCoord, dipoleLift_eq_diag]
    ring
  rw [he]
  exact (mul_le_of_le_one_right hc (Real.cos_le_one _)).trans (cos_diag_fst_le_saddleDist p)

/-- A first weighted mass norm on one positive collar extends to the cell:
outside the collar, the positive stream level bounds the distance below. -/
theorem memLp_div_saddleDist_of_cell_collar {b : ℝ} (hb : 0 < b)
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict cellSquare))
    (hw : MemLp (fun p ↦ F p / (saddleDist p : ℂ)) 2
      (volume.restrict (cellSeparatrixStrip (2 * b)))) :
    MemLp (fun p ↦ F p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare) := by
  let W := fun p ↦ F p / (saddleDist p : ℂ)
  have hm : AEStronglyMeasurable W (volume.restrict cellSquare) :=
    hF.aestronglyMeasurable.div₀
      (Complex.continuous_ofReal.comp (Metric.continuous_infDist_pt saddleSet)).aestronglyMeasurable
  have hsub : cellSquare \ cellSeparatrixStrip (2 * b) ⊆ cellSquare := sdiff_subset
  have hi := hF.mono_measure (Measure.restrict_mono_set _ hsub)
  have hout : MemLp W 2 (volume.restrict (cellSquare \ cellSeparatrixStrip (2 * b))) := by
    apply hi.of_le_mul (c := b⁻¹) (hm.mono_measure (Measure.restrict_mono_set _ hsub))
    filter_upwards [ae_restrict_mem
      (isOpen_cellSquare.measurableSet.diff (isOpen_cellSeparatrixStrip _).measurableSet)]
      with p hp
    have hpos : 0 < dipoleLift p := by
      rw [dipoleLift_eq_diag]
      exact mul_pos (mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1.1)))
        (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1.2))
    have hlevel : b ≤ levelCoord p := by
      have hn : ¬dipoleLift p < 2 * b := fun ht ↦ hp.2 ⟨hp.1, hpos, ht⟩
      dsimp only [levelCoord]
      linarith [not_lt.mp hn]
    have hd := hlevel.trans (levelCoord_le_saddleDist hp.1)
    have hd0 : 0 < saddleDist p := hb.trans_le hd
    dsimp only [W]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    calc ‖F p‖ / saddleDist p ≤ ‖F p‖ / b :=
          div_le_div_of_nonneg_left (norm_nonneg _) hb hd
         _ = b⁻¹ * ‖F p‖ := by ring
  have hi₁ : IntegrableOn (fun p ↦ ‖W p‖ ^ 2) (cellSeparatrixStrip (2 * b)) :=
    hw.integrable_norm_pow (by norm_num)
  have hi₂ : IntegrableOn (fun p ↦ ‖W p‖ ^ 2) (cellSquare \ cellSeparatrixStrip (2 * b)) :=
    hout.integrable_norm_pow (by norm_num)
  have hu : MemLp W 2 (volume.restrict
      (cellSeparatrixStrip (2 * b) ∪ (cellSquare \ cellSeparatrixStrip (2 * b)))) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_union_iff.2
      ⟨hw.aestronglyMeasurable, hout.aestronglyMeasurable⟩)).2 (hi₁.union hi₂)
  apply hu.mono_measure (Measure.restrict_mono_set _ ?_)
  intro p hp
  by_cases h : p ∈ cellSeparatrixStrip (2 * b)
  · exact Or.inl h
  · exact Or.inr ⟨hp, h⟩

end NoEmbeddedEigenvalues
