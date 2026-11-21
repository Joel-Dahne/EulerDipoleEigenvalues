module

public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddGradientCoordinates
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.RotationWeakGradient

/-!
# Weighted Cartesian gradients on a full positive cell collar

Blueprint: `lem:dd-cell-weighted-gradient`.

Rotate the actual base-quarter spatial derivative, identify each reconstructed
partial with one ordinary separatrix gradient, and cover the collar up to the
null Cartesian seams. Compactness shrinks the collar inside that gradient's
domain. Summing the two rotation characters removes the character premise.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A character has a weighted weak gradient on an entire positive cell collar. -/
theorem dd_character_cell_weighted_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (cellSeparatrixStrip (2 * b)) j (liftL2 ω) (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellSeparatrixStrip (2 * b))) := by
  obtain ⟨U, hU, hsep, D, hD⟩ := dd_separatrix_weak_gradient hlam hω hs
  obtain ⟨b₀, hb₀, hbhalf, E, hE⟩ :=
    dd_character_base_quarter_spatial_gradient hlam hω hs hκ
  obtain ⟨ε, hε, hεU⟩ := exists_cell_collar_subset hU hsep
  let b := min b₀ (ε / 2)
  have hbb : b ≤ b₀ := min_le_left _ _
  have hbε : b ≤ ε / 2 := min_le_right _ _
  have hb1 : b ≤ 1 := by linarith only [hbb, hbhalf]
  have hQU : quarterImage b ⊆ quarterImage b₀ :=
    fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.1.trans_le hbb, hp.2.2.2⟩
  have hCU : cellSeparatrixStrip (2 * b) ⊆ U := by
    intro p hp
    apply hεU
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le (by linarith only [hbε])⟩
  have he : ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (quarterImage b) j (liftL2 ω) (E j) ∧
      MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2 (volume.restrict (quarterImage b)) :=
    ⟨E, fun j ↦ ⟨(hE j).1.mono hQU,
      (hE j).2.mono_measure (Measure.restrict_mono hQU le_rfl)⟩⟩
  have ha : paritySign κ ≠ 0 := by cases κ <;> norm_num [paritySign]
  refine ⟨b, lt_min hb₀ (half_pos hε), hbb.trans_lt hbhalf, D, fun j ↦
    ⟨(hD j).2.1.mono hCU, ?_⟩⟩
  have hL := memLp_weighted_gradient_cell_collar hb1 hU (fun i ↦ (hD i).1)
    (fun i ↦ (hD i).2.1) he ha (liftL2_rotLift_ae hκ) j
  simpa only [inter_eq_right.mpr hCU] using hL

/-- The full odd--odd eigenfunction has a weighted weak gradient on one whole
positive cell collar; the two projected raw lifts are summed only a.e. -/
theorem dd_cell_weighted_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (cellSeparatrixStrip (2 * b)) j (liftL2 ω) (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellSeparatrixStrip (2 * b))) := by
  obtain ⟨bp, hposp, hhalf, Dp, hDp⟩ := dd_character_cell_weighted_gradient hlam
    (hω.rotationProjection true) (hs.rotationProjection_mem true)
    (hs.rotationProjection_character true)
  obtain ⟨bm, hposm, _, Dm, hDm⟩ := dd_character_cell_weighted_gradient hlam
    (hω.rotationProjection false) (hs.rotationProjection_mem false)
    (hs.rotationProjection_character false)
  let b := min bp bm
  have hbp : b ≤ bp := min_le_left _ _
  have hbm : b ≤ bm := min_le_right _ _
  have hsub {c : ℝ} (hc : b ≤ c) : cellSeparatrixStrip (2 * b) ⊆
      cellSeparatrixStrip (2 * c) :=
    fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.trans_le (by linarith only [hc])⟩
  have he := liftL2_add_ae (rotationProjection true ω) (rotationProjection false ω)
  rw [rotationProjection_sum] at he
  refine ⟨b, lt_min hposp hposm, hbp.trans_lt hhalf,
    fun j p ↦ Dp j p + Dm j p, fun j ↦ ⟨?_, ?_⟩⟩
  · exact (((hDp j).1.mono (hsub hbp)).add
      ((hDm j).1.mono (hsub hbm))).congr_left he.symm
  · have hp : MemLp (fun p ↦ Dp j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellSeparatrixStrip (2 * b))) :=
      (hDp j).2.mono_measure (Measure.restrict_mono (hsub hbp) le_rfl)
    have hm : MemLp (fun p ↦ Dm j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellSeparatrixStrip (2 * b))) :=
      (hDm j).2.mono_measure (Measure.restrict_mono (hsub hbm) le_rfl)
    convert hp.add hm using 1
    funext p
    exact add_div _ _ _

end NoEmbeddedEigenvalues
