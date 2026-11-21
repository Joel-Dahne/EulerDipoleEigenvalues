module

public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddQuarterTime
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterInverseFrame
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterGradient
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakDerivativeGluing

/-!
# Specified separatrix gradient and inverse-frame data

Blueprint: `lem:dd-separatrix-weak-gradient`, `lem:dd-base-quarter-inverse-frame`,
`lem:dd-base-quarter-spatial-gradient`, `lem:dd-weighted-gradient-base-overlap`.

The ordinary separatrix H¹ input supplies one weak gradient on the whole
neighbourhood. The strong base-quarter estimates and the cofactor chain rule
reconstruct weighted spatial derivatives on the quarter image. Weak uniqueness
transfers this weight to the same specified ordinary gradient on the overlap.
Character decomposition removes the auxiliary rotation-character premise.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Extract a single specified weak gradient from ordinary local H¹ regularity. -/
theorem dd_separatrix_weak_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        Measurable (D j) ∧ HasWeakPartialOn U j (liftL2 ω) (D j) ∧
          MemSobolevLocOn 0 U (D j) := by
  obtain ⟨U, hU, hsep, hH, _, _⟩ := dd_separatrix_h1 hlam hω hs
  obtain ⟨D, hD⟩ := hH.exists_measurable_weakGradient hU
  exact ⟨U, hU, hsep, D, hD⟩

/-- Retain the actual weak quarter derivatives on a common smaller strip and
construct the two weighted Cartesian inverse-frame candidates. -/
theorem dd_base_quarter_inverse_frame {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ H T : ℝ × ℝ → ℂ,
      HasWeakPartialOn (quarterOrbitStrip b) 0
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) H ∧
      HasWeakPartialOn (quarterOrbitStrip b) 1
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) T ∧
      MemLp H 2 (volume.restrict (quarterOrbitStrip b)) ∧
      MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) ∧
      ∀ j : Fin 2, MemLp (fun q ↦ quarterInverseGradient H T j q /
        (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
          (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨h₀, hh₀, hhhalf, H, T, hH, hT, hHl, hTl⟩ :=
    dd_base_quarter_weighted_derivatives hlam hω hs hκ
  obtain ⟨δ, hδ, _, hInv⟩ := quarterInverseGradient_memLp
  let b := min h₀ δ
  have hb : 0 < b := lt_min hh₀ hδ
  have hbh : b ≤ h₀ := min_le_left _ _
  have hbδ : b ≤ δ := min_le_right _ _
  have hsub : quarterOrbitStrip b ⊆ quarterOrbitStrip h₀ :=
    fun _ hq ↦ ⟨hq.1, hq.2.1.trans_le hbh, hq.2.2⟩
  have hHl' := hHl.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hTl' := hTl.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact ⟨b, hb, hbh.trans_lt hhhalf, H, T, hH.mono hsub, hT.mono hsub,
    hHl', hTl', hInv b hbδ H T hHl' hTl'⟩

/-- Weighted spatial derivatives on the base-quarter image for a character. -/
theorem dd_character_base_quarter_spatial_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (quarterImage b) j (liftL2 ω) (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2 (volume.restrict (quarterImage b)) := by
  obtain ⟨b, hb, hbhalf, H, T, hH, hT, _, _, hL⟩ :=
    dd_base_quarter_inverse_frame hlam hω hs hκ
  have hb1 : b ≤ 1 := by linarith
  exact ⟨b, hb, hbhalf, quarterSpatialGradient H T, fun j ↦
    ⟨quarterSpatialGradient_weak hb1 hH hT j, memLp_quarterSpatialGradient hb1 j (hL j)⟩⟩

/-- Remove the character premise by summing the two actual projected raw lifts. -/
theorem dd_base_quarter_spatial_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (quarterImage b) j (liftL2 ω) (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2 (volume.restrict (quarterImage b)) := by
  obtain ⟨bp, hposp, hbphalf, Dp, hDp⟩ := dd_character_base_quarter_spatial_gradient hlam
    (hω.rotationProjection true) (hs.rotationProjection_mem true)
    (hs.rotationProjection_character true)
  obtain ⟨bm, hposm, hbmhalf, Dm, hDm⟩ := dd_character_base_quarter_spatial_gradient hlam
    (hω.rotationProjection false) (hs.rotationProjection_mem false)
    (hs.rotationProjection_character false)
  let b := min bp bm
  have hbp : b ≤ bp := min_le_left _ _
  have hbm : b ≤ bm := min_le_right _ _
  have hsub {c : ℝ} (hc : b ≤ c) : quarterImage b ⊆ quarterImage c := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.trans_le hc, hp.2.2.2⟩
  have he := liftL2_add_ae (rotationProjection true ω) (rotationProjection false ω)
  rw [rotationProjection_sum] at he
  refine ⟨b, lt_min hposp hposm, hbp.trans_lt hbphalf,
    fun j p ↦ Dp j p + Dm j p, fun j ↦ ⟨?_, ?_⟩⟩
  · exact (((hDp j).1.mono (hsub hbp)).add
      ((hDm j).1.mono (hsub hbm))).congr_left he.symm
  · have hp : MemLp (fun p ↦ Dp j p / (saddleDist p : ℂ)) 2
        (volume.restrict (quarterImage b)) :=
      (hDp j).2.mono_measure (Measure.restrict_mono (hsub hbp) le_rfl)
    have hm : MemLp (fun p ↦ Dm j p / (saddleDist p : ℂ)) 2
        (volume.restrict (quarterImage b)) :=
      (hDm j).2.mono_measure (Measure.restrict_mono (hsub hbm) le_rfl)
    convert hp.add hm using 1
    funext p
    exact add_div _ _ _

/-- The ordinary specified separatrix gradient has the extra weight on its
base-quarter overlap, with no character assumption on the eigenfunction. -/
theorem dd_weighted_gradient_base_overlap {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
        HasWeakPartialOn U j (liftL2 ω) (D j) ∧
        MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
          (volume.restrict (U ∩ quarterImage b)) := by
  obtain ⟨U, hU, hsep, D, hD⟩ := dd_separatrix_weak_gradient hlam hω hs
  obtain ⟨b, hb, hbhalf, E, hE⟩ := dd_base_quarter_spatial_gradient hlam hω hs
  have hb1 : b ≤ 1 := by linarith
  refine ⟨U, hU, hsep, b, hb, hbhalf, D, fun j ↦ ⟨(hD j).2.1, ?_⟩⟩
  have hi : MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ quarterImage b)) :=
    (hE j).2.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have he := ((hD j).2.1.mono inter_subset_left).ae_eq
    (hU.inter (isOpen_quarterImage hb1)) ((hE j).1.mono inter_subset_right)
  apply hi.ae_eq
  filter_upwards [ae_restrict_of_ae he,
    ae_restrict_mem (hU.inter (isOpen_quarterImage hb1)).measurableSet] with p hp hpU
  rw [hp hpU]

end NoEmbeddedEigenvalues
