module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterChart
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.QuarterOrbits

/-!
# Covering a cell collar by the four open quarter images

Blueprint: `lem:quarter-cell-cover`, `lem:compact-cell-collar`.

The base quarter contains every collar point with `x > 0` and `y < 0`.
Rotations therefore cover the collar except for the two Cartesian axes.
These seams are null; no weak derivative is glued across them here.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The base Cartesian quadrant lies strictly inside the quarter's level radius. -/
theorem abs_diag_fst_lt_quarterRadius {p : ℝ × ℝ}
    (hp : p ∈ cellSquare) (hx : 0 < p.1) (hy : p.2 < 0) :
    |(diagCoord p).1| < Real.arccos (Real.sqrt (levelCoord p)) := by
  let a := (diagCoord p).1
  let c := (diagCoord p).2
  have hc : 0 < c := by dsimp [c, diagCoord]; linarith
  have hac : |a| < c := by rw [abs_lt]; dsimp [a, c, diagCoord]; constructor <;> linarith
  have haπ : |a| < Real.pi / 2 := hp.1
  have hcπ : c < Real.pi / 2 := (abs_lt.mp hp.2).2
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo (abs_lt.mp haπ)
  have hcos : Real.cos c < Real.cos a := by
    simpa only [Real.cos_abs] using
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg a) hcπ.le hac
  have hprod : Real.cos a * Real.cos c = levelCoord p := by
    rw [levelCoord, dipoleLift_eq_diag]; dsimp [a, c]; ring
  have hs : Real.sqrt (levelCoord p) < Real.cos a := by
    apply (Real.sqrt_lt' hca).mpr
    nlinarith
  have h := Real.arccos_lt_arccos
    (show -1 ≤ Real.sqrt (levelCoord p) by linarith [Real.sqrt_nonneg (levelCoord p)])
    hs (Real.cos_le_one a)
  rw [← Real.cos_abs a, Real.arccos_cos (abs_nonneg a) (by linarith [Real.pi_pos])] at h
  exact h

/-- A strict Cartesian quadrant lies in the corresponding open flow quarter. -/
theorem mem_quarterImage_of_quadrant {b : ℝ} (hb : b ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ cellSquare) (hh : levelCoord p ∈ Ioo 0 b)
    (hx : 0 < p.1) (hy : p.2 < 0) : p ∈ quarterImage b := by
  let a := (diagCoord p).1
  let c := (diagCoord p).2
  have hc : 0 < c := by dsimp [c, diagCoord]; linarith only [hx, hy]
  have hcπ : c < Real.pi / 2 := (abs_lt.mp hp.2).2
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1)
  have hprod : Real.cos a * Real.cos c = levelCoord p := by
    rw [levelCoord, dipoleLift_eq_diag]; dsimp [a, c]; ring
  have haA := abs_diag_fst_lt_quarterRadius hp hx hy
  have hh1 : levelCoord p < 1 := hh.2.trans_le hb
  obtain ⟨t, ht, hAt⟩ := (show a ∈ orbitA (levelCoord p) ''
      Ioo (-eighthPeriod (levelCoord p)) (eighthPeriod (levelCoord p)) by
    rw [image_orbitA_quarter hh.1 hh1]
    exact abs_lt.mp haA)
  have htL : |t| ≤ eighthPeriod (levelCoord p) := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have hβ : quarterHeight (levelCoord p) a = c := by
    unfold quarterHeight
    rw [show levelCoord p / Real.cos a = Real.cos c by
      rw [← hprod]; exact mul_div_cancel_left₀ _ hca.ne']
    exact Real.arccos_cos hc.le (by linarith only [hcπ, Real.pi_pos])
  have hBt : orbitB (levelCoord p) t = c := by
    rw [orbitB_eq_quarterHeight hh.1 hh1 htL, hAt, hβ]
  have he : dipoleOrbit (levelCoord p) t = p := by
    rw [dipoleOrbit_eq_diagInv, hAt, hBt]
    exact diagInv_diagCoord p
  exact he ▸ dipoleOrbit_mem_quarterImage hb (q := (levelCoord p, t)) ⟨hh.1, hh.2, ht⟩

/-- Rotation preserves the open cell and its level. -/
theorem rotLift_cell_level (p : ℝ × ℝ) :
    (rotLift p ∈ cellSquare ↔ p ∈ cellSquare) ∧ levelCoord (rotLift p) = levelCoord p := by
  constructor
  · have h : diagCoord (rotLift p) = (-(diagCoord p).2, (diagCoord p).1) := by
      ext <;> simp [diagCoord, rotLift] <;> ring
    simp [cellSquare, h, and_comm]
  · simp [levelCoord, dipoleLift, rotLift, Real.cos_neg, add_comm]

/-- One of the four rotations places a point off the axes in the base quadrant. -/
theorem exists_rotLift_mem_quarterImage {b : ℝ} (hb : b ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ cellSquare) (hh : levelCoord p ∈ Ioo 0 b)
    (hx : p.1 ≠ 0) (hy : p.2 ≠ 0) :
    ∃ k : Fin 4, rotLift^[k.val] p ∈ quarterImage b := by
  have hcell (k : ℕ) : rotLift^[k] p ∈ cellSquare := by
    induction k with
    | zero => exact hp
    | succ k ih => simpa only [Function.iterate_succ_apply'] using
        (rotLift_cell_level _).1.mpr ih
  have hlevel (k : ℕ) : levelCoord (rotLift^[k] p) = levelCoord p := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [Function.iterate_succ_apply', (rotLift_cell_level _).2] using ih
  have hmem (k : Fin 4) (hx' : 0 < (rotLift^[k.val] p).1)
      (hy' : (rotLift^[k.val] p).2 < 0) : rotLift^[k.val] p ∈ quarterImage b :=
    mem_quarterImage_of_quadrant hb (hcell k.val) (hlevel k.val ▸ hh) hx' hy'
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · exact ⟨3, hmem 3 (by simpa [Function.iterate_succ_apply, rotLift] using neg_pos.mpr hy)
      (by simpa [Function.iterate_succ_apply, rotLift] using hx)⟩
  · exact ⟨2, hmem 2 (by simpa [Function.iterate_succ_apply, rotLift] using neg_pos.mpr hx)
      (by simpa [Function.iterate_succ_apply, rotLift] using neg_neg_of_pos hy)⟩
  · exact ⟨0, hmem 0 hx hy⟩
  · exact ⟨1, hmem 1 hy (by simpa [rotLift] using neg_neg_of_pos hx)⟩

/-- The axes are the only omitted seams, and have zero planar volume. -/
theorem ae_cell_collar_covered {b : ℝ} (hb : b ≤ 1) :
    ∀ᵐ p : ℝ × ℝ, p ∈ cellSeparatrixStrip (2 * b) →
      ∃ k : Fin 4, rotLift^[k.val] p ∈ quarterImage b := by
  have hx : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (show ∀ᵐ x : ℝ, x ≠ 0 by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton])
  have hy : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae (show ∀ᵐ x : ℝ, x ≠ 0 by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton])
  filter_upwards [hx, hy] with p hpx hpy hp
  apply exists_rotLift_mem_quarterImage hb hp.1 _ hpx hpy
  change 0 < dipoleLift p / 2 ∧ dipoleLift p / 2 < b
  constructor <;> linarith [hp.2.1, hp.2.2]

/-- The positive cell collar is open. -/
theorem isOpen_cellSeparatrixStrip (ε : ℝ) : IsOpen (cellSeparatrixStrip ε) := by
  have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  exact isOpen_cellSquare.inter (hc.isOpen_preimage _ isOpen_Ioo)

/-- Compactness of the closed cell gives a uniform collar inside any open
neighbourhood of the lifted separatrix. -/
theorem exists_cell_collar_subset {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsep : {p | dipoleLift p = 0} ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ cellSeparatrixStrip ε ⊆ U := by
  have hK : IsCompact (closure cellSquare) :=
    (isBounded_cellNeighbourhood.subset
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)).isCompact_closure
  have hc : Continuous (fun p ↦ |dipoleLift p|) := by unfold dipoleLift; fun_prop
  obtain ⟨ε, hε, hlo⟩ := (hK.diff hU).exists_forall_le' hc.continuousOn
    (fun p hp ↦ abs_pos.mpr (fun hz ↦ hp.2 (hsep hz)))
  refine ⟨ε, hε, fun p hp ↦ ?_⟩
  by_contra hn
  have h := hlo p ⟨subset_closure hp.1, hn⟩
  rw [abs_of_pos hp.2.1] at h
  exact (not_lt_of_ge h) hp.2.2

end NoEmbeddedEigenvalues
