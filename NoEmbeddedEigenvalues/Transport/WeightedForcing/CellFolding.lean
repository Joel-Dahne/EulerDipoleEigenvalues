module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.RotationWeakGradient

/-!
# Reflected periodic copies of the positive cell

Blueprint: `def:periodic-cell-folds`, `lem:periodic-cell-cover`.

The folding maps are volume-preserving affine isometries. They preserve the
saddle lattice, while reflection reverses the dipole level. On a bounded set,
only finitely many folds can land in the positive cell.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open Real

/-- The lift of the first separatrix reflection. -/
def separatrixReflect (p : ℝ × ℝ) : ℝ × ℝ := (π - p.2, π - p.1)

/-- The signed swap that is the reflection's linear part. -/
def separatrixReflectLinear : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ({ toFun := fun p ↦ (-p.2, -p.1)
     invFun := fun p ↦ (-p.2, -p.1)
     left_inv := by intro p; simp
     right_inv := by intro p; simp
     map_add' := by intro p q; ext <;> simp [add_comm]
     map_smul' := by intro a p; ext <;> simp } :
    (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)).toContinuousLinearEquiv

/-- Linear part of a reflected or unreflected fold. -/
def cellFoldLinear (s : Bool) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  if s then separatrixReflectLinear else ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)

/-- Translation part of a fold. -/
def cellFoldTranslation (s : Bool) (n : ℤ × ℤ) : ℝ × ℝ :=
  (if s then (π, π) else 0) + ((n.1 : ℝ) * (2 * π), (n.2 : ℝ) * (2 * π))

/-- First reflect if requested, then apply an integer torus-period translation. -/
def cellFold (s : Bool) (n : ℤ × ℤ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeAffine (cellFoldLinear s) (cellFoldTranslation s n)

theorem cellFold_apply (s : Bool) (n : ℤ × ℤ) (p : ℝ × ℝ) :
    cellFold s n p = liftShift n (if s then separatrixReflect p else p) := by
  cases s <;> ext <;>
    simp [cellFold, planeAffine, cellFoldLinear, cellFoldTranslation,
      separatrixReflectLinear, separatrixReflect, liftShift] <;> ring

theorem measurePreserving_cellFold (s : Bool) (n : ℤ × ℤ) :
    MeasurePreserving (cellFold s n) := by
  apply measurePreserving_planeAffine
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  cases s <;> norm_num [LinearMap.toMatrix_apply, cellFoldLinear, separatrixReflectLinear]

/-- The folding map is an isometry for the product metric used by `saddleDist`. -/
theorem isometry_cellFold (s : Bool) (n : ℤ × ℤ) : Isometry (cellFold s n) := by
  have hA : Isometry (cellFoldLinear s) := by
    apply Isometry.of_dist_eq
    intro p q
    cases s <;> simp [cellFoldLinear, separatrixReflectLinear, Prod.dist_eq, max_comm]
  apply Isometry.of_dist_eq
  intro p q
  change dist (cellFoldLinear s p + cellFoldTranslation s n)
    (cellFoldLinear s q + cellFoldTranslation s n) = _
  rw [dist_add_right]
  exact hA.dist_eq p q

theorem cellFold_mem_saddleSet (s : Bool) (n : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : p ∈ saddleSet) : cellFold s n p ∈ saddleSet := by
  obtain ⟨m, k, ⟨j, hj⟩, rfl⟩ := hp
  cases s
  · refine ⟨m + 2 * n.1, k + 2 * n.2, ⟨j + n.1 + n.2, by omega⟩, ?_⟩
    ext <;> simp [cellFold_apply, liftShift] <;> ring
  · refine ⟨1 - k + 2 * n.1, 1 - m + 2 * n.2,
      ⟨n.1 + n.2 - j, by omega⟩, ?_⟩
    ext <;> simp [cellFold_apply, liftShift, separatrixReflect] <;> ring

/-- The inverse fold uses negated periods or swaps the two reflection periods. -/
theorem cellFold_inverse (s : Bool) (n : ℤ × ℤ) (p : ℝ × ℝ) :
    cellFold s n (cellFold s (if s then (n.2, n.1) else -n) p) = p := by
  cases s <;> ext <;> simp [cellFold_apply, liftShift, separatrixReflect] <;> ring

theorem saddleDist_cellFold (s : Bool) (n : ℤ × ℤ) (p : ℝ × ℝ) :
    saddleDist (cellFold s n p) = saddleDist p := by
  have hi : cellFold s n '' saddleSet = saddleSet := by
    apply Subset.antisymm
    · rintro q ⟨p, hp, rfl⟩
      exact cellFold_mem_saddleSet s n hp
    · intro q hq
      exact ⟨cellFold s (if s then (n.2, n.1) else -n) q,
        cellFold_mem_saddleSet _ _ hq, cellFold_inverse s n q⟩
  unfold saddleDist
  simpa only [hi] using Metric.infDist_image (isometry_cellFold s n) (x := p) (t := saddleSet)

theorem dipoleLift_liftShift (n : ℤ × ℤ) (p : ℝ × ℝ) :
    dipoleLift (liftShift n p) = dipoleLift p := by
  have he : torusProj (liftShift n p) = torusProj p := by
    ext <;> apply Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    · exact ⟨n.1, by simp [liftShift]; ring⟩
    · exact ⟨n.2, by simp [liftShift]; ring⟩
  rw [← Ψ_torusProj, he, Ψ_torusProj]

theorem dipoleLift_separatrixReflect (p : ℝ × ℝ) :
    dipoleLift (separatrixReflect p) = -dipoleLift p := by
  simp [separatrixReflect, dipoleLift, Real.cos_sub, add_comm]

/-- A fold preserves the dipole level up to its reflection sign. -/
theorem dipoleLift_cellFold (s : Bool) (n : ℤ × ℤ) (p : ℝ × ℝ) :
    dipoleLift (cellFold s n p) = (if s then -1 else 1) * dipoleLift p := by
  cases s <;> simp [cellFold_apply, dipoleLift_liftShift, dipoleLift_separatrixReflect]

/-- Every folded positive strip is contained in the nonzero absolute-level collar. -/
theorem cellFold_preimage_strip_subset (s : Bool) (n : ℤ × ℤ) (ε : ℝ) :
    cellFold s n ⁻¹' cellSeparatrixStrip ε ⊆
      {p | dipoleLift p ≠ 0 ∧ |dipoleLift p| < ε} := by
  intro p hp
  have he := dipoleLift_cellFold s n p
  have hzero : dipoleLift p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact hp.2.1.ne' he
  have habs : |dipoleLift (cellFold s n p)| = |dipoleLift p| := by
    rw [he, abs_mul]
    cases s <;> simp
  refine ⟨hzero, ?_⟩
  rw [← habs, abs_of_pos hp.2.1]
  exact hp.2.2

/-- Equal torus projections differ by an explicit integer-period shift. -/
theorem exists_liftShift_eq {p q : ℝ × ℝ} (h : torusProj q = torusProj p) :
    ∃ n : ℤ × ℤ, liftShift n p = q := by
  obtain ⟨m, hm⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp (congrArg Prod.fst h)
  obtain ⟨n, hn⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp (congrArg Prod.snd h)
  refine ⟨(m, n), ?_⟩
  ext <;> change _ + _ * (2 * π) = _ <;> linarith only [hm, hn]

/-- Every nonzero small level folds into the positive cell collar. -/
theorem exists_cellFold_mem_collar {ε : ℝ} {p : ℝ × ℝ}
    (hp0 : dipoleLift p ≠ 0) (hpε : |dipoleLift p| < ε) :
    ∃ s : Bool, ∃ n : ℤ × ℤ, cellFold s n p ∈ cellSeparatrixStrip ε := by
  have hpos {q : ℝ × ℝ} (hq : 0 < dipoleLift q) :
      ∃ n : ℤ × ℤ, liftShift n q ∈ cellSquare := by
    obtain ⟨r, hr, he⟩ := exists_mem_cellSquare
      (t := torusProj q) (by simpa only [positiveCell, mem_ofPred_eq, Ψ_torusProj] using hq)
    obtain ⟨n, hn⟩ := exists_liftShift_eq he
    exact ⟨n, hn ▸ hr⟩
  rcases lt_or_gt_of_ne hp0 with hp | hp
  · obtain ⟨n, hn⟩ := hpos (q := separatrixReflect p) (by
      rw [dipoleLift_separatrixReflect]; linarith only [hp])
    refine ⟨true, n, ?_⟩
    simpa only [cellFold_apply, Bool.true_eq, ite_true, cellSeparatrixStrip, mem_ofPred_eq,
      dipoleLift_liftShift, dipoleLift_separatrixReflect, abs_of_neg hp] using
      (show liftShift n (separatrixReflect p) ∈ cellSquare ∧
        0 < -dipoleLift p ∧ -dipoleLift p < ε from ⟨hn, neg_pos.mpr hp, by
          simpa only [abs_of_neg hp] using hpε⟩)
  · obtain ⟨n, hn⟩ := hpos hp
    refine ⟨false, n, ?_⟩
    simpa only [cellFold_apply, Bool.false_eq_true, ite_false, cellSeparatrixStrip,
      mem_ofPred_eq, dipoleLift_liftShift] using
      (show liftShift n p ∈ cellSquare ∧ 0 < dipoleLift p ∧ dipoleLift p < ε from
        ⟨hn, hp, by simpa only [abs_of_pos hp] using hpε⟩)

/-- Cartesian size of a central positive-cell point. -/
theorem norm_le_pi_of_mem_cellSquare {p : ℝ × ℝ} (hp : p ∈ cellSquare) : ‖p‖ ≤ π := by
  obtain ⟨ha, hb⟩ := hp
  rw [abs_lt] at ha hb
  dsimp [diagCoord] at ha hb
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le]
  constructor <;> constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]

/-- A fold landing in the central cell has bounded period indices. -/
theorem cellFold_mem_shiftBox {R : ℝ} {N : ℕ} (hN : 2 * π + R ≤ N)
    {p : ℝ × ℝ} (hp : ‖p‖ ≤ R) (s : Bool) {n : ℤ × ℤ}
    (hn : cellFold s n p ∈ cellSquare) : n ∈ shiftBox N := by
  have hq := norm_le_pi_of_mem_cellSquare hn
  let q := if s then separatrixReflect p else p
  have hu : ‖q‖ ≤ π + R := by
    cases s
    · exact hp.trans (by linarith only [Real.pi_pos])
    · have he : separatrixReflect p = (π, π) - Prod.swap p := rfl
      change ‖separatrixReflect p‖ ≤ _
      rw [he]
      exact (norm_sub_le _ _).trans (by
        simpa [Prod.norm_def, max_comm, abs_of_pos Real.pi_pos] using add_le_add_left hp π)
  have hbnd (i : Fin 2) : |((if i = 0 then n.1 else n.2 : ℤ) : ℝ) * (2 * π)| ≤ 2 * π + R := by
    have he : axisCoord i (cellFold s n p) = axisCoord i q +
        ((if i = 0 then n.1 else n.2 : ℤ) : ℝ) * (2 * π) := by
      rw [cellFold_apply]
      fin_cases i <;> rfl
    have hqi : |axisCoord i (cellFold s n p)| ≤ π := by
      fin_cases i
      · exact (norm_fst_le _).trans hq
      · exact (norm_snd_le _).trans hq
    have hui : |axisCoord i q| ≤ π + R := by
      fin_cases i
      · exact (norm_fst_le _).trans hu
      · exact (norm_snd_le _).trans hu
    calc _ = |axisCoord i (cellFold s n p) - axisCoord i q| := by rw [he]; ring_nf
         _ ≤ |axisCoord i (cellFold s n p)| + |axisCoord i q| := abs_sub _ _
         _ ≤ 2 * π + R := by linarith only [hqi, hui]
  have key (m : ℤ) (hm : |(m : ℝ) * (2 * π)| ≤ 2 * π + R) :
      -(N : ℤ) ≤ m ∧ m ≤ N := by
    have hpi : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
    have hb : |(m : ℝ)| ≤ N := by
      rw [abs_mul, abs_of_pos Real.two_pi_pos] at hm
      nlinarith only [hm, hN, hpi, abs_nonneg (m : ℝ)]
    exact ⟨by exact_mod_cast (abs_le.mp hb).1, by exact_mod_cast (abs_le.mp hb).2⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (key n.1 (hbnd 0)),
    Finset.mem_Icc.mpr (key n.2 (hbnd 1))⟩

end NoEmbeddedEigenvalues
