import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterTransportProjections

/-!
# Weighted first gradients and forcing growth under quarter projections

Blueprint: `lem:weighted-quarter-projections`.

Rotate the supplied weak gradient with the actual Cartesian derivative rows,
then take the same finite linear combination as for the forcing. Restricted
measure-preserving rotations and exact distance invariance retain the cell
norms. No weak gradient is replaced or evaluated along an endpoint curve.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The original supplied weighted first gradient produces weighted first
derivatives of every projected forcing on the same invariant domain. -/
theorem exists_weightedGradient_quarterCharacterProjection
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hRU : rotLift ⁻¹' U = U)
    {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ} {s : ℝ}
    (hD : ∀ j, HasWeakPartialOn U j F (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) s : ℂ)) 2
      (volume.restrict cellSquare)) (κ : ℂ) :
    ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn U j (quarterCharacterProjection κ F) (E j) ∧
      MemLp (fun p ↦ E j p / (Real.rpow (saddleDist p) s : ℂ)) 2
        (volume.restrict cellSquare) := by
  let P := fun G : ℝ × ℝ → ℂ ↦ ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
    HasWeakPartialOn U j G (E j) ∧
    MemLp (fun p ↦ E j p / (Real.rpow (saddleDist p) s : ℂ)) 2
      (volume.restrict cellSquare)
  have hadd {G H : ℝ × ℝ → ℂ} (hG : P G) (hH : P H) : P (fun p ↦ G p + H p) := by
    obtain ⟨A, hA⟩ := hG
    obtain ⟨B, hB⟩ := hH
    refine ⟨fun j p ↦ A j p + B j p, fun j ↦ ⟨(hA j).1.add (hB j).1, ?_⟩⟩
    exact ((hA j).2.add (hB j).2).ae_eq
      (Eventually.of_forall fun p ↦ (add_div _ _ _).symm)
  have hmul {G : ℝ × ℝ → ℂ} (hG : P G) (c : ℂ) : P (fun p ↦ c * G p) := by
    obtain ⟨A, hA⟩ := hG
    refine ⟨fun j p ↦ c * A j p, fun j ↦ ⟨(hA j).1.const_mul c, ?_⟩⟩
    exact ((hA j).2.const_mul c).ae_eq
      (Eventually.of_forall fun p ↦ (mul_div_assoc c (A j p) _).symm)
  have hrot {G : ℝ × ℝ → ℂ} (hG : P G) : P (G ∘ rotLift) := by
    obtain ⟨A, hA⟩ := hG
    let B := fun (j : Fin 2) (p : ℝ × ℝ) ↦
      if j = 0 then -A 1 (rotLift p) else A 0 (rotLift p)
    have hcell : rotLift ⁻¹' cellSquare = cellSquare := by
      ext p
      exact (rotLift_cell_level p).1
    have hm : MeasurePreserving rotLift (volume.restrict cellSquare)
        (volume.restrict cellSquare) := by
      simpa only [hcell] using measurePreserving_rotLift.restrict_preimage
        isOpen_cellSquare.measurableSet
    have hL (j : Fin 2) : MemLp (fun p ↦ A j (rotLift p) /
        (Real.rpow (saddleDist p) s : ℂ)) 2 (volume.restrict cellSquare) := by
      simpa only [Function.comp_def, saddleDist_rotLift] using
        (hA j).2.comp_measurePreserving hm
    refine ⟨B, fun j ↦ ⟨?_, ?_⟩⟩
    · have hd := HasWeakPartialOn.comp_rotLift hU (fun i ↦ (hA i).1) j
      rwa [hRU] at hd
    · fin_cases j
      · convert (hL 1).neg using 1
        funext p
        simp [B, neg_div]
      · simpa [B] using hL 0
  have h0 : P F := ⟨D, fun j ↦ ⟨hD j, hw j⟩⟩
  have h1 := hrot h0
  have h2 := hrot h1
  have h3 := hrot h2
  exact hmul (hadd (hadd (hadd h0 (hmul h1 (κ ^ 3))) (hmul h2 (κ ^ 2))) (hmul h3 κ)) (1 / 4)

/-- Unit-modulus quarter projections preserve the same global cell forcing
growth constant, using the original pointwise representative. -/
theorem quarterCharacterProjection_rpow_bound {g : ℝ × ℝ → ℂ} {s K : ℝ}
    {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hg : ∀ p ∈ cellSquare, ‖g p‖ ≤ K * Real.rpow (saddleDist p) s) :
    ∀ p ∈ cellSquare, ‖quarterCharacterProjection κ g p‖ ≤
      K * Real.rpow (saddleDist p) s := by
  intro p hp
  have hp1 := (rotLift_cell_level p).1.mpr hp
  have hp2 := (rotLift_cell_level (rotLift p)).1.mpr hp1
  have hp3 := (rotLift_cell_level (rotLift (rotLift p))).1.mpr hp2
  have h0 := hg p hp
  have h1 := hg _ hp1
  have h2 := hg _ hp2
  have h3 := hg _ hp3
  simp only [saddleDist_rotLift] at h1 h2 h3
  have hn1 := norm_add_le (g p) (κ ^ 3 * g (rotLift p))
  have hn2 := norm_add_le (g p + κ ^ 3 * g (rotLift p))
    (κ ^ 2 * g (rotLift (rotLift p)))
  have hn3 := norm_add_le (g p + κ ^ 3 * g (rotLift p) + κ ^ 2 * g (rotLift (rotLift p)))
    (κ * g (rotLift (rotLift (rotLift p))))
  simp only [norm_mul, norm_pow, hκ, one_pow, one_mul] at hn1 hn2 hn3
  dsimp only [quarterCharacterProjection]
  rw [norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  nlinarith

end NoEmbeddedEigenvalues
