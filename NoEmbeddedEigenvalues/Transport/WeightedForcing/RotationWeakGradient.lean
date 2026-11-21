module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.AffineJets
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterRotation
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterCellCover

/-!
# Cartesian weak gradients under quarter rotations

Blueprint: `lem:weighted-gradient-rotation`, `lem:weighted-gradient-cell-cover`.

The affine chain rule transports both derivative indices. Exact saddle-distance
invariance transports the weighted L² norms. A spatial a.e. character identity
then returns derivatives of the same raw function, not of a new representative.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The Cartesian quarter rotation as a continuous linear equivalence. -/
def rotLinear : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ({ toFun := rotLift
     invFun := fun p ↦ (-p.2, p.1)
     left_inv := by intro p; ext <;> simp [rotLift]
     right_inv := by intro p; ext <;> simp [rotLift]
     map_add' := by intro p q; ext <;> simp [rotLift, add_comm]
     map_smul' := by intro a p; ext <;> simp [rotLift] } :
    (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)).toContinuousLinearEquiv

@[simp] theorem planeAffine_rotLinear :
    (planeAffine rotLinear 0 : (ℝ × ℝ) → ℝ × ℝ) = rotLift := by
  funext p
  exact add_zero _

/-- The derivative rows of `F(y,-x)` are `-D_y(y,-x)` and `D_x(y,-x)`. -/
theorem HasWeakPartialOn.comp_rotLift {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn V j F (D j)) (j : Fin 2) :
    HasWeakPartialOn (rotLift ⁻¹' V) j (F ∘ rotLift)
      (fun p ↦ if j = 0 then -D 1 (rotLift p) else D 0 (rotLift p)) := by
  have hmp : MeasurePreserving (planeAffine rotLinear 0) := by
    rw [planeAffine_rotLinear]
    exact measurePreserving_rotLift
  have hw := HasWeakPartialOn.comp_planeAffine rotLinear 0 hmp hV hD j
  rw [planeAffine_rotLinear] at hw
  fin_cases j <;> simpa [affineCoeff, planeDirection, axisCoord, rotLinear, rotLift] using hw

/-- Weighted L² pulls back through the rotation with the exact same distance. -/
theorem memLp_div_saddleDist_comp_rotLift {V : Set (ℝ × ℝ)} (hV : MeasurableSet V)
    {D : ℝ × ℝ → ℂ}
    (hD : MemLp (fun p ↦ D p / (saddleDist p : ℂ)) 2 (volume.restrict V)) :
    MemLp (fun p ↦ D (rotLift p) / (saddleDist p : ℂ)) 2
      (volume.restrict (rotLift ⁻¹' V)) := by
  have hmp : MeasurePreserving (planeAffine rotLinear 0) := by
    rw [planeAffine_rotLinear]
    exact measurePreserving_rotLift
  simpa only [planeAffine_rotLinear, Function.comp_def, saddleDist_rotLift] using
    memLp_comp_planeAffine rotLinear 0 hmp hV hD

/-- A nonzero character transports a weighted gradient to the rotated domain. -/
theorem exists_weightedGradient_rotLift {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn V j F (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2 (volume.restrict V))
    {a : ℂ} (ha : a ≠ 0) (hchar : (F ∘ rotLift) =ᵐ[volume] fun p ↦ a * F p) :
    ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (rotLift ⁻¹' V) j F (E j) ∧
      MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2
        (volume.restrict (rotLift ⁻¹' V)) := by
  let E := fun (j : Fin 2) (p : ℝ × ℝ) ↦
    a⁻¹ * (if j = 0 then -D 1 (rotLift p) else D 0 (rotLift p))
  have he : (fun p ↦ a⁻¹ * F (rotLift p)) =ᵐ[volume] F := by
    filter_upwards [hchar] with p hp
    change F (rotLift p) = a * F p at hp
    rw [hp, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  refine ⟨E, fun j ↦ ⟨?_, ?_⟩⟩
  · exact ((HasWeakPartialOn.comp_rotLift hV (fun i ↦ (hD i).1) j).const_mul a⁻¹).congr_left he
  · have hL (i : Fin 2) := memLp_div_saddleDist_comp_rotLift hV.measurableSet (hD i).2
    fin_cases j
    · convert (hL 1).neg.const_mul a⁻¹ using 1
      funext p
      simp [E, div_eq_mul_inv, mul_assoc]
    · convert (hL 0).const_mul a⁻¹ using 1
      funext p
      simp [E, div_eq_mul_inv, mul_assoc]

/-- Iterated rotated domains retain weighted derivatives of the same function. -/
theorem exists_weightedGradient_iterate_rotLift {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {F : ℝ × ℝ → ℂ} (hD : ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn V j F (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2 (volume.restrict V))
    {a : ℂ} (ha : a ≠ 0) (hchar : (F ∘ rotLift) =ᵐ[volume] fun p ↦ a * F p)
    (k : ℕ) :
    ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (rotLift^[k] ⁻¹' V) j F (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
        (volume.restrict (rotLift^[k] ⁻¹' V)) := by
  have hR : Continuous rotLift := by unfold rotLift; fun_prop
  induction k with
  | zero => exact hD
  | succ k ih =>
    obtain ⟨D, hD⟩ := ih
    have he := exists_weightedGradient_rotLift (hV.preimage (hR.iterate k)) hD ha hchar
    simpa only [Function.iterate_succ, preimage_comp] using he

/-- A finite quarter cover transfers the weighted norm to one specified gradient
on its cell-collar overlap. The omitted Cartesian seams are null. -/
theorem memLp_weighted_gradient_cell_collar {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F : ℝ × ℝ → ℂ}
    {D : Fin 2 → ℝ × ℝ → ℂ} (hDm : ∀ j, Measurable (D j))
    (hD : ∀ j, HasWeakPartialOn U j F (D j))
    (hE : ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (quarterImage b) j F (E j) ∧
      MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2 (volume.restrict (quarterImage b)))
    {a : ℂ} (ha : a ≠ 0) (hchar : (F ∘ rotLift) =ᵐ[volume] fun p ↦ a * F p) (j : Fin 2) :
    MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ cellSeparatrixStrip (2 * b))) := by
  have hR : Continuous rotLift := by unfold rotLift; fun_prop
  let V := fun k : Fin 4 ↦ rotLift^[k.val] ⁻¹' quarterImage b
  have hV (k : Fin 4) : IsOpen (V k) := (isOpen_quarterImage hb).preimage (hR.iterate k.val)
  have hL (k : Fin 4) : MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ V k)) := by
    obtain ⟨E, hE⟩ := exists_weightedGradient_iterate_rotLift (isOpen_quarterImage hb)
      hE ha hchar k.val
    have hi : MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2
        (volume.restrict (U ∩ V k)) :=
      (hE j).2.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    have he := ((hD j).mono inter_subset_left).ae_eq (hU.inter (hV k))
      ((hE j).1.mono inter_subset_right)
    apply hi.ae_eq
    filter_upwards [ae_restrict_of_ae he,
      ae_restrict_mem (hU.inter (hV k)).measurableSet] with p hp hpU
    rw [hp hpU]
  have hm : Measurable (fun p ↦ D j p / (saddleDist p : ℂ)) :=
    (hDm j).div (Complex.measurable_ofReal.comp
      (Metric.continuous_infDist_pt saddleSet).measurable)
  have hi : IntegrableOn (fun p ↦ ‖D j p / (saddleDist p : ℂ)‖ ^ 2)
      (⋃ k : Fin 4, U ∩ V k) :=
    integrableOn_finite_iUnion.mpr fun k ↦
      (memLp_two_iff_integrable_sq_norm (hL k).aestronglyMeasurable).mp (hL k)
  have hLu := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi
  apply hLu.mono_measure (Measure.restrict_mono_ae ?_)
  filter_upwards [ae_cell_collar_covered hb] with p hp hpU
  obtain ⟨k, hk⟩ := hp hpU.2
  exact mem_iUnion.mpr ⟨k, hpU.1, hk⟩

end NoEmbeddedEigenvalues
