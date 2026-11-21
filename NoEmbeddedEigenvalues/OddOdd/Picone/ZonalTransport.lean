module

public import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalWeakPairing
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.DiagonalACL
public import NoEmbeddedEigenvalues.OddOdd.WeightedVirial.OddOddVirial

/-!
# Physical-to-diagonal weighted measure transport

The diagonal inverse sends the probability measure `zonalMeasure` to
`(2π²)⁻¹ • ddCellMeasure`. Thus weighted L² values and specified Cartesian
weak derivatives give the diagonal weak domain without boundary assumptions.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ENNReal

/-- The positive cell is precisely the inverse image of the diagonal square. -/
theorem preimage_cellSquare_diagInv : diagInv ⁻¹' cellSquare = zonalSquare := by
  ext p
  simp only [mem_preimage, cellSquare, mem_ofPred_eq, diagCoord_diagInv,
    zonalSquare, mem_prod, mem_Ioo, abs_lt, neg_div]

theorem zonalDensity_eq_ddWeight (p : ℝ × ℝ) :
    zonalDensity p = 1 / Real.pi ^ 2 * ddWeight (diagInv p) := by
  rw [zonalDensity, ddWeight, dipoleLift_eq_diag, diagCoord_diagInv]
  ring

private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (w : β → ℝ≥0∞) (hw : Measurable w) :
    Measure.map e (μ.withDensity (w ∘ e)) = (Measure.map e μ).withDensity w := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs hw e.measurable]
  rfl

/-- Probability normalization and the Jacobian, as an exact measure identity. -/
theorem map_diagInv_zonalMeasure :
    Measure.map diagInv zonalMeasure = ENNReal.ofReal (1 / (2 * Real.pi ^ 2)) • ddCellMeasure := by
  let e := diagInv.toHomeomorph.toMeasurableEquiv
  let w : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (1 / Real.pi ^ 2 * ddWeight p)
  have hw : Measurable w := by unfold w ddWeight dipoleLift; fun_prop
  have hbase : Measure.map diagInv (volume.restrict zonalSquare) =
      ENNReal.ofReal (1 / 2) • volume.restrict cellSquare := by
    rw [← preimage_cellSquare_diagInv, ← Measure.restrict_map diagInv.continuous.measurable
      isOpen_cellSquare.measurableSet, map_diagInv_volume, Measure.restrict_smul]
  have hν : zonalMeasure = (volume.restrict zonalSquare).withDensity (w ∘ e) := by
    change (volume.restrict zonalSquare).withDensity (fun p ↦ ENNReal.ofReal (zonalDensity p)) = _
    congr 1
    funext p
    exact congrArg ENNReal.ofReal (zonalDensity_eq_ddWeight p)
  have hweight : (volume.restrict cellSquare).withDensity w =
      ENNReal.ofReal (1 / Real.pi ^ 2) • ddCellMeasure := by
    have heq : w = ENNReal.ofReal (1 / Real.pi ^ 2) • (fun p ↦ ENNReal.ofReal (ddWeight p)) := by
      funext p
      exact ENNReal.ofReal_mul (by positivity)
    rw [heq, withDensity_smul (ENNReal.ofReal (1 / Real.pi ^ 2))
      (show Measurable (fun p ↦ ENNReal.ofReal (ddWeight p)) by
        unfold ddWeight dipoleLift; fun_prop)]
    rfl
  rw [hν]
  change Measure.map e ((volume.restrict zonalSquare).withDensity (w ∘ e)) = _
  rw [map_withDensity_comp e _ w hw]
  change (Measure.map diagInv (volume.restrict zonalSquare)).withDensity w = _
  rw [hbase, withDensity_smul_measure, hweight, smul_smul,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  congr 2
  ring

/-- Weighted L² membership in physical coordinates transports to the probability
measure on the diagonal square. -/
theorem memLp_zonalMeasure_comp_diagInv {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 ddCellMeasure) :
    MemLp (f ∘ diagInv) 2 zonalMeasure := by
  apply diagInv.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.1
  change MemLp f 2 (Measure.map diagInv zonalMeasure)
  rw [map_diagInv_zonalMeasure]
  exact hf.smul_measure (by finiteness)

/-- Bochner integrals retain the exact physical mass normalization. -/
theorem integral_comp_diagInv_zonalMeasure {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) :
    (∫ q, f (diagInv q) ∂zonalMeasure) =
      (1 / (2 * Real.pi ^ 2) : ℝ) • (∫ p, f p ∂ddCellMeasure) := by
  calc
    _ = ∫ p, f p ∂Measure.map diagInv zonalMeasure :=
      (diagInv.toHomeomorph.measurableEmbedding.integral_map f).symm
    _ = _ := by
      rw [map_diagInv_zonalMeasure, integral_smul_measure,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / (2 * Real.pi ^ 2) : ℝ))]

/-- Pull arbitrary a.e. physical-cell predicates back to the diagonal probability
measure; no measurability assumption on the predicate or representative is needed. -/
theorem ae_zonalMeasure_comp_diagInv {P : ℝ × ℝ → Prop}
    (hP : ∀ᵐ p ∂volume.restrict cellSquare, P p) :
    ∀ᵐ q ∂zonalMeasure, P (diagInv q) := by
  have hd : ∀ᵐ p ∂ddCellMeasure, P p :=
    (withDensity_absolutelyContinuous _ _).ae_le hP
  have hm : ∀ᵐ p ∂Measure.map diagInv zonalMeasure, P p := by
    rw [map_diagInv_zonalMeasure]
    exact Measure.ae_smul_measure hd _
  exact diagInv.toHomeomorph.measurableEmbedding.ae_map_iff.mp hm

end NoEmbeddedEigenvalues
