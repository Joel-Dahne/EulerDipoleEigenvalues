import Mathlib.MeasureTheory.Constructions.Polish.Basic
import NoEmbeddedEigenvalues.AnglePeriodization
import NoEmbeddedEigenvalues.Transport

/-!
# The transversal mollifier

Blueprint: `def:transversal-mollifier`, `lem:transversal-mollifier-support` (proved),
`lem:transversal-mollifier-congr`, `lem:transversal-mollifier-linear`,
`lem:transversal-mollifier`, `lem:transversal-mollifier-derivatives` and
`lem:transversal-mollifier-commutator` (proved from chart/coarea inputs, the derivatives
also from the full weak-gradient chain rules);
`lem:action-angle-test-chain`, `lem:action-angle-local-integrability` (proved from
chart/coarea inputs; the forward classical chain rule has no admitted dependency);
`lem:action-angle-transport`, `lem:action-angle-gradient-local-integrability` and
`lem:action-angle-weak-angular`, `def:level-dual-field`, `lem:level-dual-field`,
`lem:level-dual-weak`, `lem:action-angle-weak-level`, `lem:action-angle-weak` and
`lem:action-angle-weak-cell` (proved without admissions).

In action-angle coordinates `(h, θ)` on the punctured cell (`OrbitCoordinates.lean`), `L₀`
is `S(h)⁻¹ ∂_θ`. The transversal mollifier cuts off with `χ(h)` and mollifies in `h` at fixed
`θ`, `J_ε u = M_ε(χ U) ∘ (h, θ)` with `U = u ∘ (h, θ)⁻¹`, extended by zero off the cell.
It almost commutes with `L₀`: the commutator only sees the variation of `S` over the
smoothing window, which costs `O(ε)` times `‖L₀ u‖`. Its derivatives are `O(1/ε)`, in fact
`o(1/ε)`. This is what the `L²` virial identity (`VirialL2.lean`) needs; it uses no flow of
the virial field.

All statements are on the lift: inputs are functions on the cell square, outputs are
functions on `ℝ²` supported in a fixed compact subset of the punctured cell.
Private helpers realize the action-angle area formula as a measure-preserving map
from a weighted fundamental rectangle, transfer null sets in both directions, and
place cutoff pullbacks in unweighted `L²`. Almost every angular line is then `L²`,
which justifies integral linearity by Hölder against the compact kernel. A measurable
inverse extension reconstructs cylinder data on the cell. The upper bound for the area
density on a fixed level band transfers contraction and convergence from the cylinder
back to the plane, uniformly for small scales.

Local `L¹` transfer is proved in both directions. Positive lower and upper period bounds
on a closed interior level band compare the weighted and unweighted measures. Integer
translates of the fundamental window handle all angular seams. The classical transport
chain rules are also proved, including the reverse rule for smooth periodic strip tests.
Angular test periodization and a compact angular partition of unity give both directions
of `hasWeakL0On_iff_actionAngle`. The angular full-gradient chain rule is then a
consequence of `HasWeakPartialOn.hasWeakL0On` (in `Transport.lean`) and that transport
rule, using `∂_θ P = S Y`. Local integrability of the candidate pullback gradient follows
separately from smoothness of `P` and local `L¹` transfer. The level rule uses the smooth
phase `E = exp(2πiθ)` to construct `levelDualCoeff = (angleGrad 1, -angleGrad 0)`.
Its divergence vanishes a.e. by local symmetry of mixed derivatives. Inverse-coordinate
identities and the flow column give `2 S B = ∂_h P` off the cut. Testing the two weak
partials against `Bⱼ ψ` cancels the divergence; the area density cancels the normalization.
Angular periodization, including commutation with `∂_h`, transfers the identity to every
compact strip test. Neither forward rule needs Sobolev approximation.

The reverse full-gradient rule is also proved by direct tests. On the strip write the
cofactor column for `∂_j` as `A_j = (∂_θ Q_j, -∂_h Q_j)`, with `Q_0 = P₂`, `Q_1 = -P₁`.
Its divergence is zero by symmetry of mixed derivatives, and its entries are the area
density `2 S` times the two inverse-coordinate derivatives. Multiplying the pullback of
a cell test by these entries, extending by zero in the level direction and cutting off
with the angular partition gives genuine compact strip tests. Periodization removes the
angular cutoff, the Piola cancellation removes the zeroth-order terms, and the area
formula transfers the resulting weak identity to the whole punctured cell, across the seam.
Only `F` is assumed pointwise periodic: uniqueness of weak derivatives applied to integer
angular translates first gives a.e. periodicity of each supplied `G_i`. Averaging with the
angular partition provides exactly periodic representatives. The measure-preserving
coordinate map transfers their a.e. equality back to the cell. The smooth `angleGrad` handles
local integrability across the cut; it agrees with the raw angle partial off a null line.
No local Sobolev approximation or independent seam-gluing theorem is needed.

The commutator `transversalMollifier_hasWeakL0On` uses only the transport chain rule: the
level cutoff carries `∂_θ U = S K` from the strip to the plane, `∂_θ` commutes with `M_ε`,
the reverse chain rule gives `L₀ J_ε u = σ⁻¹ M_ε(σχK)` on the punctured cell with `σ` a
Lipschitz extension of `S` off the band, and the identity extends by zero to the plane. The
error is `σ⁻¹ (M_ε(σχK) - σ M_ε(χK))`, bounded by the Lipschitz commutator of
`LineMollifier.lean`.

The derivatives of `J_ε u` are `coordGrad`: `∂ⱼh · M_ε'(χU) + ∂ⱼθ · M_ε(∂_θ(χU))` pulled
back to the cell. Since the angle jumps across its cut, `∂ⱼθ` is replaced by `angleGrad`,
`conj(E) ∂ⱼE / (2πi)` with `E = e^{2πiθ}` smooth on the punctured cell; it agrees with
`∂ⱼθ` off the cut, a null line. `exists_coordGrad_bound` bounds `coordGrad` in `L²` for
band-supported cylinder data. For the `H¹` convergence the limit is identified with
`∇(χ(Ψ/2) u)` pointwise off the cut by the classical chain rule `chainRule_actionAngle`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal

/-! ### The classical transport chain rule -/

/-- The angular derivative of a differentiable test function is `S(h) L₀φ`. -/
theorem partialY_comp_actionAngleInv {φ : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hφ : DifferentiableAt ℝ φ (actionAngleInv q)) :
    partialY (φ ∘ actionAngleInv) q =
      orbitPeriod q.1 • classicalL0 φ (actionAngleInv q) := by
  have hd := hφ.hasFDerivAt.comp_hasDerivAt q.2 (hasDerivAt_actionAngleInv_snd q.1 q.2)
  change deriv (φ ∘ fun θ ↦ actionAngleInv (q.1, θ)) q.2 = _
  rw [hd.deriv, map_smul]
  congr 1
  rw [classicalL0, partialX_eq_fderiv hφ, partialY_eq_fderiv hφ,
    ← map_smul, ← map_smul, ← map_sub]
  congr 1
  ext <;> simp [dipoleVelocity]

/-! ### The mollifier (`def:transversal-mollifier`) -/

open scoped Classical in
/-- The cutoff `χ(Ψ/2)` on the cell square, extended by zero. -/
def cellCutoff (χ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := if p ∈ cellSquare then χ (levelCoord p) else 0

open scoped Classical in
/-- The transversal mollifier `J_ε u = M_ε(χ U) ∘ (h, θ)` on the punctured cell, with
    `U = u ∘ (h, θ)⁻¹`, and zero elsewhere. -/
def transversalMollifier (χ : ℝ → ℝ) (ε : ℝ) (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if p ∈ puncturedCell then
    mollifyFst ε (fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) (actionAngle p)
  else 0

/-- A closed level band in the closed diagonal cell square. -/
private def closedCellLevelBand (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | |(diagCoord p).1| ≤ Real.pi / 2 ∧ |(diagCoord p).2| ≤ Real.pi / 2 ∧
    a ≤ levelCoord p ∧ levelCoord p ≤ b}

private theorem isCompact_closedCellLevelBand (a b : ℝ) :
    IsCompact (closedCellLevelBand a b) := by
  have hd₁ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) := by
    unfold diagCoord
    fun_prop
  have hd₂ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) := by
    unfold diagCoord
    fun_prop
  have hl : Continuous levelCoord := by
    unfold levelCoord dipoleLift
    fun_prop
  have hc : IsClosed (closedCellLevelBand a b) :=
    (isClosed_le hd₁ continuous_const).inter
      ((isClosed_le hd₂ continuous_const).inter
        ((isClosed_le continuous_const hl).inter (isClosed_le hl continuous_const)))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
    (show closedCellLevelBand a b ⊆
      Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi from ?_)
  intro p hp
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp hp.1
  obtain ⟨h₂l, h₂u⟩ := abs_le.mp hp.2.1
  have hx : p.1 = (diagCoord p).1 + (diagCoord p).2 := by
    simp only [diagCoord]
    ring
  have hy : p.2 = (diagCoord p).1 - (diagCoord p).2 := by
    simp only [diagCoord]
    ring
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem closedCellLevelBand_subset {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    closedCellLevelBand a b ⊆ puncturedCell := by
  intro p hp
  have hprod : levelCoord p = Real.cos (diagCoord p).1 * Real.cos (diagCoord p).2 := by
    rw [levelCoord, dipoleLift_eq_diag]
    ring
  have hstrict : ∀ x : ℝ, |x| ≤ Real.pi / 2 → Real.cos x ≠ 0 → |x| < Real.pi / 2 := by
    intro x hx hn
    by_contra h
    have he : |x| = Real.pi / 2 := le_antisymm hx (le_of_not_gt h)
    apply hn
    rw [← Real.cos_abs, he, Real.cos_pi_div_two]
  have hc : p ∈ cellSquare := by
    refine ⟨hstrict _ hp.1 ?_, hstrict _ hp.2.1 ?_⟩
    · intro hz
      rw [hz, zero_mul] at hprod
      linarith [hp.2.2.1]
    · intro hz
      rw [hz, mul_zero] at hprod
      linarith [hp.2.2.1]
  refine ⟨hc, ?_⟩
  intro hz
  have he : p = 0 := mem_singleton_iff.mp hz
  have hl : levelCoord p = 1 := by simp [he, levelCoord, dipoleLift]
  linarith [hp.2.2.2]

/-- One fundamental rectangle for the action-angle parametrization. -/
private def actionRectangle : Set (ℝ × ℝ) :=
  Ioo 0 1 ×ˢ Ico (-1 / 4 : ℝ) (3 / 4)

private theorem measurableSet_actionRectangle : MeasurableSet actionRectangle :=
  measurableSet_Ioo.prod measurableSet_Ico

private def actionMeasure : Measure (ℝ × ℝ) := volume.restrict actionRectangle

private def cylinderMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4)))

private theorem actionMeasure_eq_prod : actionMeasure =
    (volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))) :=
  (Measure.prod_restrict _ _).symm

private theorem cylinder_restrict_level :
    cylinderMeasure.restrict (Ioo (0 : ℝ) 1 ×ˢ univ) = actionMeasure := by
  simp only [cylinderMeasure, ← Measure.prod_restrict, Measure.restrict_univ,
    ← actionMeasure_eq_prod]

private theorem actionMeasure_le_cylinder : actionMeasure ≤ cylinderMeasure := by
  rw [← cylinder_restrict_level]
  exact Measure.restrict_le_self

private theorem continuousOn_actionParam : ContinuousOn actionAngleInv actionRectangle :=
  contDiffOn_actionAngleInv.continuousOn.mono (fun _ hq ↦ ⟨hq.1, mem_univ _⟩)

open scoped Classical in
private def actionParam : ℝ × ℝ → ℝ × ℝ :=
  actionRectangle.piecewise actionAngleInv (fun _ ↦ 0)

private theorem measurable_actionParam : Measurable actionParam := by
  classical
  exact continuousOn_actionParam.measurable_piecewise continuous_const.continuousOn
    measurableSet_actionRectangle

open scoped Classical in
private def actionPeriod : ℝ → ℝ :=
  (Ioo (0 : ℝ) 1).piecewise orbitPeriod (fun _ ↦ 0)

private theorem measurable_actionPeriod : Measurable actionPeriod := by
  classical
  exact contDiffOn_orbitPeriod.continuousOn.measurable_piecewise
    continuous_const.continuousOn measurableSet_Ioo

private def actionWeight (q : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (2 * actionPeriod q.1)

private theorem measurable_actionWeight : Measurable actionWeight := by
  exact (measurable_const.mul (measurable_actionPeriod.comp measurable_fst)).ennreal_ofReal

private theorem actionWeight_ne_zero : ∀ᵐ q ∂actionMeasure, actionWeight q ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
  have hS := orbitPeriod_pos hq.1.1 hq.1.2
  have hw : actionWeight q = ENNReal.ofReal (2 * orbitPeriod q.1) := by
    simp [actionWeight, actionPeriod, hq.1]
  rw [hw]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

private theorem measurePreserving_actionParam :
    MeasurePreserving actionParam (actionMeasure.withDensity actionWeight)
      (volume.restrict cellSquare) := by
  classical
  refine ⟨measurable_actionParam, Measure.ext_of_lintegral _ fun f hf ↦ ?_⟩
  rw [lintegral_map' hf.aemeasurable measurable_actionParam.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul actionMeasure measurable_actionWeight
      (g := fun q ↦ f (actionParam q)) (hf.comp measurable_actionParam), actionMeasure_eq_prod]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun q ↦ actionWeight q * f (actionParam q))
    (show AEMeasurable (fun q ↦ actionWeight q * f (actionParam q)) _ from
      (measurable_actionWeight.mul (hf.comp measurable_actionParam)).aemeasurable),
    lintegral_cellSquare_actionAngle hf]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with θ hθ
  simp [actionWeight, actionPeriod, actionParam, actionRectangle, Set.piecewise, hh, hθ]

private theorem injOn_actionAngleInv : InjOn actionAngleInv actionRectangle := by
  intro q hq q' hq' he
  have h₁ := actionAngle_actionAngleInv hq.1.1 hq.1.2 hq.2
  have h₂ := actionAngle_actionAngleInv hq'.1.1 hq'.1.2 hq'.2
  exact h₁.symm.trans ((congrArg actionAngle he).trans h₂)

private theorem actionAngle_mem_rectangle {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    actionAngle p ∈ actionRectangle := by
  have hd := mem_orbitDomain hp
  have hS := orbitPeriod_pos hd.1.1 hd.1.2
  refine ⟨hd.1, ?_, ?_⟩
  · apply (le_div_iff₀ hS).mpr
    have h := hd.2.1
    dsimp [orbitPeriod] at *
    linarith
  · apply (div_lt_iff₀ hS).mpr
    have h := hd.2.2
    dsimp [orbitPeriod] at *
    linarith

/-- Extend the inverse of the parametrization measurably across its complement. -/
private def actionCoordinates : ℝ × ℝ → ℝ × ℝ :=
  Function.extend (actionRectangle.domRestrict actionAngleInv) Subtype.val (fun _ ↦ 0)

private theorem measurableEmbedding_actionParam :
    MeasurableEmbedding (actionRectangle.domRestrict actionAngleInv) :=
  continuousOn_actionParam.measurableEmbedding measurableSet_actionRectangle injOn_actionAngleInv

private theorem measurable_actionCoordinates : Measurable actionCoordinates :=
  measurableEmbedding_actionParam.measurable_extend measurable_subtype_coe measurable_const

private theorem actionCoordinates_actionAngleInv {q : ℝ × ℝ} (hq : q ∈ actionRectangle) :
    actionCoordinates (actionAngleInv q) = q :=
  measurableEmbedding_actionParam.injective.extend_apply _ _ ⟨q, hq⟩

private theorem actionCoordinates_eq_actionAngle {p : ℝ × ℝ} (hp : p ∈ puncturedCell) :
    actionCoordinates p = actionAngle p := by
  have h := actionCoordinates_actionAngleInv (actionAngle_mem_rectangle hp)
  rwa [actionAngleInv_actionAngle hp] at h

private theorem measurePreserving_actionCoordinates :
    MeasurePreserving actionCoordinates (volume.restrict cellSquare)
      (actionMeasure.withDensity actionWeight) := by
  refine ⟨measurable_actionCoordinates, ?_⟩
  rw [← measurePreserving_actionParam.map_eq,
    Measure.map_map measurable_actionCoordinates measurable_actionParam]
  calc
    Measure.map (actionCoordinates ∘ actionParam) (actionMeasure.withDensity actionWeight) =
        Measure.map id (actionMeasure.withDensity actionWeight) := by
      apply Measure.map_congr
      have hac := withDensity_absolutelyContinuous actionMeasure actionWeight
      filter_upwards [hac.ae_le (ae_restrict_mem measurableSet_actionRectangle)] with q hq
      change actionCoordinates (actionParam q) = q
      have hp : actionParam q = actionAngleInv q := by simp [actionParam, Set.piecewise, hq]
      rw [hp]
      exact actionCoordinates_actionAngleInv hq
    _ = _ := Measure.map_id

private theorem measurableSet_cellSquare : MeasurableSet cellSquare := by
  have h₁ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) := by unfold diagCoord; fun_prop
  have h₂ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) := by unfold diagCoord; fun_prop
  exact (isOpen_lt h₁ continuous_const).measurableSet.inter
    (isOpen_lt h₂ continuous_const).measurableSet

open scoped Classical in
private def actionReconstruct (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  cellSquare.indicator (F ∘ actionCoordinates)

private theorem memLp_actionReconstruct {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (actionMeasure.withDensity actionWeight)) :
    MemLp (actionReconstruct F) 2 volume ∧
      eLpNorm (actionReconstruct F) 2 volume =
        eLpNorm F 2 (actionMeasure.withDensity actionWeight) := by
  refine ⟨(memLp_indicator_iff_restrict measurableSet_cellSquare).mpr
    (hF.comp_measurePreserving measurePreserving_actionCoordinates), ?_⟩
  rw [actionReconstruct, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_cellSquare]
  exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
    measurePreserving_actionCoordinates

/-! ### Local `L¹` transfer on interior bands -/

private theorem closedCellLevelBand_eq {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    closedCellLevelBand a b = {p | p ∈ puncturedCell ∧ levelCoord p ∈ Icc a b} := by
  ext p
  constructor
  · intro hp
    exact ⟨closedCellLevelBand_subset ha hb hp, hp.2.2⟩
  · rintro ⟨hp, hlev⟩
    exact ⟨hp.1.1.le, hp.1.2.le, hlev⟩

/-- Local integrability on the cell transfers to a fundamental angular window on every
closed interior level band. No global integrability of the input is assumed. -/
theorem integrableOn_comp_actionAngleInv_levelBand {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {u : ℝ × ℝ → ℂ} (hu : LocallyIntegrableOn u puncturedCell) :
    IntegrableOn (u ∘ actionAngleInv) (Icc a b ×ˢ Ico (-1 / 4 : ℝ) (3 / 4)) := by
  classical
  let B := closedCellLevelBand a b
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Ico (-1 / 4 : ℝ) (3 / 4)
  let σ : Measure (ℝ × ℝ) := volume.restrict R
  have hB : IsCompact B := isCompact_closedCellLevelBand a b
  have hG : Integrable (B.indicator u) := (integrable_indicator_iff hB.measurableSet).mpr
    (hu.integrableOn_compact_subset (closedCellLevelBand_subset ha hb) hB)
  have hU := (measurePreserving_actionParam.integrable_comp
    hG.integrableOn.aestronglyMeasurable).mpr hG.integrableOn
  have hR : R ⊆ actionRectangle := fun q hq ↦
    ⟨⟨lt_of_lt_of_le ha hq.1.1, lt_of_le_of_lt hq.1.2 hb⟩, hq.2⟩
  have hσ : σ ≤ actionMeasure := Measure.restrict_mono hR le_rfl
  have hac : actionMeasure ≪ actionMeasure.withDensity actionWeight :=
    withDensity_absolutelyContinuous' measurable_actionWeight.aemeasurable actionWeight_ne_zero
  have heq : (fun q ↦ B.indicator u (actionParam q)) =ᵐ[σ] u ∘ actionAngleInv := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ico)] with q hq
    have hqr := hR hq
    have hP := actionAngleInv_mem_puncturedCell hqr.1.1 hqr.1.2 q.2
    have hPB : actionAngleInv q ∈ B := by
      change actionAngleInv q ∈ closedCellLevelBand a b
      rw [closedCellLevelBand_eq ha hb]
      exact ⟨hP, by simpa only [levelCoord_actionAngleInv hqr.1.1 hqr.1.2] using hq.1⟩
    simp [actionParam, Set.piecewise, hqr, Set.indicator_of_mem hPB]
  have hm := ((hU.aestronglyMeasurable.mono_ac hac).mono_measure hσ).congr heq
  have hw := (integrable_withDensity_iff_integrable_smul' measurable_actionWeight
    (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))).mp hU.norm
  have hw' := (hw.mono_measure hσ)
  have hc : ContinuousOn (fun h ↦ (2 * orbitPeriod h)⁻¹) (Icc a b) :=
    (continuousOn_const.mul (contDiffOn_orbitPeriod.continuousOn.mono
      (fun h hh ↦ ⟨lt_of_lt_of_le ha hh.1, lt_of_le_of_lt hh.2 hb⟩))).inv₀
      (fun h hh ↦ (mul_pos (by norm_num)
        (orbitPeriod_pos (lt_of_lt_of_le ha hh.1) (lt_of_le_of_lt hh.2 hb))).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  apply (hw'.const_mul (max C 0)).mono' hm
  filter_upwards [heq, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ico)] with q he hq
  have hqr := hR hq
  have hS := mul_pos (by norm_num : (0 : ℝ) < 2) (orbitPeriod_pos hqr.1.1 hqr.1.2)
  have hbound : 1 ≤ max C 0 * (2 * orbitPeriod q.1) := by
    have hi := (hC (mem_image_of_mem _ hq.1)).trans (le_max_left C 0)
    have hm := mul_le_mul_of_nonneg_right hi hS.le
    simpa only [inv_mul_cancel₀ hS.ne'] using hm
  have hwq : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
    simp [actionWeight, actionPeriod, hqr.1, (orbitPeriod_pos hqr.1.1 hqr.1.2).le]
  change ‖(u ∘ actionAngleInv) q‖ ≤
    max C 0 * ((actionWeight q).toReal • ‖B.indicator u (actionParam q)‖)
  rw [he, hwq, smul_eq_mul]
  simpa only [one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hbound (norm_nonneg ((u ∘ actionAngleInv) q))

private theorem integrableOn_comp_actionAngleInv_shift {a b : ℝ} (ha : 0 < a)
    (hb : b < 1) {u : ℝ × ℝ → ℂ} (hu : LocallyIntegrableOn u puncturedCell) (n : ℤ) :
    IntegrableOn (u ∘ actionAngleInv)
      (Icc a b ×ˢ Ico ((n : ℝ) - 1 / 4) ((n : ℝ) + 3 / 4)) := by
  classical
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Ico (-1 / 4 : ℝ) (3 / 4)
  let T : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1, q.2 - (n : ℝ))
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Ico
  have hi := (integrable_indicator_iff hR).mpr
    (integrableOn_comp_actionAngleInv_levelBand ha hb hu)
  have hT : MeasurePreserving T volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (measurePreserving_sub_right volume (n : ℝ))
  have ht := (hT.integrable_comp hi.aestronglyMeasurable).mpr hi
  rw [← integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Ico)]
  apply ht.congr (Filter.Eventually.of_forall ?_)
  intro q
  have hmem : T q ∈ R ↔ q ∈ Icc a b ×ˢ Ico ((n : ℝ) - 1 / 4) ((n : ℝ) + 3 / 4) := by
    simp only [T, R, mem_prod, mem_Ico]
    constructor <;> rintro ⟨h, h₁, h₂⟩ <;> exact ⟨h, by linarith, by linarith⟩
  by_cases hq : T q ∈ R
  · have hper : Function.Periodic (fun θ ↦ u (actionAngleInv (q.1, θ))) 1 :=
      fun θ ↦ congrArg u (actionAngleInv_add_one
        (lt_of_lt_of_le ha hq.1.1) (lt_of_le_of_lt hq.1.2 hb) θ)
    have he := hper.sub_int_mul_eq (x := q.2) n
    rw [Function.comp_apply, Set.indicator_of_mem hq, Set.indicator_of_mem (hmem.mp hq)]
    simpa only [Function.comp_apply, T, mul_one] using he
  · rw [Function.comp_apply, Set.indicator_of_notMem hq,
      Set.indicator_of_notMem (mt hmem.mpr hq)]

/-- Local integrability pulls back to the whole strip, including across every angular seam. -/
theorem locallyIntegrableOn_comp_actionAngleInv {u : ℝ × ℝ → ℂ}
    (hu : LocallyIntegrableOn u puncturedCell) :
    LocallyIntegrableOn (u ∘ actionAngleInv) actionStrip := by
  intro q hq
  have h0 : 0 < q.1 := hq.1.1
  have h1 : q.1 < 1 := hq.1.2
  let a := q.1 / 2
  let b := (q.1 + 1) / 2
  let n : ℤ := ⌊q.2 + 1 / 4⌋
  let R : ℤ → Set (ℝ × ℝ) := fun m ↦
    Icc a b ×ˢ Ico ((m : ℝ) - 1 / 4) ((m : ℝ) + 3 / 4)
  have hi : ∀ m, IntegrableOn (u ∘ actionAngleInv) (R m) := fun m ↦
    integrableOn_comp_actionAngleInv_shift (by dsimp [a]; linarith)
      (by dsimp [b]; linarith) hu m
  refine ⟨R n ∪ R (n - 1), ?_, (hi n).union (hi (n - 1))⟩
  have hnlo := Int.floor_le (q.2 + 1 / 4)
  have hnhi := Int.lt_floor_add_one (q.2 + 1 / 4)
  have hmem : Icc a b ×ˢ Ioo ((n : ℝ) - 5 / 4) ((n : ℝ) + 3 / 4) ∈ 𝓝 q := by
    apply prod_mem_nhds
    · apply Icc_mem_nhds <;> dsimp [a, b] <;> linarith
    · apply Ioo_mem_nhds <;> dsimp [n] <;> linarith
  apply nhdsWithin_le_nhds (Filter.mem_of_superset hmem ?_)
  intro z hz
  by_cases hzn : (n : ℝ) - 1 / 4 ≤ z.2
  · exact Or.inl ⟨hz.1, hzn, hz.2.2⟩
  · apply Or.inr
    change z.1 ∈ Icc a b ∧ z.2 ∈ Ico (((n - 1 : ℤ) : ℝ) - 1 / 4)
      (((n - 1 : ℤ) : ℝ) + 3 / 4)
    push_cast
    exact ⟨hz.1, by linarith [hz.2.1], by linarith⟩

/-- Pull back arbitrary representatives, not just measurable ones. -/
private theorem ae_comp_actionParam {u v : ℝ × ℝ → ℂ}
    (huv : u =ᵐ[volume.restrict cellSquare] v) :
    (fun q ↦ u (actionParam q)) =ᵐ[actionMeasure] (fun q ↦ v (actionParam q)) := by
  apply (withDensity_ae_eq measurable_actionWeight.aemeasurable actionWeight_ne_zero).mp
  exact measurePreserving_actionParam.quasiMeasurePreserving.ae_eq_comp huv

/-- A null set of parameters in the fundamental rectangle has null planar image. -/
private theorem volume_actionAngleInv_image_eq_zero {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) (hBR : B ⊆ actionRectangle) (hB0 : actionMeasure B = 0) :
    volume (actionAngleInv '' B) = 0 := by
  classical
  have hi : MeasurableSet (actionAngleInv '' B) :=
    hB.image_of_continuousOn_injOn (continuousOn_actionParam.mono hBR)
      (injOn_actionAngleInv.mono hBR)
  let ν := actionMeasure.withDensity actionWeight
  have hac : ν ≪ actionMeasure := withDensity_absolutelyContinuous _ _
  have hfull : ∀ᵐ q ∂ν, q ∈ actionRectangle :=
    hac.ae_le (ae_restrict_mem measurableSet_actionRectangle)
  have hnot : ∀ᵐ q ∂ν, q ∉ B :=
    hac.ae_le (measure_eq_zero_iff_ae_notMem.mp hB0)
  have hpre : ∀ᵐ q ∂ν, q ∉ actionParam ⁻¹' (actionAngleInv '' B) := by
    filter_upwards [hfull, hnot] with q hq hn
    rintro ⟨s, hs, he⟩
    have hparam : actionAngleInv q = actionParam q := by
      simp [actionParam, Set.piecewise, hq]
    have heq := injOn_actionAngleInv (hBR hs) hq (he.trans hparam.symm)
    exact hn (heq ▸ hs)
  have hnull : ν (actionParam ⁻¹' (actionAngleInv '' B)) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hpre
  have hcell : (volume.restrict cellSquare) (actionAngleInv '' B) = 0 :=
    (measurePreserving_actionParam.measure_preimage hi.nullMeasurableSet).symm.trans hnull
  have hsub : actionAngleInv '' B ⊆ cellSquare := by
    rintro _ ⟨q, hq, rfl⟩
    exact (actionAngleInv_mem_puncturedCell (hBR hq).1.1 (hBR hq).1.2 q.2).1
  rwa [Measure.restrict_apply hi, inter_eq_left.mpr hsub] at hcell

/-- Squared `L²` norms expressed by real integrals. -/
private theorem eLpNorm_two_sq {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ENNReal.ofReal (∫ q, ‖f q‖ ^ 2 ∂μ) := by
  calc
    _ = ∫⁻ q, ‖f q‖ₑ ^ (2 : ℝ) ∂μ :=
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf.aestronglyMeasurable
    _ = ∫⁻ q, ENNReal.ofReal (‖f q‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with q
      simp [ENNReal.ofReal_pow]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
      (Filter.Eventually.of_forall (fun q ↦ sq_nonneg ‖f q‖))).symm

private theorem eLpNorm_two_le_of_integral_sq_le {μ ν : Measure (ℝ × ℝ)}
    {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) (C : ℝ≥0)
    (hI : (∫ q, ‖f q‖ ^ 2 ∂μ) ≤ (C : ℝ) ^ 2 * ∫ q, ‖g q‖ ^ 2 ∂ν) :
    eLpNorm f 2 μ ≤ C * eLpNorm g 2 ν := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  calc
    _ = ENNReal.ofReal (∫ q, ‖f q‖ ^ 2 ∂μ) := eLpNorm_two_sq hf
    _ ≤ ENNReal.ofReal ((C : ℝ) ^ 2 * ∫ q, ‖g q‖ ^ 2 ∂ν) := ENNReal.ofReal_le_ofReal hI
    _ = (C : ENNReal) ^ 2 * eLpNorm g 2 ν ^ (2 : ℝ) := by
      rw [eLpNorm_two_sq hg]
      simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow]
    _ = _ := by simp [mul_pow]

/-- Cutoff multiplication compensates for removing the area density. -/
private theorem cutoff_sq_le_period {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ tsupport χ, χ h ^ 2 ≤ C * (2 * orbitPeriod h) := by
  have hK : IsCompact (tsupport χ) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).of_isClosed_subset (isClosed_tsupport χ)
      (fun h hh ↦ ⟨(hχs hh).1.le, (hχs hh).2.le⟩)
  have hcont : ContinuousOn (fun h ↦ χ h ^ 2 / (2 * orbitPeriod h)) (tsupport χ) :=
    (hχ.continuous.pow 2).continuousOn.div
      (continuousOn_const.mul (contDiffOn_orbitPeriod.continuousOn.mono hχs))
      (fun h hh ↦ (mul_pos (by norm_num) (orbitPeriod_pos (hχs hh).1 (hχs hh).2)).ne')
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨max C 0, le_max_right _ _, fun h hh ↦ ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) (orbitPeriod_pos (hχs hh).1 (hχs hh).2))).mp
  exact (hC (mem_image_of_mem _ hh)).trans (le_max_left _ _)

private theorem memLp_cutoff_actionMeasure {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) :
    MemLp (fun q ↦ (χ q.1 : ℂ) * u (actionParam q)) 2 actionMeasure := by
  have hU := hu.comp_measurePreserving measurePreserving_actionParam
  have hac : actionMeasure ≪ actionMeasure.withDensity actionWeight :=
    withDensity_absolutelyContinuous' measurable_actionWeight.aemeasurable actionWeight_ne_zero
  have hmU := hU.aestronglyMeasurable.mono_ac hac
  have hmχ : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ)) actionMeasure :=
    (Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_fst)).aestronglyMeasurable
  have hmF : AEStronglyMeasurable (fun q ↦ (χ q.1 : ℂ) * u (actionParam q))
      actionMeasure := hmχ.mul hmU
  have hsq := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hint : Integrable (fun q ↦ (actionWeight q).toReal * ‖u (actionParam q)‖ ^ 2)
      actionMeasure := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (integrable_withDensity_iff_integrable_smul' measurable_actionWeight
        (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))).mp hsq
  obtain ⟨C, hC, hbound⟩ := cutoff_sq_le_period hχ hχs
  apply (memLp_two_iff_integrable_sq_norm hmF).mpr
  apply (hint.const_mul C).mono' (hmF.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
  change ‖‖(χ q.1 : ℂ) * u (actionParam q)‖ ^ 2‖ ≤
    C * ((actionWeight q).toReal * ‖u (actionParam q)‖ ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hz : χ q.1 = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg hC (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  · have hs : q.1 ∈ tsupport χ := subset_closure hz
    have hw : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
      simp [actionWeight, actionPeriod, hq.1, (orbitPeriod_pos hq.1.1 hq.1.2).le]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hw]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hbound q.1 hs) (sq_nonneg ‖u (actionParam q)‖)

private theorem memLp_cutoff_actionInput {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) :
    MemLp (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) 2
      ((volume : Measure ℝ).prod (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4)))) := by
  classical
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)
  let σ := (volume : Measure ℝ).prod (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4)))
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have hrestrict : σ.restrict S = actionMeasure := by
    simp only [σ, S, ← Measure.prod_restrict, Measure.restrict_univ, ← actionMeasure_eq_prod]
  have hmem : MemLp F 2 (σ.restrict S) := by
    rw [hrestrict]
    refine MemLp.ae_eq ?_ (memLp_cutoff_actionMeasure hχ hχs hu)
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    simp [F, actionParam, Set.piecewise, hq]
  have heq : S.indicator F = F := by
    funext q
    by_cases hq : q ∈ S
    · simp [hq]
    · have h01 : q.1 ∉ Ioo (0 : ℝ) 1 := by simpa [S] using hq
      have hz : χ q.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ h01 (hχs hs))
      simp [hq, F, hz]
  have hi := (memLp_indicator_iff_restrict hS).mpr hmem
  rwa [heq] at hi

private theorem eLpNorm_actionInput_eq {χ : ℝ → ℝ} (hχs : tsupport χ ⊆ Ioo 0 1)
    (u : ℝ × ℝ → ℂ) :
    eLpNorm (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) 2 cylinderMeasure =
      eLpNorm (fun q ↦ (χ q.1 : ℂ) * u (actionParam q)) 2 actionMeasure := by
  classical
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have heq : S.indicator F = F := by
    funext q
    by_cases hq : q ∈ S
    · simp [hq]
    · have h01 : q.1 ∉ Ioo (0 : ℝ) 1 := by simpa [S] using hq
      have hz : χ q.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ h01 (hχs hs))
      simp [hq, F, hz]
  calc
    _ = eLpNorm (S.indicator F) 2 cylinderMeasure := by rw [heq]
    _ = eLpNorm F 2 actionMeasure := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hS, cylinder_restrict_level]
    _ = _ := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
      simp [F, actionParam, Set.piecewise, hq]

private theorem eLpNorm_cutoff_actionInput_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ C : ℝ≥0, ∀ u, MemLp u 2 (volume.restrict cellSquare) →
      eLpNorm (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) 2 cylinderMeasure ≤
        C * eLpNorm u 2 (volume.restrict cellSquare) := by
  obtain ⟨D, hD, hbound⟩ := cutoff_sq_le_period hχ hχs
  let C : ℝ≥0 := ⟨Real.sqrt D, Real.sqrt_nonneg D⟩
  have hC : (C : ℝ) ^ 2 = D := Real.sq_sqrt hD
  refine ⟨C, fun u hu ↦ ?_⟩
  have hU := hu.comp_measurePreserving measurePreserving_actionParam
  have hG := memLp_cutoff_actionMeasure hχ hχs hu
  have hint : Integrable (fun q ↦ (actionWeight q).toReal * ‖u (actionParam q)‖ ^ 2)
      actionMeasure := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (integrable_withDensity_iff_integrable_smul' measurable_actionWeight
        (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))).mp
        ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU)
  have hpoint : ∀ᵐ q ∂actionMeasure, ‖(χ q.1 : ℂ) * u (actionParam q)‖ ^ 2 ≤
      D * ((actionWeight q).toReal * ‖u (actionParam q)‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    by_cases hz : χ q.1 = 0
    · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
      exact mul_nonneg hD (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    · have hs : q.1 ∈ tsupport χ := subset_closure hz
      have hw : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
        simp [actionWeight, actionPeriod, hq.1, (orbitPeriod_pos hq.1.1 hq.1.2).le]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hw]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hbound q.1 hs) (sq_nonneg ‖u (actionParam q)‖)
  have hI : (∫ q, ‖(χ q.1 : ℂ) * u (actionParam q)‖ ^ 2 ∂actionMeasure) ≤
      D * ∫ q, ‖u (actionParam q)‖ ^ 2 ∂actionMeasure.withDensity actionWeight := by
    calc
      _ ≤ ∫ q, D * ((actionWeight q).toReal * ‖u (actionParam q)‖ ^ 2) ∂actionMeasure :=
        integral_mono_ae ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG)
          (hint.const_mul D) hpoint
      _ = _ := by
        rw [integral_const_mul, integral_withDensity_eq_integral_toReal_smul
          measurable_actionWeight (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))]
        rfl
  rw [eLpNorm_actionInput_eq hχs]
  calc
    _ ≤ C * eLpNorm (fun q ↦ u (actionParam q)) 2
        (actionMeasure.withDensity actionWeight) := by
      apply eLpNorm_two_le_of_integral_sq_le hG hU C
      simpa only [hC, Function.comp_apply] using hI
    _ = _ := congrArg (fun x : ENNReal ↦ (C : ENNReal) * x)
      (eLpNorm_comp_measurePreserving hu.aestronglyMeasurable measurePreserving_actionParam)

/-- Almost every angular line of an `L²` input is itself `L²`. -/
private theorem ae_memLp_action_lines {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 ((volume : Measure ℝ).prod
      (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))))) :
    ∀ᵐ θ ∂(volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))),
      MemLp (fun h ↦ F (h, θ)) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  filter_upwards [hF.aestronglyMeasurable.prodMk_right, hi.prod_left_ae] with θ hm hθ
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hθ

private theorem integrable_mollify_line {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    Integrable (fun t ↦ mollifierKernel ε (x - t) • f t) := by
  have hs : HasCompactSupport (fun t : ℝ ↦ (mollifierKernel ε t : ℂ)) :=
    (hasCompactSupport_mollifierKernel hε).comp_left (g := Complex.ofReal) (by simp)
  have hk₀ : MemLp (fun t : ℝ ↦ (mollifierKernel ε t : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp (contDiff_mollifierKernel ε).continuous)
      |>.memLp_of_hasCompactSupport hs
  have hk : MemLp (fun t : ℝ ↦ (mollifierKernel ε (x - t) : ℂ)) 2 volume :=
    hk₀.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hi : Integrable (fun t ↦ (mollifierKernel ε (x - t) : ℂ) * f t) :=
    hk.integrable_mul hf
  simpa only [Complex.real_smul] using hi

/-- A null set of exceptional angular lines gives a null set in the cell. -/
private theorem ae_of_ae_angle {P : ℝ → Prop}
    (hP : ∀ᵐ θ ∂(volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))), P θ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ puncturedCell → P (angleCoord p) := by
  classical
  obtain ⟨N, hcover, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  let B : Set (ℝ × ℝ) := actionRectangle ∩ Prod.snd ⁻¹' N
  have hB : MeasurableSet B := measurableSet_actionRectangle.inter (hN.preimage measurable_snd)
  have hB0 : actionMeasure B = 0 := by
    have havoid : ∀ᵐ q ∂actionMeasure, q.2 ∉ N := by
      rw [actionMeasure_eq_prod]
      exact Measure.quasiMeasurePreserving_snd.ae
        (measure_eq_zero_iff_ae_notMem.mp hN0)
    have hpre : actionMeasure (Prod.snd ⁻¹' N) = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr havoid
    exact measure_mono_null inter_subset_right hpre
  have himage := volume_actionAngleInv_image_eq_zero hB (show B ⊆ actionRectangle from
    inter_subset_left) hB0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp himage] with p hp
  intro hc
  by_contra hg
  exact hp ⟨actionAngle p, ⟨actionAngle_mem_rectangle hc, hcover hg⟩,
    actionAngleInv_actionAngle hc⟩

/-- Reconstruction is bounded for cylinder functions supported in a fixed interior level band. -/
private theorem exists_actionReconstruct_bound {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ C : ℝ≥0, ∀ F : ℝ × ℝ → ℂ, MemLp F 2 cylinderMeasure →
      (∀ q, q.1 ∉ Icc a b → F q = 0) →
      MemLp (actionReconstruct F) 2 volume ∧
        eLpNorm (actionReconstruct F) 2 volume ≤ C * eLpNorm F 2 cylinderMeasure := by
  have hcont : ContinuousOn (fun h ↦ 2 * orbitPeriod h) (Icc a b) :=
    continuousOn_const.mul (contDiffOn_orbitPeriod.continuousOn.mono
      (fun h hh ↦ ⟨lt_of_lt_of_le ha hh.1, lt_of_le_of_lt hh.2 hb⟩))
  obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image hcont
  let E := max D 0
  have hE : 0 ≤ E := le_max_right _ _
  let C : ℝ≥0 := ⟨Real.sqrt E, Real.sqrt_nonneg E⟩
  have hC : (C : ℝ) ^ 2 = E := Real.sq_sqrt hE
  refine ⟨C, fun F hF hzero ↦ ?_⟩
  have hFn := hF.mono_measure actionMeasure_le_cylinder
  have hmFw := hFn.aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous actionMeasure actionWeight)
  have hint := (memLp_two_iff_integrable_sq_norm hFn.aestronglyMeasurable).mp hFn
  have hpoint : ∀ᵐ q ∂actionMeasure,
      (actionWeight q).toReal * ‖F q‖ ^ 2 ≤ E * ‖F q‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    by_cases hband : q.1 ∈ Icc a b
    · have hw : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
        simp [actionWeight, actionPeriod, hq.1, (orbitPeriod_pos hq.1.1 hq.1.2).le]
      rw [hw]
      exact mul_le_mul_of_nonneg_right
        ((hD (mem_image_of_mem _ hband)).trans (le_max_left _ _)) (sq_nonneg _)
    · simp [hzero q hband]
  have hmg : AEStronglyMeasurable (fun q ↦ (actionWeight q).toReal * ‖F q‖ ^ 2)
      actionMeasure := measurable_actionWeight.ennreal_toReal.aestronglyMeasurable.mul
        (hFn.aestronglyMeasurable.norm.pow 2)
  have hg : Integrable (fun q ↦ (actionWeight q).toReal * ‖F q‖ ^ 2) actionMeasure := by
    apply (hint.const_mul E).mono' hmg
    filter_upwards [hpoint] with q hq
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))] using hq
  have hwint : Integrable (fun q ↦ ‖F q‖ ^ 2)
      (actionMeasure.withDensity actionWeight) := by
    apply (integrable_withDensity_iff_integrable_smul' measurable_actionWeight
      (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))).mpr
    simpa only [smul_eq_mul] using hg
  have hFw : MemLp F 2 (actionMeasure.withDensity actionWeight) :=
    (memLp_two_iff_integrable_sq_norm hmFw).mpr hwint
  have hI : (∫ q, ‖F q‖ ^ 2 ∂actionMeasure.withDensity actionWeight) ≤
      E * ∫ q, ‖F q‖ ^ 2 ∂actionMeasure := by
    calc
      _ = ∫ q, (actionWeight q).toReal * ‖F q‖ ^ 2 ∂actionMeasure := by
        rw [integral_withDensity_eq_integral_toReal_smul measurable_actionWeight
          (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))]
        rfl
      _ ≤ ∫ q, E * ‖F q‖ ^ 2 ∂actionMeasure := integral_mono_ae hg (hint.const_mul E) hpoint
      _ = _ := integral_const_mul _ _
  have hnorm := eLpNorm_two_le_of_integral_sq_le hFw hFn C (by simpa only [hC] using hI)
  have hrec := memLp_actionReconstruct hFw
  refine ⟨hrec.1, hrec.2.le.trans (hnorm.trans ?_)⟩
  exact mul_le_mul_of_nonneg_left (eLpNorm_mono_measure F actionMeasure_le_cylinder) bot_le

private theorem volume_origin_eq_zero : (volume : Measure (ℝ × ℝ)) {(0 : ℝ × ℝ)} = 0 := by
  change ((volume : Measure ℝ).prod volume) {(0 : ℝ × ℝ)} = 0
  exact measure_singleton _

open scoped Classical in
private theorem ae_actionReconstruct (F : ℝ × ℝ → ℂ) :
    actionReconstruct F =ᵐ[volume]
      (fun p ↦ if p ∈ puncturedCell then F (actionAngle p) else 0) := by
  classical
  have hne : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ {(0 : ℝ × ℝ)} :=
    measure_eq_zero_iff_ae_notMem.mp volume_origin_eq_zero
  filter_upwards [hne] with p hp
  by_cases hc : p ∈ cellSquare
  · have hpc : p ∈ puncturedCell := ⟨hc, hp⟩
    simp [actionReconstruct, hc, hpc, actionCoordinates_eq_actionAngle hpc]
  · have hpc : p ∉ puncturedCell := fun h ↦ hc h.1
    simp [actionReconstruct, hc, hpc]

private theorem actionReconstruct_sub (F G : ℝ × ℝ → ℂ) :
    actionReconstruct (F - G) = actionReconstruct F - actionReconstruct G := by
  classical
  funext p
  by_cases hc : p ∈ cellSquare <;> simp [actionReconstruct, hc]

private theorem ae_actionReconstruct_input (χ : ℝ → ℝ) (u : ℝ × ℝ → ℂ) :
    actionReconstruct (fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) =ᵐ[volume]
      (fun p ↦ (cellCutoff χ p : ℂ) * u p) := by
  classical
  have hne : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ {(0 : ℝ × ℝ)} :=
    measure_eq_zero_iff_ae_notMem.mp volume_origin_eq_zero
  filter_upwards [ae_actionReconstruct (fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)), hne]
    with p hp hn
  rw [hp]
  by_cases hc : p ∈ cellSquare
  · have hpc : p ∈ puncturedCell := ⟨hc, hn⟩
    rw [ite_eq_left hpc, actionAngleInv_actionAngle hpc]
    simp [cellCutoff, hc, actionAngle]
  · have hpc : p ∉ puncturedCell := fun h ↦ hc h.1
    simp [cellCutoff, hc, hpc]

/-! ### Local `L¹` reconstruction and periodic classical tests -/

/-- Local strip data reconstruct to an integrable planar function on any closed interior band. -/
theorem integrableOn_levelBand_of_comp_actionAngleInv {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {u : ℝ × ℝ → ℂ} (hu : LocallyIntegrableOn (u ∘ actionAngleInv) actionStrip) :
    IntegrableOn u {p | p ∈ puncturedCell ∧ levelCoord p ∈ Icc a b} := by
  classical
  let S : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a b}
  let F : ℝ × ℝ → ℂ := S.indicator (u ∘ actionAngleInv)
  have hS : MeasurableSet S := measurable_fst measurableSet_Icc
  have hRS : S ∩ actionRectangle = Icc a b ×ˢ Ico (-1 / 4 : ℝ) (3 / 4) := by
    ext q
    constructor
    · rintro ⟨hh, _, hθ⟩
      exact ⟨hh, hθ⟩
    · rintro ⟨hh, hθ⟩
      exact ⟨hh, ⟨lt_of_lt_of_le ha hh.1, lt_of_le_of_lt hh.2 hb⟩, hθ⟩
  have hInput := hu.integrableOn_compact_subset
    (show Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4) ⊆ actionStrip from fun q hq ↦
      ⟨⟨lt_of_lt_of_le ha hq.1.1, lt_of_le_of_lt hq.1.2 hb⟩, mem_univ _⟩)
    (isCompact_Icc.prod isCompact_Icc)
  have hF : Integrable F actionMeasure := by
    apply (integrable_indicator_iff hS).mpr
    rw [IntegrableOn, actionMeasure, Measure.restrict_restrict hS, hRS]
    exact hInput.mono_set (Set.prod_mono (Subset.refl _) Ico_subset_Icc_self)
  have hc : ContinuousOn (fun h ↦ 2 * orbitPeriod h) (Icc a b) :=
    continuousOn_const.mul (contDiffOn_orbitPeriod.continuousOn.mono
      (fun h hh ↦ ⟨lt_of_lt_of_le ha hh.1, lt_of_le_of_lt hh.2 hb⟩))
  obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image hc
  have hm : AEStronglyMeasurable (fun q ↦ (actionWeight q).toReal • F q) actionMeasure :=
    measurable_actionWeight.ennreal_toReal.aestronglyMeasurable.smul hF.aestronglyMeasurable
  have hw : Integrable (fun q ↦ (actionWeight q).toReal • F q) actionMeasure := by
    apply (hF.norm.const_mul (max D 0)).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    by_cases hh : q.1 ∈ Icc a b
    · have hwq : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
        simp [actionWeight, actionPeriod, hq.1, (orbitPeriod_pos hq.1.1 hq.1.2).le]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, hwq]
      exact mul_le_mul_of_nonneg_right
        ((hD (mem_image_of_mem _ hh)).trans (le_max_left _ _)) (norm_nonneg _)
    · have hz : F q = 0 := Set.indicator_of_notMem (show q ∉ S from hh) _
      simp only [hz, smul_zero, norm_zero, mul_zero, le_refl]
  have hFw : Integrable F (actionMeasure.withDensity actionWeight) :=
    (integrable_withDensity_iff_integrable_smul' measurable_actionWeight
      (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))).mpr hw
  have hrec : Integrable (actionReconstruct F) :=
    (integrable_indicator_iff measurableSet_cellSquare).mpr
      ((measurePreserving_actionCoordinates.integrable_comp hFw.aestronglyMeasurable).mpr hFw)
  have hB : MeasurableSet {p | p ∈ puncturedCell ∧ levelCoord p ∈ Icc a b} := by
    rw [← closedCellLevelBand_eq ha hb]
    exact (isCompact_closedCellLevelBand a b).measurableSet
  apply (integrable_indicator_iff hB).mp
  apply hrec.congr
  filter_upwards [ae_actionReconstruct F] with p hp
  rw [hp]
  by_cases hc : p ∈ puncturedCell
  · simp only [ite_eq_left hc, F, Set.indicator_apply, Function.comp_apply,
      actionAngleInv_actionAngle hc]
    simp only [S, mem_ofPred_eq, actionAngle, hc, true_and]
    rfl
  · simp [hc]

/-- Local integrability also descends through the action-angle parametrization. -/
theorem locallyIntegrableOn_of_comp_actionAngleInv {u : ℝ × ℝ → ℂ}
    (hu : LocallyIntegrableOn (u ∘ actionAngleInv) actionStrip) :
    LocallyIntegrableOn u puncturedCell := by
  intro p hp
  have hh := (mem_orbitDomain hp).1
  let a := levelCoord p / 2
  let b := (levelCoord p + 1) / 2
  refine ⟨{q | q ∈ puncturedCell ∧ levelCoord q ∈ Icc a b}, ?_,
    integrableOn_levelBand_of_comp_actionAngleInv (by dsimp [a]; linarith [hh.1])
      (by dsimp [b]; linarith [hh.2]) hu⟩
  have hl : Continuous levelCoord := by unfold levelCoord dipoleLift; fun_prop
  have hn : levelCoord ⁻¹' Icc a b ∈ 𝓝 p := hl.continuousAt.preimage_mem_nhds
    (Icc_mem_nhds (by dsimp [a]; linarith [hh.1]) (by dsimp [b]; linarith [hh.2]))
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hn)

/-- The parametrization preserves and reflects local integrability. -/
theorem locallyIntegrableOn_actionAngleInv_iff {u : ℝ × ℝ → ℂ} :
    LocallyIntegrableOn (u ∘ actionAngleInv) actionStrip ↔ LocallyIntegrableOn u puncturedCell :=
  ⟨locallyIntegrableOn_of_comp_actionAngleInv, locallyIntegrableOn_comp_actionAngleInv⟩

/-- Multiplication by the positive period does not change the local-integrability condition. -/
theorem locallyIntegrableOn_period_mul_actionAngleInv_iff {k : ℝ × ℝ → ℂ} :
    LocallyIntegrableOn (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q)) actionStrip ↔
      LocallyIntegrableOn k puncturedCell := by
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hs : ContinuousOn (fun q : ℝ × ℝ ↦ (orbitPeriod q.1 : ℂ)) actionStrip :=
    Complex.continuous_ofReal.comp_continuousOn
      (contDiffOn_orbitPeriod.continuousOn.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1))
  have hn : ∀ q ∈ actionStrip, (orbitPeriod q.1 : ℂ) ≠ 0 := fun q hq ↦
    Complex.ofReal_ne_zero.mpr (orbitPeriod_pos hq.1.1 hq.1.2).ne'
  constructor
  · intro hk
    have hi := hk.continuousOn_mul (hs.inv₀ hn) ho.isLocallyClosed
    have he : (fun q ↦ (orbitPeriod q.1 : ℂ)⁻¹ *
        ((orbitPeriod q.1 : ℂ) * k (actionAngleInv q))) =ᵐ[volume.restrict actionStrip]
        k ∘ actionAngleInv := by
      filter_upwards [ae_restrict_mem ho.measurableSet] with q hq
      simp only [← mul_assoc, inv_mul_cancel₀ (hn q hq), one_mul, Function.comp_apply]
    exact locallyIntegrableOn_of_comp_actionAngleInv (hi.congr he)
  · intro hk
    exact (locallyIntegrableOn_comp_actionAngleInv hk).continuousOn_mul hs ho.isLocallyClosed

/-- Periodic strip functions respect the inverse coordinates even outside the chosen window. -/
theorem comp_actionAngle_actionAngleInv {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {q : ℝ × ℝ}
    (hq : q ∈ actionStrip) : (F ∘ actionAngle) (actionAngleInv q) = F q := by
  let n : ℤ := ⌊q.2 + 1 / 4⌋
  have hnlo := Int.floor_le (q.2 + 1 / 4)
  have hnhi := Int.lt_floor_add_one (q.2 + 1 / 4)
  have hθ : q.2 - (n : ℝ) ∈ Ico (-1 / 4 : ℝ) (3 / 4) := by
    constructor <;> dsimp [n] <;> linarith
  have hp : Function.Periodic (fun θ ↦ actionAngleInv (q.1, θ)) 1 :=
    actionAngleInv_add_one hq.1.1 hq.1.2
  have hF : Function.Periodic (fun θ ↦ F (q.1, θ)) 1 := fun θ ↦ hper (q.1, θ)
  have he : actionAngleInv (q.1, q.2 - (n : ℝ)) = actionAngleInv q := by
    simpa only [mul_one] using hp.sub_int_mul_eq (x := q.2) n
  change F (actionAngle (actionAngleInv q)) = F q
  rw [← he, actionAngle_actionAngleInv hq.1.1 hq.1.2 hθ]
  simpa only [mul_one] using hF.sub_int_mul_eq (x := q.2) n

private theorem isOpen_puncturedCell : IsOpen puncturedCell := by
  have h₁ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) := by unfold diagCoord; fun_prop
  have h₂ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) := by unfold diagCoord; fun_prop
  exact ((isOpen_lt h₁ continuous_const).inter (isOpen_lt h₂ continuous_const)).sdiff
    isClosed_singleton

/-- The test-function chain rule in the reverse coordinates, with the angle treated modulo one. -/
theorem classicalL0_comp_actionAngle {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F actionStrip)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {p : ℝ × ℝ}
    (hp : p ∈ puncturedCell) :
    classicalL0 (F ∘ actionAngle) p =
      (orbitPeriod (levelCoord p) : ℂ)⁻¹ * partialY F (actionAngle p) := by
  have hh := (mem_orbitDomain hp).1
  have hd : DifferentiableAt ℝ (F ∘ actionAngle) p :=
    ((contDiffOn_comp_actionAngle hF hper).contDiffAt
      (isOpen_puncturedCell.mem_nhds hp)).differentiableAt (by simp)
  have he := partialY_comp_actionAngleInv (q := actionAngle p)
    (show DifferentiableAt ℝ (F ∘ actionAngle) (actionAngleInv (actionAngle p)) by
      rwa [actionAngleInv_actionAngle hp])
  have hline : (fun θ ↦ (F ∘ actionAngle) (actionAngleInv (levelCoord p, θ))) =
      (fun θ ↦ F (levelCoord p, θ)) := funext fun θ ↦
    comp_actionAngle_actionAngleInv hper ⟨hh, mem_univ _⟩
  have hpartial : partialY ((F ∘ actionAngle) ∘ actionAngleInv) (actionAngle p) =
      partialY F (actionAngle p) := by
    change deriv (fun θ ↦ (F ∘ actionAngle) (actionAngleInv (levelCoord p, θ))) (angleCoord p) = _
    rw [hline]
    rfl
  rw [hpartial, actionAngleInv_actionAngle hp, Complex.real_smul] at he
  change partialY F (actionAngle p) =
    (orbitPeriod (levelCoord p) : ℂ) * classicalL0 (F ∘ actionAngle) p at he
  have hS : (orbitPeriod (levelCoord p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (orbitPeriod_pos hh.1 hh.2).ne'
  change _ = (orbitPeriod (levelCoord p) : ℂ)⁻¹ * _
  rw [he, ← mul_assoc, inv_mul_cancel₀ hS, one_mul]

/-! ### Periodic test functions and weak transport -/

private theorem continuous_levelCoord : Continuous levelCoord := by
  unfold levelCoord dipoleLift
  fun_prop

private theorem exists_test_level_band {φ : ℝ × ℝ → ℂ} (hφ : HasCompactSupport φ)
    {l : ℝ × ℝ → ℝ} (hl : Continuous l) (hi : ∀ p ∈ tsupport φ, l p ∈ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ ∀ p, φ p ≠ 0 → l p ∈ Icc a b := by
  obtain ⟨a, ha, hlow⟩ := hφ.exists_forall_le' hl.continuousOn (fun p hp ↦ (hi p hp).1)
  obtain ⟨d, hd, hgap⟩ := hφ.exists_forall_le' (f := fun p ↦ 1 - l p) (a := (0 : ℝ))
    (continuous_const.sub hl).continuousOn (fun p hp ↦ by linarith [(hi p hp).2])
  refine ⟨a, 1 - d, ha, by linarith, fun p hp ↦ ?_⟩
  exact ⟨hlow p (subset_closure hp), by linarith [hgap p (subset_closure hp)]⟩

private theorem contDiff_of_zero_off_closed {φ : ℝ × ℝ → ℂ} {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ ∞ φ U)
    (hz : ∀ p ∉ K, φ p = 0) : ContDiff ℝ ∞ φ := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ U
  · exact hφ.contDiffAt (hU.mem_nhds hp)
  · apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ ↦ (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds (fun hk ↦ hp (hKU hk))] with q hq
    exact hz q hq

private theorem classicalL0_congr_of_eventuallyEq {φ ψ : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (he : φ =ᶠ[𝓝 p] ψ) : classicalL0 φ p = classicalL0 ψ p := by
  have hx := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto p.1)
  have hy := he.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)
  simp only [Function.comp_def, id_eq] at hx hy
  unfold classicalL0 partialX partialY
  rw [hx.deriv_eq, hy.deriv_eq]

private theorem integral_cell_supported_actionAngle {G : ℝ × ℝ → ℂ} (hG : Integrable G)
    (hs : ∀ p ∉ cellSquare, G p = 0) :
    (∫ p, G p) = ∫ q, (2 * orbitPeriod q.1) • G (actionAngleInv q) ∂actionMeasure := by
  have hmp := measurePreserving_actionParam
  have hi := integral_map hmp.measurable.aemeasurable
    (f := G) (by rw [hmp.map_eq]; exact hG.integrableOn.aestronglyMeasurable)
  rw [hmp.map_eq] at hi
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, hi,
    integral_withDensity_eq_integral_toReal_smul measurable_actionWeight
      (Filter.Eventually.of_forall (fun q ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
  have hw : (actionWeight q).toReal = 2 * orbitPeriod q.1 := by
    simp [actionWeight, actionPeriod, hq.1, (orbitPeriod_pos hq.1.1 hq.1.2).le]
  have hp : actionParam q = actionAngleInv q := by simp [actionParam, Set.piecewise, hq]
  rw [hw, hp]

open scoped Classical in
private def periodicCellTest (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  puncturedCell.indicator (F ∘ actionAngle)

private theorem isTestFunctionOn_periodicCellTest {F : ℝ × ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hF : ContDiff ℝ ∞ F)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hs : ∀ q, q.1 ∉ Icc a b → F q = 0) :
    IsTestFunctionOn puncturedCell (periodicCellTest F) := by
  classical
  let B := closedCellLevelBand a b
  have hB : IsCompact B := isCompact_closedCellLevelBand a b
  have hBU : B ⊆ puncturedCell := closedCellLevelBand_subset ha hb
  have hz : ∀ p ∉ B, periodicCellTest F p = 0 := by
    intro p hp
    by_cases hc : p ∈ puncturedCell
    · have hl : levelCoord p ∉ Icc a b := by
        intro hl
        exact hp ⟨hc.1.1.le, hc.1.2.le, hl⟩
      simp only [periodicCellTest, Set.indicator_of_mem hc, Function.comp_apply]
      exact hs (actionAngle p) hl
    · simp [periodicCellTest, hc]
  have hc : ContDiffOn ℝ ∞ (periodicCellTest F) puncturedCell :=
    (contDiffOn_comp_actionAngle hF.contDiffOn hper).congr
      (fun p hp ↦ Set.indicator_of_mem hp _)
  have ht : tsupport (periodicCellTest F) ⊆ B :=
    closure_minimal (fun p hp ↦ by_contra fun hn ↦ hp (hz p hn)) hB.isClosed
  exact ⟨contDiff_of_zero_off_closed isOpen_puncturedCell hB.isClosed hBU hc hz,
    HasCompactSupport.intro hB hz, ht.trans hBU⟩

private theorem classicalL0_periodicCellTest {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {p : ℝ × ℝ}
    (hp : p ∈ puncturedCell) : classicalL0 (periodicCellTest F) p =
      (orbitPeriod (levelCoord p) : ℂ)⁻¹ * partialY F (actionAngle p) := by
  rw [classicalL0_congr_of_eventuallyEq (ψ := F ∘ actionAngle) (by
    filter_upwards [isOpen_puncturedCell.mem_nhds hp] with q hq
    exact Set.indicator_of_mem hq _)]
  exact classicalL0_comp_actionAngle hF.contDiffOn hper hp

open scoped Classical in
private def stripTestPull (φ : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  actionStrip.indicator (φ ∘ actionAngleInv)

private theorem stripTestPull_properties {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn puncturedCell φ) :
    ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ ContDiff ℝ ∞ (stripTestPull φ) ∧
      (∀ q : ℝ × ℝ, stripTestPull φ (q.1, q.2 + 1) = stripTestPull φ q) ∧
      ∀ q, q.1 ∉ Icc a b → stripTestPull φ q = 0 := by
  classical
  obtain ⟨a, b, ha, hb, hs⟩ := exists_test_level_band hφ.hasCompactSupport
    continuous_levelCoord (fun p hp ↦ (mem_orbitDomain (hφ.tsupport_subset hp)).1)
  have hz : ∀ q, q.1 ∉ Icc a b → stripTestPull φ q = 0 := by
    intro q hq
    by_cases hh : q ∈ actionStrip
    · have hφz : φ (actionAngleInv q) = 0 := by
        by_contra hn
        exact hq (by simpa only [levelCoord_actionAngleInv hh.1.1 hh.1.2] using hs _ hn)
      simp [stripTestPull, hh, hφz]
    · simp [stripTestPull, hh]
  have hc : ContDiffOn ℝ ∞ (stripTestPull φ) actionStrip :=
    (hφ.contDiff.comp_contDiffOn contDiffOn_actionAngleInv).congr
      (fun q hq ↦ Set.indicator_of_mem hq _)
  have hK : IsClosed {q : ℝ × ℝ | q.1 ∈ Icc a b} := isClosed_Icc.preimage continuous_fst
  have hKU : {q : ℝ × ℝ | q.1 ∈ Icc a b} ⊆ actionStrip := fun q hq ↦
    ⟨⟨lt_of_lt_of_le ha hq.1, lt_of_le_of_lt hq.2 hb⟩, mem_univ _⟩
  refine ⟨a, b, ha, hb, contDiff_of_zero_off_closed (isOpen_Ioo.prod isOpen_univ) hK hKU hc hz,
    ?_, hz⟩
  intro q
  by_cases hh : q.1 ∈ Ioo (0 : ℝ) 1
  · simp [stripTestPull, actionStrip, hh, actionAngleInv_add_one hh.1 hh.2]
  · simp [stripTestPull, actionStrip, hh]

private theorem partialY_stripTestPull {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn puncturedCell φ) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    partialY (stripTestPull φ) q = orbitPeriod q.1 • classicalL0 φ (actionAngleInv q) := by
  have he : (fun θ ↦ stripTestPull φ (q.1, θ)) =
      (fun θ ↦ φ (actionAngleInv (q.1, θ))) := by
    funext θ
    exact Set.indicator_of_mem
      (show (q.1, θ) ∈ actionStrip from ⟨hq.1, mem_univ _⟩) (φ ∘ actionAngleInv)
  change deriv (fun θ ↦ stripTestPull φ (q.1, θ)) q.2 = _
  rw [he]
  exact partialY_comp_actionAngleInv (hφ.contDiff.differentiable (by simp) _)

private theorem isTestFunctionOn_partialY {U : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) : IsTestFunctionOn U (partialY φ) :=
  ⟨by simpa [coordPartial] using contDiff_coordPartial_top 1 hφ.contDiff,
    by simpa [coordPartial] using hφ.hasCompactSupport_coordPartial 1,
    (tsupport_partialY_subset φ).trans hφ.tsupport_subset⟩

private theorem integral_mul_test_actionAngle {u φ : ℝ × ℝ → ℂ}
    (hu : LocallyIntegrableOn u puncturedCell) (hφ : IsTestFunctionOn puncturedCell φ) :
    (∫ p, u p * φ p) =
      ∫ q, (2 * orbitPeriod q.1) •
        (u (actionAngleInv q) * φ (actionAngleInv q)) ∂actionMeasure := by
  apply integral_cell_supported_actionAngle
    (integrable_mul_of_tsupport_subset hu hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset)
  intro p hp
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hφ.tsupport_subset h).1), mul_zero]

private theorem integral_strip_test_periodize {A φ : ℝ × ℝ → ℂ}
    (hA : LocallyIntegrableOn A actionStrip)
    (hper : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 → A (q.1, q.2 + 1) = A q)
    (hφ : IsTestFunctionOn actionStrip φ) :
    (∫ q, A q * φ q) = ∫ q, A q * periodizeSnd φ q ∂actionMeasure :=
  integral_mul_periodizeSnd_strip measurableSet_Ioo hper
    (HasCompactSupport.hasBoundedSndSupport hφ.hasCompactSupport) hφ.tsupport_subset
    (integrable_mul_of_tsupport_subset hA hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset)

/-- Weak transport pulls back to the angular weak derivative. -/
theorem HasWeakL0On.comp_actionAngleInv {u k : ℝ × ℝ → ℂ}
    (hd : HasWeakL0On puncturedCell u k) :
    HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv)
      (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q)) := by
  have hu := locallyIntegrableOn_comp_actionAngleInv hd.1
  have hk := locallyIntegrableOn_period_mul_actionAngleInv_iff.mpr hd.2.1
  have hpu : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 →
      (u ∘ actionAngleInv) (q.1, q.2 + 1) = (u ∘ actionAngleInv) q := by
    intro q hq
    simp only [Function.comp_apply, actionAngleInv_add_one hq.1 hq.2]
  have hpk : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 →
      (orbitPeriod q.1 : ℂ) * k (actionAngleInv (q.1, q.2 + 1)) =
      (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) := by
    intro q hq
    rw [actionAngleInv_add_one hq.1 hq.2]
  refine ⟨hu, hk, fun φ hφ ↦ ?_⟩
  change (∫ q, (u ∘ actionAngleInv) q * partialY φ q) =
    -(∫ q, (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) * φ q)
  obtain ⟨a, b, ha, hb, hs⟩ := exists_test_level_band hφ.hasCompactSupport continuous_fst
    (fun q hq ↦ (hφ.tsupport_subset hq).1)
  let F := periodizeSnd φ
  have hF : ContDiff ℝ ∞ F := contDiff_periodizeSnd hφ.contDiff
    (HasCompactSupport.hasBoundedSndSupport hφ.hasCompactSupport)
  have hpF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q := periodizeSnd_periodic
  have hzF : ∀ q, q.1 ∉ Icc a b → F q = 0 :=
    fun q hq ↦ periodizeSnd_eq_zero (fun z hz ↦ by
      by_contra hn
      exact hz (hs z hn)) hq
  have hψ := isTestFunctionOn_periodicCellTest ha hb hF hpF hzF
  have hDF : partialY F = periodizeSnd (partialY φ) := funext fun q ↦
    partialY_periodizeSnd (hφ.contDiff.of_le (by simp))
      (HasCompactSupport.hasBoundedSndSupport hφ.hasCompactSupport) q
  have hleft : (∫ p, u p * classicalL0 (periodicCellTest F) p) =
      2 * (∫ q, (u ∘ actionAngleInv) q * partialY φ q) := by
    rw [integral_strip_test_periodize hu hpu (isTestFunctionOn_partialY hφ),
      integral_mul_test_actionAngle hd.1 (isTestFunctionOn_classicalL0 hψ), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    have hP := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
    rw [classicalL0_periodicCellTest hF hpF hP,
      levelCoord_actionAngleInv hq.1.1 hq.1.2, hDF]
    have he := comp_actionAngle_actionAngleInv
      (F := periodizeSnd (partialY φ)) periodizeSnd_periodic (q := q) ⟨hq.1, mem_univ _⟩
    change periodizeSnd (partialY φ) (actionAngle (actionAngleInv q)) = _ at he
    rw [he, Complex.real_smul]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Function.comp_apply]
    field_simp [(Complex.ofReal_ne_zero.mpr (orbitPeriod_pos hq.1.1 hq.1.2).ne')]
  have hright : (∫ p, k p * periodicCellTest F p) =
      2 * (∫ q, (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) * φ q) := by
    rw [integral_strip_test_periodize hk hpk hφ,
      integral_mul_test_actionAngle hd.2.1 hψ, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    have hP := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
    have he := comp_actionAngle_actionAngleInv hpF (q := q) ⟨hq.1, mem_univ _⟩
    change F (actionAngle (actionAngleInv q)) = F q at he
    simp only [periodicCellTest, Set.indicator_of_mem hP, Function.comp_apply, he,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hid := hd.2.2 (periodicCellTest F) hψ
  rw [hleft, hright, ← mul_neg] at hid
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hid

/-- The angular weak derivative descends to weak transport on the punctured cell. -/
theorem hasWeakL0On_of_actionAngle {u k : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv)
      (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q))) :
    HasWeakL0On puncturedCell u k := by
  have hu := locallyIntegrableOn_actionAngleInv_iff.mp hd.1
  have hk := locallyIntegrableOn_period_mul_actionAngleInv_iff.mp hd.2.1
  have hpu : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 →
      (u ∘ actionAngleInv) (q.1, q.2 + 1) = (u ∘ actionAngleInv) q := by
    intro q hq
    simp only [Function.comp_apply, actionAngleInv_add_one hq.1 hq.2]
  have hpk : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 →
      (orbitPeriod q.1 : ℂ) * k (actionAngleInv (q.1, q.2 + 1)) =
      (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) := by
    intro q hq
    rw [actionAngleInv_add_one hq.1 hq.2]
  refine ⟨hu, hk, fun φ hφ ↦ ?_⟩
  obtain ⟨a, b, ha, hb, hF, hpF, hzF⟩ := stripTestPull_properties hφ
  let F := stripTestPull φ
  let σ := cutoffPeriodicSnd F
  have hσ : IsTestFunctionOn actionStrip σ := isTestFunctionOn_cutoffPeriodicSnd ha hb hF hzF
  have hD : ∀ q, periodizeSnd (partialY σ) q = partialY F q :=
    periodize_partialY_cutoffPeriodicSnd hF hpF
  have hV : ∀ q, periodizeSnd σ q = F q := periodize_cutoffPeriodicSnd hpF
  have hleft : (∫ p, u p * classicalL0 φ p) =
      2 * (∫ q, (u ∘ actionAngleInv) q * partialY σ q) := by
    rw [integral_strip_test_periodize hd.1 hpu (isTestFunctionOn_partialY hσ),
      integral_mul_test_actionAngle hu (isTestFunctionOn_classicalL0 hφ), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    rw [hD, partialY_stripTestPull hφ ⟨hq.1, mem_univ _⟩]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Function.comp_apply]
    ring
  have hright : (∫ p, k p * φ p) =
      2 * (∫ q, (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) * σ q) := by
    rw [integral_strip_test_periodize hd.2.1 hpk hσ,
      integral_mul_test_actionAngle hk hφ, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq
    have hv : F q = φ (actionAngleInv q) :=
      Set.indicator_of_mem (show q ∈ actionStrip from ⟨hq.1, mem_univ _⟩) (φ ∘ actionAngleInv)
    rw [hV, hv, Complex.real_smul]
    push_cast
    ring
  have hid := hd.2.2 σ hσ
  change (∫ q, (u ∘ actionAngleInv) q * partialY σ q) =
    -(∫ q, (orbitPeriod q.1 : ℂ) * k (actionAngleInv q) * σ q) at hid
  rw [hleft, hid, mul_neg, ← hright]

/-- `L₀ u = k` weakly on the punctured cell if and only if `∂_θ U = S(h) K` weakly on the strip. -/
theorem hasWeakL0On_iff_actionAngle {u k : ℝ × ℝ → ℂ} :
    HasWeakL0On puncturedCell u k ↔
      HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv)
        (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q)) :=
  ⟨HasWeakL0On.comp_actionAngleInv, hasWeakL0On_of_actionAngle⟩

/-! ### Full weak-gradient chain rules -/

private theorem continuousOn_coordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (j : Fin 2) : ContinuousOn (coordPartial j f) U := by
  have hd := (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
    (continuousOn_const (c := if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)))
  refine hd.congr fun p hp ↦ ?_
  have hdiff : DifferentiableAt ℝ f p :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  split_ifs
  · exact partialX_eq_fderiv hdiff
  · exact partialY_eq_fderiv hdiff

private theorem contDiffOn_coordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (j : Fin 2) : ContDiffOn ℝ ∞ (coordPartial j f) U := by
  have hd := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)))
  refine hd.congr fun p hp ↦ ?_
  have hdiff : DifferentiableAt ℝ f p :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  split_ifs
  · exact partialX_eq_fderiv hdiff
  · exact partialY_eq_fderiv hdiff

private theorem coordPartial_congr_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ ψ : ℝ × ℝ → E} {p : ℝ × ℝ} (he : φ =ᶠ[𝓝 p] ψ)
    (j : Fin 2) : coordPartial j φ p = coordPartial j ψ p := by
  have hx := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto p.1)
  have hy := he.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)
  simp only [Function.comp_def, id_eq] at hx hy
  unfold coordPartial partialX partialY
  split_ifs
  · exact hx.deriv_eq
  · exact hy.deriv_eq

private theorem partialY_partialX_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {p : ℝ × ℝ} (hf : ContDiffAt ℝ ∞ f p) :
    partialY (partialX f) p = partialX (partialY f) p := by
  have hN : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q := by
    filter_upwards [(hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with q hq
    exact hq.differentiableAt one_ne_zero
  have hX : partialX f =ᶠ[𝓝 p] (fun q ↦ fderiv ℝ f q (1, 0)) :=
    hN.mono fun q hq ↦ partialX_eq_fderiv hq
  have hY : partialY f =ᶠ[𝓝 p] (fun q ↦ fderiv ℝ f q (0, 1)) :=
    hN.mono fun q hq ↦ partialY_eq_fderiv hq
  have hx := coordPartial_congr_nhds hX 1
  have hy := coordPartial_congr_nhds hY 0
  change partialY (partialX f) p = partialY (fun q ↦ fderiv ℝ f q (1, 0)) p at hx
  change partialX (partialY f) p = partialX (fun q ↦ fderiv ℝ f q (0, 1)) p at hy
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  rw [hx, hy, partialY_eq_fderiv (hfd.clm_apply (differentiableAt_const _)),
    partialX_eq_fderiv (hfd.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply hfd (differentiableAt_const _),
    fderiv_clm_apply hfd (differentiableAt_const _)]
  simpa using (hf.isSymmSndFDerivAt (by simp)) (0, 1) (1, 0)

/-- The candidate gradient of the pullback is locally integrable on the strip.
This requires only local integrability of the input gradient, not a weak identity. -/
theorem locallyIntegrableOn_actionAngleInv_gradient {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, LocallyIntegrableOn (g i) puncturedCell) (j : Fin 2) :
    LocallyIntegrableOn (fun q ↦
      ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q))
      actionStrip := by
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hc₀ := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_coordPartial ho (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) j)
  have hc₁ := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_coordPartial ho (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) j)
  exact ((locallyIntegrableOn_comp_actionAngleInv (hg 0)).continuousOn_mul hc₀
    ho.isLocallyClosed).add ((locallyIntegrableOn_comp_actionAngleInv (hg 1)).continuousOn_mul
      hc₁ ho.isLocallyClosed)

/-- A periodic locally integrable strip function descends to a locally integrable cell function. -/
theorem locallyIntegrableOn_comp_actionAngle {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hF : LocallyIntegrableOn F actionStrip) :
    LocallyIntegrableOn (F ∘ actionAngle) puncturedCell := by
  apply locallyIntegrableOn_of_comp_actionAngleInv
  apply hF.congr
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  filter_upwards [ae_restrict_mem ho.measurableSet] with q hq
  exact (comp_actionAngle_actionAngleInv hper hq).symm

/-- The full-gradient chain rule in the angular variable follows from weak transport. -/
theorem HasWeakPartialOn.comp_actionAngleInv_snd {u : ℝ × ℝ → ℂ}
    {g : Fin 2 → ℝ × ℝ → ℂ} (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) :
    HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv) (fun q ↦
      ((coordPartial 1 (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial 1 (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) := by
  have hx (q : ℝ × ℝ) :
      coordPartial 1 (fun q ↦ (actionAngleInv q).1) q =
        orbitPeriod q.1 * Real.sin (actionAngleInv q).2 := by
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def] using
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have hy (q : ℝ × ℝ) :
      coordPartial 1 (fun q ↦ (actionAngleInv q).2) q =
        orbitPeriod q.1 * (-Real.sin (actionAngleInv q).1) := by
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def] using
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have he : (fun q ↦
      ((coordPartial 1 (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial 1 (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) =
      (fun q ↦ (orbitPeriod q.1 : ℂ) *
        ((Real.sin (actionAngleInv q).2 : ℂ) * g 0 (actionAngleInv q) -
          (Real.sin (actionAngleInv q).1 : ℂ) * g 1 (actionAngleInv q))) := by
    funext q
    rw [hx, hy]
    push_cast
    ring
  rw [he]
  exact (HasWeakPartialOn.hasWeakL0On isOpen_puncturedCell (hg 0) (hg 1)).comp_actionAngleInv

/-- A fixed nonempty level band contains the cutoff and all sufficiently small mollifications
and their `h`-derivatives. -/
private theorem exists_mollify_band {χ : ℝ → ℝ} (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ a b ε₀ : ℝ, 0 < a ∧ b < 1 ∧ 0 < ε₀ ∧ tsupport χ ⊆ Icc a b ∧
      (∀ ε ∈ Ioo 0 ε₀, ∀ (G : ℝ × ℝ → ℂ) (q : ℝ × ℝ), q.1 ∉ Icc a b →
        mollifyFst ε (fun z ↦ (χ z.1 : ℂ) * G z) q = 0) ∧ a ≤ b ∧
      ∀ ε ∈ Ioo 0 ε₀, ∀ (G : ℝ × ℝ → ℂ) (q : ℝ × ℝ), q.1 ∉ Icc a b →
        mollifyFstDeriv ε (fun z ↦ (χ z.1 : ℂ) * G z) q = 0 := by
  have hs : IsCompact (tsupport χ) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).of_isClosed_subset (isClosed_tsupport χ)
      (fun t ht ↦ ⟨(hχs ht).1.le, (hχs ht).2.le⟩)
  obtain ⟨l, hl, hlow⟩ := hs.exists_forall_le' continuous_id.continuousOn
    (fun t ht ↦ (hχs ht).1)
  obtain ⟨d, hd, hgap⟩ := hs.exists_forall_le' (f := fun t : ℝ ↦ 1 - t) (a := 0)
    (continuous_const.sub continuous_id).continuousOn
    (fun t ht ↦ by linarith [(hχs ht).2])
  let r : ℝ := 1 - d
  have hr : r < 1 := by dsimp [r]; linarith
  have hupp : ∀ t ∈ tsupport χ, t ≤ r := by
    intro t ht
    dsimp [r]
    linarith [hgap t ht]
  let ε₀ := min l (1 - r) / 2
  have hε₀ : 0 < ε₀ := div_pos (lt_min hl (by linarith)) (by norm_num)
  have hmargin : ∀ ε ∈ Ioo 0 ε₀, ∀ q : ℝ × ℝ, q.1 ∉ Icc (min (l / 2) (1 / 2))
      (max ((r + 1) / 2) (1 / 2)) → ∀ t ∈ tsupport χ, ε < |q.1 - t| := by
    intro ε hε q hq t ht
    have he₁ : ε < l / 2 := by
      have h := min_le_left l (1 - r)
      dsimp [ε₀] at hε
      linarith [hε.2]
    have he₂ : ε < (1 - r) / 2 := by
      have h := min_le_right l (1 - r)
      dsimp [ε₀] at hε
      linarith [hε.2]
    have hlt : l ≤ t := hlow t ht
    have htr := hupp t ht
    rcases not_and_or.mp hq with h | h
    · have h' : q.1 < l / 2 := lt_of_lt_of_le (not_le.mp h) (min_le_left _ _)
      rw [abs_of_neg (by linarith)]
      linarith
    · have h' : (r + 1) / 2 < q.1 := lt_of_le_of_lt (le_max_left _ _) (not_le.mp h)
      rw [abs_of_pos (by linarith)]
      linarith
  refine ⟨min (l / 2) (1 / 2), max ((r + 1) / 2) (1 / 2), ε₀, lt_min (by linarith)
    (by norm_num), max_lt (by linarith) (by norm_num), hε₀, ?_, ?_,
    (min_le_right _ _).trans (le_max_right _ _), ?_⟩
  · intro t ht
    have hlt : l ≤ t := hlow t ht
    have htr := hupp t ht
    exact ⟨(min_le_left _ _).trans (by linarith), (by linarith : t ≤ (r + 1) / 2).trans
      (le_max_left _ _)⟩
  · intro ε hε u q hq
    unfold mollifyFst
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    by_cases hk : mollifierKernel ε (q.1 - t) = 0
    · simp [hk]
    by_cases ht : χ t = 0
    · simp [ht]
    have hts : t ∈ tsupport χ := subset_closure (show t ∈ Function.support χ from ht)
    have hgap := hmargin ε hε q hq t hts
    have hB : stdBump ((q.1 - t) / ε) ≠ 0 := by
      intro hz
      apply hk
      simp [mollifierKernel, hz]
    have hmem : (q.1 - t) / ε ∈ Function.support stdBump := hB
    rw [support_stdBump] at hmem
    have hleft := (lt_div_iff₀ hε.1).mp hmem.1
    have hright := (div_lt_iff₀ hε.1).mp hmem.2
    rcases lt_abs.mp hgap with h | h <;> linarith
  · intro ε hε u q hq
    unfold mollifyFstDeriv
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    by_cases ht : χ t = 0
    · simp [ht]
    have hts : t ∈ tsupport χ := subset_closure (show t ∈ Function.support χ from ht)
    have hgap := hmargin ε hε q hq t hts
    have hout : (q.1 - t) / ε ∉ tsupport stdBump := by
      have hcl : tsupport stdBump = Icc (-1) 1 := by
        rw [tsupport, support_stdBump, closure_Ioo (by norm_num)]
      rw [hcl]
      intro hm
      have h1 := (le_div_iff₀ hε.1).mp hm.1
      have h2 := (div_le_iff₀ hε.1).mp hm.2
      have := lt_abs.mp hgap
      rcases this with h | h <;> linarith
    have hz : deriv stdBump ((q.1 - t) / ε) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm ↦ hout (tsupport_deriv_subset hm))
    simp [deriv_mollifierKernel, hz]

/-! ### Helpers for the commutator -/

private theorem tsupport_levelCutoff_subset {χ : ℝ → ℝ} :
    tsupport (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ)) ⊆ Prod.fst ⁻¹' tsupport χ :=
  closure_minimal (fun q hq ↦ subset_closure (show q.1 ∈ Function.support χ from
    fun h ↦ hq (by simp [h]))) ((isClosed_tsupport χ).preimage continuous_fst)

/-- Weak derivatives on a measurable set only see the functions on that set. -/
private theorem HasWeakPartialOn.congr_on {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {j : Fin 2} {g g' h h' : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn U j g h) (hg : EqOn g g' U)
    (hh : EqOn h h' U) : HasWeakPartialOn U j g' h' := by
  refine ⟨hd.1.congr ((ae_restrict_iff' hU).mpr (Eventually.of_forall hg)),
    hd.2.1.congr ((ae_restrict_iff' hU).mpr (Eventually.of_forall hh)), fun φ hφ ↦ ?_⟩
  have e1 : (fun p ↦ g' p * coordPartial j φ p) = fun p ↦ g p * coordPartial j φ p := by
    funext p
    by_cases hp : p ∈ U
    · rw [hg hp]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφ.tsupport_subset
        (tsupport_coordPartial_subset j φ ht))), mul_zero, mul_zero]
  have e2 : (fun p ↦ h' p * φ p) = fun p ↦ h p * φ p := by
    funext p
    by_cases hp : p ∈ U
    · rw [hh hp]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφ.tsupport_subset ht)), mul_zero,
        mul_zero]
  rw [e1, e2]
  exact hd.2.2 φ hφ

private theorem locallyIntegrable_levelCutoff {c : ℝ → ℝ} (hc : Continuous c)
    (hcs : tsupport c ⊆ Ioo 0 1) {V : ℝ × ℝ → ℂ} (hV : LocallyIntegrableOn V actionStrip) :
    LocallyIntegrableOn (fun q ↦ (c q.1 : ℂ) * V q) univ := by
  set C : Set (ℝ × ℝ) := Prod.fst ⁻¹' tsupport c
  have hC : IsClosed C := (isClosed_tsupport c).preimage continuous_fst
  have hCs : C ⊆ actionStrip := fun q hq ↦ ⟨hcs hq, mem_univ _⟩
  have hcc : Continuous (fun q : ℝ × ℝ ↦ (c q.1 : ℂ)) :=
    Complex.continuous_ofReal.comp (hc.comp continuous_fst)
  rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
  intro K hK
  have hKC : IsCompact (K ∩ C) := hK.inter_right hC
  have hi : IntegrableOn (fun q ↦ (c q.1 : ℂ) * V q) (K ∩ C) :=
    (hV.integrableOn_compact_subset (inter_subset_right.trans hCs) hKC).continuousOn_mul
      hcc.continuousOn hKC
  exact hi.of_forall_sdiff_eq_zero hK.measurableSet fun q hq ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hq.2 ⟨hq.1, h⟩), Complex.ofReal_zero,
      zero_mul]

/-- A level cutoff `χ(h)` with support in `(0, 1)` carries an angular weak derivative on the
strip to one on the plane. -/
private theorem HasWeakPartialOn.levelCutoff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {U G : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn actionStrip 1 U G) :
    HasWeakPartialOn univ 1 (fun q ↦ (χ q.1 : ℂ) * U q) (fun q ↦ (χ q.1 : ℂ) * G q) := by
  have hCs : Prod.fst ⁻¹' tsupport χ ⊆ actionStrip := fun q hq ↦ ⟨hχs hq, mem_univ _⟩
  have hcd : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)
  refine ⟨locallyIntegrable_levelCutoff hχ.continuous hχs hd.1,
    locallyIntegrable_levelCutoff hχ.continuous hχs hd.2.1, fun φ hφ ↦ ?_⟩
  set ψ : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * φ q with hψ_def
  have hψ : IsTestFunctionOn actionStrip ψ :=
    ⟨hcd.mul hφ.contDiff, hφ.hasCompactSupport.mul_left,
      tsupport_mul_subset_left.trans (tsupport_levelCutoff_subset.trans hCs)⟩
  have hψd : coordPartial 1 ψ = fun q ↦ (χ q.1 : ℂ) * coordPartial 1 φ q := by
    funext q
    have hdφ : DifferentiableAt ℝ (fun t ↦ φ (q.1, t)) q.2 :=
      (hφ.contDiff.differentiable (by simp) _).comp q.2
        ((differentiableAt_const q.1).prodMk differentiableAt_id)
    simp only [coordPartial, one_ne_zero, ite_false, partialY, hψ_def]
    exact deriv_const_mul _ hdφ
  have hw := hd.2.2 ψ hψ
  rw [hψd] at hw
  calc (∫ p, (χ p.1 : ℂ) * U p * coordPartial 1 φ p)
      = ∫ p, U p * ((χ p.1 : ℂ) * coordPartial 1 φ p) := by
        congr 1; funext p; ring
    _ = -∫ p, G p * ψ p := hw
    _ = -∫ p, (χ p.1 : ℂ) * G p * φ p := by
        congr 2; funext p; simp only [hψ_def]; ring

/-- Mollification in `h` preserves `1`-periodicity in `θ`. -/
private theorem mollifyFst_periodic {ε : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) (q : ℝ × ℝ) :
    mollifyFst ε F (q.1, q.2 + 1) = mollifyFst ε F q := by
  simp only [mollifyFst]
  congr 1
  funext t
  rw [hF (t, q.2)]

/-- Strip data cut off in `h` are `1`-periodic in `θ`. -/
private theorem levelCutoff_actionInput_periodic {χ : ℝ → ℝ} (hχs : tsupport χ ⊆ Ioo 0 1)
    (s : ℝ → ℂ) (u : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    (χ q.1 : ℂ) * (s q.1 * u (actionAngleInv (q.1, q.2 + 1))) =
      (χ q.1 : ℂ) * (s q.1 * u (actionAngleInv q)) := by
  by_cases hq : q.1 ∈ Ioo (0 : ℝ) 1
  · rw [actionAngleInv_add_one hq.1 hq.2]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hq (hχs ht))]
    simp

/-- Weak transport on the punctured cell extends to the plane for functions vanishing off a
closed interior level band. -/
private theorem HasWeakL0On.univ_of_band {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {f g : ℝ × ℝ → ℂ} (hd : HasWeakL0On puncturedCell f g)
    (hf : ∀ p ∉ closedCellLevelBand a b, f p = 0)
    (hg : ∀ p ∉ closedCellLevelBand a b, g p = 0) : HasWeakL0On univ f g := by
  set B := closedCellLevelBand a b
  have hB : IsCompact B := isCompact_closedCellLevelBand a b
  have hBU : B ⊆ puncturedCell := closedCellLevelBand_subset ha hb
  have hint {v : ℝ × ℝ → ℂ} (hv : LocallyIntegrableOn v puncturedCell)
      (hz : ∀ p ∉ B, v p = 0) : LocallyIntegrableOn v univ :=
    ((hv.integrableOn_compact_subset hBU hB).integrable_of_forall_notMem_eq_zero
      hz).locallyIntegrable.locallyIntegrableOn univ
  refine ⟨hint hd.1 hf, hint hd.2.1 hg, fun φ hφ ↦ ?_⟩
  obtain ⟨V₂, hV₂o, hBV₂, hV₂c, hV₂k⟩ :=
    exists_open_between_and_isCompact_closure hB isOpen_puncturedCell hBU
  obtain ⟨V₁, hV₁o, hBV₁, hV₁c, -⟩ := exists_open_between_and_isCompact_closure hB hV₂o hBV₂
  obtain ⟨η, hη, -, hηs, hη1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₂o isClosed_closure hV₁c
  have hηt : tsupport η = closure V₂ := by rw [tsupport, hηs]
  set ψ : ℝ × ℝ → ℂ := fun p ↦ (η p : ℂ) * φ p with hψ_def
  have hψ : IsTestFunctionOn puncturedCell ψ :=
    ⟨(Complex.ofRealCLM.contDiff.comp hη).mul hφ.contDiff, by
      refine HasCompactSupport.mul_right ?_
      refine hV₂k.of_isClosed_subset (isClosed_tsupport _) ?_
      rw [← hηt]
      exact closure_mono (fun p hp ↦ by simpa using hp), by
      refine tsupport_mul_subset_left.trans ?_
      refine (closure_mono (fun p hp ↦ ?_)).trans (hηt ▸ hV₂c)
      simpa using hp⟩
  have hnear (p : ℝ × ℝ) (hp : p ∈ B) : ψ =ᶠ[𝓝 p] φ := by
    filter_upwards [hV₁o.mem_nhds (hBV₁ hp)] with q hq
    simp [hψ_def, (hη1 q).1 (subset_closure hq)]
  have e1 : (fun p ↦ f p * classicalL0 ψ p) = fun p ↦ f p * classicalL0 φ p := by
    funext p
    by_cases hp : p ∈ B
    · rw [classicalL0_congr_of_eventuallyEq (hnear p hp)]
    · rw [hf p hp, zero_mul, zero_mul]
  have e2 : (fun p ↦ g p * ψ p) = fun p ↦ g p * φ p := by
    funext p
    by_cases hp : p ∈ B
    · rw [(hnear p hp).eq_of_nhds]
    · rw [hg p hp, zero_mul, zero_mul]
  have hw := hd.2.2 ψ hψ
  rwa [e1, e2] at hw

/-- Multiplication by a bounded continuous function of the level preserves `L²`. -/
private theorem memLp_levelMul {μ : Measure (ℝ × ℝ)} {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 μ)
    {s : ℝ → ℝ} (hs : Continuous s) {M : ℝ} (hM : ∀ h, |s h| ≤ M) :
    MemLp (fun q ↦ (s q.1 : ℂ) * F q) 2 μ :=
  hF.of_le_mul
    (((Complex.continuous_ofReal.comp (hs.comp continuous_fst)).aestronglyMeasurable).mul
      hF.aestronglyMeasurable)
    (Eventually.of_forall fun q ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM q.1) (norm_nonneg _))

/-- A Lipschitz function equal to the period on a band `[a, b] ⊂ (0, 1)`, with positive
lower and finite upper bounds: `S ∘ proj_[a,b]`. -/
private theorem exists_periodExtension {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ σ : ℝ → ℝ, ∃ L : ℝ≥0, ∃ m M : ℝ, LipschitzWith L σ ∧
      (∀ h ∈ Icc a b, σ h = orbitPeriod h) ∧ 0 < m ∧ (∀ h, m ≤ σ h) ∧ ∀ h, σ h ≤ M := by
  have hIcc : Icc a b ⊆ Ioo 0 1 := fun h hh ↦ ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩
  have hSon : ContDiffOn ℝ ∞ orbitPeriod (Icc a b) := contDiffOn_orbitPeriod.mono hIcc
  obtain ⟨L, hL⟩ := hSon.exists_lipschitzOnWith (by simp) (convex_Icc a b) isCompact_Icc
  obtain ⟨h₁, hh₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    hSon.continuousOn
  obtain ⟨h₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    hSon.continuousOn
  refine ⟨fun h ↦ orbitPeriod (projIcc a b hab h), L, orbitPeriod h₁, orbitPeriod h₂, ?_,
    fun h hh ↦ by simp only [projIcc_of_mem hab hh], orbitPeriod_pos (hIcc hh₁).1 (hIcc hh₁).2,
    fun h ↦ hmin (projIcc a b hab h).2, fun h ↦ hmax (projIcc a b hab h).2⟩
  have h := hL.to_restrict.comp (LipschitzWith.projIcc hab)
  rw [mul_one] at h
  exact h

/-- The angular weak derivative of the cut-off input on the plane: `∂_θ (χU) = σ χ K`
when `L₀ u = k` on the cell and `σ = S` on a band containing the support of `χ`. -/
private theorem hasWeakPartialOn_levelCutoff_actionInput {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {a b : ℝ} (hχband : tsupport χ ⊆ Icc a b) {σ : ℝ → ℝ}
    (hσS : ∀ h ∈ Icc a b, σ h = orbitPeriod h) {u k : ℝ × ℝ → ℂ}
    (hLk : HasWeakL0On cellSquare u k) :
    HasWeakPartialOn univ 1 (fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q))
      (fun q ↦ (σ q.1 : ℂ) * ((χ q.1 : ℂ) * k (actionAngleInv q))) := by
  have hL1 : HasWeakL0On puncturedCell u k :=
    ⟨hLk.1.mono_set sdiff_subset, hLk.2.1.mono_set sdiff_subset,
      fun φ hφ ↦ hLk.2.2 φ (hφ.mono sdiff_subset)⟩
  have h2 := hL1.comp_actionAngleInv.levelCutoff hχ hχs
  have hG : (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ) *
      ((orbitPeriod q.1 : ℂ) * k (actionAngleInv q))) =
      fun q ↦ (σ q.1 : ℂ) * ((χ q.1 : ℂ) * k (actionAngleInv q)) := by
    funext q
    by_cases hq : χ q.1 = 0
    · simp [hq]
    · rw [hσS q.1 (hχband (subset_closure hq))]
      ring
  rw [hG] at h2
  exact h2

/-! ### Helpers for the derivatives -/

/-- The diagonal `x = y`, which contains the cut of the angle, is a null set. -/
private theorem volume_diagCoord_snd_eq_zero :
    (volume : Measure (ℝ × ℝ)) {p | (diagCoord p).2 = 0} = 0 := by
  have hc : IsClosed {p : ℝ × ℝ | (diagCoord p).2 = 0} :=
    isClosed_eq (by unfold diagCoord; fun_prop) continuous_const
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hc.measurableSet]
  refine Eventually.of_forall fun x ↦ ?_
  have : Prod.mk x ⁻¹' {p : ℝ × ℝ | (diagCoord p).2 = 0} = {x} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, diagCoord, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  simp [this]

/-- `e^{2πiθ}` on the plane. -/
private def angleExp (p : ℝ × ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * angleCoord p) * Complex.I)

private theorem contDiffOn_angleExp : ContDiffOn ℝ ∞ angleExp puncturedCell := by
  have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ Complex.exp (↑(2 * Real.pi * q.2) * Complex.I)) := by
    have h : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ ((2 * Real.pi * q.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)
    exact Complex.contDiff_exp.comp (h.mul contDiff_const)
  have hper : ∀ q : ℝ × ℝ, Complex.exp (↑(2 * Real.pi * (q.1, q.2 + 1).2) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * q.2) * Complex.I) := fun q ↦ by
    have : (↑(2 * Real.pi * (q.2 + 1)) * Complex.I : ℂ) =
        ↑(2 * Real.pi * q.2) * Complex.I + 2 * Real.pi * Complex.I := by push_cast; ring
    simp only [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  exact contDiffOn_comp_actionAngle hF.contDiffOn hper

/-- A smooth replacement for `∂ⱼθ`: `conj(E) ∂ⱼE / (2πi)` with `E = e^{2πiθ}`. -/
private def angleGrad (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  starRingEnd ℂ (angleExp p) * coordPartial j angleExp p / (2 * Real.pi * Complex.I)

private theorem contDiffOn_angleGrad (j : Fin 2) : ContDiffOn ℝ ∞ (angleGrad j) puncturedCell :=
  ((Complex.conjCLE.contDiff.comp_contDiffOn contDiffOn_angleExp).mul
    (contDiffOn_coordPartial isOpen_puncturedCell contDiffOn_angleExp j)).div_const _

private theorem continuousOn_angleGrad (j : Fin 2) : ContinuousOn (angleGrad j) puncturedCell :=
  (contDiffOn_angleGrad j).continuousOn

/-- Off the cut, `angleGrad` is the partial derivative of the angle. -/
private theorem angleGrad_eq {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) (j : Fin 2) :
    angleGrad j p = ((coordPartial j angleCoord p : ℝ) : ℂ) := by
  have hθ : DifferentiableAt ℝ angleCoord p :=
    (contDiffAt_angleCoord hp hcut).differentiableAt (by simp)
  have hline {g : ℝ → ℝ × ℝ} {t₀ : ℝ} (hg : g t₀ = p) {θ' : ℝ}
      (hθ' : HasDerivAt (fun t ↦ angleCoord (g t)) θ' t₀) :
      HasDerivAt (fun t ↦ angleExp (g t)) (angleExp p * (↑(2 * Real.pi * θ') * Complex.I))
        t₀ := by
    have h := ((hθ'.const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
    simpa only [angleExp, hg] using h
  have hE : coordPartial j angleExp p =
      angleExp p * (↑(2 * Real.pi * coordPartial j angleCoord p) * Complex.I) := by
    unfold coordPartial
    split_ifs
    · exact (hline rfl (hasDerivAt_partialX hθ)).deriv
    · exact (hline rfl (hasDerivAt_partialY hθ)).deriv
  have hn : starRingEnd ℂ (angleExp p) * angleExp p = 1 := by
    rw [Complex.conj_mul', angleExp, Complex.norm_exp_ofReal_mul_I]
    simp
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [angleGrad, hE, ← mul_assoc, hn, one_mul]
  field_simp
  push_cast
  ring

private theorem angleGrad_curl_zero {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hn : (diagCoord p).2 ≠ 0) :
    coordPartial 0 (angleGrad 1) p = coordPartial 1 (angleGrad 0) p := by
  let θ : ℝ × ℝ → ℂ := fun q ↦ (angleCoord q : ℂ)
  have hdiag : Continuous (fun q : ℝ × ℝ ↦ (diagCoord q).2) := by unfold diagCoord; fun_prop
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ puncturedCell ∧ (diagCoord q).2 ≠ 0 := by
    filter_upwards [isOpen_puncturedCell.mem_nhds hp,
      (isOpen_ne_fun hdiag continuous_const).mem_nhds hn] with q hq hqn
    exact ⟨hq, hqn⟩
  have he (j : Fin 2) : angleGrad j =ᶠ[𝓝 p] coordPartial j θ := by
    filter_upwards [hnear] with q hq
    have hcut : ¬((diagCoord q).2 = 0 ∧ 0 < (diagCoord q).1) := fun h ↦ hq.2 h.1
    rw [angleGrad_eq hq.1 hcut]
    have hd := (contDiffAt_angleCoord hq.1 hcut).differentiableAt (by simp)
    unfold coordPartial
    split_ifs
    · exact (hasDerivAt_partialX hd).ofReal_comp.deriv.symm
    · exact (hasDerivAt_partialY hd).ofReal_comp.deriv.symm
  rw [coordPartial_congr_nhds (he 1) 0, coordPartial_congr_nhds (he 0) 1]
  change partialX (partialY θ) p = partialY (partialX θ) p
  exact (partialY_partialX_at (Complex.ofRealCLM.contDiff.contDiffAt.comp p
    (contDiffAt_angleCoord hp (fun h ↦ hn h.1)))).symm

/-- The rotated smooth angular gradient, used as the dual coefficient for the level derivative.
The coefficients are complex-valued for compatibility with the weak derivative pairing. -/
def levelDualCoeff (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  if j = 0 then angleGrad 1 p else -angleGrad 0 p

theorem contDiffOn_levelDualCoeff (j : Fin 2) :
    ContDiffOn ℝ ∞ (levelDualCoeff j) puncturedCell := by
  unfold levelDualCoeff
  split_ifs
  · exact contDiffOn_angleGrad 1
  · exact (contDiffOn_angleGrad 0).neg

/-- Off the angle cut the dual field is the rotated gradient of the angle. -/
theorem levelDualCoeff_eq {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) (j : Fin 2) :
    levelDualCoeff j p = if j = 0 then ((coordPartial 1 angleCoord p : ℝ) : ℂ)
      else -((coordPartial 0 angleCoord p : ℝ) : ℂ) := by
  unfold levelDualCoeff
  split_ifs <;> rw [angleGrad_eq hp hcut]

/-- The dual field is divergence free almost everywhere on the punctured cell. -/
theorem levelDualCoeff_divergence_ae : ∀ᵐ p, p ∈ puncturedCell →
    coordPartial 0 (levelDualCoeff 0) p + coordPartial 1 (levelDualCoeff 1) p = 0 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero] with p hn hp
  change (diagCoord p).2 ≠ 0 at hn
  have hd := ((contDiffOn_angleGrad 0).contDiffAt
    (isOpen_puncturedCell.mem_nhds hp)).differentiableAt (by simp)
  have he := (hasDerivAt_partialY hd).neg.deriv
  change partialY (fun q ↦ -angleGrad 0 q) p = -partialY (angleGrad 0) p at he
  change partialX (angleGrad 1) p + partialY (fun q ↦ -angleGrad 0 q) p = 0
  rw [he]
  exact sub_eq_zero.mpr (angleGrad_curl_zero hp hn)

private theorem IsTestFunctionOn.mul_contDiffOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {φ b : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn U φ) (hb : ContDiffOn ℝ ∞ b U) :
    IsTestFunctionOn U (fun p ↦ b p * φ p) := by
  have hz : ∀ p ∉ tsupport φ, b p * φ p = 0 := fun p hp ↦ by
    rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  exact ⟨contDiff_of_zero_off_closed hU (isClosed_tsupport φ) hφ.tsupport_subset
    (hb.mul hφ.contDiff.contDiffOn) hz, hφ.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans hφ.tsupport_subset⟩

/-- Testing weak partial derivatives against the dual field has no zeroth-order term.
The cancellation is the divergence-free identity, and needs no Sobolev approximation. -/
theorem integral_mul_levelDualCoeff {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn puncturedCell φ) :
    (∫ p, u p * (levelDualCoeff 0 p * coordPartial 0 φ p +
      levelDualCoeff 1 p * coordPartial 1 φ p)) =
      -∫ p, (levelDualCoeff 0 p * g 0 p + levelDualCoeff 1 p * g 1 p) * φ p := by
  let ψ (j : Fin 2) : ℝ × ℝ → ℂ := fun p ↦ levelDualCoeff j p * φ p
  have hψ (j : Fin 2) : IsTestFunctionOn puncturedCell (ψ j) :=
    hφ.mul_contDiffOn isOpen_puncturedCell (contDiffOn_levelDualCoeff j)
  have hderiv (j : Fin 2) (p : ℝ × ℝ) (hp : p ∈ puncturedCell) :
      coordPartial j (ψ j) p = coordPartial j (levelDualCoeff j) p * φ p +
        levelDualCoeff j p * coordPartial j φ p := by
    have hb := ((contDiffOn_levelDualCoeff j).contDiffAt
      (isOpen_puncturedCell.mem_nhds hp)).differentiableAt (by simp)
    have hd := hφ.contDiff.differentiable (by simp) p
    unfold coordPartial
    split_ifs
    · exact partialX_mul hb hd
    · exact partialY_mul hb hd
  have il (j : Fin 2) : Integrable (fun p ↦ u p * coordPartial j (ψ j) p) :=
    integrable_mul_of_tsupport_subset (hg j).1 ((hψ j).continuous_coordPartial j)
      ((hψ j).hasCompactSupport_coordPartial j)
      ((tsupport_coordPartial_subset j (ψ j)).trans (hψ j).tsupport_subset)
  have ir (j : Fin 2) : Integrable (fun p ↦ g j p * ψ j p) :=
    integrable_mul_of_tsupport_subset (hg j).2.1 (hψ j).contDiff.continuous
      (hψ j).hasCompactSupport (hψ j).tsupport_subset
  have he : (fun p ↦ u p * (levelDualCoeff 0 p * coordPartial 0 φ p +
      levelDualCoeff 1 p * coordPartial 1 φ p)) =ᵐ[volume]
      (fun p ↦ u p * (coordPartial 0 (ψ 0) p + coordPartial 1 (ψ 1) p)) := by
    filter_upwards [levelDualCoeff_divergence_ae] with p hdiv
    by_cases hp : p ∈ puncturedCell
    · rw [hderiv 0 p hp, hderiv 1 p hp]
      linear_combination -(u p * φ p) * hdiv hp
    · have hz {f : ℝ × ℝ → ℂ} (hf : IsTestFunctionOn puncturedCell f) (j : Fin 2) :
          coordPartial j f p = 0 := image_eq_zero_of_notMem_tsupport
            (fun hs ↦ hp (hf.tsupport_subset (tsupport_coordPartial_subset j f hs)))
      rw [hz hφ 0, hz hφ 1, hz (hψ 0) 0, hz (hψ 1) 1]
      simp
  calc (∫ p, u p * (levelDualCoeff 0 p * coordPartial 0 φ p +
          levelDualCoeff 1 p * coordPartial 1 φ p)) =
        ∫ p, u p * (coordPartial 0 (ψ 0) p + coordPartial 1 (ψ 1) p) := integral_congr_ae he
    _ = (∫ p, u p * coordPartial 0 (ψ 0) p) +
        ∫ p, u p * coordPartial 1 (ψ 1) p := by
      rw [← integral_add (il 0) (il 1)]
      congr 1
      funext p
      ring
    _ = -(∫ p, g 0 p * ψ 0 p) + -(∫ p, g 1 p * ψ 1 p) := by
      rw [(hg 0).2.2 _ (hψ 0), (hg 1).2.2 _ (hψ 1)]
    _ = -∫ p, (levelDualCoeff 0 p * g 0 p + levelDualCoeff 1 p * g 1 p) * φ p := by
      rw [← neg_add, ← integral_add (ir 0) (ir 1)]
      congr 2
      funext p
      dsimp only [ψ]
      ring

/-- Weak derivatives on a measurable set are unchanged by a.e. changes on that set. -/
private theorem HasWeakPartialOn.congr_ae_on {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {j : Fin 2} {g g' h h' : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn U j g h)
    (hg : ∀ᵐ p, p ∈ U → g p = g' p) (hh : ∀ᵐ p, p ∈ U → h p = h' p) :
    HasWeakPartialOn U j g' h' := by
  refine ⟨hd.1.congr ((ae_restrict_iff' hU).mpr hg),
    hd.2.1.congr ((ae_restrict_iff' hU).mpr hh), fun φ hφ ↦ ?_⟩
  have e1 : (∫ p, g' p * coordPartial j φ p) = ∫ p, g p * coordPartial j φ p := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with p hp
    by_cases hpU : p ∈ U
    · rw [hp hpU]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hpU (hφ.tsupport_subset
        (tsupport_coordPartial_subset j φ ht))), mul_zero, mul_zero]
  have e2 : (∫ p, h' p * φ p) = ∫ p, h p * φ p := by
    refine integral_congr_ae ?_
    filter_upwards [hh] with p hp
    by_cases hpU : p ∈ U
    · rw [hp hpU]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hpU (hφ.tsupport_subset ht)), mul_zero,
        mul_zero]
  rw [e1, e2]
  exact hd.2.2 φ hφ

/-- Weak derivatives on the punctured cell extend to the plane for functions vanishing off a
closed interior level band. -/
private theorem HasWeakPartialOn.univ_of_band {a b : ℝ} (ha : 0 < a) (hb : b < 1) {j : Fin 2}
    {f g : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn puncturedCell j f g)
    (hf : ∀ p ∉ closedCellLevelBand a b, f p = 0)
    (hg : ∀ p ∉ closedCellLevelBand a b, g p = 0) : HasWeakPartialOn univ j f g := by
  set B := closedCellLevelBand a b
  have hB : IsCompact B := isCompact_closedCellLevelBand a b
  have hBU : B ⊆ puncturedCell := closedCellLevelBand_subset ha hb
  have hint {v : ℝ × ℝ → ℂ} (hv : LocallyIntegrableOn v puncturedCell)
      (hz : ∀ p ∉ B, v p = 0) : LocallyIntegrableOn v univ :=
    ((hv.integrableOn_compact_subset hBU hB).integrable_of_forall_notMem_eq_zero
      hz).locallyIntegrable.locallyIntegrableOn univ
  refine ⟨hint hd.1 hf, hint hd.2.1 hg, fun φ hφ ↦ ?_⟩
  obtain ⟨V₂, hV₂o, hBV₂, hV₂c, hV₂k⟩ :=
    exists_open_between_and_isCompact_closure hB isOpen_puncturedCell hBU
  obtain ⟨V₁, hV₁o, hBV₁, hV₁c, -⟩ := exists_open_between_and_isCompact_closure hB hV₂o hBV₂
  obtain ⟨η, hη, -, hηs, hη1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₂o isClosed_closure hV₁c
  have hηt : tsupport η = closure V₂ := by rw [tsupport, hηs]
  set ψ : ℝ × ℝ → ℂ := fun p ↦ (η p : ℂ) * φ p with hψ_def
  have hψ : IsTestFunctionOn puncturedCell ψ :=
    ⟨(Complex.ofRealCLM.contDiff.comp hη).mul hφ.contDiff, by
      refine HasCompactSupport.mul_right ?_
      refine hV₂k.of_isClosed_subset (isClosed_tsupport _) ?_
      rw [← hηt]
      exact closure_mono (fun p hp ↦ by simpa using hp), by
      refine tsupport_mul_subset_left.trans ?_
      refine (closure_mono (fun p hp ↦ ?_)).trans (hηt ▸ hV₂c)
      simpa using hp⟩
  have hnear (p : ℝ × ℝ) (hp : p ∈ B) : ψ =ᶠ[𝓝 p] φ := by
    filter_upwards [hV₁o.mem_nhds (hBV₁ hp)] with q hq
    simp [hψ_def, (hη1 q).1 (subset_closure hq)]
  have e1 : (fun p ↦ f p * coordPartial j ψ p) = fun p ↦ f p * coordPartial j φ p := by
    funext p
    by_cases hp : p ∈ B
    · rw [coordPartial_congr_nhds (hnear p hp)]
    · rw [hf p hp, zero_mul, zero_mul]
  have e2 : (fun p ↦ g p * ψ p) = fun p ↦ g p * φ p := by
    funext p
    by_cases hp : p ∈ B
    · rw [(hnear p hp).eq_of_nhds]
    · rw [hg p hp, zero_mul, zero_mul]
  have hw := hd.2.2 ψ hψ
  rwa [e1, e2] at hw

open scoped Classical in
/-- The chain rule in coordinates: `∂ⱼh · X + ∂ⱼθ · Y` on the punctured cell, with `angleGrad`
for `∂ⱼθ`, and zero elsewhere. -/
private def coordGrad (j : Fin 2) (X Y : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if p ∈ puncturedCell then
    ((coordPartial j levelCoord p : ℝ) : ℂ) * X (actionAngle p) + angleGrad j p * Y (actionAngle p)
  else 0

private theorem coordGrad_sub (j : Fin 2) (X Y X' Y' : ℝ × ℝ → ℂ) :
    coordGrad j X Y - coordGrad j X' Y' = coordGrad j (X - X') (Y - Y') := by
  funext p
  by_cases hc : p ∈ puncturedCell
  · simp only [Pi.sub_apply, coordGrad, ite_eq_left hc]
    ring
  · simp [coordGrad, hc]

/-- Coordinate gradients of band-supported cylinder data are in `L²` of the plane. -/
private theorem exists_coordGrad_bound {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ (j : Fin 2) (X Y : ℝ × ℝ → ℂ), MemLp X 2 cylinderMeasure →
      MemLp Y 2 cylinderMeasure → (∀ q : ℝ × ℝ, q.1 ∉ Icc a b → X q = 0) →
      (∀ q : ℝ × ℝ, q.1 ∉ Icc a b → Y q = 0) →
      MemLp (coordGrad j X Y) 2 volume ∧ eLpNorm (coordGrad j X Y) 2 volume ≤
        C * (eLpNorm X 2 cylinderMeasure + eLpNorm Y 2 cylinderMeasure) := by
  classical
  obtain ⟨Co, hCo⟩ := exists_actionReconstruct_bound ha hb
  set B := closedCellLevelBand a b with hB_def
  have hB : IsCompact B := isCompact_closedCellLevelBand a b
  have hBU : B ⊆ puncturedCell := closedCellLevelBand_subset ha hb
  have hmemB {p : ℝ × ℝ} (hc : p ∈ puncturedCell) (hl : levelCoord p ∈ Icc a b) : p ∈ B := by
    rw [hB_def, closedCellLevelBand_eq ha hb]
    exact ⟨hc, hl⟩
  have hlev : ContDiff ℝ ∞ levelCoord := by
    unfold levelCoord dipoleLift
    fun_prop
  have hAc (j : Fin 2) : Continuous (coordPartial j levelCoord) :=
    continuousOn_univ.mp (continuousOn_coordPartial isOpen_univ hlev.contDiffOn j)
  choose CA hCA using fun j ↦ hB.exists_bound_of_continuousOn (hAc j).continuousOn
  choose CB hCB using fun j ↦
    hB.exists_bound_of_continuousOn ((continuousOn_angleGrad j).mono hBU)
  set K : ℝ := max (max (CA 0) (CA 1)) (max (CB 0) (CB 1))
  have hKA (j : Fin 2) : CA j ≤ K := by
    fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hKB (j : Fin 2) : CB j ≤ K := by
    fin_cases j
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ENNReal.ofReal K * Co, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
    fun j X Y hX hY hXz hYz ↦ ?_⟩
  set RX : ℝ × ℝ → ℂ := fun p ↦
    if p ∈ puncturedCell then X (actionAngle p) else 0 with hRX_def
  set RY : ℝ × ℝ → ℂ := fun p ↦
    if p ∈ puncturedCell then Y (actionAngle p) else 0 with hRY_def
  have hrecX := hCo X hX hXz
  have hrecY := hCo Y hY hYz
  have hRX : MemLp RX 2 volume := MemLp.ae_eq (ae_actionReconstruct _) hrecX.1
  have hRY : MemLp RY 2 volume := MemLp.ae_eq (ae_actionReconstruct _) hrecY.1
  have hRXn : eLpNorm RX 2 volume ≤ Co * eLpNorm X 2 cylinderMeasure :=
    (eLpNorm_congr_ae (ae_actionReconstruct _)).symm.le.trans hrecX.2
  have hRYn : eLpNorm RY 2 volume ≤ Co * eLpNorm Y 2 cylinderMeasure :=
    (eLpNorm_congr_ae (ae_actionReconstruct _)).symm.le.trans hrecY.2
  have hRXz : ∀ p, RX p ≠ 0 → p ∈ B := by
    intro p hp
    by_cases hc : p ∈ puncturedCell
    · refine hmemB hc ?_
      by_contra hl
      exact hp (by simp only [hRX_def, ite_eq_left hc]; exact hXz (actionAngle p) hl)
    · simp [hRX_def, hc] at hp
  have hRYz : ∀ p, RY p ≠ 0 → p ∈ B := by
    intro p hp
    by_cases hc : p ∈ puncturedCell
    · refine hmemB hc ?_
      by_contra hl
      exact hp (by simp only [hRY_def, ite_eq_left hc]; exact hYz (actionAngle p) hl)
    · simp [hRY_def, hc] at hp
  set P1 : ℝ × ℝ → ℂ := fun p ↦ ((coordPartial j levelCoord p : ℝ) : ℂ) * RX p with hP1_def
  set P2 : ℝ × ℝ → ℂ := fun p ↦
    puncturedCell.piecewise (angleGrad j) (fun _ ↦ (0 : ℂ)) p * RY p with hP2_def
  have hdP : coordGrad j X Y = P1 + P2 := by
    funext p
    by_cases hc : p ∈ puncturedCell <;> simp [coordGrad, hP1_def, hP2_def, hRX_def, hRY_def, hc]
  have hP1 : ∀ p, ‖P1 p‖ ≤ K * ‖RX p‖ := by
    intro p
    by_cases h0 : RX p = 0
    · simp [hP1_def, h0]
    · rw [hP1_def, norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right ((hCA j p (hRXz p h0)).trans (hKA j)) (norm_nonneg _)
  have hP2 : ∀ p, ‖P2 p‖ ≤ K * ‖RY p‖ := by
    intro p
    by_cases h0 : RY p = 0
    · simp [hP2_def, h0]
    · have hpB := hRYz p h0
      rw [hP2_def, norm_mul, Set.piecewise_eq_of_mem _ _ _ (hBU hpB)]
      exact mul_le_mul_of_nonneg_right ((hCB j p hpB).trans (hKB j)) (norm_nonneg _)
  have hP1m : AEStronglyMeasurable P1 volume :=
    (Complex.continuous_ofReal.comp (hAc j)).aestronglyMeasurable.mul hRX.aestronglyMeasurable
  have hP2m : AEStronglyMeasurable P2 volume :=
    (ContinuousOn.measurable_piecewise (continuousOn_angleGrad j) continuousOn_const
      isOpen_puncturedCell.measurableSet).aestronglyMeasurable.mul hRY.aestronglyMeasurable
  have hP1n := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hP1m (Eventually.of_forall hP1) 2
  have hP2n := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hP2m (Eventually.of_forall hP2) 2
  rw [hdP]
  refine ⟨(hRX.of_le_mul hP1m (Eventually.of_forall hP1)).add
    (hRY.of_le_mul hP2m (Eventually.of_forall hP2)), ?_⟩
  calc eLpNorm (P1 + P2) 2 volume ≤ eLpNorm P1 2 volume + eLpNorm P2 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal K * (Co * eLpNorm X 2 cylinderMeasure) +
          ENNReal.ofReal K * (Co * eLpNorm Y 2 cylinderMeasure) :=
        add_le_add (hP1n.trans (by gcongr)) (hP2n.trans (by gcongr))
    _ = _ := by ring

/-! ### Helpers for the `H¹` convergence -/

/-- The level cutoff in the `h` direction: `∂_h (χU) = χ' U + χ ∂_h U`. -/
private theorem HasWeakPartialOn.levelCutoff₀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {U G : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn actionStrip 0 U G) :
    HasWeakPartialOn univ 0 (fun q ↦ (χ q.1 : ℂ) * U q)
      (fun q ↦ ((deriv χ q.1 : ℝ) : ℂ) * U q + (χ q.1 : ℂ) * G q) := by
  have hχ' : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hχ's : tsupport (deriv χ) ⊆ Ioo 0 1 := tsupport_deriv_subset.trans hχs
  have hCs : Prod.fst ⁻¹' tsupport χ ⊆ actionStrip := fun q hq ↦ ⟨hχs hq, mem_univ _⟩
  have hC's : Prod.fst ⁻¹' tsupport (deriv χ) ⊆ actionStrip := fun q hq ↦ ⟨hχ's hq, mem_univ _⟩
  refine ⟨locallyIntegrable_levelCutoff hχ.continuous hχs hd.1,
    (locallyIntegrable_levelCutoff hχ' hχ's hd.1).add
      (locallyIntegrable_levelCutoff hχ.continuous hχs hd.2.1), fun φ hφ ↦ ?_⟩
  have hcd : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)
  have hcd' : Continuous (fun q : ℝ × ℝ ↦ ((deriv χ q.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hχ'.comp continuous_fst)
  set ψ : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * φ q with hψ_def
  have hψ : IsTestFunctionOn actionStrip ψ :=
    ⟨hcd.mul hφ.contDiff, hφ.hasCompactSupport.mul_left,
      tsupport_mul_subset_left.trans (tsupport_levelCutoff_subset.trans hCs)⟩
  have hψd : coordPartial 0 ψ =
      fun q ↦ ((deriv χ q.1 : ℝ) : ℂ) * φ q + (χ q.1 : ℂ) * coordPartial 0 φ q := by
    funext q
    have hdφ : DifferentiableAt ℝ (fun t ↦ φ (t, q.2)) q.1 :=
      (hφ.contDiff.differentiable (by simp) _).comp q.1
        (differentiableAt_id.prodMk (differentiableAt_const q.2))
    have hdχ : HasDerivAt (fun t ↦ (χ t : ℂ)) ((deriv χ q.1 : ℝ) : ℂ) q.1 :=
      ((hχ.differentiable (by simp) q.1).hasDerivAt).ofReal_comp
    simp only [coordPartial, ite_true, partialX, hψ_def]
    exact (hdχ.mul hdφ.hasDerivAt).deriv
  have hw := hd.2.2 ψ hψ
  rw [hψd] at hw
  have i1 : Integrable fun p ↦ U p * (((deriv χ p.1 : ℝ) : ℂ) * φ p) :=
    integrable_mul_of_tsupport_subset hd.1 (hcd'.mul hφ.contDiff.continuous)
      hφ.hasCompactSupport.mul_left
      (tsupport_mul_subset_left.trans (tsupport_levelCutoff_subset.trans hC's))
  have i2 : Integrable fun p ↦ U p * ((χ p.1 : ℂ) * coordPartial 0 φ p) :=
    integrable_mul_of_tsupport_subset hd.1 (hcd.continuous.mul (hφ.continuous_coordPartial 0))
      (hφ.hasCompactSupport_coordPartial 0).mul_left
      (tsupport_mul_subset_left.trans (tsupport_levelCutoff_subset.trans hCs))
  have i3 : Integrable fun p ↦ G p * ψ p :=
    integrable_mul_of_tsupport_subset hd.2.1 (hcd.continuous.mul hφ.contDiff.continuous)
      hφ.hasCompactSupport.mul_left
      (tsupport_mul_subset_left.trans (tsupport_levelCutoff_subset.trans hCs))
  have e1 : (∫ p, U p * (((deriv χ p.1 : ℝ) : ℂ) * φ p + (χ p.1 : ℂ) * coordPartial 0 φ p)) =
      (∫ p, U p * (((deriv χ p.1 : ℝ) : ℂ) * φ p)) +
        ∫ p, U p * ((χ p.1 : ℂ) * coordPartial 0 φ p) := by
    rw [← integral_add i1 i2]
    congr 1; funext p; ring
  have e2 : (∫ p, (((deriv χ p.1 : ℝ) : ℂ) * U p + (χ p.1 : ℂ) * G p) * φ p) =
      (∫ p, U p * (((deriv χ p.1 : ℝ) : ℂ) * φ p)) + ∫ p, G p * ψ p := by
    rw [← integral_add i1 i3]
    congr 1; funext p; simp only [hψ_def]; ring
  have e3 : (∫ p, (χ p.1 : ℂ) * U p * coordPartial 0 φ p) =
      ∫ p, U p * ((χ p.1 : ℂ) * coordPartial 0 φ p) := by
    congr 1; funext p; ring
  rw [e1] at hw
  rw [e3, e2]
  linear_combination hw

private theorem coordPartial_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) (j : Fin 2) :
    coordPartial j f p = fderiv ℝ f p (if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)) := by
  unfold coordPartial
  split_ifs
  · exact partialX_eq_fderiv hf
  · exact partialY_eq_fderiv hf

/-- The classical chain rule for `(h, θ)⁻¹ ∘ (h, θ) = id` off the cut: for a linear form `ℓ`,
`∂ⱼh · ∂_h(ℓ ∘ P) + ∂ⱼθ · ∂_θ(ℓ ∘ P) = ℓ(eⱼ)`. -/
private theorem chainRule_actionAngle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) (ℓ : ℝ × ℝ →L[ℝ] E) (j : Fin 2) :
    coordPartial j levelCoord p • coordPartial 0 (fun q ↦ ℓ (actionAngleInv q)) (actionAngle p) +
      coordPartial j angleCoord p • coordPartial 1 (fun q ↦ ℓ (actionAngleInv q))
        (actionAngle p) = ℓ (if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)) := by
  have hlev : ContDiff ℝ ∞ levelCoord := by
    unfold levelCoord dipoleLift
    fun_prop
  have hld : DifferentiableAt ℝ levelCoord p := hlev.differentiable (by simp) p
  have hθd : DifferentiableAt ℝ angleCoord p :=
    (contDiffAt_angleCoord hp hcut).differentiableAt (by simp)
  have hA : HasFDerivAt actionAngle ((fderiv ℝ levelCoord p).prod (fderiv ℝ angleCoord p)) p :=
    hld.hasFDerivAt.prodMk hθd.hasFDerivAt
  have hstrip : actionAngle p ∈ actionStrip := ⟨(mem_orbitDomain hp).1, mem_univ _⟩
  have hPd : DifferentiableAt ℝ actionAngleInv (actionAngle p) :=
    (contDiffOn_actionAngleInv.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hstrip)).differentiableAt (by simp)
  set D := fderiv ℝ actionAngleInv (actionAngle p)
  set A := (fderiv ℝ levelCoord p).prod (fderiv ℝ angleCoord p)
  have hcomp : HasFDerivAt (actionAngleInv ∘ actionAngle) (D.comp A) p :=
    hPd.hasFDerivAt.comp p hA
  have hid : HasFDerivAt (actionAngleInv ∘ actionAngle) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p := by
    refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_puncturedCell.mem_nhds hp] with q hq
    exact actionAngleInv_actionAngle hq
  have hDA : D.comp A = ContinuousLinearMap.id ℝ (ℝ × ℝ) := hcomp.unique hid
  have hℓ : HasFDerivAt (fun q ↦ ℓ (actionAngleInv q)) (ℓ.comp D) (actionAngle p) :=
    ℓ.hasFDerivAt.comp _ hPd.hasFDerivAt
  set e : ℝ × ℝ := if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)
  have he := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ × ℝ ↦ ℓ (T e)) hDA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at he
  have hsplit : ((fderiv ℝ levelCoord p e, fderiv ℝ angleCoord p e) : ℝ × ℝ) =
      fderiv ℝ levelCoord p e • ((1 : ℝ), (0 : ℝ)) +
        fderiv ℝ angleCoord p e • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hAe : A e = (fderiv ℝ levelCoord p e, fderiv ℝ angleCoord p e) := rfl
  rw [hAe, hsplit, map_add, map_smul, map_smul, map_add, map_smul, map_smul] at he
  rw [coordPartial_eq_fderiv hld, coordPartial_eq_fderiv hθd,
    coordPartial_eq_fderiv hℓ.differentiableAt, coordPartial_eq_fderiv hℓ.differentiableAt,
    hℓ.fderiv]
  simpa using he

/-- Off the angle cut, multiplying the dual field by the area density gives `∂_h P`. -/
theorem levelDualCoeff_normalized {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) :
    ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * levelDualCoeff 0 p =
      ((coordPartial 0 (fun q ↦ (actionAngleInv q).1) (actionAngle p) : ℝ) : ℂ) ∧
    ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * levelDualCoeff 1 p =
      ((coordPartial 0 (fun q ↦ (actionAngleInv q).2) (actionAngle p) : ℝ) : ℂ) := by
  let q := actionAngle p
  let X := coordPartial 0 (fun r ↦ (actionAngleInv r).1) q
  let Y := coordPartial 0 (fun r ↦ (actionAngleInv r).2) q
  let T := coordPartial 1 (fun r ↦ (actionAngleInv r).1) q
  let V := coordPartial 1 (fun r ↦ (actionAngleInv r).2) q
  let S := orbitPeriod (levelCoord p)
  have hq : q ∈ actionStrip := ⟨(mem_orbitDomain hp).1, mem_univ _⟩
  have hP : actionAngleInv q = p := actionAngleInv_actionAngle hp
  have hd := (contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have hdx : HasDerivAt (fun h ↦ (actionAngleInv (h, q.2)).1) X q.1 :=
    hasDerivAt_partialX ((ContinuousLinearMap.fst ℝ ℝ ℝ).differentiableAt.comp q hd)
  have hdy : HasDerivAt (fun h ↦ (actionAngleInv (h, q.2)).2) Y q.1 :=
    hasDerivAt_partialX ((ContinuousLinearMap.snd ℝ ℝ ℝ).differentiableAt.comp q hd)
  have he : (fun h ↦ (Real.cos (actionAngleInv (h, q.2)).1 +
      Real.cos (actionAngleInv (h, q.2)).2) / 2) =ᶠ[𝓝 q.1] id := by
    filter_upwards [isOpen_Ioo.mem_nhds hq.1] with h hh
    exact levelCoord_actionAngleInv hh.1 hh.2 q.2
  have hn := (((hdx.cos.add hdy.cos).div_const 2).congr_of_eventuallyEq he.symm).unique
    (hasDerivAt_id q.1)
  change (-Real.sin (actionAngleInv q).1 * X + -Real.sin (actionAngleInv q).2 * Y) / 2 = 1 at hn
  rw [hP] at hn
  have hnormal : -Real.sin p.1 * X - Real.sin p.2 * Y = 2 := by linarith
  have ht : T = S * Real.sin p.2 := by
    change coordPartial 1 (fun r ↦ (actionAngleInv r).1) q = orbitPeriod q.1 * Real.sin p.2
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def, hP] using
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have hv : V = S * (-Real.sin p.1) := by
    change coordPartial 1 (fun r ↦ (actionAngleInv r).2) q = orbitPeriod q.1 * (-Real.sin p.1)
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def, hP] using
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have hdet : X * V - T * Y = 2 * S := by
    rw [ht, hv]
    linear_combination S * hnormal
  have hyx := chainRule_actionAngle hp hcut (ContinuousLinearMap.fst ℝ ℝ ℝ) 1
  have hyy := chainRule_actionAngle hp hcut (ContinuousLinearMap.snd ℝ ℝ ℝ) 1
  have hxx := chainRule_actionAngle hp hcut (ContinuousLinearMap.fst ℝ ℝ ℝ) 0
  have hxy := chainRule_actionAngle hp hcut (ContinuousLinearMap.snd ℝ ℝ ℝ) 0
  change coordPartial 1 levelCoord p * X + coordPartial 1 angleCoord p * T = 0 at hyx
  change coordPartial 1 levelCoord p * Y + coordPartial 1 angleCoord p * V = 1 at hyy
  change coordPartial 0 levelCoord p * X + coordPartial 0 angleCoord p * T = 1 at hxx
  change coordPartial 0 levelCoord p * Y + coordPartial 0 angleCoord p * V = 0 at hxy
  have hcy : (2 * S) * coordPartial 1 angleCoord p = X := by
    calc _ = (X * V - T * Y) * coordPartial 1 angleCoord p := by rw [hdet]
      _ = X * (coordPartial 1 levelCoord p * Y + coordPartial 1 angleCoord p * V) -
          Y * (coordPartial 1 levelCoord p * X + coordPartial 1 angleCoord p * T) := by ring
      _ = X := by rw [hyy, hyx]; ring
  have hcx : (2 * S) * coordPartial 0 angleCoord p = -Y := by
    calc _ = (X * V - T * Y) * coordPartial 0 angleCoord p := by rw [hdet]
      _ = X * (coordPartial 0 levelCoord p * Y + coordPartial 0 angleCoord p * V) -
          Y * (coordPartial 0 levelCoord p * X + coordPartial 0 angleCoord p * T) := by ring
      _ = -Y := by rw [hxy, hxx]; ring
  constructor
  · rw [levelDualCoeff_eq hp hcut 0]
    change ((2 * S : ℝ) : ℂ) * ((coordPartial 1 angleCoord p : ℝ) : ℂ) = (X : ℂ)
    exact_mod_cast hcy
  · rw [levelDualCoeff_eq hp hcut 1]
    change ((2 * S : ℝ) : ℂ) * -((coordPartial 0 angleCoord p : ℝ) : ℂ) = (Y : ℂ)
    have he : (2 * S) * (-coordPartial 0 angleCoord p) = Y := by linarith
    exact_mod_cast he

private theorem partialX_comp_actionAngleInv {φ : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hq : q ∈ actionStrip) (hφ : DifferentiableAt ℝ φ (actionAngleInv q)) :
    partialX (φ ∘ actionAngleInv) q =
      ((coordPartial 0 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ) *
        coordPartial 0 φ (actionAngleInv q) +
      ((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ) *
        coordPartial 1 φ (actionAngleInv q) := by
  have hd := (contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have hx := hasDerivAt_partialX
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).differentiableAt.comp q hd)
  have hy := hasDerivAt_partialX
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).differentiableAt.comp q hd)
  have hc := hφ.hasFDerivAt.comp_hasDerivAt q.1 (hx.prodMk hy)
  have he : partialX (φ ∘ actionAngleInv) q =
      fderiv ℝ φ (actionAngleInv q)
        (partialX (fun r ↦ (actionAngleInv r).1) q, partialX (fun r ↦ (actionAngleInv r).2) q) :=
    hc.deriv
  rw [he]
  have hs : (partialX (fun r ↦ (actionAngleInv r).1) q,
      partialX (fun r ↦ (actionAngleInv r).2) q) =
      partialX (fun r ↦ (actionAngleInv r).1) q • ((1 : ℝ), (0 : ℝ)) +
        partialX (fun r ↦ (actionAngleInv r).2) q • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hs, map_add, map_smul, map_smul, ← partialX_eq_fderiv hφ, ← partialY_eq_fderiv hφ]
  simp only [Complex.real_smul, coordPartial, ↓reduceIte, Fin.reduceEq]

private theorem partialX_actionAngleInv_add_one {q : ℝ × ℝ} (hq : q ∈ actionStrip)
    (ℓ : ℝ × ℝ →L[ℝ] ℝ) :
    partialX (fun r ↦ ℓ (actionAngleInv r)) (q.1, q.2 + 1) =
      partialX (fun r ↦ ℓ (actionAngleInv r)) q := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hq.1] with h hh
  rw [actionAngleInv_add_one hh.1 hh.2]

private theorem ae_actionAngleInv_off_diagonal :
    ∀ᵐ q ∂actionMeasure, (diagCoord (actionAngleInv q)).2 ≠ 0 := by
  have hn : ∀ᵐ p ∂(volume.restrict cellSquare), (diagCoord p).2 ≠ 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero)
  have hp := measurePreserving_actionParam.quasiMeasurePreserving.ae hn
  have hb := (ae_withDensity_iff measurable_actionWeight).mp hp
  filter_upwards [hb, actionWeight_ne_zero,
    ae_restrict_mem measurableSet_actionRectangle] with q hq hw hr
  have he : actionParam q = actionAngleInv q := by simp [actionParam, piecewise, hr]
  simpa only [he] using hq hw

private theorem partialX_periodicCellTest_pull {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    partialX (periodicCellTest F ∘ actionAngleInv) q = partialX F q := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hq.1] with h hh
  have hp := actionAngleInv_mem_puncturedCell hh.1 hh.2 q.2
  change periodicCellTest F (actionAngleInv (h, q.2)) = F (h, q.2)
  rw [periodicCellTest, indicator_of_mem hp]
  exact comp_actionAngle_actionAngleInv hper ⟨hh, mem_univ _⟩

/-- The chain rule for weak derivatives in the level variable, from the cell to the strip. -/
theorem HasWeakPartialOn.comp_actionAngleInv_fst {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) :
    HasWeakPartialOn actionStrip 0 (u ∘ actionAngleInv) (fun q ↦
      ((coordPartial 0 (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial 0 (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) := by
  refine ⟨locallyIntegrableOn_comp_actionAngleInv (hg 0).1,
    locallyIntegrableOn_actionAngleInv_gradient (fun i ↦ (hg i).2.1) 0, ?_⟩
  intro φ hφ
  let D : ℝ × ℝ → ℂ := fun q ↦
    ((coordPartial 0 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
      ((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)
  have hD := locallyIntegrableOn_actionAngleInv_gradient (fun i ↦ (hg i).2.1) 0
  have hpD : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 → D (q.1, q.2 + 1) = D q := by
    intro q hq
    have hx := partialX_actionAngleInv_add_one (q := q) ⟨hq, mem_univ _⟩
      (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have hy := partialX_actionAngleInv_add_one (q := q) ⟨hq, mem_univ _⟩
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
    change coordPartial 0 (fun r ↦ (actionAngleInv r).1) (q.1, q.2 + 1) =
      coordPartial 0 (fun r ↦ (actionAngleInv r).1) q at hx
    change coordPartial 0 (fun r ↦ (actionAngleInv r).2) (q.1, q.2 + 1) =
      coordPartial 0 (fun r ↦ (actionAngleInv r).2) q at hy
    dsimp only [D]
    rw [hx, hy, actionAngleInv_add_one hq.1 hq.2]
  have hpu : ∀ q : ℝ × ℝ, q.1 ∈ Ioo (0 : ℝ) 1 →
      (u ∘ actionAngleInv) (q.1, q.2 + 1) = (u ∘ actionAngleInv) q := by
    intro q hq
    simp only [Function.comp_apply, actionAngleInv_add_one hq.1 hq.2]
  have hφx : IsTestFunctionOn actionStrip (partialX φ) :=
    ⟨by simpa [coordPartial] using contDiff_coordPartial_top 0 hφ.contDiff,
      by simpa [coordPartial] using hφ.hasCompactSupport_coordPartial 0,
      (tsupport_partialX_subset φ).trans hφ.tsupport_subset⟩
  obtain ⟨a, b, ha, hb, hs⟩ := exists_test_level_band hφ.hasCompactSupport continuous_fst
    (fun q hq ↦ (hφ.tsupport_subset hq).1)
  let F := periodizeSnd φ
  have hF : ContDiff ℝ ∞ F := contDiff_periodizeSnd hφ.contDiff
    (HasCompactSupport.hasBoundedSndSupport hφ.hasCompactSupport)
  have hpF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q := periodizeSnd_periodic
  have hzF : ∀ q, q.1 ∉ Icc a b → F q = 0 :=
    fun q hq ↦ periodizeSnd_eq_zero (fun z hz ↦ by
      by_contra hn
      exact hz (hs z hn)) hq
  let ψ := periodicCellTest F
  have hψ : IsTestFunctionOn puncturedCell ψ := isTestFunctionOn_periodicCellTest ha hb hF hpF hzF
  have hDF : partialX F = periodizeSnd (partialX φ) := funext fun q ↦
    partialX_periodizeSnd (hφ.contDiff.of_le (by simp))
      (HasCompactSupport.hasBoundedSndSupport hφ.hasCompactSupport) q
  let op : ℝ × ℝ → ℂ := fun p ↦ levelDualCoeff 0 p * coordPartial 0 ψ p +
    levelDualCoeff 1 p * coordPartial 1 ψ p
  have hO (j : Fin 2) : IsTestFunctionOn puncturedCell
      (fun p ↦ levelDualCoeff j p * coordPartial j ψ p) := by
    have hdψ : IsTestFunctionOn puncturedCell (coordPartial j ψ) :=
      ⟨contDiff_coordPartial_top j hψ.contDiff, hψ.hasCompactSupport_coordPartial j,
        (tsupport_coordPartial_subset j ψ).trans hψ.tsupport_subset⟩
    exact hdψ.mul_contDiffOn isOpen_puncturedCell (contDiffOn_levelDualCoeff j)
  have hop : IsTestFunctionOn puncturedCell op :=
    ⟨(hO 0).contDiff.add (hO 1).contDiff, (hO 0).hasCompactSupport.add (hO 1).hasCompactSupport,
      (tsupport_add _ _).trans (union_subset (hO 0).tsupport_subset (hO 1).tsupport_subset)⟩
  let k : ℝ × ℝ → ℂ := fun p ↦ levelDualCoeff 0 p * g 0 p + levelDualCoeff 1 p * g 1 p
  have hk : LocallyIntegrableOn k puncturedCell :=
    ((hg 0).2.1.continuousOn_mul (contDiffOn_levelDualCoeff 0).continuousOn
      isOpen_puncturedCell.isLocallyClosed).add
      ((hg 1).2.1.continuousOn_mul (contDiffOn_levelDualCoeff 1).continuousOn
        isOpen_puncturedCell.isLocallyClosed)
  have hnorm (q : ℝ × ℝ) (hq : q ∈ actionRectangle)
      (hn : (diagCoord (actionAngleInv q)).2 ≠ 0) :
      ((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 0 (actionAngleInv q) =
        ((coordPartial 0 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ) ∧
      ((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 1 (actionAngleInv q) =
        ((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ) := by
    have he := levelDualCoeff_normalized
      (actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2) (fun h ↦ hn h.1)
    rw [levelCoord_actionAngleInv hq.1.1 hq.1.2,
      actionAngle_actionAngleInv hq.1.1 hq.1.2 hq.2] at he
    exact he
  have hleft : (∫ p, u p * op p) = ∫ q, (u ∘ actionAngleInv) q * partialX φ q := by
    rw [integral_mul_test_actionAngle (hg 0).1 hop,
      integral_strip_test_periodize (locallyIntegrableOn_comp_actionAngleInv (hg 0).1) hpu hφx]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle,
      ae_actionAngleInv_off_diagonal] with q hq hn
    have hN := hnorm q hq hn
    have hchain : partialX F q =
        ((coordPartial 0 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ) *
          coordPartial 0 ψ (actionAngleInv q) +
        ((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ) *
          coordPartial 1 ψ (actionAngleInv q) := by
      rw [← partialX_periodicCellTest_pull hpF ⟨hq.1, mem_univ _⟩]
      exact partialX_comp_actionAngleInv ⟨hq.1, mem_univ _⟩
        (hψ.contDiff.differentiable (by simp) _)
    change ((2 * orbitPeriod q.1 : ℝ) : ℂ) * (u (actionAngleInv q) * op (actionAngleInv q)) =
      u (actionAngleInv q) * periodizeSnd (partialX φ) q
    rw [← hDF]
    dsimp only [op]
    calc _ = u (actionAngleInv q) *
          ((((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 0 (actionAngleInv q)) *
              coordPartial 0 ψ (actionAngleInv q) +
            (((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 1 (actionAngleInv q)) *
              coordPartial 1 ψ (actionAngleInv q)) := by ring
      _ = u (actionAngleInv q) * partialX F q := by rw [hN.1, hN.2, ← hchain]
  have hright : (∫ p, k p * ψ p) = ∫ q, D q * φ q := by
    rw [integral_mul_test_actionAngle hk hψ, integral_strip_test_periodize hD hpD hφ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle,
      ae_actionAngleInv_off_diagonal] with q hq hn
    have hN := hnorm q hq hn
    have he : ψ (actionAngleInv q) = F q := by
      change periodicCellTest F (actionAngleInv q) = F q
      rw [periodicCellTest, indicator_of_mem
        (actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2)]
      exact comp_actionAngle_actionAngleInv hpF ⟨hq.1, mem_univ _⟩
    change ((2 * orbitPeriod q.1 : ℝ) : ℂ) * (k (actionAngleInv q) * ψ (actionAngleInv q)) =
      D q * F q
    rw [he]
    dsimp only [k, D]
    calc _ =
        ((((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 0 (actionAngleInv q)) *
            g 0 (actionAngleInv q) +
          (((2 * orbitPeriod q.1 : ℝ) : ℂ) * levelDualCoeff 1 (actionAngleInv q)) *
            g 1 (actionAngleInv q)) * F q := by ring
      _ = _ := by rw [hN.1, hN.2]
  have hw := integral_mul_levelDualCoeff hg hψ
  change (∫ p, u p * op p) = -∫ p, k p * ψ p at hw
  rw [hleft, hright] at hw
  exact hw

/-- The full chain rule from the cell to the strip, assembled from the two
    coordinate derivatives. -/
theorem HasWeakPartialOn.comp_actionAngleInv {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) (j : Fin 2) :
    HasWeakPartialOn actionStrip j (u ∘ actionAngleInv) (fun q ↦
      ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) := by
  fin_cases j
  · exact HasWeakPartialOn.comp_actionAngleInv_fst hg
  · exact HasWeakPartialOn.comp_actionAngleInv_snd hg

/-! ### Cofactors for the reverse weak-gradient rule -/

private theorem add_snd_eq (q : ℝ × ℝ) (r : ℝ) : q + (0, r) = (q.1, q.2 + r) := by
  ext <;> simp

private def stripDualPotential (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  if j = 0 then ((actionAngleInv q).2 : ℂ) else -((actionAngleInv q).1 : ℂ)

private def stripCofactor (j i : Fin 2) (q : ℝ × ℝ) : ℂ :=
  if i = 0 then partialY (stripDualPotential j) q else -partialX (stripDualPotential j) q

private theorem contDiffOn_stripDualPotential (j : Fin 2) :
    ContDiffOn ℝ ∞ (stripDualPotential j) actionStrip := by
  have hx := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv)
  have hy := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv)
  fin_cases j
  · change ContDiffOn ℝ ∞ (fun q ↦ ((actionAngleInv q).2 : ℂ)) actionStrip
    exact hy
  · change ContDiffOn ℝ ∞ (fun q ↦ -((actionAngleInv q).1 : ℂ)) actionStrip
    exact hx.neg

private theorem contDiffOn_stripCofactor (j i : Fin 2) :
    ContDiffOn ℝ ∞ (stripCofactor j i) actionStrip := by
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  fin_cases i
  · change ContDiffOn ℝ ∞ (partialY (stripDualPotential j)) actionStrip
    exact contDiffOn_coordPartial ho (contDiffOn_stripDualPotential j) 1
  · change ContDiffOn ℝ ∞ (fun q ↦ -partialX (stripDualPotential j) q) actionStrip
    exact (contDiffOn_coordPartial ho (contDiffOn_stripDualPotential j) 0).neg

private theorem stripCofactor_periodic (j i : Fin 2) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    stripCofactor j i (q.1, q.2 + 1) = stripCofactor j i q := by
  have he : (fun r : ℝ × ℝ ↦ stripDualPotential j (r + (0, 1))) =ᶠ[𝓝 q]
      stripDualPotential j := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hq] with r hr
    simp [add_snd_eq, stripDualPotential, actionAngleInv_add_one hr.1.1 hr.1.2]
  have hx := coordPartial_congr_nhds he 0
  have hy := coordPartial_congr_nhds he 1
  simp only [coordPartial_translate] at hx hy
  have hx' : partialX (stripDualPotential j) (q.1, q.2 + 1) =
      partialX (stripDualPotential j) q := by simpa [coordPartial, add_snd_eq] using hx
  have hy' : partialY (stripDualPotential j) (q.1, q.2 + 1) =
      partialY (stripDualPotential j) q := by simpa [coordPartial, add_snd_eq] using hy
  fin_cases i <;> simp [stripCofactor, hx', hy']

/-- The Piola cancellation for a two-dimensional cofactor column. -/
private theorem stripCofactor_divergence (j : Fin 2) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    coordPartial 0 (stripCofactor j 0) q + coordPartial 1 (stripCofactor j 1) q = 0 := by
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hf := (contDiffOn_stripDualPotential j).contDiffAt (ho.mem_nhds hq)
  have hx : DifferentiableAt ℝ (partialX (stripDualPotential j)) q := by
    simpa [coordPartial] using
      ((contDiffOn_coordPartial ho (contDiffOn_stripDualPotential j) 0).contDiffAt
        (ho.mem_nhds hq)).differentiableAt (by simp)
  have hn := (hasDerivAt_partialY hx).neg.deriv
  change partialY (fun r ↦ -partialX (stripDualPotential j) r) q =
    -partialY (partialX (stripDualPotential j)) q at hn
  change partialX (partialY (stripDualPotential j)) q +
    partialY (fun r ↦ -partialX (stripDualPotential j) r) q = 0
  rw [hn, partialY_partialX_at hf]
  ring

private theorem coordPartial_ofReal {f : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f q) (i : Fin 2) :
    coordPartial i (fun r ↦ (f r : ℂ)) q = ((coordPartial i f q : ℝ) : ℂ) := by
  fin_cases i
  · exact (hasDerivAt_partialX hf).ofReal_comp.deriv
  · exact (hasDerivAt_partialY hf).ofReal_comp.deriv

private theorem coordPartial_neg {f : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f q) (i : Fin 2) :
    coordPartial i (fun r ↦ -f r) q = -coordPartial i f q := by
  fin_cases i
  · exact (hasDerivAt_partialX hf).neg.deriv
  · exact (hasDerivAt_partialY hf).neg.deriv

private theorem stripCofactor_eq (j i : Fin 2) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    stripCofactor j i q = if j = 0 then
      (if i = 0 then ((coordPartial 1 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ)
        else -((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ))
      else (if i = 0 then -((coordPartial 1 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ)
        else ((coordPartial 0 (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ)) := by
  have hd := (contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).differentiableAt.comp q hd
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).differentiableAt.comp q hd
  have hxc := Complex.ofRealCLM.differentiableAt.comp q hx
  fin_cases j <;> fin_cases i
  · change partialY (fun r ↦ ((actionAngleInv r).2 : ℂ)) q =
      ((partialY (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ)
    exact coordPartial_ofReal hy 1
  · change -partialX (fun r ↦ ((actionAngleInv r).2 : ℂ)) q =
      -((partialX (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ)
    exact congrArg Neg.neg (coordPartial_ofReal hy 0)
  · change partialY (fun r ↦ -((actionAngleInv r).1 : ℂ)) q =
      -((partialY (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ)
    exact (coordPartial_neg hxc 1).trans (congrArg Neg.neg (coordPartial_ofReal hx 1))
  · change -partialX (fun r ↦ -((actionAngleInv r).1 : ℂ)) q =
      ((partialX (fun r ↦ (actionAngleInv r).1) q : ℝ) : ℂ)
    have he := (coordPartial_neg hxc 0).trans (congrArg Neg.neg (coordPartial_ofReal hx 0))
    change partialX (fun r ↦ -((actionAngleInv r).1 : ℂ)) q = _ at he
    rw [he, neg_neg]
    rfl

/-- The strip cofactor column equals the area density times the inverse coordinate row. -/
private theorem stripCofactor_normalized {p : ℝ × ℝ} (hp : p ∈ puncturedCell)
    (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1)) (j : Fin 2) :
    stripCofactor j 0 (actionAngle p) =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * ((coordPartial j levelCoord p : ℝ) : ℂ) ∧
      stripCofactor j 1 (actionAngle p) =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * angleGrad j p := by
  let q := actionAngle p
  have hq : q ∈ actionStrip := ⟨(mem_orbitDomain hp).1, mem_univ _⟩
  have hP : actionAngleInv q = p := actionAngleInv_actionAngle hp
  have hA00 := stripCofactor_eq 0 0 hq
  have hA01 := stripCofactor_eq 0 1 hq
  have hA10 := stripCofactor_eq 1 0 hq
  have hA11 := stripCofactor_eq 1 1 hq
  norm_num at hA00 hA01 hA10 hA11
  have ht : coordPartial 1 (fun r ↦ (actionAngleInv r).1) q =
      orbitPeriod (levelCoord p) * Real.sin p.2 := by
    change coordPartial 1 (fun r ↦ (actionAngleInv r).1) q = orbitPeriod q.1 * Real.sin p.2
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def, hP] using
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have hv : coordPartial 1 (fun r ↦ (actionAngleInv r).2) q =
      orbitPeriod (levelCoord p) * (-Real.sin p.1) := by
    change coordPartial 1 (fun r ↦ (actionAngleInv r).2) q = orbitPeriod q.1 * (-Real.sin p.1)
    simpa [coordPartial, partialY, dipoleVelocity, smul_eq_mul, Function.comp_def, hP] using
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2
        (hasDerivAt_actionAngleInv_snd q.1 q.2)).deriv
  have hlx : coordPartial 0 levelCoord p = -Real.sin p.1 / 2 := by
    simp [coordPartial, levelCoord, dipoleLift, partialX]
  have hly : coordPartial 1 levelCoord p = -Real.sin p.2 / 2 := by
    simp [coordPartial, levelCoord, dipoleLift, partialY]
  obtain ⟨hnx, hny⟩ := levelDualCoeff_normalized hp hcut
  change ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * angleGrad 1 p = _ at hnx
  change ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * (-angleGrad 0 p) = _ at hny
  fin_cases j
  · constructor
    · change stripCofactor 0 0 q =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * ((coordPartial 0 levelCoord p : ℝ) : ℂ)
      rw [hA00, hv, hlx]
      push_cast
      ring
    · change stripCofactor 0 1 q =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * angleGrad 0 p
      change ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * (-angleGrad 0 p) =
        ((coordPartial 0 (fun r ↦ (actionAngleInv r).2) q : ℝ) : ℂ) at hny
      rw [hA01, ← hny]
      ring
  · constructor
    · change stripCofactor 1 0 q =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * ((coordPartial 1 levelCoord p : ℝ) : ℂ)
      rw [hA10, ht, hly]
      push_cast
      ring
    · exact hA11.trans hnx.symm

private theorem stripCofactor_chain {φ : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hp : p ∈ puncturedCell) (hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1))
    (hφ : DifferentiableAt ℝ φ p) (j : Fin 2) :
    stripCofactor j 0 (actionAngle p) * coordPartial 0 (φ ∘ actionAngleInv) (actionAngle p) +
      stripCofactor j 1 (actionAngle p) * coordPartial 1 (φ ∘ actionAngleInv) (actionAngle p) =
        ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * coordPartial j φ p := by
  let q := actionAngle p
  let ℓ := fderiv ℝ φ p
  have hq : q ∈ actionStrip := ⟨(mem_orbitDomain hp).1, mem_univ _⟩
  have hP : actionAngleInv q = p := actionAngleInv_actionAngle hp
  have hd := (contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have hφ' : DifferentiableAt ℝ φ (actionAngleInv q) := by rwa [hP]
  have hcomp := hφ'.hasFDerivAt.comp q hd.hasFDerivAt
  have hlin := ℓ.hasFDerivAt.comp q hd.hasFDerivAt
  have he (i : Fin 2) : coordPartial i (fun r ↦ ℓ (actionAngleInv r)) q =
      coordPartial i (φ ∘ actionAngleInv) q := by
    change coordPartial i (⇑ℓ ∘ actionAngleInv) q = _
    rw [coordPartial_eq_fderiv hlin.differentiableAt,
      coordPartial_eq_fderiv hcomp.differentiableAt, hlin.fderiv, hcomp.fderiv, hP]
  have hchain := chainRule_actionAngle hp hcut ℓ j
  rw [Complex.real_smul, Complex.real_smul, he 0, he 1] at hchain
  have hlast : ℓ (if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1)) = coordPartial j φ p :=
    (coordPartial_eq_fderiv hφ j).symm
  rw [hlast] at hchain
  obtain ⟨hN₀, hN₁⟩ := stripCofactor_normalized hp hcut j
  rw [hN₀, hN₁, angleGrad_eq hp hcut j]
  linear_combination ((2 * orbitPeriod (levelCoord p) : ℝ) : ℂ) * hchain

private theorem coordPartial_mul_at {f g : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) (i : Fin 2) :
    coordPartial i (fun r ↦ f r * g r) q =
      coordPartial i f q * g q + f q * coordPartial i g q := by
  fin_cases i
  · exact partialX_mul hf hg
  · exact partialY_mul hf hg

private def cofactorTest (j i : Fin 2) (φ : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  stripCofactor j i q * stripTestPull φ q

private theorem cofactorTest_properties (j i : Fin 2) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn puncturedCell φ) :
    ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ ContDiff ℝ ∞ (cofactorTest j i φ) ∧
      (∀ q : ℝ × ℝ, cofactorTest j i φ (q.1, q.2 + 1) = cofactorTest j i φ q) ∧
      ∀ q, q.1 ∉ Icc a b → cofactorTest j i φ q = 0 := by
  obtain ⟨a, b, ha, hb, hT, hpT, hzT⟩ := stripTestPull_properties hφ
  have hz : ∀ q, q.1 ∉ Icc a b → cofactorTest j i φ q = 0 := by
    intro q hq
    simp only [cofactorTest, hzT q hq, mul_zero]
  have hK : IsClosed {q : ℝ × ℝ | q.1 ∈ Icc a b} := isClosed_Icc.preimage continuous_fst
  have hKU : {q : ℝ × ℝ | q.1 ∈ Icc a b} ⊆ actionStrip := fun q hq ↦
    ⟨⟨lt_of_lt_of_le ha hq.1, lt_of_le_of_lt hq.2 hb⟩, mem_univ _⟩
  refine ⟨a, b, ha, hb, contDiff_of_zero_off_closed (isOpen_Ioo.prod isOpen_univ)
    hK hKU ((contDiffOn_stripCofactor j i).mul hT.contDiffOn) hz, ?_, hz⟩
  intro q
  by_cases hq : q.1 ∈ Ioo (0 : ℝ) 1
  · simp only [cofactorTest, stripCofactor_periodic j i ⟨hq, mem_univ _⟩, hpT q]
  · simp [cofactorTest, stripTestPull, actionStrip, hq]

private theorem cofactorTest_deriv (j i : Fin 2) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn puncturedCell φ) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    coordPartial i (cofactorTest j i φ) q =
      coordPartial i (stripCofactor j i) q * φ (actionAngleInv q) +
        stripCofactor j i q * coordPartial i (φ ∘ actionAngleInv) q := by
  have ho : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have he : stripTestPull φ =ᶠ[𝓝 q] φ ∘ actionAngleInv := by
    filter_upwards [ho.mem_nhds hq] with r hr
    exact Set.indicator_of_mem hr _
  have hT := (stripTestPull_properties hφ).choose_spec.choose_spec.2.2.1
  change coordPartial i (fun r ↦ stripCofactor j i r * stripTestPull φ r) q = _
  rw [coordPartial_mul_at
    (((contDiffOn_stripCofactor j i).contDiffAt (ho.mem_nhds hq)).differentiableAt (by simp))
    (hT.differentiable (by simp) q) i, coordPartial_congr_nhds he i,
    show stripTestPull φ q = φ (actionAngleInv q) from he.eq_of_nhds]

private theorem periodize_coordPartial_cutoff {H : ℝ × ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) (hpH : ∀ q : ℝ × ℝ, H (q.1, q.2 + 1) = H q)
    (i : Fin 2) (q : ℝ × ℝ) :
    periodizeSnd (coordPartial i (cutoffPeriodicSnd H)) q = coordPartial i H q := by
  have hσ : ContDiff ℝ ∞ (cutoffPeriodicSnd H) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_anglePartition).mul hH
  have he : periodizeSnd (cutoffPeriodicSnd H) = H := funext (periodize_cutoffPeriodicSnd hpH)
  fin_cases i
  · have hd := partialX_periodizeSnd (hσ.of_le (by simp)) (bounded_cutoffPeriodicSnd H) q
    rw [he] at hd
    exact hd.symm
  · exact periodize_partialY_cutoffPeriodicSnd hH hpH q

private theorem integrable_actionMeasure_mul_band {A H : ℝ × ℝ → ℂ} {a b : ℝ}
    (hA : LocallyIntegrableOn A actionStrip) (ha : 0 < a) (hb : b < 1)
    (hH : Continuous H) (hz : ∀ q, q.1 ∉ Icc a b → H q = 0) :
    Integrable (fun q ↦ A q * H q) actionMeasure := by
  let K := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨lt_of_lt_of_le ha hq.1.1, lt_of_le_of_lt hq.1.2 hb⟩, mem_univ _⟩
  have hi := (hA.integrableOn_compact_subset hKU hK).mul_continuousOn hH.continuousOn hK
  have hi' : IntegrableOn (fun q ↦ A q * H q) K actionMeasure :=
    hi.mono_measure Measure.restrict_le_self
  apply hi'.integrable_of_ae_notMem_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_actionRectangle] with q hq hqK
  have hn : q.1 ∉ Icc a b := fun hh ↦ hqK ⟨hh, hq.2.1, hq.2.2.le⟩
  rw [hz q hn, mul_zero]

private theorem band_coordPartial_zero {H : ℝ × ℝ → ℂ} {a b : ℝ}
    (hz : ∀ q, q.1 ∉ Icc a b → H q = 0) (i : Fin 2) :
    ∀ q, q.1 ∉ Icc a b → coordPartial i H q = 0 := by
  have hs : tsupport H ⊆ {q : ℝ × ℝ | q.1 ∈ Icc a b} :=
    closure_minimal (fun q hq ↦ by_contra fun hn ↦ hq (hz q hn))
      (isClosed_Icc.preimage continuous_fst)
  exact fun q hq ↦ image_eq_zero_of_notMem_tsupport
    (fun ht ↦ hq (hs (tsupport_coordPartial_subset i H ht)))

/-! ### Periodic representatives of weak strip derivatives -/

private theorem measurePreserving_sndShift (r : ℝ) :
    MeasurePreserving (MeasurableEquiv.addRight ((0 : ℝ), r)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume (0 : ℝ)).prod
    (measurePreserving_add_right volume r)

private theorem locallyIntegrableOn_sndShift {A : ℝ × ℝ → ℂ}
    (hA : LocallyIntegrableOn A actionStrip) (r : ℝ) :
    LocallyIntegrableOn (fun q ↦ A (q.1, q.2 + r)) actionStrip := by
  apply (locallyIntegrableOn_iff (isOpen_Ioo.prod isOpen_univ).isLocallyClosed).2
  intro K hKU hK
  have hi := hA.integrableOn_compact_subset
    (show (fun q : ℝ × ℝ ↦ q + (0, r)) '' K ⊆ actionStrip from by
      rintro _ ⟨q, hq, rfl⟩
      simpa [actionStrip] using hKU hq)
    (hK.image (continuous_id.add continuous_const))
  have h := (measurePreserving_sndShift r).integrableOn_image
    (MeasurableEquiv.addRight ((0 : ℝ), r)).measurableEmbedding |>.mp hi
  change IntegrableOn (fun q ↦ A (q + (0, r))) K volume at h
  convert h using 1
  funext q
  congr 1
  ext <;> simp

/-- Periodicity of a weakly differentiable function forces periodicity of each
weak derivative a.e.; no pointwise periodicity of the supplied representative is assumed. -/
private theorem HasWeakPartialOn.sndShift_ae {F G : ℝ × ℝ → ℂ} {j : Fin 2}
    (hd : HasWeakPartialOn actionStrip j F G)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) (n : ℤ) :
    ∀ᵐ q, q ∈ actionStrip → G (q.1, q.2 + n) = G q := by
  have hpF (q : ℝ × ℝ) : F (q.1, q.2 + n) = F q := by
    have hp : Function.Periodic (fun θ ↦ F (q.1, θ)) 1 := fun θ ↦ hper (q.1, θ)
    simpa only [mul_one] using (hp.int_mul n) q.2
  have hs : HasWeakPartialOn actionStrip j F (fun q ↦ G (q.1, q.2 + n)) := by
    refine ⟨hd.1, locallyIntegrableOn_sndShift hd.2.1 n, fun φ hφ ↦ ?_⟩
    let v : ℝ × ℝ := (0, -(n : ℝ))
    let ψ : ℝ × ℝ → ℂ := fun p ↦ φ (p + v)
    have hψs : tsupport ψ ⊆ (fun p ↦ p + v) ⁻¹' tsupport φ :=
      closure_minimal (fun p hp ↦ subset_closure hp)
        ((isClosed_tsupport φ).preimage (continuous_id.add continuous_const))
    have hψ : IsTestFunctionOn actionStrip ψ :=
      ⟨hφ.contDiff.comp (contDiff_id.add contDiff_const),
        hφ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight v), fun p hp ↦ by
          have h := hφ.tsupport_subset (hψs hp)
          simpa [actionStrip, v] using h⟩
    have hm := measurePreserving_sndShift (-(n : ℝ))
    calc (∫ q, F q * coordPartial j φ q) =
          ∫ q, F (q.1, q.2 + n) * coordPartial j φ q := by simp only [hpF]
         _ = ∫ p, F p * coordPartial j ψ p := by
          simpa [ψ, v, coordPartial_translate] using
            (hm.integral_comp' (fun q ↦ F (q.1, q.2 + n) * coordPartial j φ q)).symm
         _ = -∫ p, G p * ψ p := hd.2.2 ψ hψ
         _ = -∫ q, G (q.1, q.2 + n) * φ q := by
          congr 1
          simpa [ψ, v] using hm.integral_comp' (fun q ↦ G (q.1, q.2 + n) * φ q)
  exact hs.ae_eq (isOpen_Ioo.prod isOpen_univ) hd

/-- Averaging a weak derivative with the angular partition gives an exactly
periodic representative, equal to the supplied derivative a.e. on the strip. -/
private theorem HasWeakPartialOn.periodize_cutoff_ae {F G : ℝ × ℝ → ℂ} {j : Fin 2}
    (hd : HasWeakPartialOn actionStrip j F G)
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) :
    ∀ᵐ q, q ∈ actionStrip → periodizeSnd (cutoffPeriodicSnd G) q = G q := by
  have hall : ∀ᵐ q, ∀ n : ℤ, q ∈ actionStrip → G (q.1, q.2 + n) = G q :=
    ae_all_iff.2 (fun n ↦ hd.sndShift_ae hper n)
  filter_upwards [hall] with q hq hqS
  have hρ : ∀ q, anglePartition q ≠ 0 → |q.2| ≤ 1 := anglePartition_support_le
  have hσ : ∀ q, cutoffPeriodicSnd G q ≠ 0 → |q.2| ≤ 1 := by
    intro q hq
    apply anglePartition_support_le q
    intro hz
    exact hq (by simp [cutoffPeriodicSnd, hz])
  obtain ⟨N, hN⟩ := exists_nat_gt (1 + |q.2|)
  rw [periodizeSnd_eq_sum hσ hN.le (le_refl |q.2|)]
  simp_rw [cutoffPeriodicSnd, fun n ↦ hq n hqS]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum,
    ← periodizeSnd_eq_sum hρ hN.le (le_refl |q.2|), periodize_anglePartition]
  simp

private def reverseCoordGrad (j : Fin 2) (G : Fin 2 → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((coordPartial j levelCoord p : ℝ) : ℂ) * G 0 (actionAngle p) +
    angleGrad j p * G 1 (actionAngle p)

private theorem locallyIntegrableOn_reverseCoordGrad {G : Fin 2 → ℝ × ℝ → ℂ}
    (hper : ∀ i, ∀ q : ℝ × ℝ, G i (q.1, q.2 + 1) = G i q)
    (hG : ∀ i, LocallyIntegrableOn (G i) actionStrip) (j : Fin 2) :
    LocallyIntegrableOn (reverseCoordGrad j G) puncturedCell := by
  have hlev : ContDiff ℝ ∞ levelCoord := by unfold levelCoord dipoleLift; fun_prop
  have hh := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_coordPartial isOpen_puncturedCell hlev.contDiffOn j)
  exact ((locallyIntegrableOn_comp_actionAngle (hper 0) (hG 0)).continuousOn_mul hh
    isOpen_puncturedCell.isLocallyClosed).add
      ((locallyIntegrableOn_comp_actionAngle (hper 1) (hG 1)).continuousOn_mul
        (continuousOn_angleGrad j) isOpen_puncturedCell.isLocallyClosed)

/-- The reverse weak rule for exactly periodic representatives. Cofactor-weighted
periodic tests make the Piola cancellation remove the zeroth-order terms. -/
private theorem HasWeakPartialOn.comp_actionAngle_periodic {F : ℝ × ℝ → ℂ}
    {G : Fin 2 → ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hpG : ∀ i, ∀ q : ℝ × ℝ, G i (q.1, q.2 + 1) = G i q)
    (hG : ∀ i, HasWeakPartialOn actionStrip i F (G i)) (j : Fin 2) :
    HasWeakPartialOn puncturedCell j (F ∘ actionAngle) (reverseCoordGrad j G) := by
  have hu := locallyIntegrableOn_comp_actionAngle hper (hG 0).1
  have hk := locallyIntegrableOn_reverseCoordGrad hpG (fun i ↦ (hG i).2.1) j
  refine ⟨hu, hk, fun φ hφ ↦ ?_⟩
  let H := fun i ↦ cofactorTest j i φ
  let σ := fun i ↦ cutoffPeriodicSnd (H i)
  choose a b ha hb hH hpH hzH using (fun i ↦ cofactorTest_properties j i hφ)
  have hσ (i : Fin 2) : IsTestFunctionOn actionStrip (σ i) :=
    isTestFunctionOn_cutoffPeriodicSnd (ha i) (hb i) (hH i) (hzH i)
  have hDσ (i : Fin 2) : IsTestFunctionOn actionStrip (coordPartial i (σ i)) :=
    ⟨contDiff_coordPartial_top i (hσ i).contDiff, (hσ i).hasCompactSupport_coordPartial i,
      (tsupport_coordPartial_subset i (σ i)).trans (hσ i).tsupport_subset⟩
  have hD (i : Fin 2) : ∀ q, periodizeSnd (coordPartial i (σ i)) q = coordPartial i (H i) q :=
    periodize_coordPartial_cutoff (hH i) (hpH i) i
  have hV (i : Fin 2) : ∀ q, periodizeSnd (σ i) q = H i q :=
    periodize_cutoffPeriodicSnd (hpH i)
  have il (i : Fin 2) : Integrable (fun q ↦ F q * coordPartial i (H i) q) actionMeasure :=
    integrable_actionMeasure_mul_band (hG 0).1 (ha i) (hb i)
      (contDiff_coordPartial_top i (hH i)).continuous (band_coordPartial_zero (hzH i) i)
  have ir (i : Fin 2) : Integrable (fun q ↦ G i q * H i q) actionMeasure :=
    integrable_actionMeasure_mul_band (hG i).2.1 (ha i) (hb i) (hH i).continuous (hzH i)
  have hleft_i (i : Fin 2) : (∫ q, F q * coordPartial i (σ i) q) =
      ∫ q, F q * coordPartial i (H i) q ∂actionMeasure := by
    rw [integral_strip_test_periodize (hG 0).1 (fun q _ ↦ hper q) (hDσ i)]
    simp_rw [hD i]
  have hright_i (i : Fin 2) : (∫ q, G i q * σ i q) =
      ∫ q, G i q * H i q ∂actionMeasure := by
    rw [integral_strip_test_periodize (hG i).2.1 (fun q _ ↦ hpG i q) (hσ i)]
    simp_rw [hV i]
  have hφj : IsTestFunctionOn puncturedCell (coordPartial j φ) :=
    ⟨contDiff_coordPartial_top j hφ.contDiff, hφ.hasCompactSupport_coordPartial j,
      (tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset⟩
  have hleft : (∫ p, (F ∘ actionAngle) p * coordPartial j φ p) =
      (∫ q, F q * coordPartial 0 (σ 0) q) + ∫ q, F q * coordPartial 1 (σ 1) q := by
    rw [integral_mul_test_actionAngle hu hφj, hleft_i 0, hleft_i 1,
      ← integral_add (il 0) (il 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle,
      ae_actionAngleInv_off_diagonal] with q hq hn
    have hqS : q ∈ actionStrip := ⟨hq.1, mem_univ _⟩
    have hp := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
    have hcut : ¬((diagCoord (actionAngleInv q)).2 = 0 ∧
        0 < (diagCoord (actionAngleInv q)).1) := fun h ↦ hn h.1
    have hAP := actionAngle_actionAngleInv hq.1.1 hq.1.2 hq.2
    have hc := stripCofactor_chain hp hcut (hφ.contDiff.differentiable (by simp) _) j
    rw [hAP, levelCoord_actionAngleInv hq.1.1 hq.1.2] at hc
    have hdiv := stripCofactor_divergence j hqS
    rw [comp_actionAngle_actionAngleInv hper hqS, Complex.real_smul]
    change _ = F q * coordPartial 0 (cofactorTest j 0 φ) q +
      F q * coordPartial 1 (cofactorTest j 1 φ) q
    rw [cofactorTest_deriv j 0 hφ hqS, cofactorTest_deriv j 1 hφ hqS]
    linear_combination -(F q) * hc - (F q * φ (actionAngleInv q)) * hdiv
  have hright : (∫ p, reverseCoordGrad j G p * φ p) =
      (∫ q, G 0 q * σ 0 q) + ∫ q, G 1 q * σ 1 q := by
    rw [integral_mul_test_actionAngle hk hφ, hright_i 0, hright_i 1,
      ← integral_add (ir 0) (ir 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_actionRectangle,
      ae_actionAngleInv_off_diagonal] with q hq hn
    have hqS : q ∈ actionStrip := ⟨hq.1, mem_univ _⟩
    have hp := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
    have hcut : ¬((diagCoord (actionAngleInv q)).2 = 0 ∧
        0 < (diagCoord (actionAngleInv q)).1) := fun h ↦ hn h.1
    have hAP := actionAngle_actionAngleInv hq.1.1 hq.1.2 hq.2
    have hN := stripCofactor_normalized hp hcut j
    rw [hAP, levelCoord_actionAngleInv hq.1.1 hq.1.2] at hN
    have hT : stripTestPull φ q = φ (actionAngleInv q) := Set.indicator_of_mem hqS _
    simp only [Complex.real_smul, reverseCoordGrad, H, cofactorTest, hT, hAP, hN.1, hN.2]
    ring
  rw [hleft, hright, (hG 0).2.2 (σ 0) (hσ 0), (hG 1).2.2 (σ 1) (hσ 1)]
  ring

/-- Strip null sets remain null after evaluation at the chosen inverse coordinates. -/
private theorem ae_comp_actionAngle {A B : ℝ × ℝ → ℂ}
    (he : ∀ᵐ q, q ∈ actionStrip → A q = B q) :
    ∀ᵐ p, p ∈ puncturedCell → A (actionAngle p) = B (actionAngle p) := by
  have hrect : A =ᵐ[actionMeasure] B := by
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_actionRectangle]
      with q hq hr
    exact hq ⟨hr.1, mem_univ _⟩
  have hw := (withDensity_absolutelyContinuous actionMeasure actionWeight).ae_le hrect
  have hp := measurePreserving_actionCoordinates.quasiMeasurePreserving.ae hw
  have hg := (ae_restrict_iff' measurableSet_cellSquare).mp hp
  filter_upwards [hg] with p hp hpC
  rw [← actionCoordinates_eq_actionAngle hpC]
  exact hp hpC.1

/-- The chain rule for weak derivatives from the strip to the cell, for functions that are
    `1`-periodic in `θ`. The angle jumps across its cut, a null set, where its partial
    derivatives are irrelevant. -/
theorem HasWeakPartialOn.comp_actionAngle {F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hG : ∀ i, HasWeakPartialOn actionStrip i F (G i)) (j : Fin 2) :
    HasWeakPartialOn puncturedCell j (F ∘ actionAngle) (fun p ↦
      ((coordPartial j levelCoord p : ℝ) : ℂ) * G 0 (actionAngle p) +
        ((coordPartial j angleCoord p : ℝ) : ℂ) * G 1 (actionAngle p)) := by
  let Gp : Fin 2 → ℝ × ℝ → ℂ := fun i ↦ periodizeSnd (cutoffPeriodicSnd (G i))
  have hpG : ∀ i, ∀ q : ℝ × ℝ, Gp i (q.1, q.2 + 1) = Gp i q :=
    fun _ ↦ periodizeSnd_periodic
  have heG (i : Fin 2) : ∀ᵐ q, q ∈ actionStrip → Gp i q = G i q :=
    (hG i).periodize_cutoff_ae hper
  have hGp (i : Fin 2) : HasWeakPartialOn actionStrip i F (Gp i) :=
    (hG i).congr_ae_on (isOpen_Ioo.prod isOpen_univ).measurableSet
      (Eventually.of_forall (fun _ _ ↦ rfl)) (by
        filter_upwards [heG i] with q hq hqS
        exact (hq hqS).symm)
  have hd := HasWeakPartialOn.comp_actionAngle_periodic hper hpG hGp j
  apply hd.congr_ae_on isOpen_puncturedCell.measurableSet
    (Eventually.of_forall (fun _ _ ↦ rfl))
  filter_upwards [ae_comp_actionAngle (heG 0), ae_comp_actionAngle (heG 1),
    measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero] with p h0 h1 hn hp
  unfold reverseCoordGrad
  rw [h0 hp, h1 hp, angleGrad_eq hp (fun h ↦ hn h.1) j]

/-- `χ(Ψ/2)` vanishes near every point off the cell square. -/
private theorem cellCutoff_eventuallyEq_zero {χ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hχband : tsupport χ ⊆ Icc a b) {p : ℝ × ℝ} (hp : p ∉ cellSquare) :
    cellCutoff χ =ᶠ[𝓝 p] fun _ ↦ 0 := by
  classical
  have hd₁ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) := by unfold diagCoord; fun_prop
  have hd₂ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) := by unfold diagCoord; fun_prop
  set S : Set (ℝ × ℝ) := {q | |(diagCoord q).1| ≤ Real.pi / 2 ∧ |(diagCoord q).2| ≤ Real.pi / 2}
  have hS : IsClosed S :=
    (isClosed_le hd₁ continuous_const).inter (isClosed_le hd₂ continuous_const)
  have hcl : closure cellSquare ⊆ S :=
    closure_minimal (fun q hq ↦ ⟨hq.1.le, hq.2.le⟩) hS
  have hprod (q : ℝ × ℝ) :
      levelCoord q = Real.cos (diagCoord q).1 * Real.cos (diagCoord q).2 := by
    rw [levelCoord, dipoleLift_eq_diag]
    ring
  have hV : IsOpen ({q | levelCoord q < a} ∪ (closure cellSquare)ᶜ) :=
    (isOpen_lt continuous_levelCoord continuous_const).union isClosed_closure.isOpen_compl
  have hpV : p ∈ {q | levelCoord q < a} ∪ (closure cellSquare)ᶜ := by
    by_cases hpc : p ∈ closure cellSquare
    · left
      have hpS := hcl hpc
      have hz : levelCoord p = 0 := by
        rw [hprod]
        have hne : ¬(|(diagCoord p).1| < Real.pi / 2 ∧ |(diagCoord p).2| < Real.pi / 2) := hp
        rcases not_and_or.mp hne with h | h
        · have he : |(diagCoord p).1| = Real.pi / 2 := le_antisymm hpS.1 (not_lt.mp h)
          rw [← Real.cos_abs, he, Real.cos_pi_div_two, zero_mul]
        · have he : |(diagCoord p).2| = Real.pi / 2 := le_antisymm hpS.2 (not_lt.mp h)
          rw [← Real.cos_abs (diagCoord p).2, he, Real.cos_pi_div_two, mul_zero]
      change levelCoord p < a
      rw [hz]
      exact ha
    · right
      exact hpc
  filter_upwards [hV.mem_nhds hpV] with q hq
  by_cases hqc : q ∈ cellSquare
  · have hl : levelCoord q < a := by
      rcases hq with h | h
      · exact h
      · exact absurd (subset_closure hqc) h
    have hz : χ (levelCoord q) = 0 :=
      image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr hl) (hχband ht).1
    simp [cellCutoff, hqc, hz]
  · simp [cellCutoff, hqc]

/-! ### Statements -/

section Statements

variable {χ : ℝ → ℝ}

/-- Scalars pass through `J_ε`. -/
theorem transversalMollifier_const_mul (ε : ℝ) (c : ℂ) (u : ℝ × ℝ → ℂ) :
    transversalMollifier χ ε (fun p ↦ c * u p) = fun p ↦ c * transversalMollifier χ ε u p := by
  funext p
  simp only [transversalMollifier, mollifyFst]
  split_ifs
  · rw [← integral_const_mul]
    congr 1
    funext h'
    simp only [Complex.real_smul]
    ring
  · simp

/-! #### `lem:transversal-mollifier-support` -/

/-- For small `ε`, `J_ε u` vanishes off a fixed compact subset of the punctured cell. -/
theorem transversalMollifier_eq_zero (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ K, IsCompact K ∧ K ⊆ puncturedCell ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ u p, p ∉ K →
      transversalMollifier χ ε u p = 0 := by
  obtain ⟨a, b, ε₀, ha, hb, hε₀, _, hband, -, -⟩ := exists_mollify_band hχs
  refine ⟨closedCellLevelBand a b, isCompact_closedCellLevelBand _ _,
    closedCellLevelBand_subset ha hb, ε₀, hε₀, ?_⟩
  intro ε hε u p hp
  by_cases hc : p ∈ puncturedCell
  · rw [transversalMollifier, ite_eq_left hc]
    apply hband ε hε (fun z ↦ u (actionAngleInv z)) (actionAngle p)
    intro hh
    exact hp ⟨hc.1.1.le, hc.1.2.le, hh⟩
  · simp [transversalMollifier, hc]

/-! #### `lem:transversal-mollifier-linear` -/

/-- `J_ε` is additive on `L²` of the cell, up to null sets. The smooth, cell-supported
cutoff ensures integrability of the separate convolutions. -/
theorem transversalMollifier_add (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1)
    {ε : ℝ} (hε : 0 < ε) {u v : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) (hv : MemLp v 2 (volume.restrict cellSquare)) :
    transversalMollifier χ ε (u + v) =ᵐ[volume]
      transversalMollifier χ ε u + transversalMollifier χ ε v := by
  classical
  let F : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ := fun w q ↦ (χ q.1 : ℂ) * w (actionAngleInv q)
  have hFu := memLp_cutoff_actionInput hχ hχs hu
  have hFv := memLp_cutoff_actionInput hχ hχs hv
  have hsum : (fun q : ℝ × ℝ ↦ (χ q.1 : ℂ) *
      (u (actionAngleInv q) + v (actionAngleInv q))) = F u + F v := by
    funext q
    simp [F, mul_add]
  have hlines : ∀ᵐ θ ∂(volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))),
      ∀ x, mollifyFst ε (F u + F v) (x, θ) =
        mollifyFst ε (F u) (x, θ) + mollifyFst ε (F v) (x, θ) := by
    filter_upwards [ae_memLp_action_lines hFu, ae_memLp_action_lines hFv] with θ hU hV
    intro x
    simp only [mollifyFst, Pi.add_apply, smul_add]
    exact integral_add (integrable_mollify_line hε hU x) (integrable_mollify_line hε hV x)
  filter_upwards [ae_of_ae_angle hlines] with p hp
  by_cases hc : p ∈ puncturedCell
  · simp only [transversalMollifier, ite_eq_left hc, Pi.add_apply]
    rw [hsum]
    exact hp hc (levelCoord p)
  · simp [transversalMollifier, hc]

/-! #### `lem:transversal-mollifier-congr` -/

/-- A cell-supported cutoff makes `J_ε u` independent of the representative on the cell.
Neither integrability of the inputs nor regularity of the cutoff is needed. -/
theorem transversalMollifier_congr_ae (hχs : tsupport χ ⊆ Ioo 0 1)
    {ε : ℝ} {u v : ℝ × ℝ → ℂ} (huv : u =ᵐ[volume.restrict cellSquare] v) :
    transversalMollifier χ ε u =ᵐ[volume] transversalMollifier χ ε v := by
  classical
  have hpull := ae_comp_actionParam huv
  rw [actionMeasure_eq_prod] at hpull
  have hswap := (Measure.measurePreserving_swap
    (μ := volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4)))
    (ν := volume.restrict (Ioo (0 : ℝ) 1))).quasiMeasurePreserving.ae hpull
  have hlines₀ := Measure.ae_ae_of_ae_prod hswap
  let Good : ℝ → Prop := fun θ ↦ ∀ᵐ h ∂(volume : Measure ℝ),
    (χ h : ℂ) * u (actionAngleInv (h, θ)) = (χ h : ℂ) * v (actionAngleInv (h, θ))
  have hlines : ∀ᵐ θ ∂(volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))), Good θ := by
    filter_upwards [hlines₀, ae_restrict_mem measurableSet_Ico] with θ hθ hθI
    have he := (ae_restrict_iff' measurableSet_Ioo).mp hθ
    filter_upwards [he] with h hh
    by_cases h01 : h ∈ Ioo (0 : ℝ) 1
    · have hp : actionParam (h, θ) = actionAngleInv (h, θ) := by
        simp [actionParam, actionRectangle, Set.piecewise, h01, hθI]
      have hh' := hh h01
      change u (actionParam (h, θ)) = v (actionParam (h, θ)) at hh'
      rw [hp] at hh'
      exact congrArg (fun z : ℂ ↦ (χ h : ℂ) * z) hh'
    · have hz : χ h = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ h01 (hχs ht))
      simp [hz]
  filter_upwards [ae_of_ae_angle hlines] with p hp
  by_cases hc : p ∈ puncturedCell
  · have hgood : Good (angleCoord p) := hp hc
    simp only [transversalMollifier, ite_eq_left hc, mollifyFst]
    apply integral_congr_ae
    filter_upwards [hgood] with h hh
    exact congrArg (fun z : ℂ ↦ mollifierKernel ε ((actionAngle p).1 - h) • z) hh
  · simp [transversalMollifier, hc]

/-! #### `lem:transversal-mollifier` -/

/-- For small `ε`, `J_ε` is bounded from `L²` of the cell to `L²(ℝ²)`, uniformly in `ε`. -/
theorem memLp_transversalMollifier (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ ε₀ > 0, ∃ C : ℝ≥0, ∀ ε ∈ Ioo 0 ε₀, ∀ u, MemLp u 2 (volume.restrict cellSquare) →
      MemLp (transversalMollifier χ ε u) 2 volume ∧
        eLpNorm (transversalMollifier χ ε u) 2 volume ≤
          C * eLpNorm u 2 (volume.restrict cellSquare) := by
  obtain ⟨a, b, ε₀, ha, hb, hε₀, _, hband, -, -⟩ := exists_mollify_band hχs
  obtain ⟨Ci, hCi⟩ := eLpNorm_cutoff_actionInput_le hχ hχs
  obtain ⟨Co, hCo⟩ := exists_actionReconstruct_bound ha hb
  refine ⟨ε₀, hε₀, Co * Ci, fun ε hε u hu ↦ ?_⟩
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)
  have hM := eLpNorm_mollifyFst_le hε.1 (memLp_cutoff_actionInput hχ hχs hu)
  have hrec := hCo (mollifyFst ε F) hM.1 (hband ε hε (fun z ↦ u (actionAngleInv z)))
  have hJ : actionReconstruct (mollifyFst ε F) =ᵐ[volume] transversalMollifier χ ε u :=
    ae_actionReconstruct _
  refine ⟨MemLp.ae_eq hJ hrec.1, ?_⟩
  calc
    _ = eLpNorm (actionReconstruct (mollifyFst ε F)) 2 volume := eLpNorm_congr_ae hJ.symm
    _ ≤ Co * eLpNorm (mollifyFst ε F) 2 cylinderMeasure := hrec.2
    _ ≤ Co * (Ci * eLpNorm u 2 (volume.restrict cellSquare)) :=
      mul_le_mul_of_nonneg_left (hM.2.trans (hCi u hu)) bot_le
    _ = _ := by simp [ENNReal.coe_mul, mul_assoc]

/-- `J_ε u → χ(Ψ/2) u` in `L²`. -/
theorem tendsto_transversalMollifier (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1)
    {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict cellSquare)) :
    Tendsto (fun ε ↦ eLpNorm (fun p ↦ transversalMollifier χ ε u p - cellCutoff χ p * u p) 2
      volume) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨a, b, ε₀, ha, hb, hε₀, hχband, hband, -, -⟩ := exists_mollify_band hχs
  obtain ⟨Co, hCo⟩ := exists_actionReconstruct_bound ha hb
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)
  have hF := memLp_cutoff_actionInput hχ hχs hu
  have hlim : Tendsto (fun ε ↦ (Co : ENNReal) *
      eLpNorm (mollifyFst ε F - F) 2 cylinderMeasure) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, F, cylinderMeasure] using
      ENNReal.Tendsto.const_mul (tendsto_mollifyFst hF)
      (Or.inr (ENNReal.coe_ne_top : (Co : ENNReal) ≠ ⊤))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ENNReal)) (𝓝[>] 0) (𝓝 0)) hlim
  · exact Filter.Eventually.of_forall (fun _ ↦ bot_le)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hε hεlt
    have hεband : ε ∈ Ioo 0 ε₀ := ⟨hε, hεlt⟩
    have hM := eLpNorm_mollifyFst_le hε hF
    have hzero : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → (mollifyFst ε F - F) q = 0 := by
      intro q hq
      have hz : χ q.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hq (hχband hs))
      simp only [Pi.sub_apply]
      rw [hband ε hεband (fun z ↦ u (actionAngleInv z)) q hq]
      simp [F, hz]
    have hrec := hCo (mollifyFst ε F - F) (hM.1.sub hF) hzero
    have hJ : actionReconstruct (mollifyFst ε F) =ᵐ[volume] transversalMollifier χ ε u :=
      ae_actionReconstruct _
    have heq : actionReconstruct (mollifyFst ε F - F) =ᵐ[volume]
        (fun p ↦ transversalMollifier χ ε u p - (cellCutoff χ p : ℂ) * u p) := by
      rw [actionReconstruct_sub]
      exact hJ.sub (ae_actionReconstruct_input χ u)
    exact (eLpNorm_congr_ae heq.symm).le.trans hrec.2

/-! #### `lem:transversal-mollifier-derivatives` (stated) -/

/-- For `u ∈ H¹` of the cell, `J_ε u → χ(Ψ/2) u` in `H¹(ℝ²)`. -/
theorem tendsto_transversalMollifier_partial (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare))
    (hg : ∀ i, HasWeakPartialOn cellSquare i u (g i))
    (hg2 : ∀ i, MemLp (g i) 2 (volume.restrict cellSquare)) :
    ∃ d : Fin 2 → ℝ → ℝ × ℝ → ℂ,
      (∀ᶠ ε in 𝓝[>] 0, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
        MemLp (d j ε) 2 volume) ∧
      ∀ j, Tendsto (fun ε ↦ eLpNorm (fun p ↦ d j ε p -
          (((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * u p + cellCutoff χ p * g j p)) 2 volume)
        (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨a, b, ε₀, ha, hb, hε₀, hχband, hband, hab, hdband⟩ := exists_mollify_band hχs
  obtain ⟨C, hC, hCb⟩ := exists_coordGrad_bound ha hb
  have hmemB {p : ℝ × ℝ} (hc : p ∈ puncturedCell) (hl : levelCoord p ∈ Icc a b) :
      p ∈ closedCellLevelBand a b := by
    rw [closedCellLevelBand_eq ha hb]
    exact ⟨hc, hl⟩
  have hχ'd : ContDiff ℝ ∞ (deriv χ) := by simpa using hχ.iterate_deriv 1
  have hχ's : tsupport (deriv χ) ⊆ Ioo 0 1 := tsupport_deriv_subset.trans hχs
  have hχz {h : ℝ} (hh : h ∉ Icc a b) : χ h = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht ↦ hh (hχband ht)
  have hχ'z {h : ℝ} (hh : h ∉ Icc a b) : deriv χ h = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht ↦ hh (hχband (tsupport_deriv_subset ht))
  -- The coordinate derivatives of the input, from the chain rule into the strip.
  set c0 : Fin 2 → ℝ × ℝ → ℝ := fun i ↦ coordPartial i (fun q ↦ (actionAngleInv q).1)
  set c1 : Fin 2 → ℝ × ℝ → ℝ := fun i ↦ coordPartial i (fun q ↦ (actionAngleInv q).2)
  have hstripO : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hc0 (i : Fin 2) : ContinuousOn (c0 i) actionStrip :=
    continuousOn_coordPartial hstripO (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) i
  have hc1 (i : Fin 2) : ContinuousOn (c1 i) actionStrip :=
    continuousOn_coordPartial hstripO (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) i
  set DU : Fin 2 → ℝ × ℝ → ℂ := fun i q ↦
    (c0 i q : ℂ) * g 0 (actionAngleInv q) + (c1 i q : ℂ) * g 1 (actionAngleInv q) with hDU_def
  have hU (i : Fin 2) : HasWeakPartialOn actionStrip i (u ∘ actionAngleInv) (DU i) :=
    HasWeakPartialOn.comp_actionAngleInv (fun i ↦ (hg i).mono sdiff_subset) i
  set F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q) with hF_def
  set Fh : ℝ × ℝ → ℂ := fun q ↦
    ((deriv χ q.1 : ℝ) : ℂ) * (u ∘ actionAngleInv) q + (χ q.1 : ℂ) * DU 0 q with hFh_def
  set Fθ : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * DU 1 q with hFθ_def
  have hF0 : HasWeakPartialOn univ 0 F Fh := (hU 0).levelCutoff₀ hχ hχs
  have hF1 : HasWeakPartialOn univ 1 F Fθ := (hU 1).levelCutoff hχ hχs
  have hpF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q := fun q ↦ by
    have h := levelCutoff_actionInput_periodic hχs (fun _ ↦ 1) u q
    simp only [one_mul] at h
    exact h
  -- `L²` bounds in coordinates.
  have hK : IsCompact (Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)) := isCompact_Icc.prod isCompact_Icc
  have hKs : Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4) ⊆ actionStrip :=
    fun q hq ↦ ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt hb⟩, mem_univ _⟩
  have hsnd : ∀ᵐ q ∂cylinderMeasure, q.2 ∈ Ico (-1 / 4 : ℝ) (3 / 4) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ico)
  have hcoefL {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f actionStrip) {w : ℝ × ℝ → ℂ}
      (hw : MemLp w 2 (volume.restrict cellSquare)) :
      MemLp (fun q ↦ (f q : ℂ) * ((χ q.1 : ℂ) * w (actionAngleInv q))) 2 cylinderMeasure := by
    obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn (hf.mono hKs)
    have hX := memLp_cutoff_actionInput hχ hχs hw
    have he : (fun q ↦ (f q : ℂ) * ((χ q.1 : ℂ) * w (actionAngleInv q))) =
        fun q ↦ ((actionStrip.piecewise f (fun _ ↦ 0) q : ℝ) : ℂ) *
          ((χ q.1 : ℂ) * w (actionAngleInv q)) := by
      funext q
      by_cases hq : q ∈ actionStrip
      · rw [Set.piecewise_eq_of_mem _ _ _ hq]
      · have hq1 : q.1 ∉ Icc a b := fun h ↦ hq ⟨⟨ha.trans_le h.1, h.2.trans_lt hb⟩, mem_univ _⟩
        simp [hχz hq1]
    refine hX.of_le_mul (c := Cf) ?_ ?_
    · rw [he]
      exact (Complex.continuous_ofReal.measurable.comp (ContinuousOn.measurable_piecewise hf
        continuousOn_const hstripO.measurableSet)).aestronglyMeasurable.mul hX.aestronglyMeasurable
    · filter_upwards [hsnd] with q hq
      by_cases hχq : χ q.1 = 0
      · simp [hχq]
      · have hqK : q ∈ Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4) :=
          ⟨hχband (subset_closure hχq), Ico_subset_Icc_self hq⟩
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_right (hCf q hqK) (norm_nonneg _)
  have hFhL : MemLp Fh 2 cylinderMeasure := by
    have he : Fh = fun q ↦ ((deriv χ q.1 : ℝ) : ℂ) * u (actionAngleInv q) +
        ((c0 0 q : ℂ) * ((χ q.1 : ℂ) * g 0 (actionAngleInv q)) +
          (c1 0 q : ℂ) * ((χ q.1 : ℂ) * g 1 (actionAngleInv q))) := by
      funext q
      simp only [hFh_def, hDU_def, Function.comp_apply]
      ring
    rw [he]
    exact (memLp_cutoff_actionInput hχ'd hχ's hu).add
      ((hcoefL (hc0 0) (hg2 0)).add (hcoefL (hc1 0) (hg2 1)))
  have hFθL : MemLp Fθ 2 cylinderMeasure := by
    have he : Fθ = fun q ↦ (c0 1 q : ℂ) * ((χ q.1 : ℂ) * g 0 (actionAngleInv q)) +
        (c1 1 q : ℂ) * ((χ q.1 : ℂ) * g 1 (actionAngleInv q)) := by
      funext q
      simp only [hFθ_def, hDU_def]
      ring
    rw [he]
    exact (hcoefL (hc0 1) (hg2 0)).add (hcoefL (hc1 1) (hg2 1))
  have hFhz : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → Fh q = 0 := fun q hq ↦ by
    simp [hFh_def, hχz hq, hχ'z hq]
  have hFθz : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → Fθ q = 0 := fun q hq ↦ by
    simp [hFθ_def, hχz hq]
  have hFloc : LocallyIntegrable F := locallyIntegrableOn_univ.mp hF1.1
  have hFcyl : MemLp F 2 cylinderMeasure := memLp_cutoff_actionInput hχ hχs hu
  have hMX := (tendsto_smul_mollifyFstDeriv hFcyl).1
  -- The derivatives.
  set d : Fin 2 → ℝ → ℝ × ℝ → ℂ := fun j ε ↦
    coordGrad j (mollifyFstDeriv ε F) (mollifyFst ε Fθ) with hd_def
  have hXband (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) :
      ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFstDeriv ε F q = 0 :=
    fun q hq ↦ hdband ε hε (fun z ↦ u (actionAngleInv z)) q hq
  have hYband (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) :
      ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFst ε Fθ q = 0 :=
    fun q hq ↦ hband ε hε (DU 1) q hq
  have hweak : ∀ ε ∈ Ioo 0 ε₀, ∀ j,
      HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) := by
    intro ε hε j
    have hX := hasWeakPartialOn_mollifyFst hε.1 hFloc
    have hY := hF1.mollify hε.1
    set G : Fin 2 → ℝ × ℝ → ℂ := fun i ↦ if i = 0 then mollifyFstDeriv ε F else mollifyFst ε Fθ
      with hG_def
    have hG : ∀ i, HasWeakPartialOn actionStrip i (mollifyFst ε F) (G i) := by
      intro i
      fin_cases i
      · simpa [hG_def] using hX.mono (subset_univ _)
      · simpa [hG_def] using hY.mono (subset_univ _)
    have hc := HasWeakPartialOn.comp_actionAngle (mollifyFst_periodic hpF) hG j
    have hcell : HasWeakPartialOn puncturedCell j (transversalMollifier χ ε u) (d j ε) := by
      refine hc.congr_ae_on isOpen_puncturedCell.measurableSet
        (Eventually.of_forall fun p hp ↦ ?_) ?_
      · simp only [Function.comp_apply, transversalMollifier, ite_eq_left hp, hF_def]
      · filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero]
          with p hp hcp
        have hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1) := fun h ↦ hp h.1
        simp [hd_def, coordGrad, hcp, hG_def, angleGrad_eq hcp hcut j]
    refine hcell.univ_of_band ha hb (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · by_cases hc : p ∈ puncturedCell
      · simp only [transversalMollifier, ite_eq_left hc]
        exact hband ε hε _ _ fun hl ↦ hp (hmemB hc hl)
      · simp [transversalMollifier, hc]
    · by_cases hc : p ∈ puncturedCell
      · have hl : levelCoord p ∉ Icc a b := fun hl ↦ hp (hmemB hc hl)
        simp only [hd_def, coordGrad, ite_eq_left hc]
        rw [hXband ε hε (actionAngle p) hl, hYband ε hε (actionAngle p) hl, mul_zero, mul_zero,
          add_zero]
      · simp [hd_def, coordGrad, hc]
  -- The limit is the gradient of `χ(Ψ/2) u`.
  have hlimit (j : Fin 2) : coordGrad j Fh Fθ =ᵐ[volume] fun p ↦
      ((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * u p + cellCutoff χ p * g j p := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero,
      measure_eq_zero_iff_ae_notMem.mp volume_origin_eq_zero] with p hp hp0
    by_cases hc : p ∈ puncturedCell
    · have hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1) := fun h ↦ hp h.1
      have hlev : ContDiff ℝ ∞ levelCoord := by
        unfold levelCoord dipoleLift
        fun_prop
      have hld : DifferentiableAt ℝ levelCoord p := hlev.differentiable (by simp) p
      have hcomp : HasFDerivAt (fun q ↦ χ (levelCoord q))
          (deriv χ (levelCoord p) • fderiv ℝ levelCoord p) p :=
        ((hχ.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt p hld.hasFDerivAt
      have hnear : cellCutoff χ =ᶠ[𝓝 p] fun q ↦ χ (levelCoord q) := by
        filter_upwards [isOpen_puncturedCell.mem_nhds hc] with q hq
        simp [cellCutoff, hq.1]
      have hcc : coordPartial j (cellCutoff χ) p =
          deriv χ (levelCoord p) * coordPartial j levelCoord p := by
        rw [coordPartial_congr_nhds hnear, coordPartial_eq_fderiv hcomp.differentiableAt,
          hcomp.fderiv, coordPartial_eq_fderiv hld]
        simp
      have hcp : cellCutoff χ p = χ (levelCoord p) := by simp [cellCutoff, hc.1]
      have hk0 := chainRule_actionAngle hc hcut (ContinuousLinearMap.fst ℝ ℝ ℝ) j
      have hk1 := chainRule_actionAngle hc hcut (ContinuousLinearMap.snd ℝ ℝ ℝ) j
      simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul] at hk0 hk1
      set e : ℝ × ℝ := if j = 0 then ((1 : ℝ), (0 : ℝ)) else (0, 1) with he_def
      have hgj : g j p = (e.1 : ℂ) * g 0 p + (e.2 : ℂ) * g 1 p := by
        fin_cases j <;> simp [he_def]
      have hk0' := congrArg (fun x : ℝ ↦ (x : ℂ)) hk0
      have hk1' := congrArg (fun x : ℝ ↦ (x : ℂ)) hk1
      push_cast at hk0' hk1'
      have hP := actionAngleInv_actionAngle hc
      have haa : (actionAngle p).1 = levelCoord p := rfl
      simp only [coordGrad, ite_eq_left hc, hFh_def, hFθ_def, hDU_def, Function.comp_apply, hP,
        angleGrad_eq hc hcut j, hcc, hcp, haa]
      change _ = _ * u p + (χ (levelCoord p) : ℂ) * g j p
      rw [hgj]
      push_cast
      linear_combination ((χ (levelCoord p) : ℂ) * g 0 p) * hk0' +
        ((χ (levelCoord p) : ℂ) * g 1 p) * hk1'
    · have hpc : p ∉ cellSquare := fun h ↦ hc ⟨h, hp0⟩
      have hz := cellCutoff_eventuallyEq_zero ha hχband hpc
      have hd0 : coordPartial j (cellCutoff χ) p = 0 := by
        rw [coordPartial_congr_nhds hz]
        unfold coordPartial
        split_ifs <;> simp [partialX, partialY]
      simp [coordGrad, hc, hd0, hz.eq_of_nhds]
  -- Convergence.
  have hac : cylinderMeasure ≪ (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.AbsolutelyContinuous.rfl.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hbound : ∀ j, ∀ ε ∈ Ioo 0 ε₀, eLpNorm (fun p ↦ d j ε p -
      (((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * u p + cellCutoff χ p * g j p)) 2 volume ≤
        C * (eLpNorm (mollifyFst ε Fh - Fh) 2 cylinderMeasure +
          eLpNorm (mollifyFst ε Fθ - Fθ) 2 cylinderMeasure) := by
    intro j ε hε
    have he : (fun p ↦ d j ε p -
        (((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * u p + cellCutoff χ p * g j p)) =ᵐ[volume]
        coordGrad j (mollifyFstDeriv ε F - Fh) (mollifyFst ε Fθ - Fθ) := by
      filter_upwards [hlimit j] with p hp
      rw [← hp, ← coordGrad_sub]
      rfl
    have hXe : mollifyFstDeriv ε F - Fh =ᵐ[cylinderMeasure] mollifyFst ε Fh - Fh :=
      hac.ae_eq ((mollifyFstDeriv_ae_eq hε.1 hF0).sub EventuallyEq.rfl)
    obtain ⟨-, hn⟩ := hCb j _ _ ((hMX ε hε.1).sub hFhL)
      ((eLpNorm_mollifyFst_le hε.1 hFθL).1.sub hFθL)
      (fun q hq ↦ by simp [hXband ε hε q hq, hFhz q hq])
      (fun q hq ↦ by simp [hYband ε hε q hq, hFθz q hq])
    rw [eLpNorm_congr_ae he]
    exact hn.trans_eq (by rw [eLpNorm_congr_ae hXe])
  refine ⟨d, ?_, fun j ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε j
    refine ⟨hweak ε hε j, ?_⟩
    exact (hCb j _ _ (hMX ε hε.1) (eLpNorm_mollifyFst_le hε.1 hFθL).1 (hXband ε hε)
      (hYband ε hε)).1
  · have hlim := ENNReal.Tendsto.const_mul (a := C)
      ((tendsto_mollifyFst hFhL).add (tendsto_mollifyFst hFθL)) (Or.inr hC)
    simp only [add_zero, mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact hbound j ε hε

/-- For `u, L₀ u ∈ L²` of the cell, `J_ε u ∈ H¹(ℝ²)` with `ε ‖∇J_ε u‖ → 0`. -/
theorem transversalMollifier_hasWeakPartialOn (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u k : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) (hk : MemLp k 2 (volume.restrict cellSquare))
    (hL : HasWeakL0On cellSquare u k) :
    ∃ d : Fin 2 → ℝ → ℝ × ℝ → ℂ,
      (∀ᶠ ε in 𝓝[>] 0, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
        MemLp (d j ε) 2 volume) ∧
      ∀ j, Tendsto (fun ε ↦ ENNReal.ofReal ε * eLpNorm (d j ε) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨a, b, ε₀, ha, hb, hε₀, hχband, hband, hab, hdband⟩ := exists_mollify_band hχs
  obtain ⟨σ, L, m, M, hσL, hσS, hm, hσm, hσM⟩ := exists_periodExtension ha hb hab
  have hσabs (h : ℝ) : |σ h| ≤ M := by rw [abs_of_pos (hm.trans_le (hσm h))]; exact hσM h
  obtain ⟨C, hC, hCb⟩ := exists_coordGrad_bound ha hb
  have hmemB {p : ℝ × ℝ} (hc : p ∈ puncturedCell) (hl : levelCoord p ∈ Icc a b) :
      p ∈ closedCellLevelBand a b := by
    rw [closedCellLevelBand_eq ha hb]
    exact ⟨hc, hl⟩
  -- Coordinates: `F = χU`, `Kc = χK`, `Gm = σχK`.
  set F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q) with hF_def
  set Kc : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * k (actionAngleInv q) with hKc_def
  set Gm : ℝ × ℝ → ℂ := fun q ↦ (σ q.1 : ℂ) * Kc q with hGm_def
  have hpF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q := fun q ↦ by
    have h := levelCutoff_actionInput_periodic hχs (fun _ ↦ 1) u q
    simp only [one_mul] at h
    exact h
  have h2 : HasWeakPartialOn univ 1 F Gm :=
    hasWeakPartialOn_levelCutoff_actionInput hχ hχs hχband hσS hL
  have hFloc : LocallyIntegrable F := locallyIntegrableOn_univ.mp h2.1
  have hFcyl : MemLp F 2 cylinderMeasure := memLp_cutoff_actionInput hχ hχs hu
  have hKcL : MemLp Kc 2 cylinderMeasure := memLp_cutoff_actionInput hχ hχs hk
  have hGmL : MemLp Gm 2 cylinderMeasure := memLp_levelMul hKcL hσL.continuous hσabs
  obtain ⟨hMX, hlimX⟩ := tendsto_smul_mollifyFstDeriv hFcyl
  have hGm' : Gm = fun z ↦ (χ z.1 : ℂ) * ((σ z.1 : ℂ) * k (actionAngleInv z)) := by
    funext z
    simp only [hGm_def, hKc_def]
    ring
  -- The derivatives: the chain rule in coordinates, with `angleGrad` for `∂ⱼθ`.
  set d : Fin 2 → ℝ → ℝ × ℝ → ℂ := fun j ε ↦
    coordGrad j (mollifyFstDeriv ε F) (mollifyFst ε Gm) with hd_def
  have key : ∀ ε ∈ Ioo 0 ε₀, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
      MemLp (d j ε) 2 volume ∧ eLpNorm (d j ε) 2 volume ≤
        C * (eLpNorm (mollifyFstDeriv ε F) 2 cylinderMeasure + eLpNorm Gm 2 cylinderMeasure) := by
    intro ε hε j
    have hXband : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFstDeriv ε F q = 0 :=
      fun q hq ↦ hdband ε hε (fun z ↦ u (actionAngleInv z)) q hq
    have hGband : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFst ε Gm q = 0 := fun q hq ↦ by
      rw [hGm']
      exact hband ε hε _ q hq
    -- The weak derivative on the punctured cell, then on the plane.
    have hX := hasWeakPartialOn_mollifyFst hε.1 hFloc
    have hY := h2.mollify hε.1
    set G : Fin 2 → ℝ × ℝ → ℂ := fun i ↦ if i = 0 then mollifyFstDeriv ε F else mollifyFst ε Gm
      with hG_def
    have hG : ∀ i, HasWeakPartialOn actionStrip i (mollifyFst ε F) (G i) := by
      intro i
      fin_cases i
      · simpa [hG_def] using hX.mono (subset_univ _)
      · simpa [hG_def] using hY.mono (subset_univ _)
    have hc := HasWeakPartialOn.comp_actionAngle (mollifyFst_periodic hpF) hG j
    have hcell : HasWeakPartialOn puncturedCell j (transversalMollifier χ ε u) (d j ε) := by
      refine hc.congr_ae_on isOpen_puncturedCell.measurableSet
        (Eventually.of_forall fun p hp ↦ ?_) ?_
      · simp only [Function.comp_apply, transversalMollifier, ite_eq_left hp, hF_def]
      · filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_diagCoord_snd_eq_zero]
          with p hp hcp
        have hcut : ¬((diagCoord p).2 = 0 ∧ 0 < (diagCoord p).1) := fun h ↦ hp h.1
        simp [hd_def, coordGrad, hcp, hG_def, angleGrad_eq hcp hcut j]
    have hweak := hcell.univ_of_band ha hb (fun p hp ↦ by
      by_cases hc : p ∈ puncturedCell
      · simp only [transversalMollifier, ite_eq_left hc]
        exact hband ε hε _ _ fun hl ↦ hp (hmemB hc hl)
      · simp [transversalMollifier, hc]) (fun p hp ↦ by
      by_cases hc : p ∈ puncturedCell
      · have hl : levelCoord p ∉ Icc a b := fun hl ↦ hp (hmemB hc hl)
        simp only [hd_def, coordGrad, ite_eq_left hc]
        rw [hXband (actionAngle p) hl, hGband (actionAngle p) hl, mul_zero, mul_zero, add_zero]
      · simp [hd_def, coordGrad, hc])
    have hMG := eLpNorm_mollifyFst_le hε.1 hGmL
    obtain ⟨hdL, hdn⟩ := hCb j _ _ (hMX ε hε.1) hMG.1 hXband hGband
    exact ⟨hweak, hdL, hdn.trans (by gcongr; exact hMG.2)⟩
  refine ⟨d, ?_, fun j ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε j
    exact ⟨(key ε hε j).1, (key ε hε j).2.1⟩
  · have hlim1 : Tendsto (fun ε ↦ C * eLpNorm (ε • mollifyFstDeriv ε F) 2 cylinderMeasure)
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := C) hlimX (Or.inr hC)
      simp only [mul_zero] at h
      exact h
    have hlim2 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * (C * eLpNorm Gm 2 cylinderMeasure))
        (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
        simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      have h := ENNReal.Tendsto.mul_const h0
        (Or.inr (ENNReal.mul_ne_top hC hGmL.eLpNorm_ne_top))
        (b := C * eLpNorm Gm 2 cylinderMeasure)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hlim1.add hlim2) (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    calc ENNReal.ofReal ε * eLpNorm (d j ε) 2 volume
        ≤ ENNReal.ofReal ε * (C * (eLpNorm (mollifyFstDeriv ε F) 2 cylinderMeasure +
            eLpNorm Gm 2 cylinderMeasure)) := by
          gcongr
          exact (key ε hε j).2.2
      _ = _ := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hε.1.le]
          ring

/-! #### `lem:transversal-mollifier-commutator` -/

/-- `[L₀, J_ε] u = O(ε ‖L₀ u‖)`, uniformly in `u`. -/
theorem transversalMollifier_hasWeakL0On (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₀, ∀ u k : ℝ × ℝ → ℂ,
      MemLp u 2 (volume.restrict cellSquare) → MemLp k 2 (volume.restrict cellSquare) →
      HasWeakL0On cellSquare u k →
      ∃ kε, HasWeakL0On univ (transversalMollifier χ ε u) kε ∧ MemLp kε 2 volume ∧
        eLpNorm (kε - transversalMollifier χ ε k) 2 volume ≤
          ENNReal.ofReal (C * ε) * eLpNorm k 2 (volume.restrict cellSquare) := by
  classical
  obtain ⟨a, b, ε₀, ha, hb, hε₀, hχband, hband, hab, -⟩ := exists_mollify_band hχs
  obtain ⟨σ, L, m, M, hσL, hσS, hm, hσm, hσM⟩ := exists_periodExtension ha hb hab
  have hσc : Continuous σ := hσL.continuous
  have hσ0 (h : ℝ) : σ h ≠ 0 := (hm.trans_le (hσm h)).ne'
  have hσabs (h : ℝ) : |σ h| ≤ M := by rw [abs_of_pos (hm.trans_le (hσm h))]; exact hσM h
  have hσinv (h : ℝ) : |(σ h)⁻¹| ≤ m⁻¹ := by
    rw [abs_inv, abs_of_pos (hm.trans_le (hσm h))]
    exact inv_anti₀ hm (hσm h)
  -- Constants.
  obtain ⟨Ci, hCi⟩ := eLpNorm_cutoff_actionInput_le hχ hχs
  obtain ⟨Co, hCo⟩ := exists_actionReconstruct_bound ha hb
  refine ⟨ε₀, hε₀, Co * m⁻¹ * L * Ci, fun ε hε u k hu hk hLk ↦ ?_⟩
  -- Coordinates: `F = χU`, `Kc = χK`, `Gm = σχK`.
  set F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q) with hF_def
  set Kc : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * k (actionAngleInv q) with hKc_def
  set Gm : ℝ × ℝ → ℂ := fun q ↦ (σ q.1 : ℂ) * Kc q with hGm_def
  set kε : ℝ × ℝ → ℂ := fun p ↦ if p ∈ puncturedCell then
    (σ (levelCoord p) : ℂ)⁻¹ * mollifyFst ε Gm (actionAngle p) else 0 with hkε_def
  have hpF : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q := fun q ↦ by
    have h := levelCutoff_actionInput_periodic hχs (fun _ ↦ 1) u q
    simp only [one_mul] at h
    exact h
  have hpG : ∀ q : ℝ × ℝ, Gm (q.1, q.2 + 1) = Gm q := fun q ↦ by
    have h := levelCutoff_actionInput_periodic hχs (fun h ↦ (σ h : ℂ)) k q
    simp only [hGm_def, hKc_def]
    linear_combination h
  -- Both outputs vanish off the band.
  have hzero_mem {p : ℝ × ℝ} (hp : p ∉ closedCellLevelBand a b) (hc : p ∈ puncturedCell) :
      levelCoord p ∉ Icc a b := fun hl ↦ hp (by
    rw [closedCellLevelBand_eq ha hb]
    exact ⟨hc, hl⟩)
  have hGm' : Gm = fun z ↦ (χ z.1 : ℂ) * ((σ z.1 : ℂ) * k (actionAngleInv z)) := by
    funext z
    simp only [hGm_def, hKc_def]
    ring
  have hGband : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFst ε Gm q = 0 := fun q hq ↦ by
    rw [hGm']
    exact hband ε hε _ q hq
  have hKband : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → mollifyFst ε Kc q = 0 :=
    fun q hq ↦ hband ε hε (fun z ↦ k (actionAngleInv z)) q hq
  -- The weak transport derivative.
  have h2 : HasWeakPartialOn univ 1 F Gm :=
    hasWeakPartialOn_levelCutoff_actionInput hχ hχs hχband hσS hLk
  have h3 := h2.mollify hε.1
  have h4 : HasWeakPartialOn actionStrip 1 (transversalMollifier χ ε u ∘ actionAngleInv)
      (fun q ↦ (orbitPeriod q.1 : ℂ) * kε (actionAngleInv q)) := by
    refine (h3.mono (subset_univ _)).congr_on (measurableSet_Ioo.prod MeasurableSet.univ)
      (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    · have hP := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
      have he := comp_actionAngle_actionAngleInv (F := mollifyFst ε F)
        (mollifyFst_periodic hpF) hq
      simp only [Function.comp_apply, transversalMollifier, ite_eq_left hP] at he ⊢
      exact he.symm
    · have hP := actionAngleInv_mem_puncturedCell hq.1.1 hq.1.2 q.2
      have he := comp_actionAngle_actionAngleInv (F := mollifyFst ε Gm)
        (mollifyFst_periodic hpG) hq
      simp only [Function.comp_apply] at he
      simp only [hkε_def, ite_eq_left hP, levelCoord_actionAngleInv hq.1.1 hq.1.2, he]
      by_cases hm : q.1 ∈ Icc a b
      · rw [hσS q.1 hm, ← mul_assoc, mul_inv_cancel₀ (by
          exact_mod_cast (orbitPeriod_pos hq.1.1 hq.1.2).ne'), one_mul]
      · rw [hGband q hm, mul_zero, mul_zero]
  have h5 : HasWeakL0On univ (transversalMollifier χ ε u) kε := by
    refine (hasWeakL0On_of_actionAngle h4).univ_of_band ha hb (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · by_cases hc : p ∈ puncturedCell
      · simp only [transversalMollifier, ite_eq_left hc]
        exact hband ε hε _ _ (hzero_mem hp hc)
      · simp [transversalMollifier, hc]
    · by_cases hc : p ∈ puncturedCell
      · simp only [hkε_def, ite_eq_left hc]
        rw [hGband (actionAngle p) (hzero_mem hp hc), mul_zero]
      · simp [hkε_def, hc]
  -- `L²` bounds in coordinates.
  have hKcL : MemLp Kc 2 cylinderMeasure := memLp_cutoff_actionInput hχ hχs hk
  have hKcn : eLpNorm Kc 2 cylinderMeasure ≤ Ci * eLpNorm k 2 (volume.restrict cellSquare) :=
    hCi k hk
  have hGmL : MemLp Gm 2 cylinderMeasure := memLp_levelMul hKcL hσc hσabs
  have hMG : MemLp (mollifyFst ε Gm) 2 cylinderMeasure := (eLpNorm_mollifyFst_le hε.1 hGmL).1
  have hMK : MemLp (mollifyFst ε Kc) 2 cylinderMeasure := (eLpNorm_mollifyFst_le hε.1 hKcL).1
  have hσi : Continuous fun h ↦ (σ h)⁻¹ := hσc.inv₀ hσ0
  have hinvmul {V : ℝ × ℝ → ℂ} (hV : MemLp V 2 cylinderMeasure) :
      MemLp (fun q ↦ (σ q.1 : ℂ)⁻¹ * V q) 2 cylinderMeasure ∧
        eLpNorm (fun q ↦ (σ q.1 : ℂ)⁻¹ * V q) 2 cylinderMeasure ≤
          ENNReal.ofReal m⁻¹ * eLpNorm V 2 cylinderMeasure := by
    have hm := memLp_levelMul hV hσi hσinv
    have he : (fun q ↦ (((σ q.1)⁻¹ : ℝ) : ℂ) * V q) = fun q ↦ (σ q.1 : ℂ)⁻¹ * V q := by
      funext q
      rw [Complex.ofReal_inv]
    rw [he] at hm
    refine ⟨hm, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm.aestronglyMeasurable
      (Eventually.of_forall fun q ↦ ?_) 2⟩
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
    exact mul_le_mul_of_nonneg_right (hσinv q.1) (norm_nonneg _)
  -- `k_ε` reconstructs `Ψ = σ⁻¹ M_ε(σχK)`.
  set Ψ : ℝ × ℝ → ℂ := fun q ↦ (σ q.1 : ℂ)⁻¹ * mollifyFst ε Gm q with hΨ_def
  have hΨz : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → Ψ q = 0 := fun q hq ↦ by
    simp only [hΨ_def, hGband q hq, mul_zero]
  have hrecΨ := hCo Ψ (hinvmul hMG).1 hΨz
  have hkΨ : actionReconstruct Ψ =ᵐ[volume] kε := ae_actionReconstruct Ψ
  -- The commutator `Φ = σ⁻¹ (M_ε(σχK) - σ M_ε(χK))`.
  set B : ℝ × ℝ → ℂ := fun q ↦ mollifyFst ε Gm q - (σ q.1 : ℂ) * mollifyFst ε Kc q with hB_def
  have hBL : MemLp B 2 cylinderMeasure := hMG.sub (memLp_levelMul hMK hσc hσabs)
  have hBn : eLpNorm B 2 cylinderMeasure ≤
      ENNReal.ofReal (ε * L) * eLpNorm Kc 2 cylinderMeasure :=
    eLpNorm_mollifyFst_mul_sub_le hε.1 hσL hKcL
  set Φ : ℝ × ℝ → ℂ := fun q ↦ (σ q.1 : ℂ)⁻¹ * B q with hΦ_def
  have hΦz : ∀ q : ℝ × ℝ, q.1 ∉ Icc a b → Φ q = 0 := fun q hq ↦ by
    simp only [hΦ_def, hB_def, hGband q hq, hKband q hq, mul_zero, sub_zero]
  have hrecΦ := hCo Φ (hinvmul hBL).1 hΦz
  have heq : actionReconstruct Φ =ᵐ[volume] kε - transversalMollifier χ ε k := by
    filter_upwards [ae_actionReconstruct Φ] with p hp
    rw [hp]
    by_cases hc : p ∈ puncturedCell
    · simp only [Pi.sub_apply, hkε_def, transversalMollifier, ite_eq_left hc, hΦ_def, hB_def]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hσ0 _)), one_mul]
      rfl
    · simp [hkε_def, transversalMollifier, hc]
  refine ⟨kε, h5, MemLp.ae_eq hkΨ hrecΨ.1, ?_⟩
  have hC : ENNReal.ofReal ((Co : ℝ) * m⁻¹ * L * Ci * ε) =
      (Co : ENNReal) * (ENNReal.ofReal m⁻¹ * (ENNReal.ofReal (ε * L) * Ci)) := by
    have h₁ : 0 ≤ (Co : ℝ) * m⁻¹ := mul_nonneg Co.coe_nonneg (inv_nonneg.mpr hm.le)
    have h₂ : 0 ≤ (Co : ℝ) * m⁻¹ * L := mul_nonneg h₁ L.coe_nonneg
    rw [ENNReal.ofReal_mul (mul_nonneg h₂ Ci.coe_nonneg), ENNReal.ofReal_mul h₂,
      ENNReal.ofReal_mul h₁, ENNReal.ofReal_mul Co.coe_nonneg,
      ENNReal.ofReal_mul hε.1.le, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal]
    ring
  calc eLpNorm (kε - transversalMollifier χ ε k) 2 volume
      = eLpNorm (actionReconstruct Φ) 2 volume := eLpNorm_congr_ae heq.symm
    _ ≤ Co * eLpNorm Φ 2 cylinderMeasure := hrecΦ.2
    _ ≤ Co * (ENNReal.ofReal m⁻¹ * eLpNorm B 2 cylinderMeasure) := by
        gcongr
        exact (hinvmul hBL).2
    _ ≤ Co * (ENNReal.ofReal m⁻¹ * (ENNReal.ofReal (ε * L) *
          (Ci * eLpNorm k 2 (volume.restrict cellSquare)))) := by
        gcongr
        exact hBn.trans (by gcongr)
    _ = _ := by
        rw [hC]
        ring

end Statements

end NoEmbeddedEigenvalues
