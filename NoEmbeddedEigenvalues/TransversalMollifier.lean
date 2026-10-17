import Mathlib.MeasureTheory.Constructions.Polish.Basic
import NoEmbeddedEigenvalues.LineMollifier
import NoEmbeddedEigenvalues.Transport

/-!
# The transversal mollifier

Blueprint: `def:transversal-mollifier`, `lem:transversal-mollifier-support` (proved),
`lem:transversal-mollifier-congr`, `lem:transversal-mollifier-linear` and
`lem:transversal-mollifier` (proved from chart/coarea inputs);
stated: `lem:action-angle-weak`, `lem:transversal-mollifier-derivatives`,
`lem:transversal-mollifier-commutator`.

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
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal

/-! ### Weak derivatives in action-angle coordinates (`lem:action-angle-weak`, stated) -/

/-- `L₀ u = k` weakly on the punctured cell if and only if `∂_θ U = S(h) K` weakly on the
    strip, where `U, K` are `u, k` in action-angle coordinates. -/
theorem hasWeakL0On_iff_actionAngle {u k : ℝ × ℝ → ℂ} :
    HasWeakL0On puncturedCell u k ↔
      HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv)
        (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q)) := by
  sorry

/-- The chain rule for weak derivatives from the cell to the strip. -/
theorem HasWeakPartialOn.comp_actionAngleInv {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) (j : Fin 2) :
    HasWeakPartialOn actionStrip j (u ∘ actionAngleInv) (fun q ↦
      ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) := by
  sorry

/-- The chain rule for weak derivatives from the strip to the cell, for functions that are
    `1`-periodic in `θ`. The angle jumps across its cut, a null set, where its partial
    derivatives are irrelevant. -/
theorem HasWeakPartialOn.comp_actionAngle {F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hG : ∀ i, HasWeakPartialOn actionStrip i F (G i)) (j : Fin 2) :
    HasWeakPartialOn puncturedCell j (F ∘ actionAngle) (fun p ↦
      ((coordPartial j levelCoord p : ℝ) : ℂ) * G 0 (actionAngle p) +
        ((coordPartial j angleCoord p : ℝ) : ℂ) * G 1 (actionAngle p)) := by
  sorry

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

/-- A fixed level band contains both the cutoff and all sufficiently small mollifications. -/
private theorem exists_mollify_band {χ : ℝ → ℝ} (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ a b ε₀ : ℝ, 0 < a ∧ b < 1 ∧ 0 < ε₀ ∧ tsupport χ ⊆ Icc a b ∧
      ∀ ε ∈ Ioo 0 ε₀, ∀ (u : ℝ × ℝ → ℂ) (q : ℝ × ℝ), q.1 ∉ Icc a b →
        mollifyFst ε (fun z ↦ (χ z.1 : ℂ) * u (actionAngleInv z)) q = 0 := by
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
  refine ⟨l / 2, (r + 1) / 2, ε₀, by linarith, by linarith, hε₀, ?_, ?_⟩
  · intro t ht
    have hlt : l ≤ t := hlow t ht
    have htr := hupp t ht
    exact ⟨by linarith, by linarith⟩
  · intro ε hε u q hq
    have he₁ : ε < l / 2 := by
      have h := min_le_left l (1 - r)
      dsimp [ε₀] at hε
      linarith [hε.2]
    have he₂ : ε < (1 - r) / 2 := by
      have h := min_le_right l (1 - r)
      dsimp [ε₀] at hε
      linarith [hε.2]
    unfold mollifyFst
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    by_cases hk : mollifierKernel ε (q.1 - t) = 0
    · simp [hk]
    by_cases ht : χ t = 0
    · simp [ht]
    have hts : t ∈ tsupport χ := subset_closure (show t ∈ Function.support χ from ht)
    have hlt : l ≤ t := hlow t hts
    have htr := hupp t hts
    have hB : stdBump ((q.1 - t) / ε) ≠ 0 := by
      intro hz
      apply hk
      simp [mollifierKernel, hz]
    have hmem : (q.1 - t) / ε ∈ Function.support stdBump := hB
    rw [support_stdBump] at hmem
    have hleft := (lt_div_iff₀ hε.1).mp hmem.1
    have hright := (div_lt_iff₀ hε.1).mp hmem.2
    exact False.elim (hq ⟨by linarith, by linarith⟩)

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
  obtain ⟨a, b, ε₀, ha, hb, hε₀, _, hband⟩ := exists_mollify_band hχs
  refine ⟨closedCellLevelBand a b, isCompact_closedCellLevelBand _ _,
    closedCellLevelBand_subset ha hb, ε₀, hε₀, ?_⟩
  intro ε hε u p hp
  by_cases hc : p ∈ puncturedCell
  · rw [transversalMollifier, ite_eq_left hc]
    apply hband ε hε u (actionAngle p)
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
  obtain ⟨a, b, ε₀, ha, hb, hε₀, _, hband⟩ := exists_mollify_band hχs
  obtain ⟨Ci, hCi⟩ := eLpNorm_cutoff_actionInput_le hχ hχs
  obtain ⟨Co, hCo⟩ := exists_actionReconstruct_bound ha hb
  refine ⟨ε₀, hε₀, Co * Ci, fun ε hε u hu ↦ ?_⟩
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)
  have hM := eLpNorm_mollifyFst_le hε.1 (memLp_cutoff_actionInput hχ hχs hu)
  have hrec := hCo (mollifyFst ε F) hM.1 (hband ε hε u)
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
  obtain ⟨a, b, ε₀, ha, hb, hε₀, hχband, hband⟩ := exists_mollify_band hχs
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
      rw [hband ε hεband u q hq]
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
  sorry

/-- For `u, L₀ u ∈ L²` of the cell, `J_ε u ∈ H¹(ℝ²)` with `ε ‖∇J_ε u‖ → 0`. -/
theorem transversalMollifier_hasWeakPartialOn (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u k : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) (hk : MemLp k 2 (volume.restrict cellSquare))
    (hL : HasWeakL0On cellSquare u k) :
    ∃ d : Fin 2 → ℝ → ℝ × ℝ → ℂ,
      (∀ᶠ ε in 𝓝[>] 0, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
        MemLp (d j ε) 2 volume) ∧
      ∀ j, Tendsto (fun ε ↦ ENNReal.ofReal ε * eLpNorm (d j ε) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-! #### `lem:transversal-mollifier-commutator` (stated) -/

/-- `[L₀, J_ε] u = O(ε ‖L₀ u‖)`, uniformly in `u`. -/
theorem transversalMollifier_hasWeakL0On (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₀, ∀ u k : ℝ × ℝ → ℂ,
      MemLp u 2 (volume.restrict cellSquare) → MemLp k 2 (volume.restrict cellSquare) →
      HasWeakL0On cellSquare u k →
      ∃ kε, HasWeakL0On univ (transversalMollifier χ ε u) kε ∧ MemLp kε 2 volume ∧
        eLpNorm (kε - transversalMollifier χ ε k) 2 volume ≤
          ENNReal.ofReal (C * ε) * eLpNorm k 2 (volume.restrict cellSquare) := by
  sorry

end Statements

end NoEmbeddedEigenvalues
