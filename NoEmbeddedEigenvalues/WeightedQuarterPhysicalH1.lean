import NoEmbeddedEigenvalues.OrdinaryQuarterGradient
import NoEmbeddedEigenvalues.TransportAxisGluing
import NoEmbeddedEigenvalues.WeightedTransportH1Data
import NoEmbeddedEigenvalues.WeakDerivativeGluing

/-!
# Physical H¹ from all four original weighted quarter fields

The inverse frame supplies genuine finite physical norms on each open quarter.
Weak locality and uniqueness identify a single off-axis gradient; a finite
quarter cover supplies its full collar norms. Transverse-cutoff extension and
the global weak transport equation remove the axis jumps without evaluating
raw line values or imposing a separate trace matching hypothesis.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

private theorem rotation_pow_apply (k : ℕ) (p : ℝ × ℝ) :
    (rotLinear ^ k) p = rotLift^[k] p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change rotLift ((rotLinear ^ k) p) = rotLift (rotLift^[k] p)
    rw [ih]

private def rotationChart (k : ℕ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := planeAffine (rotLinear ^ k) 0

private theorem rotationChart_apply (k : ℕ) :
    (rotationChart k : (ℝ × ℝ) → ℝ × ℝ) = rotLift^[k] := by
  funext p
  simp only [rotationChart, planeAffine_apply, add_zero, rotation_pow_apply]

private theorem rotationChart_preserving (k : ℕ) : MeasurePreserving (rotationChart k) := by
  simpa only [rotationChart_apply] using measurePreserving_rotLift.iterate k

/-- The physical image of a recentered quarter, with its original rotation. -/
def rotatedQuarterImage (k : Fin 4) (b : ℝ) : Set (ℝ × ℝ) :=
  rotLift^[k.val] '' quarterImage b

theorem isOpen_rotatedQuarterImage {b : ℝ} (hb : b ≤ 1) (k : Fin 4) :
    IsOpen (rotatedQuarterImage k b) := by
  change IsOpen (rotLift^[k.val] '' quarterImage b)
  rw [← rotationChart_apply]
  exact (rotationChart k.val).isOpenMap _ (isOpen_quarterImage hb)

/-- Weighted weak data on each recentered quarter give ordinary H¹ on its
physical image, retaining the same raw unknown and the same collar. -/
theorem HasWeightedQuarterDerivatives.physical_quarters
    {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {v : ℝ × ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {A B : Fin 4 → ℝ × ℝ → ℂ} (hAB : HasWeightedQuarterDerivatives b v A B) :
    ∀ k, MemSobolevOn 1 (rotatedQuarterImage k b) v := by
  intro k
  have hb1 : b ≤ 1 := by linarith
  let R := rotationChart k.val
  have hR : MeasurePreserving R := rotationChart_preserving k.val
  have hbase : MemSobolevOn 1 (quarterImage b) (v ∘ R) := by
    have hvR := memLp_comp_planeAffine (rotLinear ^ k.val) 0 hR hU.measurableSet hv
    have hRU : quarterImage b ⊆ R ⁻¹' U := by
      intro p hp
      apply hcell
      change (rotationChart k.val) p ∈ cellSquare
      rw [rotationChart_apply]
      have hc : p ∈ cellSquare := hp.1.1.1
      induction k.val with
      | zero => exact hc
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (rotLift_cell_level _).1.mpr ih
    refine ⟨hvR.mono_measure (Measure.restrict_mono_set _ hRU), fun j ↦ ?_⟩
    have hH : HasWeakPartialOn (quarterOrbitStrip b) 0
        (fun q ↦ (v ∘ R) (dipoleOrbit q.1 q.2)) (A k) := by
      simpa only [Function.comp_apply, R, rotationChart_apply, recenteredQuarterMap] using (hAB k).1
    have hT : HasWeakPartialOn (quarterOrbitStrip b) 1
        (fun q ↦ (v ∘ R) (dipoleOrbit q.1 q.2)) (B k) := by
      simpa only [Function.comp_apply, R, rotationChart_apply, recenteredQuarterMap]
        using (hAB k).2.1
    have hHA : MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * A k q) 2
        (volume.restrict (quarterOrbitStrip b)) := by
      simpa only [recenteredQuarterMap, saddleDist_rotLift_iterate] using (hAB k).2.2.1
    have hTB : MemLp (fun q ↦ B k q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) := by
      simpa only [recenteredQuarterMap, saddleDist_rotLift_iterate] using (hAB k).2.2.2
    exact ⟨quarterSpatialGradient (A k) (B k) j, quarterSpatialGradient_weak hb1 hH hT j,
      memLp_quarterSpatialGradient_ordinary hb1 j
        (quarterInverseGradient_ordinary_memLp hb hbh hHA hTB j)⟩
  have hback := hbase.comp_planeAffine_symm (rotLinear ^ k.val) 0 hR (isOpen_quarterImage hb1)
  have hdomain : R.symm ⁻¹' quarterImage b = rotatedQuarterImage k b := by
    rw [rotatedQuarterImage, ← rotationChart_apply]
    change R.symm ⁻¹' quarterImage b = R '' quarterImage b
    ext p
    constructor
    · intro hp
      exact ⟨R.symm p, hp, R.apply_symm_apply p⟩
    · rintro ⟨q, hq, rfl⟩
      simpa only [mem_preimage, R.symm_apply_apply] using hq
  have hfun : (v ∘ R) ∘ R.symm = v := by
    funext p
    simp only [Function.comp_apply, R.apply_symm_apply]
  change MemSobolevOn 1 (R.symm ⁻¹' quarterImage b) ((v ∘ R) ∘ R.symm) at hback
  simpa only [hdomain, hfun] using hback

/-- The four actual physical images cover the collar off the Cartesian axes.
This is a pointwise open cover, separate from any weak gluing assertion. -/
theorem exists_mem_rotatedQuarterImage {b : ℝ} (hb : b ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ cellSeparatrixStrip (2 * b)) (hx : p.1 ≠ 0) (hy : p.2 ≠ 0) :
    ∃ k : Fin 4, p ∈ rotatedQuarterImage k b := by
  have hh : levelCoord p ∈ Ioo 0 b := by
    change 0 < dipoleLift p / 2 ∧ dipoleLift p / 2 < b
    constructor <;> linarith [hp.2.1, hp.2.2]
  obtain ⟨k, hk⟩ := exists_rotLift_mem_quarterImage hb hp.1 hh hx hy
  fin_cases k
  · exact ⟨0, p, hk, rfl⟩
  · refine ⟨3, rotLift p, hk, ?_⟩
    simp [Function.iterate_succ_apply, rotLift]
  · refine ⟨2, rotLift^[2] p, hk, ?_⟩
    simp [Function.iterate_succ_apply, rotLift]
  · refine ⟨1, rotLift^[3] p, hk, ?_⟩
    simp [Function.iterate_succ_apply, rotLift]

/-- One measurable off-axis gradient has genuine full-collar norms, obtained
from the four physical quarter norms. No weak identity is extended here. -/
theorem HasWeightedQuarterDerivatives.exists_off_axis_gradient
    {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {v : ℝ × ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {A B : Fin 4 → ℝ × ℝ → ℂ} (hAB : HasWeightedQuarterDerivatives b v A B) :
    ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (cellSeparatrixStrip (2 * b) \ {p | p.1 = 0 ∨ p.2 = 0}) j v (D j) ∧
      MemLp (D j) 2 (volume.restrict (cellSeparatrixStrip (2 * b))) := by
  let V := cellSeparatrixStrip (2 * b)
  let O := V \ {p | p.1 = 0 ∨ p.2 = 0}
  have hb1 : b ≤ 1 := by linarith
  have hV : IsOpen V := isOpen_cellSeparatrixStrip _
  have hO : IsOpen O := hV.sdiff
    ((isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq continuous_snd continuous_const))
  have hQ := hAB.physical_quarters hb hbh hU hv hcell
  have hloc : MemSobolevLocOn 1 O v := by
    apply memSobolevLocOn_of_locally
    intro p hp
    have hn := not_or.mp hp.2
    obtain ⟨k, hk⟩ := exists_mem_rotatedQuarterImage hb1 hp.1 hn.1 hn.2
    exact ⟨rotatedQuarterImage k b, isOpen_rotatedQuarterImage hb1 k, hk,
      (hQ k).memSobolevLocOn⟩
  obtain ⟨D, hD⟩ := hloc.exists_measurable_weakGradient hO
  refine ⟨D, fun j ↦ ⟨(hD j).2.1, ?_⟩⟩
  have hL (k : Fin 4) : MemLp (D j) 2
      (volume.restrict (O ∩ rotatedQuarterImage k b)) := by
    obtain ⟨E, hE, hEL⟩ := (hQ k).2 j
    have he := ((hD j).2.1.mono inter_subset_left).ae_eq
      (hO.inter (isOpen_rotatedQuarterImage hb1 k)) (hE.mono inter_subset_right)
    apply (hEL.mono_measure (Measure.restrict_mono_set _ inter_subset_right)).ae_eq
    filter_upwards [ae_restrict_of_ae he,
      ae_restrict_mem (hO.inter (isOpen_rotatedQuarterImage hb1 k)).measurableSet] with p he hp
    exact (he hp).symm
  have hLi : IntegrableOn (fun p ↦ ‖D j p‖ ^ 2) (⋃ k : Fin 4, O ∩ rotatedQuarterImage k b) :=
    integrableOn_finite_iUnion.mpr fun k ↦
      (memLp_two_iff_integrable_sq_norm (hL k).aestronglyMeasurable).mp (hL k)
  have hLu := (memLp_two_iff_integrable_sq_norm
    (hD j).1.aestronglyMeasurable).mpr hLi
  apply hLu.mono_measure (Measure.restrict_mono_ae ?_)
  have hn : ∀ᵐ x : ℝ, x ≠ 0 := by
    simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hn,
    Measure.quasiMeasurePreserving_snd.ae hn] with p hx hy hp
  obtain ⟨k, hk⟩ := exists_mem_rotatedQuarterImage hb1 hp hx hy
  exact mem_iUnion.mpr ⟨k, ⟨hp, not_or.mpr ⟨hx, hy⟩⟩, hk⟩

/-- Physical inverse-frame reconstruction and distributional no-jump gluing on
exactly the supplied positive cell collar. -/
theorem IsTransportPair.cell_h1_of_weighted_quarter_derivatives
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2)
    {A B : Fin 4 → ℝ × ℝ → ℂ} (hAB : HasWeightedQuarterDerivatives b v A B) :
    MemSobolevOn 1 (cellSeparatrixStrip (2 * b)) v := by
  let V := cellSeparatrixStrip (2 * b)
  have hV : IsOpen V := isOpen_cellSeparatrixStrip _
  have hVU : V ⊆ U := fun p hp ↦ hcell (subset_closure hp.1)
  have hf : MemSobolevOn 1 V f := (hp.memSobolevOn.mono hVU).of_succ
  choose E hE hEL using hf.2
  obtain ⟨D, hD⟩ := hAB.exists_off_axis_gradient hb hbh hp.isOrbitUnion.1 hp.memLp
    (subset_closure.trans hcell)
  have hG (j : Fin 2) : MemLp (fun p ↦ D j p + E j p) 2 (volume.restrict V) :=
    (hD j).2.add (hEL j)
  have hoff (j : Fin 2) : HasWeakPartialOn (V \ {p | p.1 = 0 ∨ p.2 = 0}) j
      (fun p ↦ v p + f p) (fun p ↦ D j p + E j p) :=
    (hD j).1.add ((hE j).mono sdiff_subset)
  have hzero : (0 : ℝ × ℝ) ∉ V := by
    intro h0
    have h := h0.2.2
    norm_num [dipoleLift] at h
    linarith
  have hsin : ∀ p ∈ V, ∀ j : Fin 2,
      (if j = 0 then p.1 else p.2) ≠ 0 →
        Real.sin (if j = 0 then p.1 else p.2) ≠ 0 := by
    intro p hpv j hn
    have ha := abs_lt.mp hpv.1.1
    have hc := abs_lt.mp hpv.1.2
    dsimp only [diagCoord] at ha hc
    fin_cases j
    · change Real.sin p.1 ≠ 0
      change p.1 ≠ 0 at hn
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).not.mpr hn
    · change Real.sin p.2 ≠ 0
      change p.2 ≠ 0 at hn
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).not.mpr hn
  have hAll := (hp.hasWeakL0On.mono hVU).h1_of_off_axes hV
    ((hp.memLp.mono_measure (Measure.restrict_mono_set _ hVU)).add hf.1)
    hG hoff hzero hsin
  have he : (fun p ↦ v p + f p + (-1 : ℂ) * f p) = v := by
    funext p
    ring
  have hfinal := hAll.add (hf.const_mul (-1))
  rw [he] at hfinal
  exact hfinal

end NoEmbeddedEigenvalues
