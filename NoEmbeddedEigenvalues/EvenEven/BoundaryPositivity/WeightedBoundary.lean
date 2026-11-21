module

public import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.BoundaryForm
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1Estimates

/-!
# The weighted second-order boundary domain

Blueprint: `def:weighted-boundary-domain`, `lem:weighted-boundary-linear`,
`lem:boundary-jet-weighted`, and `lem:weighted-boundary-local`.

`HasWeightedBoundaryH2 F D E` specifies H¹ data `(F,D)` on `(-1,1)`, local
absolute continuity of `D` with a.e. derivative `E`, and square integrability
of `(1-x²)E`. It imposes neither global L² integrability of `E` nor endpoint
traces of `D`. Only the value `F` has the H¹ traces constructed earlier.

This is a representative/derivative predicate, not a normed quotient space.
The distributional weak-test bridge, density, and Sobolev boundary positivity
are not asserted here.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Interval Topology

/-- Weighted second-order regularity on the separatrix interval, with explicit
    first and second derivatives. Endpoint and outside values are unrestricted. -/
structure HasWeightedBoundaryH2 (F D E : ℝ → ℂ) : Prop where
  h1 : HasIntervalH1 (-1) 1 F D
  locally_absolutelyContinuous_first : ∀ c d, -1 < c → c ≤ d → d < 1 →
    AbsolutelyContinuousOnInterval D c d
  hasDerivAt_first_ae : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt D (E x) x
  memLp_weighted_second :
    MemLp (fun x ↦ (boundaryWeight x : ℂ) * E x) 2 (volume.restrict (Ioo (-1) 1))

/-- Membership without specifying representatives of the two derivatives. -/
def MemWeightedBoundaryH2 (F : ℝ → ℂ) : Prop :=
  ∃ D E, HasWeightedBoundaryH2 F D E

/-- The weighted domain includes first-order membership and hence value traces. -/
theorem HasWeightedBoundaryH2.memH1 {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) : MemIntervalH1 (-1) 1 F := ⟨D, h.h1⟩

/-- Closure of the weighted domain under addition. -/
theorem HasWeightedBoundaryH2.add {F D E G H K : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (k : HasWeightedBoundaryH2 G H K) :
    HasWeightedBoundaryH2 (F + G) (D + H) (E + K) where
  h1 := h.h1.add k.h1
  locally_absolutelyContinuous_first c d hc hcd hd :=
    (h.locally_absolutelyContinuous_first c d hc hcd hd).add
      (k.locally_absolutelyContinuous_first c d hc hcd hd)
  hasDerivAt_first_ae := by
    filter_upwards [h.hasDerivAt_first_ae, k.hasDerivAt_first_ae] with x hx hk hi
    exact (hx hi).add (hk hi)
  memLp_weighted_second := by
    simpa only [Pi.add_def, mul_add] using
      h.memLp_weighted_second.add k.memLp_weighted_second

/-- Closure of the weighted domain under complex scalar multiplication. -/
theorem HasWeightedBoundaryH2.smul {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (z : ℂ) :
    HasWeightedBoundaryH2 (z • F) (z • D) (z • E) where
  h1 := h.h1.smul z
  locally_absolutelyContinuous_first c d hc hcd hd :=
    AbsolutelyContinuousOnInterval.const_smul z
      (h.locally_absolutelyContinuous_first c d hc hcd hd)
  hasDerivAt_first_ae := by
    filter_upwards [h.hasDerivAt_first_ae] with x hx hi
    exact (hx hi).const_smul z
  memLp_weighted_second := by
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using
      h.memLp_weighted_second.const_smul z

/-- A continuous function on a compact interval is essentially bounded there. -/
theorem memLp_top_of_continuousOn_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f ⊤ (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm
  apply memLp_top_of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC (mem_image_of_mem (fun x ↦ ‖f x‖) hx)

/-- A continuous derivative on a compact interval gives absolute continuity. -/
theorem absolutelyContinuous_of_continuousOn_derivative {a b : ℝ} {F D : ℝ → ℂ}
    (hab : a ≤ b) (hD : ContinuousOn D (Icc a b))
    (hder : ∀ x ∈ Icc a b, HasDerivAt F (D x) x) :
    AbsolutelyContinuousOnInterval F a b := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hD.nnnorm
  have hL : LipschitzOnWith C F (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx ↦ (hder x hx).hasDerivWithinAt)
      (fun x hx ↦ hC (mem_image_of_mem (fun x ↦ ‖D x‖₊) hx))
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
  simpa only [uIcc_of_le hab] using hL

/-- Classical boundary jets belong to the weighted second-order domain. -/
theorem BoundaryJet.hasWeightedBoundaryH2 (J : BoundaryJet) :
    HasWeightedBoundaryH2 J.value J.first J.second where
  h1 := {
    memLp_value := ((memLp_top_of_continuousOn_Icc J.continuous_value).mono_exponent
      (by simp)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    memLp_derivative := ((memLp_top_of_continuousOn_Icc J.continuous_first).mono_exponent
      (by simp)).mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    locally_absolutelyContinuous := fun c d hc hcd hd ↦
      absolutelyContinuous_of_continuousOn_derivative hcd
        (J.continuous_first.mono (Icc_subset_Icc hc.le hd.le))
        (fun x hx ↦ J.deriv_value x ⟨hc.le.trans hx.1, hx.2.trans hd.le⟩)
    hasDerivAt_ae := Eventually.of_forall (fun x hx ↦ J.deriv_value x (Ioo_subset_Icc_self hx)) }
  locally_absolutelyContinuous_first c d hc hcd hd :=
    absolutelyContinuous_of_continuousOn_derivative hcd
      (J.continuous_second.mono (Icc_subset_Icc hc.le hd.le))
      (fun x hx ↦ J.deriv_first x ⟨hc.le.trans hx.1, hx.2.trans hd.le⟩)
  hasDerivAt_first_ae :=
    Eventually.of_forall (fun x hx ↦ J.deriv_first x (Ioo_subset_Icc_self hx))
  memLp_weighted_second := by
    have hC : ContinuousOn (fun x ↦ (boundaryWeight x : ℂ) * J.second x) (Icc (-1) 1) := by
      exact (Complex.continuous_ofReal.comp (continuous_const.sub
        (continuous_id.pow 2))).continuousOn.mul J.continuous_second
    exact ((memLp_top_of_continuousOn_Icc hC).mono_exponent (by simp)).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)

/-- Away from the degenerate endpoints, the second derivative is locally L². -/
theorem HasWeightedBoundaryH2.memLp_second_local {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {c d : ℝ} (hc : -1 < c) (hd : d < 1) :
    MemLp E 2 (volume.restrict (Ioo c d)) := by
  have hw : ∀ x ∈ Icc c d, (boundaryWeight x : ℂ) ≠ 0 := by
    intro x hx
    have hpos : 0 < boundaryWeight x := by
      unfold boundaryWeight
      nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
        (show 0 < 1 + x by linarith [hx.1])]
    exact_mod_cast hpos.ne'
  have hcont : ContinuousOn (fun x ↦ (boundaryWeight x : ℂ)⁻¹) (Icc c d) := by
    apply ContinuousOn.inv₀ _ hw
    unfold boundaryWeight
    fun_prop
  have hinv : MemLp (fun x ↦ (boundaryWeight x : ℂ)⁻¹) ⊤
      (volume.restrict (Ioo c d)) :=
    (memLp_top_of_continuousOn_Icc hcont).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hweight := h.memLp_weighted_second.mono_measure
    (Measure.restrict_mono (Ioo_subset_Ioo hc.le hd.le) le_rfl)
  have hprod : MemLp ((fun x ↦ (boundaryWeight x : ℂ)⁻¹) *
      (fun x ↦ (boundaryWeight x : ℂ) * E x)) 2 (volume.restrict (Ioo c d)) :=
    hinv.mul hweight
  apply MemLp.ae_eq _ hprod
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [Pi.mul_apply]
  rw [← mul_assoc, inv_mul_cancel₀ (hw x (Ioo_subset_Icc_self hx)), one_mul]

/-- The first derivative has ordinary H¹ regularity on each interior subinterval. -/
theorem HasWeightedBoundaryH2.first_hasIntervalH1 {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {c d : ℝ} (hc : -1 < c) (hd : d < 1) :
    HasIntervalH1 c d D E where
  memLp_value := h.h1.memLp_derivative.mono_measure
    (Measure.restrict_mono (Ioo_subset_Ioo hc.le hd.le) le_rfl)
  memLp_derivative := h.memLp_second_local hc hd
  locally_absolutelyContinuous u v hcu huv hvd :=
    h.locally_absolutelyContinuous_first u v (hc.trans hcu) huv (hvd.trans hd)
  hasDerivAt_ae := by
    filter_upwards [h.hasDerivAt_first_ae] with x hx hi
    exact hx ⟨hc.trans hi.1, hi.2.trans hd⟩

/-- The H¹ value traces of a classical jet are its ordinary endpoint values. -/
theorem BoundaryJet.weighted_extension_eq (J : BoundaryJet) :
    EqOn (intervalH1Extension (-1) 1 J.value J.first) J.value (Icc (-1) 1) := by
  intro x hx
  exact (J.hasWeightedBoundaryH2.h1.extension_unique (by norm_num)
    J.continuous_value (fun _ _ ↦ rfl) hx).symm

/-- Closure under subtraction, keeping explicit derivative representatives. -/
theorem HasWeightedBoundaryH2.sub {F D E G H K : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (k : HasWeightedBoundaryH2 G H K) :
    HasWeightedBoundaryH2 (F - G) (D - H) (E - K) := by
  simpa only [neg_one_smul, ← sub_eq_add_neg] using h.add (k.smul (-1))

/-- Affine functions belong to the weighted domain with zero second derivative. -/
theorem hasWeightedBoundaryH2_affine (a b : ℂ) :
    HasWeightedBoundaryH2 (fun x ↦ a + b * (x : ℂ)) (fun _ ↦ b) (fun _ ↦ 0) := by
  let J : BoundaryJet := {
    value := fun x ↦ a + b * (x : ℂ)
    first := fun _ ↦ b
    second := fun _ ↦ 0
    continuous_value := by fun_prop
    continuous_first := continuousOn_const
    continuous_second := continuousOn_const
    deriv_value := fun x _ ↦ by
      simpa using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_id x)).const_mul b |>.const_add a
    deriv_first := fun x _ ↦ hasDerivAt_const x b }
  exact J.hasWeightedBoundaryH2

/-- Subtracting an affine function leaves the weighted second derivative unchanged. -/
theorem HasWeightedBoundaryH2.subAffine {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (a b : ℂ) :
    HasWeightedBoundaryH2 (fun x ↦ F x - a - b * (x : ℂ)) (fun x ↦ D x - b) E := by
  convert h.sub (hasWeightedBoundaryH2_affine a b) using 1 <;>
    ext x <;> simp [sub_add_eq_sub_sub]

end NoEmbeddedEigenvalues
