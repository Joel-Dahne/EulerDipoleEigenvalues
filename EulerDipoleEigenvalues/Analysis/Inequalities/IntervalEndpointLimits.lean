module

public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import EulerDipoleEigenvalues.EvenEven.BoundaryPositivity.WeightedBoundary

/-! # Interval integral exhaustion and L² endpoint bounds -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Complex ComplexConjugate MeasureTheory Set Filter
open scoped Interval Topology

/-! ### Square-integrable functions near an endpoint -/

/-- A square-integrable function satisfies `liminf (b - x) |g x|² = 0` at the right
    endpoint, for its values at every point (not only almost everywhere). -/
theorem frequently_sub_mul_sq_lt_right {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) (Ioo a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in 𝓝[<] b, (b - x) * ‖g x‖ ^ 2 < ε := by
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hcon
  have hcb : max l a < b := max_lt hl hab
  have hgc : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) (Ioo (max l a) b) :=
    hg.mono_set (Ioo_subset_Ioo_left (le_max_right l a))
  have hinv : IntegrableOn (fun x ↦ (x - b)⁻¹) (Ioo (max l a) b) := by
    refine Integrable.mono' (hgc.const_mul ε⁻¹) ?_ ?_
    · exact (measurable_id.sub_const b).inv.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hbx : 0 < b - x := sub_pos.2 hx.2
      have hle : ε ≤ (b - x) * ‖g x‖ ^ 2 :=
        not_lt.1 (hsub ⟨(le_max_left l a).trans_lt hx.1, hx.2⟩)
      rw [norm_inv, Real.norm_eq_abs, abs_sub_comm, abs_of_pos hbx]
      calc (b - x)⁻¹ = ε⁻¹ * (ε / (b - x)) := by field_simp
        _ ≤ ε⁻¹ * ‖g x‖ ^ 2 := by
          gcongr
          rw [div_le_iff₀ hbx]
          linarith
  rcases intervalIntegrable_sub_inv_iff.1
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le).2 hinv) with h | h
  · exact hcb.ne h
  · exact h right_mem_uIcc

/-- The left-endpoint version of `frequently_sub_mul_sq_lt_right`. -/
theorem frequently_sub_mul_sq_lt_left {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) (Ioo a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ x in 𝓝[>] a, (x - a) * ‖g x‖ ^ 2 < ε := by
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hcon
  have hac : a < min u b := lt_min hu hab
  have hgc : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) (Ioo a (min u b)) :=
    hg.mono_set (Ioo_subset_Ioo_right (min_le_right u b))
  have hinv : IntegrableOn (fun x ↦ (x - a)⁻¹) (Ioo a (min u b)) := by
    refine Integrable.mono' (hgc.const_mul ε⁻¹) ?_ ?_
    · exact (measurable_id.sub_const a).inv.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxa : 0 < x - a := sub_pos.2 hx.1
      have hle : ε ≤ (x - a) * ‖g x‖ ^ 2 :=
        not_lt.1 (hsub ⟨hx.1, hx.2.trans_le (min_le_left u b)⟩)
      rw [norm_inv, Real.norm_eq_abs, abs_of_pos hxa]
      calc (x - a)⁻¹ = ε⁻¹ * (ε / (x - a)) := by field_simp
        _ ≤ ε⁻¹ * ‖g x‖ ^ 2 := by
          gcongr
          rw [div_le_iff₀ hxa]
          linarith
  rcases intervalIntegrable_sub_inv_iff.1
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).2 hinv) with h | h
  · exact hac.ne h
  · exact h left_mem_uIcc

/-! ### Exhaustion of an interval -/

section Exhaustion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `P` is a primitive of an integrable `g` on `[c,b)` and comes arbitrarily close to
    `L` near `b`, then `∫ c..b g = L - P c`. -/
theorem intervalIntegral_eq_of_frequently_right {g P : ℝ → E} {c b : ℝ} {L : E}
    (hcb : c < b) (hg : IntervalIntegrable g volume c b)
    (hP : ∀ x ∈ Ioo c b, (∫ t in c..x, g t) = P x - P c)
    (hL : ∀ ε > 0, ∃ᶠ x in 𝓝[<] b, ‖P x - L‖ < ε) :
    (∫ t in c..b, g t) = L - P c := by
  have hcont := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  rw [uIcc_of_le hcb.le] at hcont
  have htend : Tendsto (fun x ↦ ∫ t in c..x, g t) (𝓝[<] b) (𝓝 (∫ t in c..b, g t)) :=
    ((hcont b (right_mem_Icc.2 hcb.le)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT hcb) Ioo_subset_Icc_self)).tendsto
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨x, hxL, hxI, hxc⟩ := ((hL (ε / 2) (half_pos hε)).and_eventually
    ((Metric.tendsto_nhds.1 htend (ε / 2) (half_pos hε)).and (Ioo_mem_nhdsLT hcb))).exists
  rw [hP x hxc, dist_eq_norm] at hxI
  rw [dist_eq_norm]
  calc ‖(∫ t in c..b, g t) - (L - P c)‖
      = ‖(P x - L) - ((P x - P c) - ∫ t in c..b, g t)‖ := by congr 1; abel
    _ ≤ ‖P x - L‖ + ‖(P x - P c) - ∫ t in c..b, g t‖ := norm_sub_le _ _
    _ ≤ ε := by linarith

/-- The left-endpoint version of `intervalIntegral_eq_of_frequently_right`. -/
theorem intervalIntegral_eq_of_frequently_left {g P : ℝ → E} {a c : ℝ} {L : E}
    (hac : a < c) (hg : IntervalIntegrable g volume a c)
    (hP : ∀ x ∈ Ioo a c, (∫ t in x..c, g t) = P c - P x)
    (hL : ∀ ε > 0, ∃ᶠ x in 𝓝[>] a, ‖P x - L‖ < ε) :
    (∫ t in a..c, g t) = P c - L := by
  have hcont := intervalIntegral.continuousOn_primitive_interval' hg.symm left_mem_uIcc
  rw [uIcc_of_ge hac.le] at hcont
  have htend : Tendsto (fun x ↦ ∫ t in c..x, g t) (𝓝[>] a) (𝓝 (∫ t in c..a, g t)) :=
    ((hcont a (left_mem_Icc.2 hac.le)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hac) Ioo_subset_Icc_self)).tendsto
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨x, hxL, hxI, hxc⟩ := ((hL (ε / 2) (half_pos hε)).and_eventually
    ((Metric.tendsto_nhds.1 htend (ε / 2) (half_pos hε)).and (Ioo_mem_nhdsGT hac))).exists
  rw [intervalIntegral.integral_symm, hP x hxc, dist_eq_norm] at hxI
  rw [dist_eq_norm, intervalIntegral.integral_symm]
  calc ‖-(∫ t in c..a, g t) - (P c - L)‖
      = ‖(-(P c - P x) - ∫ t in c..a, g t) - (P x - L)‖ := by congr 1; abel
    _ ≤ ‖-(P c - P x) - ∫ t in c..a, g t‖ + ‖P x - L‖ := norm_sub_le _ _
    _ ≤ ε := by linarith

/-- Exhaustion of `(a,b)`: a primitive on the open interval that comes arbitrarily
    close to `La` and `Lb` near the endpoints computes the integral. -/
theorem intervalIntegral_eq_of_frequently {g P : ℝ → E} {a b : ℝ} {La Lb : E}
    (hab : a < b) (hg : IntervalIntegrable g volume a b)
    (hP : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, (∫ t in x..y, g t) = P y - P x)
    (ha : ∀ ε > 0, ∃ᶠ x in 𝓝[>] a, ‖P x - La‖ < ε)
    (hb : ∀ ε > 0, ∃ᶠ x in 𝓝[<] b, ‖P x - Lb‖ < ε) :
    (∫ t in a..b, g t) = Lb - La := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hmu : (a + b) / 2 ∈ [[a, b]] := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self hm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hmu))
    (hg.mono_set (uIcc_subset_uIcc hmu right_mem_uIcc)),
    intervalIntegral_eq_of_frequently_left hm.1
      (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hmu))
      (fun x hx ↦ hP x ⟨hx.1, hx.2.trans hm.2⟩ _ hm) ha,
    intervalIntegral_eq_of_frequently_right hm.2
      (hg.mono_set (uIcc_subset_uIcc hmu right_mem_uIcc))
      (fun x hx ↦ hP _ hm x ⟨hm.1.trans hx.1, hx.2⟩) hb]
  abel

end Exhaustion

end EulerDipoleEigenvalues
