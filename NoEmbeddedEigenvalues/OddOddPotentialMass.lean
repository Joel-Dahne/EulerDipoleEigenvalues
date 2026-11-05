import NoEmbeddedEigenvalues.OddOddVirial
import NoEmbeddedEigenvalues.OddOddBulkIntegrability
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Corner subtraction for the odd–odd weighted value mass

The two torus saddle values have a trigonometric interpolant. Its nonconstant
part is antisymmetric under coordinate exchange and integrates to zero against
F on a stream truncation. This avoids a measurable partition into corner sectors.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology Real
open scoped NNReal

private theorem corner_mass_two_saddles (u : L2) :
    ddCornerMass u = 2 * (‖continuousRep u (torusProj (π, 0))‖ ^ 2 +
      ‖continuousRep u (torusProj (0, π))‖ ^ 2) := by
  norm_num [ddCornerMass, Fin.sum_univ_succ, ddArcEnd, Function.iterate_succ_apply,
    rotLift, torusProj, Angle.coe_neg, Angle.neg_coe_pi]
  ring

private theorem potential_swap (p : ℝ × ℝ) : ddF p.swap = ddF p := by
  simp only [ddF, gradSq_dipoleLift, dipoleLift, Prod.fst_swap, Prod.snd_swap,
    add_comm]
  ring

private theorem truncated_swap (ε : ℝ) :
    Prod.swap ⁻¹' ddTruncatedCell ε = ddTruncatedCell ε := by
  ext p
  simp [ddTruncatedCell, cellSquare, diagCoord, dipoleLift, add_comm, abs_div,
    abs_sub_comm]

private theorem odd_potential_integral_zero (ε : ℝ) :
    (∫ p in ddTruncatedCell ε, ddF p * (cos p.1 - cos p.2)) = 0 := by
  have mp : MeasurePreserving Prod.swap
      (volume.restrict (ddTruncatedCell ε)) (volume.restrict (ddTruncatedCell ε)) := by
    simpa only [Measure.volume_eq_prod, truncated_swap] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := volume)).restrict_preimage_emb
        MeasurableEquiv.prodComm.measurableEmbedding (ddTruncatedCell ε)
  have h := mp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
    (fun p : ℝ × ℝ ↦ ddF p * (cos p.1 - cos p.2))
  have hn : (fun p : ℝ × ℝ ↦ ddF p.swap * (cos p.swap.1 - cos p.swap.2)) =
      fun p ↦ -(ddF p * (cos p.1 - cos p.2)) := by
    funext p
    rw [potential_swap]
    dsimp only [Prod.swap]
    ring
  change (∫ p in ddTruncatedCell ε, ddF p.swap * (cos p.swap.1 - cos p.swap.2)) = _ at h
  rw [hn, integral_neg] at h
  linarith

private theorem shifted_power_integrable (P : ℝ × ℝ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ‖p - P‖ ^ (-(3 / 2 : ℝ))) cellSquare := by
  have hd : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hi : LocallyIntegrable (fun p : ℝ × ℝ ↦ ‖p‖ ^ (-(3 / 2 : ℝ))) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := (3 / 2 : ℝ))
      (by simp [hd]) (by norm_num [hd])
    · exact Eventually.of_forall fun p ↦ by
        rw [Real.norm_of_nonneg (rpow_nonneg (norm_nonneg _) _), one_mul]
    · have hm : Measurable (fun p : ℝ × ℝ ↦ ‖p‖ ^ (-(3 / 2 : ℝ))) := by fun_prop
      exact hm.aestronglyMeasurable
  have hb : Bornology.IsBounded cellSquare := isBounded_cellNeighbourhood.subset
    fun _ hp ↦ closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  have hc := hb.isCompact_closure.image
    (by fun_prop : Continuous (fun p : ℝ × ℝ ↦ p - P))
  have hI := hi.integrableOn_isCompact hc
  have mp : MeasurePreserving (fun p : ℝ × ℝ ↦ p - P) volume volume :=
    measurePreserving_sub_right volume P
  exact ((mp.integrableOn_image (Homeomorph.subRight P).measurableEmbedding).mp hI).mono_set
    subset_closure

private def valueMass (u : L2) (p : ℝ × ℝ) : ℝ :=
  ‖continuousRep u (torusProj p)‖ ^ 2

private def massMean (u : L2) : ℝ := (valueMass u (π, 0) + valueMass u (0, π)) / 2

private def massSlope (u : L2) : ℝ := (valueMass u (0, π) - valueMass u (π, 0)) / 4

private def massInterpolant (u : L2) (p : ℝ × ℝ) : ℝ :=
  massMean u + massSlope u * (cos p.1 - cos p.2)

private def valueRemainder (u : L2) (p : ℝ × ℝ) : ℝ :=
  valueMass u p - massInterpolant u p

private theorem massMean_corner (u : L2) : massMean u = ddCornerMass u / 4 := by
  rw [corner_mass_two_saddles]
  dsimp [massMean, valueMass]
  ring

private theorem valueMass_holder {u : L2} (hu : MemSobolev 2 u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p q : ℝ × ℝ,
      |valueMass u p - valueMass u q| ≤ K * √(dist p q) := by
  obtain ⟨C, hC⟩ := exists_holderWith_of_memSobolev_two (α := (1 / 2 : ℝ≥0))
    (by norm_num)
  obtain ⟨v, hv, hH, -⟩ := hC u hu
  have : (volume : Measure Torus).IsOpenPosMeasure := by
    change (volume : Measure (AddCircle (2 * π) × AddCircle (2 * π))).IsOpenPosMeasure
    infer_instance
  have heq : (continuousRep u : Torus → ℂ) = v :=
    Measure.eq_of_ae_eq ((coeFn_eq_continuousRep hu).symm.trans hv)
      (continuousRep u).continuous (hH.continuous (by norm_num))
  rw [← heq] at hH
  set D : ℝ := ((C * Real.toNNReal √(sobolevNormSq 2 u) : ℝ≥0) : ℝ)
  set M := ‖continuousRep u‖
  have hD : 0 ≤ D := NNReal.coe_nonneg _
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨2 * M * D, by positivity, fun p q ↦ ?_⟩
  have hd : ‖continuousRep u (torusProj p) - continuousRep u (torusProj q)‖ ≤
      D * √(dist p q) := by
    simpa only [D, dist_eq_norm, sqrt_eq_rpow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat] using
      hH.dist_le_of_le (dist_torusProj_le p q)
  set a := ‖continuousRep u (torusProj p)‖
  set b := ‖continuousRep u (torusProj q)‖
  have ha : a ≤ M := (continuousRep u).norm_coe_le_norm _
  have hb : b ≤ M := (continuousRep u).norm_coe_le_norm _
  have hdiff : |a - b| ≤ D * √(dist p q) :=
    (abs_norm_sub_norm_le _ _).trans hd
  calc |valueMass u p - valueMass u q| = |a - b| * (a + b) := by
         change |a ^ 2 - b ^ 2| = _
         rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
           abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
       _ ≤ (D * √(dist p q)) * (2 * M) :=
         mul_le_mul hdiff (by linarith) (by positivity) (by positivity)
       _ = 2 * M * D * √(dist p q) := by ring

private def cellCorners : Finset (ℝ × ℝ) := {(π, 0), (0, π), (-π, 0), (0, -π)}

private theorem remainder_corner_zero (u : L2) {P : ℝ × ℝ} (hP : P ∈ cellCorners) :
    valueRemainder u P = 0 := by
  simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl <;>
    norm_num [valueRemainder, massInterpolant, massMean, massSlope, valueMass,
      torusProj, Angle.coe_neg, Angle.neg_coe_pi] <;> ring

private theorem remainder_holder {u : L2} (hu : MemSobolev 2 u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p q : ℝ × ℝ, dist p q ≤ π →
      |valueRemainder u p - valueRemainder u q| ≤ K * √(dist p q) := by
  obtain ⟨K, hK, hmass⟩ := valueMass_holder hu
  refine ⟨K + 2 * |massSlope u| * (1 + π), by positivity, fun p q hpq ↦ ?_⟩
  have hd0 : 0 ≤ dist p q := dist_nonneg
  have hs := sq_sqrt hd0
  have ht : √(dist p q) ≤ 1 + dist p q := by
    nlinarith [sqrt_nonneg (dist p q), sq_nonneg (√(dist p q) - 1)]
  have hd : dist p q ≤ (1 + π) * √(dist p q) := by
    nlinarith [sqrt_nonneg (dist p q), mul_nonneg (sub_nonneg.mpr hpq)
      (sqrt_nonneg (dist p q))]
  have hx : |cos p.1 - cos q.1| ≤ dist p q := (abs_cos_sub_cos_le _ _).trans
    (by simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _)
  have hy : |cos p.2 - cos q.2| ≤ dist p q := (abs_cos_sub_cos_le _ _).trans
    (by simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _)
  have hδ : |(cos p.1 - cos p.2) - (cos q.1 - cos q.2)| ≤ 2 * dist p q := by
    have h := abs_sub (cos p.1 - cos q.1) (cos p.2 - cos q.2)
    have hid : (cos p.1 - cos p.2) - (cos q.1 - cos q.2) =
        (cos p.1 - cos q.1) - (cos p.2 - cos q.2) := by ring
    rw [hid]
    linarith
  have hA : |massInterpolant u p - massInterpolant u q| ≤
      2 * |massSlope u| * (1 + π) * √(dist p q) := by
    have hid : massInterpolant u p - massInterpolant u q =
        massSlope u * ((cos p.1 - cos p.2) - (cos q.1 - cos q.2)) := by
      dsimp [massInterpolant]
      ring
    rw [hid, abs_mul]
    calc _ ≤ |massSlope u| * (2 * dist p q) :=
           mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
         _ ≤ |massSlope u| * (2 * ((1 + π) * √(dist p q))) := by gcongr
         _ = _ := by ring
  have hid : valueRemainder u p - valueRemainder u q =
      (valueMass u p - valueMass u q) - (massInterpolant u p - massInterpolant u q) := by
    dsimp [valueRemainder]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by nlinarith [hmass p q])

private theorem cos_snd_le_saddleDist (p : ℝ × ℝ) : cos (diagCoord p).2 ≤ saddleDist p := by
  have hne : saddleSet.Nonempty := ⟨(π, 0), 1, 0, by decide, by simp⟩
  apply (Metric.le_infDist hne).mpr
  rintro q ⟨m, n, ⟨k, hk⟩, rfl⟩
  have he : ((m : ℝ) * π - n * π) / 2 = ((k : ℝ) - n) * π + π / 2 := by
    have hk' : (m : ℝ) + n = 2 * k + 1 := by exact_mod_cast hk
    nlinarith [congrArg (fun x : ℝ ↦ x * π) hk']
  have hz : cos (diagCoord ((m : ℝ) * π, n * π)).2 = 0 := by
    simp only [diagCoord, he, cos_add, cos_pi_div_two, sin_pi_div_two, mul_zero,
      sub_mul, sin_sub, sin_int_mul_pi, zero_mul, sub_zero]
  have hc := abs_cos_sub_cos_le (diagCoord p).2 (diagCoord ((m : ℝ) * π, n * π)).2
  rw [hz, sub_zero] at hc
  apply (le_abs_self _).trans (hc.trans ?_)
  have hx : |p.1 - m * π| ≤ dist p ((m : ℝ) * π, n * π) := by
    simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hy : |p.2 - n * π| ≤ dist p ((m : ℝ) * π, n * π) := by
    simp only [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
  calc |(diagCoord p).2 - (diagCoord ((m : ℝ) * π, n * π)).2| =
      |(p.1 - m * π) - (p.2 - n * π)| / 2 := by
        rw [show (diagCoord p).2 - (diagCoord ((m : ℝ) * π, n * π)).2 =
          ((p.1 - m * π) - (p.2 - n * π)) / 2 by simp [diagCoord]; ring,
          abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
       _ ≤ (|p.1 - m * π| + |p.2 - n * π|) / 2 := by gcongr; exact abs_sub _ _
       _ ≤ dist p ((m : ℝ) * π, n * π) := by linarith

private theorem choose_cell_corner {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    ∃ P ∈ cellCorners, dist p P = π - |(diagCoord p).1| - |(diagCoord p).2| := by
  set a := (diagCoord p).1
  set b := (diagCoord p).2
  have hx : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
  have hy : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
  obtain ⟨haL, haU⟩ := abs_lt.mp hp.1
  obtain ⟨hbL, hbU⟩ := abs_lt.mp hp.2
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · refine ⟨(π, 0), by simp [cellCorners], ?_⟩
    change max |p.1 - π| |p.2 - 0| = π - |a| - |b|
    rw [hx, hy, sub_zero, abs_of_nonneg ha, abs_of_nonneg hb,
      abs_of_nonpos (by dsimp [a, b] at *; linarith : a + b - π ≤ 0)]
    convert max_eq_left (show |a - b| ≤ -(a + b - π) by
      rw [abs_le]; constructor <;> dsimp [a, b] at * <;> linarith) using 1
    ring
  · refine ⟨(0, π), by simp [cellCorners], ?_⟩
    change max |p.1 - 0| |p.2 - π| = π - |a| - |b|
    rw [hx, hy, sub_zero, abs_of_nonneg ha, abs_of_nonpos hb,
      abs_of_nonpos (by dsimp [a, b] at *; linarith : a - b - π ≤ 0)]
    convert max_eq_right (show |a + b| ≤ -(a - b - π) by
      rw [abs_le]; constructor <;> dsimp [a, b] at * <;> linarith) using 1
    ring
  · refine ⟨(0, -π), by simp [cellCorners], ?_⟩
    change max |p.1 - 0| |p.2 - -π| = π - |a| - |b|
    rw [hx, hy, sub_zero, abs_of_nonpos ha, abs_of_nonneg hb,
      abs_of_nonneg (by dsimp [a, b] at *; linarith : 0 ≤ a - b - -π)]
    convert max_eq_right (show |a + b| ≤ a - b - -π by
      rw [abs_le]; constructor <;> dsimp [a, b] at * <;> linarith) using 1
    ring
  · refine ⟨(-π, 0), by simp [cellCorners], ?_⟩
    change max |p.1 - -π| |p.2 - 0| = π - |a| - |b|
    rw [hx, hy, sub_zero, abs_of_nonpos ha, abs_of_nonpos hb,
      abs_of_nonneg (by dsimp [a, b] at *; linarith : 0 ≤ a + b - -π)]
    convert max_eq_left (show |a - b| ≤ a + b - -π by
      rw [abs_le]; constructor <;> dsimp [a, b] at * <;> linarith) using 1
    ring

private theorem corner_distance_bound {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    ∃ P ∈ cellCorners, 0 < dist p P ∧ dist p P ≤ π ∧ dist p P ≤ π * saddleDist p := by
  obtain ⟨P, hP, hd⟩ := choose_cell_corner hp
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · rw [hd]
    linarith [hp.1, hp.2]
  · rw [hd]
    linarith [abs_nonneg (diagCoord p).1, abs_nonneg (diagCoord p).2]
  · have hedge {t : ℝ} (ht : |t| < π / 2) : π / 2 - |t| ≤ π / 2 * cos t := by
      have h := one_sub_mul_le_cos (abs_nonneg t) ht.le
      rw [cos_abs] at h
      calc π / 2 - |t| = π / 2 * (1 - 2 / π * |t|) := by field_simp
           _ ≤ π / 2 * cos t := mul_le_mul_of_nonneg_left h pi_div_two_pos.le
    rw [hd]
    have hc := add_le_add (cos_diag_fst_le_saddleDist p) (cos_snd_le_saddleDist p)
    have hm := mul_le_mul_of_nonneg_left hc pi_div_two_pos.le
    linarith [hedge hp.1, hedge hp.2]

private theorem potential_remainder_integrable {u : L2} (hu : MemSobolev 2 u) :
    IntegrableOn (fun p ↦ ddF p * valueRemainder u p) cellSquare := by
  obtain ⟨K, hK, hR⟩ := remainder_holder hu
  have hi : IntegrableOn (fun p : ℝ × ℝ ↦
      ∑ P ∈ cellCorners, ‖p - P‖ ^ (-(3 / 2 : ℝ))) cellSquare :=
    integrable_finsetSum _ (fun P _ ↦ shifted_power_integrable P)
  have mF : Measurable ddF := by
    change Measurable (fun p ↦ ddF p)
    simp only [ddF, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have mR : Continuous (valueRemainder u) := by
    unfold valueRemainder valueMass massInterpolant
    have hc := (continuousRep u).continuous.comp isOpenQuotientMap_torusProj.continuous
    fun_prop
  apply (hi.const_mul (K * (16 * π ^ 4))).mono'
    (mF.aestronglyMeasurable.mul mR.aestronglyMeasurable)
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  filter_upwards [ae_restrict_mem hcell] with p hp
  obtain ⟨P, hP, ht0, htπ, htd⟩ := corner_distance_bound hp
  have hrem := hR p P htπ
  rw [remainder_corner_zero u hP, sub_zero, dist_eq_norm] at hrem
  rw [dist_eq_norm] at ht0 htπ htd
  set t := ‖p - P‖
  obtain ⟨hF0, hF⟩ := ddF_mul_saddleDist_sq_bound hp
  have ht2 : t ^ 2 ≤ π ^ 2 * saddleDist p ^ 2 := by
    convert pow_le_pow_left₀ ht0.le htd 2 using 1
    ring
  have hFt : ddF p * t ^ 2 ≤ 16 * π ^ 4 := by
    calc _ ≤ ddF p * (π ^ 2 * saddleDist p ^ 2) := mul_le_mul_of_nonneg_left ht2 hF0
         _ = π ^ 2 * (ddF p * saddleDist p ^ 2) := by ring
         _ ≤ π ^ 2 * (16 * π ^ 2) := mul_le_mul_of_nonneg_left hF (sq_nonneg _)
         _ = 16 * π ^ 4 := by ring
  have hid : t ^ 2 * t ^ (-(3 / 2 : ℝ)) = √t := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
    norm_num [sqrt_eq_rpow]
  have hsum : t ^ (-(3 / 2 : ℝ)) ≤
      ∑ Q ∈ cellCorners, ‖p - Q‖ ^ (-(3 / 2 : ℝ)) :=
    Finset.single_le_sum (fun Q _ ↦ rpow_nonneg (norm_nonneg _) _) hP
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hF0]
  calc _ ≤ ddF p * (K * √t) := mul_le_mul_of_nonneg_left hrem hF0
       _ = K * (ddF p * t ^ 2) * t ^ (-(3 / 2 : ℝ)) := by rw [← hid]; ring
       _ ≤ K * (16 * π ^ 4) * t ^ (-(3 / 2 : ℝ)) := by gcongr
       _ ≤ K * (16 * π ^ 4) *
           ∑ Q ∈ cellCorners, ‖p - Q‖ ^ (-(3 / 2 : ℝ)) := by gcongr

private theorem coefficient_integrable_truncation {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn ddF (ddTruncatedCell ε) := by
  have hb : Bornology.IsBounded (ddTruncatedCell ε) :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  have : IsFiniteMeasure (volume.restrict (ddTruncatedCell ε)) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have h := ddVirialDensity_integrable hε (u := 0) (e := fun _ ↦ (1 : ℂ))
    (ux := 0) (uy := 0) MemLp.zero (memLp_const _) MemLp.zero MemLp.zero
  apply h.congr_fun _ (isOpen_ddTruncatedCell ε).measurableSet
  intro p _
  simp [ddVirialDensity, ddMatrixForm, normalDeriv, tangentDeriv]

private theorem odd_coefficient_integrable_truncation {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun p ↦ ddF p * (cos p.1 - cos p.2)) (ddTruncatedCell ε) := by
  apply (coefficient_integrable_truncation hε).mul_bdd
    (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ cos p.1 - cos p.2)).aestronglyMeasurable
  exact Eventually.of_forall fun p ↦ by
    simpa only [Real.norm_eq_abs, show (1 + 1 : ℝ) = 2 by norm_num] using
      (abs_sub (cos p.1) (cos p.2)).trans (add_le_add (abs_cos_le_one _) (abs_cos_le_one _))

private theorem potential_mass_decomposition {u : L2} (hu : MemSobolev 2 u)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ p in ddTruncatedCell ε, ddF p * ‖liftL2 u p‖ ^ 2) =
      (∫ p in ddTruncatedCell ε, ddF p * valueRemainder u p) +
        massMean u * ∫ p in ddTruncatedCell ε, ddF p := by
  have hR := (potential_remainder_integrable hu).mono_set
    (show ddTruncatedCell ε ⊆ cellSquare from fun _ hp ↦ hp.1)
  have hF := (coefficient_integrable_truncation hε).const_mul (massMean u)
  have hδ := (odd_coefficient_integrable_truncation hε).const_mul (massSlope u)
  have hid : (fun p ↦ ddF p * valueMass u p) =
      ((fun p ↦ ddF p * valueRemainder u p) + (fun p ↦ massMean u * ddF p)) +
        (fun p ↦ massSlope u * (ddF p * (cos p.1 - cos p.2))) := by
    funext p
    dsimp [valueRemainder, massInterpolant]
    ring
  calc _ = ∫ p in ddTruncatedCell ε, ddF p * valueMass u p := by
         apply integral_congr_ae
         filter_upwards [ae_restrict_of_ae (liftL2_ae_eq (coeFn_eq_continuousRep hu))]
           with p hp
         rw [hp]
         rfl
       _ = _ := by
         rw [hid]
         change (∫ p in ddTruncatedCell ε,
           (ddF p * valueRemainder u p + massMean u * ddF p) +
             massSlope u * (ddF p * (cos p.1 - cos p.2))) = _
         have hsum := integral_add (hR.add hF) hδ
         have hsum' := integral_add hR hF
         simp only [Pi.add_apply] at hsum hsum'
         rw [hsum, hsum']
         simp only [integral_const_mul, odd_potential_integral_zero, mul_zero, add_zero]

/-- Subtracting the corner logarithm from the weighted value mass leaves a finite
limit. This value-only statement does not require even reflection parity. -/
theorem dd_potential_mass_finite_part {u : L2} (hu : MemSobolev 2 u) :
    ∃ V : ℝ, Tendsto (fun ε ↦
      (∫ p in ddTruncatedCell ε, ddF p * ‖liftL2 u p‖ ^ 2) -
        ddLogCounterterm u ε) (𝓝[>] 0) (𝓝 V) := by
  have hlim := (tendsto_ddTruncatedCell_integral (potential_remainder_integrable hu)).add
    (dd_finite_part.2.const_mul (massMean u))
  refine ⟨_, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [potential_mass_decomposition hu hε]
  dsimp only [ddLogCounterterm]
  rw [massMean_corner]
  ring

end NoEmbeddedEigenvalues
