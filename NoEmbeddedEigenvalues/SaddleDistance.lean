import NoEmbeddedEigenvalues.SaddleTaylorJet
import NoEmbeddedEigenvalues.LocalL2Multipliers
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Distance to the discrete saddle lattice

Blueprint: `lem:saddle-distance-comparison`, `lem:saddle-distance-weight-transfer`.

Distinct lifted saddles are separated by at least π in the product metric.
On the π/2 ball about one saddle, saddle distance is exactly distance to that
saddle. Euclidean radius differs by a bounded factor, not by equality.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Uniform separation of the lifted saddle lattice. -/
theorem pi_le_dist_saddles {c d : ℝ × ℝ} (hc : c ∈ saddleSet) (hd : d ∈ saddleSet)
    (hne : c ≠ d) : Real.pi ≤ dist c d := by
  obtain ⟨m, n, _, rfl⟩ := hc
  obtain ⟨k, l, _, rfl⟩ := hd
  have hi {a b : ℤ} (h : a ≠ b) : Real.pi ≤ |(a : ℝ) * Real.pi - b * Real.pi| := by
    have hz : (1 : ℝ) ≤ |(a : ℝ) - b| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    rw [← sub_mul, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  by_cases hm : m = k
  · have hn : n ≠ l := by intro h; apply hne; simp [hm, h]
    exact (hi hn).trans (le_max_right _ _)
  · exact (hi hm).trans (le_max_left _ _)

/-- The saddle set has no finite accumulation point. -/
theorem isClosed_saddleSet : IsClosed saddleSet :=
  Metric.isClosed_of_pairwise_le_dist Real.pi_pos fun _ hc _ hd hne ↦
    pi_le_dist_saddles hc hd hne

/-- Vanishing distance identifies an actual lifted saddle, not just a closure point. -/
theorem saddleDist_eq_zero_iff {p : ℝ × ℝ} : saddleDist p = 0 ↔ p ∈ saddleSet :=
  (isClosed_saddleSet.mem_iff_infDist_zero
    ⟨(0, Real.pi), 0, 1, by decide, by simp⟩).symm

/-- On a small ball the chosen saddle realizes the distance infimum. -/
theorem saddleDist_eq_dist {c p : ℝ × ℝ} (hc : c ∈ saddleSet)
    (hp : dist p c < Real.pi / 2) : saddleDist p = dist p c := by
  apply le_antisymm (Metric.infDist_le_dist_of_mem hc)
  apply (Metric.le_infDist ⟨c, hc⟩).mpr
  intro q hq
  by_cases he : q = c
  · simp [he]
  · have hs := pi_le_dist_saddles hc hq (Ne.symm he)
    have ht := dist_triangle c p q
    rw [dist_comm c p] at ht
    linarith

/-- A uniform comparison between the Euclidean and product-metric radii. -/
theorem localRadius_le_two_dist (c p : ℝ × ℝ) : localRadius c p ≤ 2 * dist p c := by
  have hr : 0 ≤ localRadius c p := Real.sqrt_nonneg _
  have hs : localRadius c p ^ 2 = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hx : |p.1 - c.1| ≤ dist p c := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |p.2 - c.2| ≤ dist p c := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hx2 := sq_le_sq₀ (abs_nonneg _) dist_nonneg |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg _) dist_nonneg |>.mpr hy
  rw [sq_abs] at hx2 hy2
  nlinarith [dist_nonneg (x := p) (y := c)]

/-- The fixed-saddle Euclidean radius is controlled by saddle distance near c. -/
theorem localRadius_le_two_saddleDist {c p : ℝ × ℝ} (hc : c ∈ saddleSet)
    (hp : dist p c < Real.pi / 2) : localRadius c p ≤ 2 * saddleDist p := by
  rw [saddleDist_eq_dist hc hp]
  exact localRadius_le_two_dist c p

/-- Transfer a fixed-saddle radial local L² norm to the lattice distance on a
small neighbourhood. Only a bounded measurable multiplier is used. -/
theorem MemSobolevLocOn.div_saddleDist_of_radius {c : ℝ × ℝ} (hc : c ∈ saddleSet)
    {U : Set (ℝ × ℝ)} (hU : U ⊆ Metric.ball c (Real.pi / 2)) {s : ℝ} (hs : 0 ≤ s)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 0 U
      (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ))) :
    MemSobolevLocOn 0 U (fun p ↦ F p / (Real.rpow (saddleDist p) s : ℂ)) := by
  have hr : Measurable (localRadius c) := by unfold localRadius; fun_prop
  have hd : Measurable saddleDist := (Metric.continuous_infDist_pt saddleSet).measurable
  let G := fun p ↦ (Real.rpow (localRadius c p / saddleDist p) s : ℂ)
  have hG : Measurable G := by
    apply Complex.continuous_ofReal.measurable.comp
    simpa only [Real.rpow_eq_pow, Pi.div_apply] using (hr.div hd).pow_const s
  have hbound : ∀ p ∈ U, ‖G p‖ ≤ Real.rpow 2 s := by
    intro p hp
    have hratio : localRadius c p / saddleDist p ≤ 2 :=
      div_le_of_le_mul₀ Metric.infDist_nonneg (by norm_num)
        (localRadius_le_two_saddleDist hc (hU hp))
    have hpos : 0 ≤ localRadius c p / saddleDist p :=
      div_nonneg (Real.sqrt_nonneg _) Metric.infDist_nonneg
    dsimp only [G]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ Real.rpow (localRadius c p / saddleDist p) s from
        Real.rpow_nonneg hpos s)]
    exact Real.rpow_le_rpow hpos hratio hs
  apply (hF.zero_mul_bounded hG hbound).congr_ae_on
  filter_upwards [ae_saddleDist_ne_zero] with p hp _
  have hdpos : 0 < saddleDist p := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hp)
  have hrpos : 0 < localRadius c p := hdpos.trans_le (saddleDist_le_localRadius hc p)
  have he : Real.rpow (localRadius c p / saddleDist p) s =
      Real.rpow (localRadius c p) s / Real.rpow (saddleDist p) s := by
    simp only [Real.rpow_eq_pow]
    exact Real.div_rpow hrpos.le hdpos.le s
  have hn : (Real.rpow (localRadius c p) s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hrpos s).ne'
  dsimp only [G]
  rw [he]
  push_cast
  field_simp

end NoEmbeddedEigenvalues
