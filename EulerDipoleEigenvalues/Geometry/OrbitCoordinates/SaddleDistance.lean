module

public import EulerDipoleEigenvalues.Geometry.OrbitCoordinates.SaddleTaylorJet
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalL2Multipliers
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SobolevMultipliers
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Distance to the discrete saddle lattice -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
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

/-- The fixed-saddle Euclidean radius is controlled by saddle distance near c. -/
theorem localRadius_le_two_saddleDist {c p : ℝ × ℝ} (hc : c ∈ saddleSet)
    (hp : dist p c < Real.pi / 2) : localRadius c p ≤ 2 * saddleDist p := by
  rw [saddleDist_eq_dist hc hp]
  exact localRadius_le_two_dist c p

end EulerDipoleEigenvalues
