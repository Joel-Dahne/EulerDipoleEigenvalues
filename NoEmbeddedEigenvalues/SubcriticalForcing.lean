import NoEmbeddedEigenvalues.OrbitCoordinates

/-!
# Pointwise forcing growth on the cell and its quarter orbits

Blueprint: `lem:cell-forcing-growth`, `lem:subcritical-forcing-orbit-bounds`.

A continuous forcing's corner growth bound extends to the entire cell by
compactness. The exponential saddle-distance bound gives time decay; the
endpoint distance bound gives the precise level power. The original raw
continuous representative is retained throughout.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- A corner growth bound for the original continuous representative extends
to the whole cell; no extra pointwise bound away from the corners is assumed. -/
theorem exists_cell_forcing_rpow_bound {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ} {s : ℝ}
    (hb : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hs : 0 < s)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) s) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ cellSquare, ‖g p‖ ≤ K * Real.rpow (saddleDist p) s := by
  simp only [Real.rpow_eq_pow] at hbound ⊢
  obtain ⟨C, ε, hC, hε, hnear⟩ := hbound
  have hc : IsCompact (closure cellSquare) :=
    (hb.subset (subset_closure.trans hcell)).isCompact_closure
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (hg.mono hcell)
  let K := max C (|M| / ε ^ s) + 1
  have hK : 0 < K := by dsimp [K]; linarith [le_max_left C (|M| / ε ^ s)]
  have hCK : C ≤ K := by dsimp [K]; linarith [le_max_left C (|M| / ε ^ s)]
  have hMK : |M| / ε ^ s ≤ K := by
    dsimp [K]; linarith [le_max_right C (|M| / ε ^ s)]
  refine ⟨K, hK, fun p hp ↦ ?_⟩
  have hd : 0 ≤ saddleDist p := Metric.infDist_nonneg
  by_cases he : saddleDist p < ε
  · exact (hnear p hp he).trans (mul_le_mul_of_nonneg_right hCK (rpow_nonneg hd _))
  · have hpow : ε ^ s ≤ saddleDist p ^ s := rpow_le_rpow hε.le (le_of_not_gt he) hs.le
    calc ‖g p‖ ≤ M := hM p (subset_closure hp)
         _ ≤ |M| := le_abs_self _
         _ = (|M| / ε ^ s) * ε ^ s := by rw [div_mul_cancel₀ _ (rpow_pos_of_pos hε s).ne']
         _ ≤ (|M| / ε ^ s) * saddleDist p ^ s :=
          mul_le_mul_of_nonneg_left hpow (div_nonneg (abs_nonneg _) (rpow_nonneg hε.le _))
         _ ≤ K * saddleDist p ^ s := mul_le_mul_of_nonneg_right hMK (rpow_nonneg hd _)

/-- A global cell growth bound gives a common exponential time-decay constant
and endpoint level-power bound, independently of any oscillation frequency. -/
theorem forcing_rpow_orbit_bounds {g : ℝ × ℝ → ℂ} {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K)
    (hbound : ∀ p ∈ cellSquare, ‖g p‖ ≤ K * Real.rpow (saddleDist p) s) :
    ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧ h₀ < 1 / 2 ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| ≤ eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ M * exp (-s * |t|)) ∧
      (∀ h ∈ Ioo 0 h₀, ∀ t, |t| = eighthPeriod h →
        ‖g (dipoleOrbit h t)‖ ≤ M * Real.rpow h (s / 2)) := by
  simp only [Real.rpow_eq_pow] at hbound ⊢
  obtain ⟨c, B, r, _, hr, hdist⟩ := saddleDist_dipoleOrbit
  let h₀ := min r (1 / 2) / 2
  have hm : 0 < min r (1 / 2) := lt_min hr (by norm_num)
  have hh₀ : 0 < h₀ := half_pos hm
  have hh₀r : h₀ < r := (half_lt_self hm).trans_le (min_le_left _ _)
  have hh₀h : h₀ < 1 / 2 := (half_lt_self hm).trans_le (min_le_right _ _)
  let M := K * (|B| ^ s + π ^ s) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMB : K * |B| ^ s ≤ M := by
    dsimp [M]; nlinarith [mul_nonneg hK.le (rpow_nonneg pi_pos.le s)]
  have hMπ : K * π ^ s ≤ M := by
    dsimp [M]; nlinarith [mul_nonneg hK.le (rpow_nonneg (abs_nonneg B) s)]
  have hpoint (h : ℝ) (hh : h ∈ Ioo 0 h₀) (t : ℝ) : dipoleOrbit h t ∈ cellSquare := by
    have hh1 : h < 1 := by linarith [hh.2.trans hh₀h]
    have hp : dipoleOrbit h t ∈ puncturedCell := by
      simpa only [actionAngleInv, div_mul_cancel₀ t (orbitPeriod_pos hh.1 hh1).ne'] using
        actionAngleInv_mem_puncturedCell hh.1 hh1 (t / orbitPeriod h)
    exact hp.1
  refine ⟨M, h₀, hM, hh₀, hh₀h, ?_, ?_⟩
  · intro h hh t ht
    have hd : saddleDist (dipoleOrbit h t) ≤ |B| * exp (-|t|) :=
      (hdist h ⟨hh.1, hh.2.trans hh₀r⟩ t ht).2.trans
        (mul_le_mul_of_nonneg_right (le_abs_self B) (exp_pos _).le)
    calc ‖g (dipoleOrbit h t)‖ ≤ K * saddleDist (dipoleOrbit h t) ^ s :=
          hbound _ (hpoint h hh t)
         _ ≤ K * (|B| * exp (-|t|)) ^ s :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow Metric.infDist_nonneg hd hs.le) hK.le
         _ = K * |B| ^ s * exp (-s * |t|) := by
          rw [mul_rpow (abs_nonneg B) (exp_pos _).le, ← exp_mul,
            show -|t| * s = -s * |t| by ring]
          ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hMB (exp_pos _).le
  · intro h hh t ht
    have hh1 : h < 1 := by linarith [hh.2.trans hh₀h]
    calc ‖g (dipoleOrbit h t)‖ ≤ K * saddleDist (dipoleOrbit h t) ^ s :=
          hbound _ (hpoint h hh t)
         _ ≤ K * (π * √h) ^ s :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow Metric.infDist_nonneg
            (saddleDist_dipoleOrbit_endpoints hh.1 hh1 ht).2 hs.le) hK.le
         _ = K * π ^ s * h ^ (s / 2) := by
          rw [mul_rpow pi_pos.le (sqrt_nonneg _), sqrt_eq_rpow, ← rpow_mul hh.1.le,
            show (1 / 2 : ℝ) * s = s / 2 by ring]
          ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hMπ (rpow_nonneg hh.1.le _)

end NoEmbeddedEigenvalues
