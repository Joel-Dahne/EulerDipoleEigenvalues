module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SaddleDistanceWeights

/-!
# Compact pointwise growth bounds at the saddle lattice

Pointwise radial bounds for a continuous function at every saddle give one
lattice-distance growth bound on each compact localization. A finite open
cover, not a uniform radius over the infinite lattice, supplies the constant.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open Set MeasureTheory
open scoped Topology

/-- Local pointwise saddle growth has a common constant on a compact set. -/
theorem saddle_growth_bound_on_compact {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {s : ℝ} (hs : 0 ≤ s)
    (hlocal : ∀ c ∈ saddleSet, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ p ∈ localDisk c r, ‖F p‖ ≤ C * Real.rpow (localRadius c p) s)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ‖F p‖ ≤ C * Real.rpow (saddleDist p) s := by
  classical
  simp only [Real.rpow_eq_pow] at hlocal ⊢
  have hloc : ∀ c : ℝ × ℝ, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ p ∈ Metric.ball c r, ‖F p‖ ≤ C * saddleDist p ^ s := by
    intro c
    by_cases hc : c ∈ saddleSet
    · obtain ⟨ρ, C, hρ, hC, hb⟩ := hlocal c hc
      let r := min (ρ / 4) (Real.pi / 4)
      have hr : 0 < r := lt_min (by positivity) (by positivity)
      refine ⟨r, C * (2 : ℝ) ^ s, hr, by positivity, fun p hp ↦ ?_⟩
      have hpρ : localRadius c p < ρ := by
        have hh := localRadius_le_two_dist c p
        have hp' : dist p c < r := hp
        have hh' := min_le_left (ρ / 4) (Real.pi / 4)
        change r ≤ ρ / 4 at hh'
        linarith
      have hnear : dist p c < Real.pi / 2 :=
        (show dist p c < r from hp).trans_le
          ((min_le_right _ _).trans (by linarith [Real.pi_pos]))
      have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (localRadius_le_two_saddleDist hc hnear) hs
      calc
        ‖F p‖ ≤ C * localRadius c p ^ s := hb p hpρ
        _ ≤ C * (2 * saddleDist p) ^ s := mul_le_mul_of_nonneg_left hpow hC.le
        _ = (C * (2 : ℝ) ^ s) * saddleDist p ^ s := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
            (show 0 ≤ saddleDist p from Metric.infDist_nonneg)]
          ring
    · have hd : 0 < saddleDist c := lt_of_le_of_ne Metric.infDist_nonneg
        (Ne.symm (mt saddleDist_eq_zero_iff.mp hc))
      have hdcont : Continuous saddleDist := Metric.continuous_infDist_pt saddleSet
      have he : ∀ᶠ p in 𝓝 c, ‖F p‖ < ‖F c‖ + 1 ∧ saddleDist c / 2 < saddleDist p :=
        (hF.norm.continuousAt.eventually (gt_mem_nhds (by linarith))).and
          (hdcont.continuousAt.eventually (lt_mem_nhds (half_lt_self hd)))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
      let C := (‖F c‖ + 1) / (saddleDist c / 2) ^ s
      have hden : 0 < (saddleDist c / 2) ^ s := Real.rpow_pos_of_pos (by linarith) s
      have hC : 0 < C := div_pos (by positivity) hden
      refine ⟨r, C, hr, hC, fun p hp ↦ ?_⟩
      have hh := hball (show dist p c < r from hp)
      have hpw := Real.rpow_le_rpow (by linarith : 0 ≤ saddleDist c / 2) hh.2.le hs
      calc
        ‖F p‖ ≤ ‖F c‖ + 1 := hh.1.le
        _ = C * (saddleDist c / 2) ^ s := (div_mul_cancel₀ _ hden.ne').symm
        _ ≤ C * saddleDist p ^ s := mul_le_mul_of_nonneg_left hpw hC.le
  choose r C hr hC hb using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c ↦ Metric.ball c (r c))
    (fun _ ↦ Metric.isOpen_ball) (fun p _ ↦ mem_iUnion.mpr ⟨p, Metric.mem_ball_self (hr p)⟩)
  have hsum : 0 ≤ ∑ c ∈ t, C c := Finset.sum_nonneg fun c _ ↦ (hC c).le
  refine ⟨1 + ∑ c ∈ t, C c, by linarith, fun p hp ↦ ?_⟩
  obtain ⟨c, hct, hpc⟩ := mem_iUnion₂.mp (ht hp)
  have hle : C c ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun x _ ↦ (hC x).le) hct
  exact (hb c p hpc).trans (mul_le_mul_of_nonneg_right
    (hle.trans (by linarith)) (Real.rpow_nonneg Metric.infDist_nonneg s))

end EulerDipoleEigenvalues
