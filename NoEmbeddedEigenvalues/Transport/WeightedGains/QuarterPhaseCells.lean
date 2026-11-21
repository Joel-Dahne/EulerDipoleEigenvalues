import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorGeometry

/-!
# Complete quarter-phase cells accumulating at zero

Blueprint: `lem:complete-phase-cells`.

The positive phase handles both signs of the spectral parameter. Its endpoint
lattice gives adjacent complete cells with a central resonance. No exact
geometric progression of physical levels is asserted.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Filter
open scoped Topology

private theorem exp_I_flip {x y : ℝ} (h : |x - y| = Real.pi) :
    Complex.exp (Complex.I * (x : ℂ)) = -Complex.exp (Complex.I * (y : ℂ)) := by
  rcases (abs_eq Real.pi_pos.le).1 h with h | h
  · have hx : x = y + Real.pi := by linarith
    rw [hx, Complex.ofReal_add, mul_add, mul_comm Complex.I (Real.pi : ℂ),
      Complex.exp_add_pi_mul_I]
  · have hx : x = y - Real.pi := by linarith
    rw [hx, Complex.ofReal_sub, mul_sub, mul_comm Complex.I (Real.pi : ℂ),
      Complex.exp_sub_pi_mul_I]

/-- Arbitrarily small collars partition into complete cells, with genuine
nonresonant endpoints and a specified central resonance in each cell. -/
theorem exists_complete_phase_cells {lam : ℝ} (hlam : lam ≠ 0)
    {κ : ℂ} (hκ : κ ^ 4 = 1) {η : ℝ} (hη : 0 < η) :
    ∃ e z : ℕ → ℝ, StrictAnti e ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ n, 0 < e n ∧ e n < η ∧ IsPhaseCellEndpoint lam κ (e n) ∧
        quarterDivisor lam κ (e n) ≠ 0) ∧
      (∀ n, e (n + 1) < z n ∧ z n < e n ∧ quarterDivisor lam κ (z n) = 0 ∧
        |quarterPhase lam (e (n + 1)) - quarterPhase lam (z n)| = Real.pi ∧
        |quarterPhase lam (e n) - quarterPhase lam (z n)| = Real.pi) := by
  let δ := min η 1
  have hδ : 0 < δ := lt_min hη one_pos
  let P := quarterPhase |lam|
  have hA : 0 < 2 * |lam| := mul_pos (by norm_num) (abs_pos.2 hlam)
  have hd (h : ℝ) (hh : h ∈ Ioo 0 δ) :
      HasDerivAt P (2 * |lam| * deriv eighthPeriod h) h :=
    (deriv_eighthPeriod_neg hh.1 (hh.2.trans_le (min_le_right _ _))).1.hasDerivAt.const_mul _
  have hc : ContinuousOn P (Ioo 0 δ) := fun h hh ↦ (hd h hh).continuousAt.continuousWithinAt
  have ha : StrictAntiOn P (Ioo 0 δ) := by
    intro x hx y hy hxy
    exact mul_lt_mul_of_pos_left (eighthPeriod_strictAntiOn
      ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
      ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩ hxy) hA
  have htop : Tendsto P (𝓝[>] 0) atTop := tendsto_eighthPeriod_atTop.const_mul_atTop hA
  have hnegκ : (-κ) ^ 4 = 1 := by
    calc (-κ) ^ 4 = κ ^ 4 := by ring
         _ = 1 := hκ
  obtain ⟨θ, hθ⟩ := positive_phase_lattice hlam hnegκ
  obtain ⟨ρ, hρ, e, he, _⟩ := phase_lattice_enumeration hδ hc ha htop θ
    (by positivity : 0 < 2 * Real.pi)
  have hem (n : ℕ) : e n ∈ Ioo 0 δ := ⟨(he n).1.1, (he n).1.2.trans hρ.2⟩
  have hdec : StrictAnti e := by
    apply strictAnti_nat_of_succ_lt
    intro n
    by_contra hn
    have := ha.antitoneOn (hem n) (hem (n + 1)) (le_of_not_gt hn)
    linarith [(he n).2.2, Real.pi_pos]
  have hep (n : ℕ) : IsPhaseCellEndpoint lam κ (e n) :=
    (sub_eq_zero.1 ((hθ _).2 (he n).2.1)).symm
  have hκne : κ ≠ 0 := by intro h; simp [h] at hκ
  have hene (n : ℕ) : quarterDivisor lam κ (e n) ≠ 0 := by
    rw [quarterDivisor, hep n, sub_neg_eq_add, ← two_mul]
    exact mul_ne_zero (by norm_num) hκne
  have hm (n : ℕ) : ∃ x ∈ Ioo (e (n + 1)) (e n), P x = P (e n) + Real.pi := by
    apply intermediate_value_Ioo' (hdec (Nat.lt_succ_self n)).le
      (hc.mono (Icc_subset_Ioo (hem (n + 1)).1 (hem n).2))
    constructor <;> linarith [(he n).2.2, Real.pi_pos]
  choose z hz hzeq using hm
  have habs (x y : ℝ) : |quarterPhase lam x - quarterPhase lam y| = |P x - P y| := by
    dsimp only [P, quarterPhase]
    rw [← mul_sub, ← mul_sub]
    simp only [abs_mul, abs_abs]
  have heq (n : ℕ) : P (e n) = P (e 0) + n * (2 * Real.pi) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_add, Nat.cast_one]; linarith [(he n).2.2]
  have htend : Tendsto e atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    let t := min ε (δ / 2)
    have ht : t ∈ Ioo 0 δ := ⟨lt_min hε (half_pos hδ),
      (min_le_right _ _).trans_lt (half_lt_self hδ)⟩
    obtain ⟨m, hm⟩ := exists_nat_gt ((P t - P (e 0)) / (2 * Real.pi))
    refine ⟨m, fun n hn ↦ ?_⟩
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn
    have hPe : P t < P (e n) := by
      rw [heq]
      have := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).1 hm
      nlinarith [mul_le_mul_of_nonneg_right hmn (by positivity : 0 ≤ 2 * Real.pi)]
    have het : e n < t := by
      by_contra h
      exact (not_le_of_gt hPe) (ha.antitoneOn ht (hem n) (le_of_not_gt h))
    rw [Real.dist_eq, sub_zero, abs_of_pos (hem n).1]
    exact het.trans_le (min_le_left _ _)
  refine ⟨e, z, hdec, htend, ?_, ?_⟩
  · intro n
    exact ⟨(hem n).1, (hem n).2.trans_le (min_le_left _ _), hep n, hene n⟩
  · intro n
    have hl : |quarterPhase lam (e (n + 1)) - quarterPhase lam (z n)| = Real.pi := by
      rw [habs, hzeq, abs_of_nonneg (by linarith [(he n).2.2, Real.pi_pos])]
      linarith [(he n).2.2]
    have hu : |quarterPhase lam (e n) - quarterPhase lam (z n)| = Real.pi := by
      rw [habs, hzeq, show P (e n) - (P (e n) + Real.pi) = -Real.pi by ring,
        abs_neg, abs_of_pos Real.pi_pos]
    refine ⟨(hz n).1, (hz n).2, ?_, hl, hu⟩
    have hx := exp_I_flip (x := quarterPhase lam (z n))
      (y := quarterPhase lam (e n)) (by simpa only [abs_sub_comm] using hu)
    rw [hep n, neg_neg] at hx
    exact sub_eq_zero.2 hx.symm

end NoEmbeddedEigenvalues
