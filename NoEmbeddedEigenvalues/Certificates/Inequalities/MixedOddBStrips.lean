module

public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBStripCheck
public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBStripPower
public import Mathlib.Tactic.IntervalCases

/-!
# The twenty mixed odd-in-b endpoint signs
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Set

private theorem endpoint_nonneg {n m : ℕ} (p : BernsteinIntTable n m)
    (t : BernsteinMidTree) (hc : t.check (bernsteinIntFromPower p) = true)
    {D z k v : ℝ} (hD : 0 < D) (he : bernsteinIntPowerEval p z k = D * v)
    (hz : z ∈ Icc (0 : ℝ) 1) (hk : k ∈ Icc (0 : ℝ) 1) : 0 ≤ v := by
  have h := t.power_nonneg p hc hz hk
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h hD

/-- The twenty polynomial signs on the rescaled unit squares. -/
theorem mixed_odd_b_strip_signs (j : ℕ) (hj : j < 10) (z k : ℝ)
    (hz : z ∈ Icc 0 1) (hk : k ∈ Icc 0 1) :
    0 ≤ mixedOddBStripLower j z k ∧ 0 ≤ mixedOddBStripUpper j z k := by
  interval_cases j
  · exact ⟨endpoint_nonneg _ _ oddBLower0_check (by norm_num [oddBLower0Scale])
      (oddBLower0_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper0_check (by norm_num [oddBUpper0Scale])
        (oddBUpper0_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower1_check (by norm_num [oddBLower1Scale])
      (oddBLower1_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper1_check (by norm_num [oddBUpper1Scale])
        (oddBUpper1_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower2_check (by norm_num [oddBLower2Scale])
      (oddBLower2_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper2_check (by norm_num [oddBUpper2Scale])
        (oddBUpper2_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower3_check (by norm_num [oddBLower3Scale])
      (oddBLower3_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper3_check (by norm_num [oddBUpper3Scale])
        (oddBUpper3_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower4_check (by norm_num [oddBLower4Scale])
      (oddBLower4_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper4_check (by norm_num [oddBUpper4Scale])
        (oddBUpper4_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower5_check (by norm_num [oddBLower5Scale])
      (oddBLower5_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper5_check (by norm_num [oddBUpper5Scale])
        (oddBUpper5_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower6_check (by norm_num [oddBLower6Scale])
      (oddBLower6_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper6_check (by norm_num [oddBUpper6Scale])
        (oddBUpper6_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower7_check (by norm_num [oddBLower7Scale])
      (oddBLower7_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper7_check (by norm_num [oddBUpper7Scale])
        (oddBUpper7_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower8_check (by norm_num [oddBLower8Scale])
      (oddBLower8_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper8_check (by norm_num [oddBUpper8Scale])
        (oddBUpper8_power z k) hz hk⟩
  · exact ⟨endpoint_nonneg _ _ oddBLower9_check (by norm_num [oddBLower9Scale])
      (oddBLower9_power z k) hz hk,
      endpoint_nonneg _ _ oddBUpper9_check (by norm_num [oddBUpper9Scale])
        (oddBUpper9_power z k) hz hk⟩

end NoEmbeddedEigenvalues
