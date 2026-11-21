import NoEmbeddedEigenvalues.Certificates.Tools.BernsteinSeparable
import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddAAlgebra

/-!
# Mixed odd-in-a Bernstein certificate

Each checked power table represents the cleared residual on one of the two
triangles of the cosine square. Kernel reduction checks the intermediate
table after the first-axis transform, and then the signs after the second.
Each first-axis table is reused across boxes with the same first interval.
-/

namespace NoEmbeddedEigenvalues

open Set

private def axis1Left (i : Fin 18) (j : Fin 33) : ℚ :=
  (mixedOddAAxis1LeftInt i j : ℚ) / mixedOddAAxis1LeftScale

private theorem axis1Left_eq :
    ∀ i j, certificateAxisBox 0 (1 / 2) (fun k ↦ mixedOddAPower1 k j) i =
      axis1Left i j := by
  decide +kernel

private def axis1Right (i : Fin 18) (j : Fin 33) : ℚ :=
  (mixedOddAAxis1RightInt i j : ℚ) / mixedOddAAxis1RightScale

private theorem axis1Right_eq :
    ∀ i j, certificateAxisBox (1 / 2) 1 (fun k ↦ mixedOddAPower1 k j) i =
      axis1Right i j := by
  decide +kernel

private def axis2Left (i : Fin 18) (j : Fin 31) : ℚ :=
  (mixedOddAAxis2LeftInt i j : ℚ) / mixedOddAAxis2LeftScale

private theorem axis2Left_eq :
    ∀ i j, certificateAxisBox 0 (1 / 2) (fun k ↦ mixedOddAPower2 k j) i =
      axis2Left i j := by
  decide +kernel

private def axis2Right (i : Fin 18) (j : Fin 31) : ℚ :=
  (mixedOddAAxis2RightInt i j : ℚ) / mixedOddAAxis2RightScale

private theorem axis2Right_eq :
    ∀ i j, certificateAxisBox (1 / 2) 1 (fun k ↦ mixedOddAPower2 k j) i =
      axis2Right i j := by
  decide +kernel

private theorem box_nonneg {m : ℕ} {p : Fin 18 → Fin (m + 1) → ℚ}
    {a b c d : ℚ} {axis : Fin 18 → Fin (m + 1) → ℚ}
    (he : ∀ i j, certificateAxisBox a b (fun k ↦ p k j) i = axis i j)
    (hs : ∀ i j, 0 ≤ certificateAxisBox c d (axis i) j) :
    ∀ i j, 0 ≤ certificateBoxCoeff p a b c d i j := by
  intro i j
  rw [certificateBoxCoeff_separable]
  simp only [he]
  exact hs i j

private theorem mixedOddAPower1_left :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower1 0 (1 / 2) 0 1 i j :=
  box_nonneg axis1Left_eq (by decide +kernel)

private theorem mixedOddAPower1_right :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower1 (1 / 2) 1 0 1 i j :=
  box_nonneg axis1Right_eq (by decide +kernel)

private theorem mixedOddAPower2_left_bottom :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower2 0 (1 / 2) 0 (1 / 2) i j :=
  box_nonneg axis2Left_eq (by decide +kernel)

private theorem mixedOddAPower2_left_top :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower2 0 (1 / 2) (1 / 2) 1 i j :=
  box_nonneg axis2Left_eq (by decide +kernel)

private theorem mixedOddAPower2_right_bottom :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower2 (1 / 2) 1 0 (1 / 2) i j :=
  box_nonneg axis2Right_eq (by decide +kernel)

private theorem mixedOddAPower2_right_top :
    ∀ i j, 0 ≤ certificateBoxCoeff mixedOddAPower2 (1 / 2) 1 (1 / 2) 1 i j :=
  box_nonneg axis2Right_eq (by decide +kernel)

private theorem power1_nonneg {t q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ certificatePolynomial mixedOddAPower1 t q := by
  rcases le_total t (1 / 2) with ht' | ht'
  · exact certificate_bernstein_nonneg mixedOddAPower1 (by norm_num) (by norm_num)
      mixedOddAPower1_left (by norm_num; exact ⟨ht.1, ht'⟩) (by norm_num; exact hq)
  · exact certificate_bernstein_nonneg mixedOddAPower1 (by norm_num) (by norm_num)
      mixedOddAPower1_right (by norm_num; exact ⟨ht', ht.2⟩) (by norm_num; exact hq)

private theorem power2_nonneg {t q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ certificatePolynomial mixedOddAPower2 t q := by
  rcases le_total t (1 / 2) with ht' | ht' <;> rcases le_total q (1 / 2) with hq' | hq'
  · exact certificate_bernstein_nonneg mixedOddAPower2 (by norm_num) (by norm_num)
      mixedOddAPower2_left_bottom
      (by norm_num; exact ⟨ht.1, ht'⟩) (by norm_num; exact ⟨hq.1, hq'⟩)
  · exact certificate_bernstein_nonneg mixedOddAPower2 (by norm_num) (by norm_num)
      mixedOddAPower2_left_top
      (by norm_num; exact ⟨ht.1, ht'⟩) (by norm_num; exact ⟨hq', hq.2⟩)
  · exact certificate_bernstein_nonneg mixedOddAPower2 (by norm_num) (by norm_num)
      mixedOddAPower2_right_bottom
      (by norm_num; exact ⟨ht', ht.2⟩) (by norm_num; exact ⟨hq.1, hq'⟩)
  · exact certificate_bernstein_nonneg mixedOddAPower2 (by norm_num) (by norm_num)
      mixedOddAPower2_right_top
      (by norm_num; exact ⟨ht', ht.2⟩) (by norm_num; exact ⟨hq', hq.2⟩)

theorem mixed_odd_a_residual_nonneg {h k : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hk : k ∈ Ioo (0 : ℝ) 1) : 0 ≤ mixedOddAResidual (h, k) := by
  have hs : 0 < h + k := add_pos hh.1 hk.1
  have hr : 0 < 2 - h ^ 2 - k ^ 2 := by
    linarith [pow_lt_one₀ hh.1.le hh.2 (n := 2) (by decide),
      pow_lt_one₀ hk.1.le hk.2 (n := 2) (by decide)]
  have hn : 0 ≤ mixedOddAScaledNumerator h k := by
    rcases le_total h k with hl | hl
    · have hq : h / k ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hh.1.le hk.1.le, (div_le_one hk.1).2 hl⟩
      have he := mixed_odd_a_power1_identity k (h / k)
      rw [mul_div_cancel₀ h hk.1.ne'] at he
      rw [he]
      exact mul_nonneg (pow_nonneg hk.1.le _) (power1_nonneg ⟨hk.1.le, hk.2.le⟩ hq)
    · have hq : k / h ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hk.1.le hh.1.le, (div_le_one hh.1).2 hl⟩
      have he := mixed_odd_a_power2_identity h (k / h)
      rw [mul_div_cancel₀ k hh.1.ne'] at he
      rw [he]
      exact mul_nonneg (pow_nonneg hh.1.le _) (power2_nonneg ⟨hh.1.le, hh.2.le⟩ hq)
  rw [mixed_odd_a_clear h k hs.ne' hr.ne'] at hn
  exact nonneg_of_mul_nonneg_right hn (by positivity)

end NoEmbeddedEigenvalues
