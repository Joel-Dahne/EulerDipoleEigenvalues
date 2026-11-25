module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterMeasureTransport

/-!
# Saddle weights for the forcing transport derivative

Blueprint: `lem:saddle-transport-weights`.

Each sine coefficient is at most the saddle distance and at most one.
Consequently its absolute value is at most the square root of that distance.
Multiplying a gradient component weighted by d⁻³ᐟ² therefore gives a
transport term weighted by d⁻², without a cutoff or a bound on the distance.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Each velocity coefficient vanishes at least linearly at the saddle lattice. -/
theorem abs_sin_axis_le_saddleDist (p : ℝ × ℝ) (j : Fin 2) :
    |Real.sin (if j = 0 then p.1 else p.2)| ≤ saddleDist p := by
  have hne : saddleSet.Nonempty := ⟨(0, -Real.pi), 0, -1, by decide, by simp⟩
  apply (Metric.le_infDist hne).2
  rintro q ⟨m, n, _, rfl⟩
  split_ifs
  · have h := Real.abs_sin_sub_sin_le p.1 (m * Real.pi)
    rw [Real.sin_int_mul_pi, sub_zero] at h
    exact h.trans (le_max_left _ _)
  · have h := Real.abs_sin_sub_sin_le p.2 (n * Real.pi)
    rw [Real.sin_int_mul_pi, sub_zero] at h
    exact h.trans (le_max_right _ _)

/-- The bounded sine coefficients gain half a saddle-distance power. -/
theorem abs_sin_axis_le_sqrt_saddleDist (p : ℝ × ℝ) (j : Fin 2) :
    |Real.sin (if j = 0 then p.1 else p.2)| ≤ Real.sqrt (saddleDist p) := by
  have h₀ := abs_nonneg (Real.sin (if j = 0 then p.1 else p.2))
  have h₁ := Real.abs_sin_le_one (if j = 0 then p.1 else p.2)
  have h₂ := abs_sin_axis_le_saddleDist p j
  have hr : 0 ≤ saddleDist p := Metric.infDist_nonneg
  have hsq : |Real.sin (if j = 0 then p.1 else p.2)| ^ 2 ≤ saddleDist p := calc
    _ ≤ |Real.sin (if j = 0 then p.1 else p.2)| * saddleDist p := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left h₂ h₀
    _ ≤ 1 * saddleDist p := mul_le_mul_of_nonneg_right h₁ hr
    _ = _ := one_mul _
  nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg (saddleDist p)]

/-- The squared-distance transport weight is dominated by the given
three-halves gradient weight, including the totalized values at a saddle. -/
theorem norm_sin_mul_div_saddleDist_sq_le (p : ℝ × ℝ) (j : Fin 2) (z : ℂ) :
    ‖(Real.sin (if j = 0 then p.1 else p.2) : ℂ) * z / (saddleDist p ^ 2 : ℂ)‖ ≤
      ‖z / (Real.rpow (saddleDist p) (3 / 2) : ℂ)‖ := by
  let r := saddleDist p
  have hr : 0 ≤ r := Metric.infDist_nonneg
  by_cases hz : r = 0
  · have hz' : saddleDist p = 0 := hz
    simp [hz', Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have hp : 0 < Real.rpow r (3 / 2) := Real.rpow_pos_of_pos hrp _
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hrp
  have hw : Real.sqrt r * Real.rpow r (3 / 2) = r ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    change r ^ (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ) = r ^ 2
    rw [← Real.rpow_add hrp]
    norm_num
  change ‖(Real.sin (if j = 0 then p.1 else p.2) : ℂ) * z / (r ^ 2 : ℂ)‖ ≤
    ‖z / (Real.rpow r (3 / 2) : ℂ)‖
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_pos hp]
  calc
    _ ≤ Real.sqrt r * ‖z‖ / r ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (abs_sin_axis_le_sqrt_saddleDist p j) (norm_nonneg z))
      (sq_nonneg r)
    _ = ‖z‖ / Real.rpow r (3 / 2) := by
      rw [← hw]
      field_simp

/-- Each weighted gradient component supplies its weighted sine-transport term. -/
theorem memLp_sin_mul_div_saddleDist_sq {U : Set (ℝ × ℝ)} {D : ℝ × ℝ → ℂ}
    (hm : Measurable D)
    (hD : MemLp (fun p ↦ D p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict U)) (j : Fin 2) :
    MemLp (fun p ↦ (Real.sin (if j = 0 then p.1 else p.2) : ℂ) * D p /
      (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict U) := by
  have hd : Continuous saddleDist := Metric.continuous_infDist_pt saddleSet
  have hmeas : Measurable (fun p ↦
      (Real.sin (if j = 0 then p.1 else p.2) : ℂ) * D p / (saddleDist p ^ 2 : ℂ)) := by
    split_ifs <;> fun_prop
  apply hD.of_le_mul (c := 1) hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun p ↦ by
    simpa only [one_mul] using norm_sin_mul_div_saddleDist_sq_le p j (D p)

end EulerDipoleEigenvalues
