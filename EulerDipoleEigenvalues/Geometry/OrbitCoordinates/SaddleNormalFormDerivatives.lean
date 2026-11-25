module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SmoothJetBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Differentiated bounds in the orthonormal saddle chart -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Set Real
open scoped ContDiff

private theorem classicalRealJet_separated (w : List (Fin 2)) (f g : ℝ → ℝ) :
    classicalRealJet w (fun q ↦ f q.1 * g q.2) =
      fun q ↦ iteratedDeriv (w.count 0) f q.1 * iteratedDeriv (w.count 1) g q.2 := by
  induction w with
  | nil => simp [classicalRealJet, iteratedDeriv_zero]
  | cons j w ih =>
    funext q
    rw [classicalRealJet, ih]
    fin_cases j
    · simp [coordPartial, partialX, iteratedDeriv_succ, deriv_mul_const_field]
    · simp [coordPartial, partialY, iteratedDeriv_succ, deriv_const_mul_field]

private theorem counts_eq_length (w : List (Fin 2)) : w.count 0 + w.count 1 = w.length := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    fin_cases j <;> simp <;> omega

private theorem classicalComplexJet_ofReal (w : List (Fin 2)) {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    classicalComplexJet w (fun q ↦ (f q : ℂ)) =
      fun q ↦ (classicalRealJet w f q : ℂ) := by
  have hs (v : List (Fin 2)) : ContDiff ℝ ∞ (classicalRealJet v f) := by
    induction v with
    | nil => exact hf
    | cons j v ih =>
      exact contDiffOn_univ.mp (contDiffOn_coordPartial isOpen_univ ih.contDiffOn j)
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [classicalComplexJet, ih, classicalRealJet]
    unfold coordPartial
    split_ifs
    · exact partialX_ofReal ((hs w).differentiable (by simp))
    · exact partialY_ofReal ((hs w).differentiable (by simp))

private def chartSine (t : ℝ) : ℝ := √2 * sin (t / √2)

private theorem deriv_chartSine : deriv chartSine = fun t ↦ cos (t / √2) := by
  funext t
  have h := (((hasDerivAt_id t).div_const (√2)).sin).const_mul (√2)
  change deriv (fun y ↦ √2 * sin (y / √2)) t = _
  rw [show deriv (fun y ↦ √2 * sin (y / √2)) t = √2 * (cos (t / √2) * (1 / √2))
    from h.deriv]
  field_simp

private theorem chartSine_zero_jet (n : ℕ) (hn : n ≤ 2) :
    iteratedDeriv n chartSine 0 = iteratedDeriv n id 0 := by
  interval_cases n
  · simp [iteratedDeriv_zero, chartSine]
  · simp [iteratedDeriv_one, deriv_chartSine]
  · have hz : deriv (fun x : ℝ ↦ cos (x / √2)) 0 = 0 := by simp
    simp [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, deriv_chartSine, hz]

private theorem saddle_chart_eq_chartSine {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    (fun q ↦ dipoleLift (saddleOrthoChart P q)) = fun q ↦ chartSine q.1 * chartSine q.2 := by
  funext q
  rw [saddle_dipole_factorization hP]
  have h (t : ℝ) : t * sinc (t / √2) = chartSine t := by
    by_cases ht : t = 0
    · simp [ht, chartSine]
    · rw [sinc_of_ne_zero (div_ne_zero ht (by positivity)), chartSine]
      field_simp
  rw [show q.1 * q.2 * saddleFactor q = (q.1 * sinc (q.1 / √2)) *
      (q.2 * sinc (q.2 / √2)) by unfold saddleFactor; ring, h, h]

private theorem saddle_chart_jets {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    (w : List (Fin 2)) (hw : w.length < 4) :
    classicalRealJet w (fun q ↦ dipoleLift (saddleOrthoChart P q)) 0 =
      classicalRealJet w (fun q : ℝ × ℝ ↦ q.1 * q.2) 0 := by
  rw [saddle_chart_eq_chartSine hP, classicalRealJet_separated, show
    (fun q : ℝ × ℝ ↦ q.1 * q.2) = (fun q ↦ id q.1 * id q.2) by rfl,
    classicalRealJet_separated]
  have hcount := counts_eq_length w
  change iteratedDeriv (w.count 0) chartSine 0 * iteratedDeriv (w.count 1) chartSine 0 =
    iteratedDeriv (w.count 0) id 0 * iteratedDeriv (w.count 1) id 0
  by_cases h₀ : w.count 0 ≤ 2
  · by_cases h₁ : w.count 1 ≤ 2
    · rw [chartSine_zero_jet _ h₀, chartSine_zero_jet _ h₁]
    · rw [show w.count 0 = 0 by omega]
      simp [iteratedDeriv_zero, chartSine]
  · rw [show w.count 1 = 0 by omega]
    simp [iteratedDeriv_zero, chartSine]

private theorem saddle_chart_remainder_bounds {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ q ∈ localDisk 0 ρ,
      ∀ w : List (Fin 2), w.length ≤ 3 →
        |classicalRealJet w (fun v ↦ dipoleLift (saddleOrthoChart P v) - v.1 * v.2) q| ≤
          C * localRadius 0 q ^ (4 - w.length) := by
  let F : ℝ × ℝ → ℝ := fun q ↦ dipoleLift (saddleOrthoChart P q)
  let G : ℝ × ℝ → ℝ := fun q ↦ q.1 * q.2
  have hF : ContDiff ℝ ∞ F := by dsimp [F, dipoleLift, saddleOrthoChart]; fun_prop
  have hG : ContDiff ℝ ∞ G := by dsimp [G]; fun_prop
  have hFc : ContDiff ℝ ∞ (fun q ↦ (F q : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hGc : ContDiff ℝ ∞ (fun q ↦ (G q : ℂ)) := Complex.ofRealCLM.contDiff.comp hG
  have hflat (w : List (Fin 2)) (hw : w.length < 4) :
      classicalComplexJet w (fun q ↦ ((F q - G q : ℝ) : ℂ)) 0 = 0 := by
    simp only [Complex.ofReal_sub]
    rw [classicalComplexJet_sub_on isOpen_univ hFc.contDiffOn hGc.contDiffOn w (mem_univ 0),
      classicalComplexJet_ofReal w hF, classicalComplexJet_ofReal w hG]
    change ((classicalRealJet w F 0 : ℝ) : ℂ) - (classicalRealJet w G 0 : ℂ) = 0
    rw [show classicalRealJet w F 0 = classicalRealJet w G 0 from saddle_chart_jets hP w hw,
      sub_self]
  have hFG : ContDiff ℝ ∞ (fun q ↦ ((F q - G q : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hF.sub hG)
  obtain ⟨ρ, C, hρ, hC, _, hb⟩ := exists_radial_classicalJet_flat_bounds isOpen_univ (mem_univ 0)
    hFG.contDiffOn 4 hflat
  refine ⟨ρ, C, hρ, hC, fun q hq w hw ↦ ?_⟩
  simpa only [classicalComplexJet_ofReal w (hF.sub hG), Complex.norm_real, Real.norm_eq_abs]
    using hb w (by omega) q hq

private theorem abs_chartSine_le (t : ℝ) : |chartSine t| ≤ |t| := by
  have hs : 0 < √(2 : ℝ) := by positivity
  rw [chartSine, abs_mul, abs_of_pos hs]
  calc
    _ ≤ √2 * |t / √2| := mul_le_mul_of_nonneg_left abs_sin_le_abs hs.le
    _ = _ := by rw [abs_div, abs_of_pos hs]; field_simp

private theorem gradSq_saddle_chart {P : ℝ × ℝ} (hP : P ∈ saddleSet) (q : ℝ × ℝ) :
    gradSq dipoleLift (saddleOrthoChart P q) =
      (cos (q.1 / √2) * chartSine q.2) ^ 2 + (chartSine q.1 * cos (q.2 / √2)) ^ 2 := by
  obtain ⟨m, n, _, rfl⟩ := hP
  have hxs : cos ((m : ℝ) * π) ^ 2 = 1 := by
    simpa only [sin_int_mul_pi, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
      sin_sq_add_cos_sq ((m : ℝ) * π)
  have hys : cos ((n : ℝ) * π) ^ 2 = 1 := by
    simpa only [sin_int_mul_pi, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
      sin_sq_add_cos_sq ((n : ℝ) * π)
  simp only [gradSq_dipoleLift, saddleOrthoChart, sin_add, sin_int_mul_pi, zero_mul, zero_add,
    mul_pow, hxs, hys, one_mul, chartSine, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rcases sq_eq_one_iff.mp hxs with hs | hs
  all_goals
    simp only [hs, one_mul, neg_one_mul, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [add_div, sub_div]
    simp only [sin_add, sin_sub]
    ring

private theorem abs_sq_sub_sq_le {a b R D : ℝ} (ha : |a| ≤ R) (hb : |b| ≤ R)
    (hd : |a - b| ≤ D) : |a ^ 2 - b ^ 2| ≤ D * (2 * R) := by
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
  have hsum := (abs_add_le a b).trans (add_le_add ha hb)
  exact mul_le_mul hd (hsum.trans_eq (by ring)) (abs_nonneg _) ((abs_nonneg _).trans hd)

/-- Value, gradient-square and differentiated Taylor bounds for the explicit dipole
(`lem:saddle-normal-form-derivatives`). The constants do not depend on the point q. -/
theorem saddle_normal_form_derivatives {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ q ∈ localDisk 0 ρ,
      (∀ w : List (Fin 2), w.length ≤ 3 →
        |classicalRealJet w (fun v ↦ dipoleLift (saddleOrthoChart P v) - v.1 * v.2) q| ≤
          C * localRadius 0 q ^ (4 - w.length)) ∧
      |gradSq dipoleLift (saddleOrthoChart P q) - localRadius 0 q ^ 2| ≤
        C * localRadius 0 q ^ 4 := by
  obtain ⟨ρ, C, hρ, hC, hjet⟩ := saddle_chart_remainder_bounds hP
  refine ⟨ρ, 4 * C, hρ, by positivity, fun q hq ↦ ⟨?_, ?_⟩⟩
  · intro w hw
    exact (hjet q hq w hw).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sqrt_nonneg _) _))
  let X := cos (q.1 / √2) * chartSine q.2
  let Y := chartSine q.1 * cos (q.2 / √2)
  let r := localRadius 0 q
  have hr : r = √(q.1 ^ 2 + q.2 ^ 2) := by simp [r, localRadius]
  have hr2 : r ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by rw [hr, sq_sqrt (by positivity)]
  have hq₁ : |q.1| ≤ r := by rw [hr]; exact abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hq₂ : |q.2| ≤ r := by rw [hr]; exact abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hX : |X| ≤ r := calc
    |X| ≤ 1 * |q.2| := by
      dsimp only [X]
      rw [abs_mul]
      exact mul_le_mul (abs_cos_le_one _) (abs_chartSine_le _) (abs_nonneg _) zero_le_one
    _ ≤ r := by rwa [one_mul]
  have hY : |Y| ≤ r := calc
    |Y| ≤ |q.1| * 1 := by
      dsimp only [Y]
      rw [abs_mul]
      exact mul_le_mul (abs_chartSine_le _) (abs_cos_le_one _) (abs_nonneg _) (abs_nonneg _)
    _ ≤ r := by rwa [mul_one]
  have heq : (fun v ↦ dipoleLift (saddleOrthoChart P v) - v.1 * v.2) =
      fun v ↦ chartSine v.1 * chartSine v.2 - v.1 * v.2 :=
    funext fun v ↦ congrArg (fun a ↦ a - v.1 * v.2) (congrFun (saddle_chart_eq_chartSine hP) v)
  have hd (t : ℝ) : HasDerivAt chartSine (cos (t / √2)) t := by
    have hs : DifferentiableAt ℝ chartSine t := by unfold chartSine; fun_prop
    simpa only [deriv_chartSine] using hs.hasDerivAt
  have hdx : HasDerivAt (fun t ↦ chartSine t * chartSine q.2 - t * q.2) (X - q.2) q.1 := by
    simpa only [one_mul] using! ((hd q.1).mul_const (chartSine q.2)).fun_sub
      ((hasDerivAt_id q.1).mul_const q.2)
  have hdy : HasDerivAt (fun t ↦ chartSine q.1 * chartSine t - q.1 * t) (Y - q.1) q.2 := by
    simpa only [mul_one] using! ((hd q.2).const_mul (chartSine q.1)).fun_sub
      ((hasDerivAt_id q.2).const_mul q.1)
  have hdiffX : |X - q.2| ≤ C * r ^ 3 := by
    have h := hjet q hq [0] (by decide)
    rw [heq] at h
    change |deriv (fun t ↦ chartSine t * chartSine q.2 - t * q.2) q.1| ≤ C * r ^ 3 at h
    rwa [hdx.deriv] at h
  have hdiffY : |Y - q.1| ≤ C * r ^ 3 := by
    have h := hjet q hq [1] (by decide)
    rw [heq] at h
    change |deriv (fun t ↦ chartSine q.1 * chartSine t - q.1 * t) q.2| ≤ C * r ^ 3 at h
    rwa [hdy.deriv] at h
  rw [gradSq_saddle_chart hP]
  change |X ^ 2 + Y ^ 2 - r ^ 2| ≤ _
  rw [hr2, show X ^ 2 + Y ^ 2 - (q.1 ^ 2 + q.2 ^ 2) =
    (X ^ 2 - q.2 ^ 2) + (Y ^ 2 - q.1 ^ 2) by ring]
  calc
    _ ≤ |X ^ 2 - q.2 ^ 2| + |Y ^ 2 - q.1 ^ 2| := abs_add_le _ _
    _ ≤ (C * r ^ 3) * (2 * r) + (C * r ^ 3) * (2 * r) :=
      add_le_add (abs_sq_sub_sq_le hX hq₂ hdiffX) (abs_sq_sub_sq_le hY hq₁ hdiffY)
    _ = _ := by ring

end EulerDipoleEigenvalues
