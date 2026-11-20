import NoEmbeddedEigenvalues.Analysis.ZonalModes
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Endpoint cutoffs for weak zonal testing

These cutoffs exhaust the open latitude interval. Their derivatives need not
be uniformly bounded, but `cos a * χ' a` is uniformly bounded and eventually
zero at every interior point. Combined with the endpoint factor in mode
derivatives, this permits dominated convergence against weighted L¹ values.
No boundary traces or approximation in a weighted Sobolev norm are involved.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Filter
open scoped Topology ContDiff

/-- Smooth cutoffs supported strictly inside the open latitude interval. -/
def zonalCutoff (n : ℕ) (a : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) - 1)

theorem contDiff_zonalCutoff (n : ℕ) : ContDiff ℝ ∞ (zonalCutoff n) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem zonalCutoff_mem_Icc (n : ℕ) (a : ℝ) : zonalCutoff n a ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem deriv_transition_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · apply IsLocalMin.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  · apply IsLocalMax.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y

theorem bound_deriv_transition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    ((show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv
      (by norm_num)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (show |deriv Real.smoothTransition x| ≤ C by simpa using hC x hx).trans
      (le_max_left _ _)
  · have hx' : x ≤ 0 ∨ 1 ≤ x := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      exact hx.imp le_of_lt le_of_lt
    rw [deriv_transition_zero hx', abs_zero]
    exact le_max_right _ _

theorem deriv_zonalCutoff (n : ℕ) (a : ℝ) :
    deriv (zonalCutoff n) a =
      deriv Real.smoothTransition (((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) - 1) *
        (-2 * ((n : ℝ) + 1) * a) := by
  apply HasDerivAt.deriv
  have hi : HasDerivAt (fun t : ℝ ↦ ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - t ^ 2) - 1)
      (-2 * ((n : ℝ) + 1) * a) a := by
    convert ((((hasDerivAt_id a).pow 2).const_sub ((Real.pi / 2) ^ 2)).const_mul
      ((n : ℝ) + 1)).sub_const 1 using 1
    · rfl
    · simp only [id_eq]
      ring
  have ht : Differentiable ℝ Real.smoothTransition :=
    Real.smoothTransition.contDiff.differentiable (n := 1) (by norm_num)
  exact (ht _).hasDerivAt.comp a hi

private def cutoffCore (n : ℕ) : Set ℝ :=
  {a | 1 ≤ ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2)}

private theorem cutoffCore_subset (n : ℕ) :
    cutoffCore n ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) := by
  intro a ha
  have hd : 0 < (Real.pi / 2) ^ 2 - a ^ 2 := by
    have hN : 0 < (n : ℝ) + 1 := by positivity
    change 1 ≤ ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) at ha
    nlinarith
  have hr : 0 < Real.pi / 2 := by positivity
  constructor <;> nlinarith

private theorem tsupport_zonalCutoff_subset_core (n : ℕ) :
    tsupport (zonalCutoff n) ⊆ cutoffCore n := by
  apply closure_minimal
  · intro a ha
    have h := mt Real.smoothTransition.zero_iff_nonpos.mpr ha
    change 1 ≤ ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2)
    linarith [lt_of_not_ge h]
  · exact isClosed_le continuous_const (by fun_prop)

theorem tsupport_zonalCutoff_subset (n : ℕ) :
    tsupport (zonalCutoff n) ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) :=
  (tsupport_zonalCutoff_subset_core n).trans (cutoffCore_subset n)

theorem hasCompactSupport_zonalCutoff (n : ℕ) : HasCompactSupport (zonalCutoff n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_zonalCutoff_subset n).trans Ioo_subset_Icc_self)

/-- Both the value and its derivative stabilize at every interior point. -/
theorem zonalCutoff_eventually {a : ℝ} (ha : a ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    ∀ᶠ n : ℕ in atTop, zonalCutoff n a = 1 ∧ deriv (zonalCutoff n) a = 0 := by
  have hd : 0 < (Real.pi / 2) ^ 2 - a ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr ha.2) (show 0 < Real.pi / 2 + a by linarith [ha.1])
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ((Real.pi / 2) ^ 2 - a ^ 2))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 1 ≤ ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) - 1 := by
    have := (div_lt_iff₀ hd).mp hN
    nlinarith
  exact ⟨Real.smoothTransition.one_of_one_le hlarge,
    by rw [deriv_zonalCutoff, deriv_transition_zero (Or.inr hlarge), zero_mul]⟩

/-- The endpoint factor compensates for the growing cutoff derivative. -/
theorem zonalCutoff_deriv_cos_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n a, a ∈ Ioo (-Real.pi / 2) (Real.pi / 2) →
      |deriv (zonalCutoff n) a| * |Real.cos a| ≤ C := by
  obtain ⟨C, hC, hb⟩ := bound_deriv_transition
  refine ⟨4 * C, by positivity, fun n a ha ↦ ?_⟩
  let x := ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) - 1
  by_cases hz : deriv Real.smoothTransition x = 0
  · simp only [deriv_zonalCutoff, show deriv Real.smoothTransition
      (((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) - 1) = 0 from hz,
      zero_mul, abs_zero]
    positivity
  have hx : x < 1 := lt_of_not_ge fun h ↦ hz (deriv_transition_zero (Or.inr h))
  have hd : 0 ≤ (Real.pi / 2) ^ 2 - a ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ha.2.le)
      (show 0 ≤ Real.pi / 2 + a by linarith [ha.1])
    nlinarith
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hcos1 : |Real.cos a| ≤ Real.pi / 2 - a := by
    simpa [Real.cos_pi_div_two, abs_of_nonpos (by linarith [ha.2] : a - Real.pi / 2 ≤ 0)]
      using Real.abs_cos_sub_cos_le a (Real.pi / 2)
  have hcos2 : |Real.cos a| ≤ Real.pi / 2 + a := by
    simpa [Real.cos_neg, Real.cos_pi_div_two, sub_neg_eq_add, add_comm,
      abs_of_nonneg (by linarith [ha.1] : 0 ≤ a + Real.pi / 2)] using
      Real.abs_cos_sub_cos_le a (-(Real.pi / 2))
  have hac : |a| * |Real.cos a| ≤ (Real.pi / 2) ^ 2 - a ^ 2 := by
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0]
      have h := mul_le_mul_of_nonneg_left hcos1 ha0
      have h' := mul_nonneg (show 0 ≤ Real.pi / 2 by positivity) (sub_nonneg.mpr ha.2.le)
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge ha0)]
      have h := mul_le_mul_of_nonneg_left hcos2 (by linarith : 0 ≤ -a)
      have h' := mul_nonneg (show 0 ≤ Real.pi / 2 by positivity)
        (show 0 ≤ Real.pi / 2 + a by linarith [ha.1])
      nlinarith
  calc
    |deriv (zonalCutoff n) a| * |Real.cos a| =
        2 * |deriv Real.smoothTransition x| * ((n : ℝ) + 1) * (|a| * |Real.cos a|) := by
      rw [deriv_zonalCutoff, abs_mul, abs_mul, abs_mul, abs_of_nonneg hN]
      norm_num
      ring
    _ ≤ 2 * C * ((n : ℝ) + 1) * ((Real.pi / 2) ^ 2 - a ^ 2) := by gcongr; exact hb x
    _ ≤ 4 * C := by dsimp [x] at hx; nlinarith

end NoEmbeddedEigenvalues
