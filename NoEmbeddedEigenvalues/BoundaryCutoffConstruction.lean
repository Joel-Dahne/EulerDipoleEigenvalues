import NoEmbeddedEigenvalues.BoundaryCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A uniformly controlled smooth endpoint cutoff family

Blueprint: `def:boundary-cutoff-family`, `lem:boundary-cutoff-existence`,
and `lem:boundary-cutoff-approximation`.

The fixed smooth transition is rescaled at the two endpoints. Compactness of
its derivative supports supplies constants independent of the layer width.

Not used by the main argument: positivity of the boundary form on the weighted
domain is proved directly in `WeightedBoundaryForm.lean`. Kept as infrastructure
(decision of 2026-10-15).
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Topology ContDiff

private abbrev ρ := Real.smoothTransition

private theorem smooth_ρ : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff
private theorem smooth_ρ₁ : ContDiff ℝ ∞ (deriv ρ) :=
  (contDiff_infty_iff_deriv.mp smooth_ρ).2
private theorem deriv_ρ (x : ℝ) : HasDerivAt ρ (deriv ρ x) x :=
  (smooth_ρ.differentiable (by simp) x).hasDerivAt
private theorem deriv_ρ₁ (x : ℝ) : HasDerivAt (deriv ρ) (deriv (deriv ρ) x) x :=
  (smooth_ρ₁.differentiable (by simp) x).hasDerivAt

private theorem compact_deriv_ρ : HasCompactSupport (deriv ρ) := by
  change IsCompact (closure (Function.support (deriv ρ)))
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  by_cases hneg : x < 0
  · have heq : ρ =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by simpa using heq.deriv_eq)
  · have hpos : 1 < x := lt_of_not_ge (fun h ↦ hn ⟨le_of_not_gt hneg, h⟩)
    have heq : ρ =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by simpa using heq.deriv_eq)

/-- A single finite constant bounds the first two derivatives of the fixed profile. -/
theorem exists_smoothTransition_derivative_bound :
    ∃ B : ℝ, 1 ≤ B ∧ (∀ x, |deriv Real.smoothTransition x| ≤ B) ∧
      ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ B := by
  obtain ⟨B₁, hB₁⟩ := compact_deriv_ρ.exists_bound_of_continuous smooth_ρ₁.continuous
  obtain ⟨B₂, hB₂⟩ := compact_deriv_ρ.deriv.exists_bound_of_continuous
    (smooth_ρ₁.continuous_deriv (by simp))
  refine ⟨max 1 (max B₁ B₂), le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (hB₁ x).trans ((le_max_left B₁ B₂).trans (le_max_right _ _))
  · intro x
    exact (hB₂ x).trans ((le_max_right B₁ B₂).trans (le_max_right _ _))

/-- The transition coordinate measured from the left endpoint. -/
def boundaryCutoffLeft (η x : ℝ) : ℝ := 4 * (x + 1) / η - 2

/-- The transition coordinate measured from the right endpoint. -/
def boundaryCutoffRight (η x : ℝ) : ℝ := 4 * (1 - x) / η - 2

/-- The real smooth endpoint cutoff. For `η > 0` it vanishes near both endpoints. -/
def boundaryCutoffValue (η x : ℝ) : ℝ :=
  ρ (boundaryCutoffLeft η x) * ρ (boundaryCutoffRight η x)

/-- Explicit first derivative of the cutoff. -/
def boundaryCutoffFirst (η x : ℝ) : ℝ :=
  (4 / η) * (deriv ρ (boundaryCutoffLeft η x) * ρ (boundaryCutoffRight η x) -
    ρ (boundaryCutoffLeft η x) * deriv ρ (boundaryCutoffRight η x))

/-- Explicit second derivative of the cutoff. -/
def boundaryCutoffSecond (η x : ℝ) : ℝ :=
  (4 / η) ^ 2 * (deriv (deriv ρ) (boundaryCutoffLeft η x) * ρ (boundaryCutoffRight η x) -
    2 * deriv ρ (boundaryCutoffLeft η x) * deriv ρ (boundaryCutoffRight η x) +
    ρ (boundaryCutoffLeft η x) * deriv (deriv ρ) (boundaryCutoffRight η x))

private theorem deriv_left (η x : ℝ) : HasDerivAt (boundaryCutoffLeft η) (4 / η) x := by
  change HasDerivAt (fun y ↦ 4 * (y + 1) / η - 2) (4 / η) x
  simpa using (((hasDerivAt_id x).add_const 1).const_mul 4).div_const η |>.sub_const 2

private theorem deriv_right (η x : ℝ) : HasDerivAt (boundaryCutoffRight η) (-(4 / η)) x := by
  change HasDerivAt (fun y ↦ 4 * (1 - y) / η - 2) (-(4 / η)) x
  simpa [neg_div] using (((hasDerivAt_id x).const_sub 1).const_mul 4).div_const η |>.sub_const 2

/-- Smoothness of the real cutoff, on the whole real line. -/
theorem contDiff_boundaryCutoffValue (η : ℝ) : ContDiff ℝ ∞ (boundaryCutoffValue η) := by
  unfold boundaryCutoffValue boundaryCutoffLeft boundaryCutoffRight
  fun_prop

/-- The first-derivative formula, valid even at the endpoints. -/
theorem hasDerivAt_boundaryCutoffValue (η x : ℝ) :
    HasDerivAt (boundaryCutoffValue η) (boundaryCutoffFirst η x) x := by
  convert ((deriv_ρ _).comp x (deriv_left η x)).mul
    ((deriv_ρ _).comp x (deriv_right η x)) using 1
  · rfl
  · simp only [boundaryCutoffFirst, Function.comp_apply]
    ring

/-- The second-derivative formula. -/
theorem hasDerivAt_boundaryCutoffFirst (η x : ℝ) :
    HasDerivAt (boundaryCutoffFirst η) (boundaryCutoffSecond η x) x := by
  have hL := (deriv_ρ _).comp x (deriv_left η x)
  have hR := (deriv_ρ _).comp x (deriv_right η x)
  have hL₁ := (deriv_ρ₁ _).comp x (deriv_left η x)
  have hR₁ := (deriv_ρ₁ _).comp x (deriv_right η x)
  convert ((hL₁.mul hR).sub (hL.mul hR₁)).const_mul (4 / η) using 1
  · rfl
  · simp only [boundaryCutoffSecond, Function.comp_apply]
    ring

/-- The real cutoff regarded as a classical complex boundary jet. -/
def boundaryCutoffJet (η : ℝ) : BoundaryJet where
  value x := (boundaryCutoffValue η x : ℂ)
  first x := (boundaryCutoffFirst η x : ℂ)
  second x := (boundaryCutoffSecond η x : ℂ)
  continuous_value :=
    (Complex.continuous_ofReal.comp (contDiff_boundaryCutoffValue η).continuous).continuousOn
  continuous_first := by
    have hc := smooth_ρ₁.continuous
    unfold boundaryCutoffFirst boundaryCutoffLeft boundaryCutoffRight
    fun_prop
  continuous_second := by
    have hc := smooth_ρ₁.continuous
    have hc₂ := smooth_ρ₁.continuous_deriv (by simp)
    unfold boundaryCutoffSecond boundaryCutoffLeft boundaryCutoffRight
    fun_prop
  deriv_value x _ := (hasDerivAt_boundaryCutoffValue η x).ofReal_comp
  deriv_first x _ := (hasDerivAt_boundaryCutoffFirst η x).ofReal_comp

private theorem eventually_value_one {η x : ℝ}
    (hL : 1 < boundaryCutoffLeft η x) (hR : 1 < boundaryCutoffRight η x) :
    boundaryCutoffValue η =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [(deriv_left η x).continuousAt.eventually (Ioi_mem_nhds hL),
    (deriv_right η x).continuousAt.eventually (Ioi_mem_nhds hR)] with y hyL hyR
  simp only [boundaryCutoffValue, Real.smoothTransition.one_of_one_le hyL.le,
    Real.smoothTransition.one_of_one_le hyR.le, mul_one]

private theorem first_zero_of_flat {η x : ℝ}
    (hL : 1 < boundaryCutoffLeft η x) (hR : 1 < boundaryCutoffRight η x) :
    boundaryCutoffFirst η x = 0 := by
  simpa only [(hasDerivAt_boundaryCutoffValue η x).deriv, deriv_const] using
    (eventually_value_one hL hR).deriv_eq

private theorem jet_flat {η x : ℝ}
    (hL : 1 < boundaryCutoffLeft η x) (hR : 1 < boundaryCutoffRight η x) :
    boundaryCutoffValue η x = 1 ∧ boundaryCutoffFirst η x = 0 ∧
      boundaryCutoffSecond η x = 0 := by
  refine ⟨(eventually_value_one hL hR).eq_of_nhds, first_zero_of_flat hL hR, ?_⟩
  have heq : boundaryCutoffFirst η =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [(deriv_left η x).continuousAt.eventually (Ioi_mem_nhds hL),
      (deriv_right η x).continuousAt.eventually (Ioi_mem_nhds hR)] with y hyL hyR
    exact first_zero_of_flat hyL hyR
  simpa only [(hasDerivAt_boundaryCutoffFirst η x).deriv, deriv_const] using heq.deriv_eq

private theorem abs_ρ_le_one (x : ℝ) : |ρ x| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem first_bound {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B)
    (hB₁ : ∀ x, |deriv ρ x| ≤ B) (x : ℝ) :
    |boundaryCutoffFirst η x| ≤ 8 * B / η := by
  let L := boundaryCutoffLeft η x
  let R := boundaryCutoffRight η x
  have h₁ : |deriv ρ L * ρ R| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hB₁ L) (abs_ρ_le_one R) (abs_nonneg _) (by linarith)).trans_eq (mul_one B)
  have h₂ : |ρ L * deriv ρ R| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (abs_ρ_le_one L) (hB₁ R) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  change |(4 / η) * (deriv ρ L * ρ R - ρ L * deriv ρ R)| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) / η)]
  calc
    _ ≤ (4 / η) * (|deriv ρ L * ρ R| + |ρ L * deriv ρ R|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ (4 / η) * (B + B) := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
    _ = _ := by ring

private theorem second_bound {η B : ℝ} (hB : 1 ≤ B)
    (hB₁ : ∀ x, |deriv ρ x| ≤ B) (hB₂ : ∀ x, |deriv (deriv ρ) x| ≤ B) (x : ℝ) :
    |boundaryCutoffSecond η x| ≤ 32 * (B + B ^ 2) / η ^ 2 := by
  let L := boundaryCutoffLeft η x
  let R := boundaryCutoffRight η x
  have h₁ : |deriv (deriv ρ) L * ρ R| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hB₂ L) (abs_ρ_le_one R) (abs_nonneg _) (by linarith)).trans_eq (mul_one B)
  have h₂ : |2 * deriv ρ L * deriv ρ R| ≤ 2 * B ^ 2 := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      _ ≤ (2 * B) * B := mul_le_mul
        (mul_le_mul_of_nonneg_left (hB₁ L) (by norm_num)) (hB₁ R) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h₃ : |ρ L * deriv (deriv ρ) R| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (abs_ρ_le_one L) (hB₂ R) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  change |(4 / η) ^ 2 * (deriv (deriv ρ) L * ρ R -
    2 * deriv ρ L * deriv ρ R + ρ L * deriv (deriv ρ) R)| ≤ _
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (4 / η) ^ 2 * ((|deriv (deriv ρ) L * ρ R| + |2 * deriv ρ L * deriv ρ R|) +
        |ρ L * deriv (deriv ρ) R|) := mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) (sq_nonneg _)
    _ ≤ (4 / η) ^ 2 * ((B + 2 * B ^ 2) + B) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add h₁ h₂) h₃) (sq_nonneg _)
    _ = _ := by ring

private theorem flat_on_core {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Icc (-1 + η) (1 - η)) :
    boundaryCutoffValue η x = 1 ∧ boundaryCutoffFirst η x = 0 ∧
      boundaryCutoffSecond η x = 0 := by
  apply jet_flat
  · have hl : 3 < 4 * (x + 1) / η := (lt_div_iff₀ hη).mpr (by linarith [hx.1])
    unfold boundaryCutoffLeft
    linarith
  · have hr : 3 < 4 * (1 - x) / η := (lt_div_iff₀ hη).mpr (by linarith [hx.2])
    unfold boundaryCutoffRight
    linarith

private theorem value_mem_Icc (η x : ℝ) : boundaryCutoffValue η x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- A derivative bound for the fixed profile gives a uniform constant for all widths. -/
theorem boundaryCutoffJet_control {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B)
    (hB₁ : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hB₂ : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ B) :
    BoundaryCutoffControl η (32 * (B + 1) ^ 2) (boundaryCutoffJet η) where
  support_value := by
    intro x hx
    have hL : 0 < boundaryCutoffLeft η x := by
      by_contra hz
      apply hx
      simp only [boundaryCutoffJet, boundaryCutoffValue,
        Real.smoothTransition.zero_of_nonpos (le_of_not_gt hz), zero_mul, ofReal_zero]
    have hR : 0 < boundaryCutoffRight η x := by
      by_contra hz
      apply hx
      simp only [boundaryCutoffJet, boundaryCutoffValue,
        Real.smoothTransition.zero_of_nonpos (le_of_not_gt hz), mul_zero, ofReal_zero]
    have hl : 2 * η < 4 * (x + 1) := (lt_div_iff₀ hη).mp (by
      unfold boundaryCutoffLeft at hL
      linarith)
    have hr : 2 * η < 4 * (1 - x) := (lt_div_iff₀ hη).mp (by
      unfold boundaryCutoffRight at hR
      linarith)
    exact ⟨by linarith, by linarith⟩
  core_value x hx := by
    change (boundaryCutoffValue η x : ℂ) = 1
    rw [(flat_on_core hη hx).1, ofReal_one]
  core_first x hx := by
    change (boundaryCutoffFirst η x : ℂ) = 0
    rw [(flat_on_core hη hx).2.1, ofReal_zero]
  core_second x hx := by
    change (boundaryCutoffSecond η x : ℂ) = 0
    rw [(flat_on_core hη hx).2.2, ofReal_zero]
  value_error_le x _ := by
    change ‖(boundaryCutoffValue η x : ℂ) - 1‖ ≤ 1
    rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hr := value_mem_Icc η x
    exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  first_le x _ := by
    change ‖(boundaryCutoffFirst η x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (first_bound hη hB hB₁ x).trans
    apply (div_le_div_iff_of_pos_right hη).mpr
    nlinarith [sq_nonneg B]
  second_le x _ := by
    change ‖(boundaryCutoffSecond η x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (second_bound hB hB₁ hB₂ x).trans
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hη)).mpr
    nlinarith

/-- A fixed choice of a bound for the two profile derivatives. -/
def boundaryCutoffDerivativeBound : ℝ := Classical.choose exists_smoothTransition_derivative_bound

/-- The common cutoff constant, independent of the layer width. -/
def boundaryCutoffConstant : ℝ := 32 * (boundaryCutoffDerivativeBound + 1) ^ 2

/-- The constructed family satisfies the cutoff specification for every positive width. -/
theorem boundaryCutoff_control (η : ℝ) (hη : 0 < η) :
    BoundaryCutoffControl η boundaryCutoffConstant (boundaryCutoffJet η) := by
  obtain ⟨hB, hB₁, hB₂⟩ := Classical.choose_spec exists_smoothTransition_derivative_bound
  exact boundaryCutoffJet_control hη hB hB₁ hB₂

/-- The constructed family has a single nonnegative control constant. -/
theorem exists_controlled_boundaryCutoffs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Ioc (0 : ℝ) 1, BoundaryCutoffControl η C (boundaryCutoffJet η) :=
  ⟨boundaryCutoffConstant, by unfold boundaryCutoffConstant; positivity,
    fun η hη ↦ boundaryCutoff_control η hη.1⟩

/-- The complex-valued cutoff is smooth on all of ℝ, not just the closed interval. -/
theorem contDiff_boundaryCutoffJet_value (η : ℝ) :
    ContDiff ℝ ∞ (boundaryCutoffJet η).value := by
  change ContDiff ℝ ∞ (fun x ↦ (boundaryCutoffValue η x : ℂ))
  simpa only [Function.comp_def, ofRealCLM_apply] using
    ofRealCLM.contDiff.comp (contDiff_boundaryCutoffValue η)

/-- The explicit cutoff product remains in the weighted domain. -/
theorem HasWeightedBoundaryH2.boundaryCutoff_mem {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) (η : ℝ) :
    HasWeightedBoundaryH2 (fun x ↦ (boundaryCutoffJet η).value x * F x)
      (fun x ↦ (boundaryCutoffJet η).first x * F x + (boundaryCutoffJet η).value x * D x)
      (fun x ↦ (boundaryCutoffJet η).second x * F x +
        2 * (boundaryCutoffJet η).first x * D x + (boundaryCutoffJet η).value x * E x) :=
  h.mul_boundaryJet (boundaryCutoffJet η)

/-- The explicit cutoff product has compact support strictly inside the interval. -/
theorem boundaryCutoff_support {η : ℝ} (hη : 0 < η) (F : ℝ → ℂ) :
    HasCompactSupport (fun x ↦ (boundaryCutoffJet η).value x * F x) ∧
      Function.support (fun x ↦ (boundaryCutoffJet η).value x * F x) ⊆ Ioo (-1 : ℝ) 1 :=
  ⟨(boundaryCutoff_control η hη).hasCompactSupport_mul F,
    (boundaryCutoff_control η hη).support_mul_subset hη F⟩

/-- The explicit cutoff product has zero value traces. -/
theorem HasWeightedBoundaryH2.boundaryCutoff_memH10 {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) {η : ℝ} (hη : 0 < η) :
    MemIntervalH10 (-1) 1 (fun x ↦ (boundaryCutoffJet η).value x * F x) :=
  h.cutoff_memH10 (boundaryCutoff_control η hη) hη

/-- Unconditional endpoint cutoff approximation in the three weighted graph components. -/
theorem HasWeightedBoundaryH2.boundaryCutoff_convergence {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E)
    (ha : intervalH1Extension (-1) 1 F D (-1) = 0)
    (hb : intervalH1Extension (-1) 1 F D 1 = 0) :
    Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖(boundaryCutoffJet η).value x * F x - F x‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) ∧
      Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1,
        ‖(boundaryCutoffJet η).first x * F x + (boundaryCutoffJet η).value x * D x - D x‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) ∧
      Tendsto (fun η ↦ ∫ x in (-1 : ℝ)..1, ‖(boundaryWeight x : ℂ) *
        ((boundaryCutoffJet η).second x * F x + 2 * (boundaryCutoffJet η).first x * D x +
          (boundaryCutoffJet η).value x * E x - E x)‖ ^ 2)
        (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) :=
  h.cutoff_convergence (fun η hη ↦ boundaryCutoff_control η hη.1)
    (by unfold boundaryCutoffConstant; positivity) ha hb

end NoEmbeddedEigenvalues
