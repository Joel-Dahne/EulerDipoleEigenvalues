module

public import Mathlib.Analysis.ODE.ExistUnique
public import NoEmbeddedEigenvalues.Geometry.Cells.Cells
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.Period

/-! # Global existence and the dipole flow -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Set Filter Metric
open scoped NNReal Topology

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local solutions on `[-T, T]` for a bounded, globally Lipschitz field. -/
theorem exists_local_solution {f : E → E} {L K : ℝ≥0} (hb : ∀ x, ‖f x‖ ≤ L)
    (hl : LipschitzWith K f) (x : E) (T : ℝ≥0) :
    ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Icc (-(T : ℝ)) T, HasDerivWithinAt α (f (α t)) (Icc (-T) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨by simp, T.2⟩
  have hPL : IsPicardLindelof (fun _ ↦ f) (tmin := -(T : ℝ)) (tmax := T) ⟨0, h0⟩ x
      (L * T) 0 L K :=
    IsPicardLindelof.of_time_independent (fun y _ ↦ hb y) (hl.lipschitzOnWith)
      (by simp)
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- A bounded, globally Lipschitz autonomous field has a global integral curve through every
    point. -/
theorem exists_global_solution {f : E → E} {L K : ℝ≥0} (hb : ∀ x, ‖f x‖ ≤ L)
    (hl : LipschitzWith K f) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  choose α hα0 hαd using fun n : ℕ ↦ exists_local_solution hb hl x ((n : ℝ≥0) + 1)
  have hT : ∀ n : ℕ, (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := fun n ↦ by push_cast; rfl
  simp only [hT] at hαd
  have hderiv : ∀ n : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivAt (α n) (f (α n t)) t := fun n t ht ↦
    (hαd n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n t ht ↦ (hαd n t ht).continuousWithinAt
  have hagree : ∀ m n : ℕ, m ≤ n →
      EqOn (α m) (α n) (Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1)) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hsub : Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    refine ODE_solution_unique_of_mem_Icc (v := fun _ ↦ f) (s := fun _ ↦ univ) (K := K)
      (fun _ _ ↦ hl.lipschitzOnWith) (t₀ := 0) ⟨by linarith, by linarith⟩ (hcont m)
      (fun t ht ↦ hderiv m t ht) (fun _ _ ↦ trivial)
      ((hcont n).mono (Icc_subset_Icc (by linarith) (by linarith)))
      (fun t ht ↦ hderiv n t (hsub ht)) (fun _ _ ↦ trivial) (by rw [hα0, hα0])
  let γ : ℝ → E := fun t ↦ α ⌈|t|⌉₊ t
  have hγ : ∀ n : ℕ, ∀ s ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), γ s = α n s := by
    intro n s hs
    have habs : |s| < (n : ℝ) + 1 := abs_lt.2 hs
    rcases le_total ⌈|s|⌉₊ n with hle | hle
    · apply hagree _ _ hle
      have := Nat.le_ceil |s|
      constructor <;> linarith [neg_abs_le s, le_abs_self s]
    · exact (hagree _ _ hle (Ioo_subset_Icc_self hs)).symm
  refine ⟨γ, by simp [γ, hα0], fun t ↦ ?_⟩
  set n := ⌈|t|⌉₊
  have ht : t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    have := Nat.le_ceil |t|
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have heq : γ =ᶠ[𝓝 t] α n :=
    eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hγ n s hs
  exact (hderiv n t ht).congr_of_eventuallyEq heq

end Global

/-! ### The dipole flow -/

/-- The dipole velocity `Y = ∇⊥Ψ = (sin y, -sin x)` on the lift. -/
def dipoleVelocity (p : ℝ × ℝ) : ℝ × ℝ := (sin p.2, -sin p.1)

theorem norm_dipoleVelocity_le (p : ℝ × ℝ) : ‖dipoleVelocity p‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  simp only [dipoleVelocity, Prod.norm_def, Real.norm_eq_abs, abs_neg, NNReal.coe_one]
  exact max_le (abs_sin_le_one _) (abs_sin_le_one _)

theorem lipschitzWith_dipoleVelocity : LipschitzWith 1 dipoleVelocity := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  simp only [dipoleVelocity, Prod.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  refine max_le ((abs_sin_sub_sin_le _ _).trans (le_max_right _ _)) ?_
  rw [show -sin p.1 - -sin q.1 = -(sin p.1 - sin q.1) by ring, abs_neg]
  exact (abs_sin_sub_sin_le _ _).trans (le_max_left _ _)

/-- The global flow of the dipole velocity: `dipoleFlow x 0 = x` and
    `∂ₜ dipoleFlow x t = Y (dipoleFlow x t)`. -/
def dipoleFlow (x : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  Classical.choose (exists_global_solution norm_dipoleVelocity_le lipschitzWith_dipoleVelocity x)

theorem dipoleFlow_zero (x : ℝ × ℝ) : dipoleFlow x 0 = x :=
  (Classical.choose_spec
    (exists_global_solution norm_dipoleVelocity_le lipschitzWith_dipoleVelocity x)).1

theorem hasDerivAt_dipoleFlow (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (dipoleFlow x) (dipoleVelocity (dipoleFlow x t)) t :=
  (Classical.choose_spec
    (exists_global_solution norm_dipoleVelocity_le lipschitzWith_dipoleVelocity x)).2 t

/-- Every global integral curve of the dipole velocity through `x` is the flow. -/
theorem eq_dipoleFlow {γ : ℝ → ℝ × ℝ} {x : ℝ × ℝ} (h0 : γ 0 = x)
    (hγ : ∀ t, HasDerivAt γ (dipoleVelocity (γ t)) t) : γ = dipoleFlow x :=
  ODE_solution_unique_univ (v := fun _ ↦ dipoleVelocity) (s := fun _ ↦ univ) (t₀ := 0)
    (fun _ ↦ lipschitzWith_dipoleVelocity.lipschitzOnWith) (fun t ↦ ⟨hγ t, trivial⟩)
    (fun t ↦ ⟨hasDerivAt_dipoleFlow x t, trivial⟩) (by rw [h0, dipoleFlow_zero])

theorem hasDerivAt_dipoleFlow_fst (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (dipoleFlow x s).1) (sin (dipoleFlow x t).2) t :=
  hasFDerivAt_fst.comp_hasDerivAt (f := dipoleFlow x) t (hasDerivAt_dipoleFlow x t)

theorem hasDerivAt_dipoleFlow_snd (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (dipoleFlow x s).2) (-sin (dipoleFlow x t).1) t :=
  hasFDerivAt_snd.comp_hasDerivAt (f := dipoleFlow x) t (hasDerivAt_dipoleFlow x t)

/-- `Ψ` is conserved by the flow. -/
theorem dipoleLift_dipoleFlow (x : ℝ × ℝ) (t : ℝ) : dipoleLift (dipoleFlow x t) = dipoleLift x := by
  have hd : ∀ s, HasDerivAt (fun s ↦ dipoleLift (dipoleFlow x s)) 0 s := by
    intro s
    have h := ((hasDerivAt_dipoleFlow_fst x s).cos).add ((hasDerivAt_dipoleFlow_snd x s).cos)
    convert h using 1
    · rfl
    · ring
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv)
  rw [hc t 0, dipoleFlow_zero]

/-- The flow property `φ_{s+t} = φ_t ∘ φ_s`. -/
theorem dipoleFlow_add (x : ℝ × ℝ) (s t : ℝ) :
    dipoleFlow x (s + t) = dipoleFlow (dipoleFlow x s) t := by
  have h := eq_dipoleFlow (γ := fun t ↦ dipoleFlow x (s + t)) (x := dipoleFlow x s)
    (by simp) fun t ↦ by
      simpa using (hasDerivAt_dipoleFlow x (s + t)).comp_const_add s t
  exact congrFun h t

/-- A linear map `M` that reverses the velocity, `Y ∘ M = -M ∘ Y`, maps the flow to itself
    with time reversed. -/
theorem dipoleFlow_reverse {M : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hM : ∀ p, dipoleVelocity (M p) = -M (dipoleVelocity p)) (x : ℝ × ℝ) (t : ℝ) :
    dipoleFlow (M x) t = M (dipoleFlow x (-t)) := by
  have h := eq_dipoleFlow (γ := fun t ↦ M (dipoleFlow x (-t))) (x := M x)
    (by simp [dipoleFlow_zero]) fun t ↦ by
      have h1 := (hasDerivAt_dipoleFlow x (-t)).scomp t (hasDerivAt_neg t)
      have h2 := M.hasFDerivAt.comp_hasDerivAt t h1
      convert h2 using 1
      · rfl
      · rw [hM, neg_one_smul, map_neg]
  exact (congrFun h t).symm

/-- In diagonal coordinates the flow is `ȧ = -cos a sin b`. -/
theorem hasDerivAt_diag_fst (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (diagCoord (dipoleFlow x s)).1)
      (-cos (diagCoord (dipoleFlow x t)).1 * sin (diagCoord (dipoleFlow x t)).2) t := by
  have h := ((hasDerivAt_dipoleFlow_fst x t).add (hasDerivAt_dipoleFlow_snd x t)).div_const 2
  convert h using 1
  · rfl
  set p := dipoleFlow x t
  simp only [diagCoord]
  rw [show p.2 = (p.1 + p.2) / 2 - (p.1 - p.2) / 2 by ring,
    show p.1 = (p.1 + p.2) / 2 + (p.1 - p.2) / 2 by ring, sin_add, sin_sub]
  ring_nf

/-- In diagonal coordinates the flow is `ḃ = sin a cos b`. -/
theorem hasDerivAt_diag_snd (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (diagCoord (dipoleFlow x s)).2)
      (sin (diagCoord (dipoleFlow x t)).1 * cos (diagCoord (dipoleFlow x t)).2) t := by
  have h := ((hasDerivAt_dipoleFlow_fst x t).sub (hasDerivAt_dipoleFlow_snd x t)).div_const 2
  convert h using 1
  · rfl
  set p := dipoleFlow x t
  simp only [diagCoord]
  rw [show p.2 = (p.1 + p.2) / 2 - (p.1 - p.2) / 2 by ring,
    show p.1 = (p.1 + p.2) / 2 + (p.1 - p.2) / 2 by ring, sin_add, sin_sub]
  ring_nf

/-- A continuous function that never takes the value `v` and starts below it stays below it. -/
theorem lt_of_forall_ne {f : ℝ → ℝ} (hf : Continuous f) {v : ℝ} (hne : ∀ t, f t ≠ v)
    (h0 : f 0 < v) (t : ℝ) : f t < v := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hf.continuousOn
    (show v ∈ uIcc (f 0) (f t) from mem_uIcc.2 (Or.inl ⟨h0.le, hle⟩))
  exact hne s hs

end NoEmbeddedEigenvalues
