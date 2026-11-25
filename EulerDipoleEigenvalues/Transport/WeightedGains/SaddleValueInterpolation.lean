module

public import EulerDipoleEigenvalues.Transport.PeriodicComparison.GoodWindows

/-!
# Smooth interpolation of the four cell-saddle values

Blueprint: `lem:saddle-value-interpolation`.

Quadratic coordinate polynomials interpolate arbitrary values at (±π,0)
and (0,±π). No cutoff, neighbourhood size or periodicity is required.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open Set
open scoped ContDiff

/-- A lifted saddle in the closed positive cell is one of its four corners. -/
theorem eq_corner_of_mem_saddleSet_closure_cellSquare {p : ℝ × ℝ}
    (hp : p ∈ saddleSet) (hc : p ∈ closure cellSquare) :
    p = (Real.pi, 0) ∨ p = (-Real.pi, 0) ∨
      p = (0, Real.pi) ∨ p = (0, -Real.pi) := by
  have hd : |(diagCoord p).1| ≤ Real.pi / 2 ∧ |(diagCoord p).2| ≤ Real.pi / 2 := by
    have hsub : cellSquare ⊆ {q : ℝ × ℝ |
        |(diagCoord q).1| ≤ Real.pi / 2 ∧ |(diagCoord q).2| ≤ Real.pi / 2} :=
      fun q hq ↦ ⟨hq.1.le, hq.2.le⟩
    have h1 : IsClosed {q : ℝ × ℝ | |(diagCoord q).1| ≤ Real.pi / 2} :=
      isClosed_le (by unfold diagCoord; fun_prop) continuous_const
    have h2 : IsClosed {q : ℝ × ℝ | |(diagCoord q).2| ≤ Real.pi / 2} :=
      isClosed_le (by unfold diagCoord; fun_prop) continuous_const
    exact closure_minimal hsub (h1.inter h2) hc
  rcases hp with ⟨m, n, hodd, rfl⟩
  have hb (s : ℝ) (hs : |s * Real.pi / 2| ≤ Real.pi / 2) : |s| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos] at hs
    norm_num at hs
    have hm : |s| * Real.pi ≤ 1 * Real.pi := by linarith only [hs]
    exact le_of_mul_le_mul_right hm Real.pi_pos
  have hsR : |(m : ℝ) + (n : ℝ)| ≤ 1 := hb _ (by
    convert hd.1 using 1
    congr 1
    dsimp only [diagCoord]
    ring)
  have hdR : |(m : ℝ) - (n : ℝ)| ≤ 1 := hb _ (by
    convert hd.2 using 1
    congr 1
    dsimp only [diagCoord]
    ring)
  have hsZ : (-1 : ℤ) ≤ m + n ∧ m + n ≤ 1 := by exact_mod_cast abs_le.mp hsR
  have hdZ : (-1 : ℤ) ≤ m - n ∧ m - n ≤ 1 := by exact_mod_cast abs_le.mp hdR
  rcases hodd with ⟨j, hj⟩
  have hm : (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
      (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by omega
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- A globally smooth quadratic profile can match any prescribed raw values
at all saddles of the closed cell, independently of their representatives elsewhere. -/
theorem exists_smooth_saddle_interpolant (g : ℝ × ℝ → ℂ) :
    ∃ P : ℝ × ℝ → ℂ, ContDiff ℝ ∞ P ∧
      ∀ q ∈ saddleSet, q ∈ closure cellSquare → P q = g q := by
  let P : ℝ × ℝ → ℂ := fun p ↦
    g (Real.pi, 0) * ((p.1 : ℂ) * ((p.1 : ℂ) + Real.pi) / (2 * (Real.pi : ℂ) ^ 2)) +
    g (-Real.pi, 0) * ((p.1 : ℂ) * ((p.1 : ℂ) - Real.pi) / (2 * (Real.pi : ℂ) ^ 2)) +
    g (0, Real.pi) * ((p.2 : ℂ) * ((p.2 : ℂ) + Real.pi) / (2 * (Real.pi : ℂ) ^ 2)) +
    g (0, -Real.pi) * ((p.2 : ℂ) * ((p.2 : ℂ) - Real.pi) / (2 * (Real.pi : ℂ) ^ 2))
  have hx : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hy : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  refine ⟨P, by dsimp only [P]; fun_prop, ?_⟩
  intro q hq hqc
  rcases eq_corner_of_mem_saddleSet_closure_cellSquare hq hqc with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [P]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring

end EulerDipoleEigenvalues
