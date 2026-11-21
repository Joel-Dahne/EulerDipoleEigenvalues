module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The logarithmic-cylinder symbol

The variable `ξ` is angular Fourier frequency in the noncompact logarithmic
coordinate, so the derivative symbol is `I * ξ` (not `2 * π * I * ξ`).
A discrete nonresonance condition gives a uniform elliptic bound, including
large angular modes and large continuous frequencies. This module concerns
spectral functions; it does not identify them with physical weak derivatives.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Symbol of `(∂t - a)² + ∂θ²` at angular frequencies `(ξ,m)`. -/
def cylinderSymbol (a ξ : ℝ) (m : ℕ) : ℂ :=
  (Complex.I * (ξ : ℂ) - (a : ℂ)) ^ 2 - (m : ℂ) ^ 2

/-- Exact factorization of the squared symbol, before any norm estimate. -/
theorem cylinderSymbol_norm_sq (a ξ : ℝ) (m : ℕ) :
    ‖cylinderSymbol a ξ m‖ ^ 2 =
      (ξ ^ 2 + (a - (m : ℝ)) ^ 2) * (ξ ^ 2 + (a + (m : ℝ)) ^ 2) := by
  rw [Complex.sq_norm]
  simp [cylinderSymbol, Complex.normSq_apply, pow_two]
  ring

/-- Avoiding a subset of natural frequencies gives a uniform positive gap. -/
theorem exists_uniform_nat_frequency_gap {a : ℝ} {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ m ∈ M, δ ≤ |a - (m : ℝ)| := by
  classical
  let S := Finset.range (Nat.ceil a + 1)
  have hS : S.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let b : ℕ → ℝ := fun m ↦ if m ∈ M then |a - (m : ℝ)| else 1
  have hb (m : ℕ) : 0 < b m := by
    dsimp only [b]
    split_ifs with hm
    · exact abs_pos.mpr (sub_ne_zero.mpr (hgap m hm))
    · norm_num
  let δ := min 1 (S.inf' hS b)
  have hδ : 0 < δ := lt_min zero_lt_one ((Finset.lt_inf'_iff hS).mpr fun m _ ↦ hb m)
  refine ⟨δ, hδ, min_le_left _ _, fun m hm ↦ ?_⟩
  by_cases hsmall : m < Nat.ceil a + 1
  · have he := (min_le_right 1 (S.inf' hS b)).trans
      (Finset.inf'_le b (Finset.mem_range.mpr hsmall : m ∈ S))
    simpa only [b, hm, ite_true] using he
  · have hn : Nat.ceil a + 1 ≤ m := by omega
    have hn' : (Nat.ceil a : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hn
    have ha := Nat.le_ceil a
    have hlarge : 1 ≤ |a - (m : ℝ)| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact (min_le_left _ _).trans hlarge

/-- Uniform order-two ellipticity on any nonresonant subset of angular modes. -/
theorem cylinderSymbol_elliptic_bound {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ m ∈ M, ∀ ξ : ℝ,
      1 + ξ ^ 2 + (m : ℝ) ^ 2 ≤ B * ‖cylinderSymbol a ξ m‖ := by
  obtain ⟨δ, hδ, hδone, hδgap⟩ := exists_uniform_nat_frequency_gap hgap
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδsqone : δ ^ 2 ≤ 1 := by nlinarith
  let K := 3 + 2 * a ^ 2
  have hK : 1 ≤ K := by dsimp only [K]; nlinarith [sq_nonneg a]
  let B := K / δ ^ 2
  have hB : 1 ≤ B := (le_div_iff₀ hδsq).mpr (by nlinarith)
  refine ⟨B, hB, fun m hm ξ ↦ ?_⟩
  have hd : δ ^ 2 ≤ (a - (m : ℝ)) ^ 2 := by
    have hh := (sq_le_sq₀ hδ.le (abs_nonneg (a - (m : ℝ)))).mpr (hδgap m hm)
    simpa only [sq_abs] using hh
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  let w := 1 + ξ ^ 2 + (m : ℝ) ^ 2
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hf : 0 ≤ ξ ^ 2 + (a - (m : ℝ)) ^ 2 := by positivity
  have hlarge : w ≤ ξ ^ 2 + (a + (m : ℝ)) ^ 2 := by
    dsimp only [w]
    nlinarith [mul_nonneg (by linarith : 0 ≤ a) hm0]
  have hmm : (m : ℝ) ^ 2 ≤ 2 * a ^ 2 + 2 * (a - (m : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (2 * a - (m : ℝ))]
  have hsmall : δ ^ 2 * w ≤ K * (ξ ^ 2 + (a - (m : ℝ)) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hmm (sq_nonneg δ)
    have h2 := mul_le_mul_of_nonneg_right hd (sq_nonneg a)
    have h3 := mul_le_mul_of_nonneg_right hδsqone (sq_nonneg (a - (m : ℝ)))
    have h4 := mul_le_mul_of_nonneg_right hδsqone (sq_nonneg ξ)
    have h5 := mul_nonneg (sq_nonneg a) (sq_nonneg ξ)
    dsimp only [w, K]
    nlinarith only [h1, h2, h3, h4, h5, hd, sq_nonneg ξ]
  have hprod : δ ^ 2 * w ^ 2 ≤ K * ‖cylinderSymbol a ξ m‖ ^ 2 := by
    calc
      δ ^ 2 * w ^ 2 = (δ ^ 2 * w) * w := by ring
      _ ≤ (K * (ξ ^ 2 + (a - (m : ℝ)) ^ 2)) * w :=
        mul_le_mul_of_nonneg_right hsmall hw
      _ ≤ (K * (ξ ^ 2 + (a - (m : ℝ)) ^ 2)) *
          (ξ ^ 2 + (a + (m : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hlarge (mul_nonneg (by linarith) hf)
      _ = K * ‖cylinderSymbol a ξ m‖ ^ 2 := by rw [cylinderSymbol_norm_sq]; ring
  have hs : w ^ 2 ≤ B * ‖cylinderSymbol a ξ m‖ ^ 2 := by
    dsimp only [B]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hδsq).mpr (by nlinarith only [hprod])
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hBB (sq_nonneg ‖cylinderSymbol a ξ m‖)
  have hn := norm_nonneg (cylinderSymbol a ξ m)
  have hBn : 0 ≤ B * ‖cylinderSymbol a ξ m‖ := mul_nonneg (by linarith) hn
  nlinarith only [hs, hh, hw, hBn]

/-- Nonresonance rules out zeros of the symbol at every real frequency. -/
theorem cylinderSymbol_ne_zero {a ξ : ℝ} (ha : 0 < a) {m : ℕ}
    (hgap : a ≠ (m : ℝ)) : cylinderSymbol a ξ m ≠ 0 := by
  have h1 : 0 < ξ ^ 2 + (a - (m : ℝ)) ^ 2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr hgap))
  have h2 : 0 < ξ ^ 2 + (a + (m : ℝ)) ^ 2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)))
  have hh : 0 < ‖cylinderSymbol a ξ m‖ ^ 2 := by
    rw [cylinderSymbol_norm_sq]
    exact mul_pos h1 h2
  intro he
  simp only [he, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), lt_self_iff_false] at hh

/-- The order-two spectral Sobolev weight. -/
def cylinderSobolevWeight (p : ℝ × ℕ) : ℝ := 1 + p.1 ^ 2 + (p.2 : ℝ) ^ 2

/-- The spectral Sobolev weight never vanishes. -/
theorem one_le_cylinderSobolevWeight (p : ℝ × ℕ) : 1 ≤ cylinderSobolevWeight p := by
  dsimp only [cylinderSobolevWeight]
  nlinarith [sq_nonneg p.1, sq_nonneg (p.2 : ℝ)]

theorem measurable_cylinderSymbol (a : ℝ) :
    Measurable (fun p : ℝ × ℕ ↦ cylinderSymbol a p.1 p.2) := by
  have hx := Complex.measurable_ofReal.comp (measurable_fst : Measurable (Prod.fst : ℝ × ℕ → ℝ))
  have hm := (measurable_of_countable (fun n : ℕ ↦ (n : ℂ))).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℕ → ℕ))
  exact ((measurable_const.mul hx).sub measurable_const).pow_const 2 |>.sub (hm.pow_const 2)

theorem measurable_cylinderSobolevWeight : Measurable cylinderSobolevWeight := by
  have hm := (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × ℕ → ℕ))
  exact (measurable_const.add (measurable_fst.pow_const 2)).add (hm.pow_const 2)

/-- A genuine spectral L2 inverse with two-derivative weight and a uniform norm
bound. The measure may be the product spectral measure restricted to the allowed
modes; no physical-space Fourier or weak-derivative identification is assumed. -/
theorem cylinder_spectral_inverse {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (μ : Measure (ℝ × ℕ)),
      (∀ᵐ p ∂μ, p.2 ∈ M) → ∀ G : ℝ × ℕ → ℂ, MemLp G 2 μ →
      let V := fun p ↦ G p / cylinderSymbol a p.1 p.2
      MemLp V 2 μ ∧
      MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ ∧
      (∀ᵐ p ∂μ, cylinderSymbol a p.1 p.2 * V p = G p) ∧
      eLpNorm (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ ≤
        ENNReal.ofReal B * eLpNorm G 2 μ := by
  obtain ⟨B, hB, hbound⟩ := cylinderSymbol_elliptic_bound ha hgap
  refine ⟨B, hB, fun μ hM G hG ↦ ?_⟩
  let V := fun p ↦ G p / cylinderSymbol a p.1 p.2
  have hVm : AEStronglyMeasurable V μ :=
    (hG.aemeasurable.div (measurable_cylinderSymbol a).aemeasurable).aestronglyMeasurable
  have hWm : AEStronglyMeasurable
      (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) μ :=
    (Complex.measurable_ofReal.comp measurable_cylinderSobolevWeight).aestronglyMeasurable.mul hVm
  have hpoint : ∀ᵐ p ∂μ,
      ‖(cylinderSobolevWeight p : ℂ) * V p‖ ≤ B * ‖G p‖ := by
    filter_upwards [hM] with p hp
    have hz := cylinderSymbol_ne_zero (by linarith : 0 < a) (hgap p.2 hp) (ξ := p.1)
    have hn := norm_pos_iff.mpr hz
    have hw := (one_le_cylinderSobolevWeight p).trans' zero_le_one
    dsimp only [V]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
      ← mul_div_assoc]
    apply (div_le_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_right (hbound p.2 hp p.1) (norm_nonneg (G p))
    dsimp only [cylinderSobolevWeight]
    nlinarith only [hh]
  have hWV : MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ :=
    hG.of_le_mul hWm hpoint
  have hV : MemLp V 2 μ := by
    apply hWV.of_le_mul hVm (c := 1)
    exact Filter.Eventually.of_forall fun p ↦ by
      rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((one_le_cylinderSobolevWeight p).trans' zero_le_one)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_cylinderSobolevWeight p) (norm_nonneg (V p))
  refine ⟨hV, hWV, ?_, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hWm hpoint 2⟩
  filter_upwards [hM] with p hp
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (cylinderSymbol_ne_zero (by linarith) (hgap p.2 hp))

end NoEmbeddedEigenvalues
