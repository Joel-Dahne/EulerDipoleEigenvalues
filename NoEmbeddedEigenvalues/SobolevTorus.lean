import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import NoEmbeddedEigenvalues.Derivatives

/-!
# Sobolev spaces on the torus

Blueprint: `def:sobolev-torus`, `lem:elliptic-torus`; `lem:sobolev-embedding` (stated).

`Hˢ(𝕋²)` consists of the `g ∈ L²` with `∑ (1 + |k|²)ˢ |ĝ_k|² < ∞`, and derivatives are
the Fourier multipliers `i k_j` (`HasFourierPartial`). On this scale `Δ⁻¹` gains two
derivatives and `∂_j` loses one, with explicit constants.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex

/-- The Sobolev weight `(1 + |k|²)ˢ`. -/
def sobolevWeight (s : ℝ) (k : ℤ × ℤ) : ℝ := (1 + (normSq k : ℝ)) ^ s

/-- `g ∈ Hˢ(𝕋²)`: the weighted coefficients are square summable. -/
def MemSobolev (s : ℝ) (g : L2) : Prop :=
  Summable fun k ↦ sobolevWeight s k * ‖fourierCoeff g k‖ ^ 2

/-- The squared `Hˢ` norm `∑ (1 + |k|²)ˢ |ĝ_k|²`; meaningful when `MemSobolev s g`. -/
def sobolevNormSq (s : ℝ) (g : L2) : ℝ := ∑' k, sobolevWeight s k * ‖fourierCoeff g k‖ ^ 2

theorem normSq_nonneg' (k : ℤ × ℤ) : (0 : ℝ) ≤ normSq k := by
  unfold normSq
  push_cast
  positivity

theorem one_le_one_add_normSq (k : ℤ × ℤ) : (1 : ℝ) ≤ 1 + normSq k := by
  linarith [normSq_nonneg' k]

theorem sobolevWeight_pos (s : ℝ) (k : ℤ × ℤ) : 0 < sobolevWeight s k :=
  Real.rpow_pos_of_pos (by linarith [normSq_nonneg' k]) s

theorem sobolevWeight_zero (k : ℤ × ℤ) : sobolevWeight 0 k = 1 := by
  simp [sobolevWeight]

theorem sobolevWeight_add_one (s : ℝ) (k : ℤ × ℤ) :
    sobolevWeight (s + 1) k = sobolevWeight s k * (1 + normSq k) := by
  unfold sobolevWeight
  rw [Real.rpow_add_one (by linarith [normSq_nonneg' k])]

theorem sobolevWeight_add_two (s : ℝ) (k : ℤ × ℤ) :
    sobolevWeight (s + 2) k = sobolevWeight s k * (1 + normSq k) ^ 2 := by
  rw [show s + 2 = (s + 1) + 1 by ring, sobolevWeight_add_one, sobolevWeight_add_one]
  ring

theorem sobolevWeight_mono {s t : ℝ} (hst : s ≤ t) (k : ℤ × ℤ) :
    sobolevWeight s k ≤ sobolevWeight t k :=
  Real.rpow_le_rpow_of_exponent_le (one_le_one_add_normSq k) hst

/-- Every `L²` function is in `H⁰`. -/
theorem memSobolev_zero (g : L2) : MemSobolev 0 g := by
  simpa [MemSobolev, sobolevWeight_zero] using summable_sq_fourierCoeff g

/-- `Hᵗ ⊆ Hˢ` for `s ≤ t`. -/
theorem MemSobolev.mono {s t : ℝ} {g : L2} (h : MemSobolev t g) (hst : s ≤ t) :
    MemSobolev s g :=
  Summable.of_nonneg_of_le (fun k ↦ by have := sobolevWeight_pos s k; positivity)
    (fun k ↦ mul_le_mul_of_nonneg_right (sobolevWeight_mono hst k) (sq_nonneg _)) h

/-- Every `L²` function is in `Hˢ` for `s ≤ 0`. -/
theorem memSobolev_of_nonpos {s : ℝ} (hs : s ≤ 0) (g : L2) : MemSobolev s g :=
  (memSobolev_zero g).mono hs

theorem fourierCoeff_zero_fun (k : ℤ × ℤ) : fourierCoeff (0 : L2) k = 0 := by
  simpa using fourierCoeff_smul 0 (0 : L2) k

theorem memSobolev_zero_fun (s : ℝ) : MemSobolev s 0 := by
  simp [MemSobolev, fourierCoeff_zero_fun]

theorem MemSobolev.add {s : ℝ} {g h : L2} (hg : MemSobolev s g) (hh : MemSobolev s h) :
    MemSobolev s (g + h) := by
  refine Summable.of_nonneg_of_le (fun k ↦ by have := sobolevWeight_pos s k; positivity)
    (fun k ↦ ?_) ((Summable.add hg hh).mul_left 2)
  have hw := (sobolevWeight_pos s k).le
  rw [fourierCoeff_add]
  have : ‖fourierCoeff g k + fourierCoeff h k‖ ^ 2 ≤
      2 * (‖fourierCoeff g k‖ ^ 2 + ‖fourierCoeff h k‖ ^ 2) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (fourierCoeff g k)
      (fourierCoeff h k)) 2
    nlinarith [sq_nonneg (‖fourierCoeff g k‖ - ‖fourierCoeff h k‖)]
  calc sobolevWeight s k * ‖fourierCoeff g k + fourierCoeff h k‖ ^ 2
      ≤ sobolevWeight s k * (2 * (‖fourierCoeff g k‖ ^ 2 + ‖fourierCoeff h k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this hw
    _ = 2 * (sobolevWeight s k * ‖fourierCoeff g k‖ ^ 2 +
        sobolevWeight s k * ‖fourierCoeff h k‖ ^ 2) := by ring

theorem MemSobolev.smul {s : ℝ} {g : L2} (hg : MemSobolev s g) (c : ℂ) :
    MemSobolev s (c • g) := by
  simpa [MemSobolev, fourierCoeff_smul, norm_mul, mul_pow, mul_left_comm] using
    hg.mul_left (‖c‖ ^ 2)

/-- `Hˢ(𝕋²)` as a complex subspace of `L²`. -/
def sobolevSubmodule (s : ℝ) : Submodule ℂ L2 where
  carrier := {g | MemSobolev s g}
  add_mem' := MemSobolev.add
  zero_mem' := memSobolev_zero_fun s
  smul_mem' c _ hg := MemSobolev.smul hg c

/-! ### Elliptic regularity -/

/-- Coefficientwise, `Δ⁻¹` gains two derivatives with constant `4`. -/
theorem sobolevWeight_mul_fourierCoeff_invLap_le (s : ℝ) (ω : L2) (k : ℤ × ℤ) :
    sobolevWeight (s + 2) k * ‖fourierCoeff (invLap ω) k‖ ^ 2 ≤
      4 * (sobolevWeight s k * ‖fourierCoeff ω k‖ ^ 2) := by
  have hw := (sobolevWeight_pos s k).le
  rw [fourierCoeff_invLap]
  split_ifs with hk
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · have hpos : (0 : ℤ) < normSq k := normSq_pos k hk
    have hn : (1 : ℝ) ≤ normSq k := by exact_mod_cast hpos
    have hn0 : (0 : ℝ) < normSq k := by linarith
    rw [norm_div, norm_neg, Complex.norm_intCast, abs_of_pos hn0, sobolevWeight_add_two, div_pow]
    have hq : (1 + (normSq k : ℝ)) ^ 2 ≤ 4 * (normSq k : ℝ) ^ 2 := by nlinarith
    have hc := sq_nonneg ‖fourierCoeff ω k‖
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    calc sobolevWeight s k * (1 + (normSq k : ℝ)) ^ 2 * ‖fourierCoeff ω k‖ ^ 2
        = (sobolevWeight s k * ‖fourierCoeff ω k‖ ^ 2) * (1 + (normSq k : ℝ)) ^ 2 := by ring
      _ ≤ (sobolevWeight s k * ‖fourierCoeff ω k‖ ^ 2) * (4 * (normSq k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring

/-- `Δ⁻¹ : Hˢ → Hˢ⁺²`. -/
theorem MemSobolev.invLap {s : ℝ} {ω : L2} (h : MemSobolev s ω) :
    MemSobolev (s + 2) (invLap ω) :=
  Summable.of_nonneg_of_le (fun k ↦ by have := sobolevWeight_pos (s + 2) k; positivity)
    (sobolevWeight_mul_fourierCoeff_invLap_le s ω) (h.mul_left 4)

/-- `Δ⁻¹ : Hˢ → Hˢ⁺²` is bounded: `‖Δ⁻¹ω‖²_{s+2} ≤ 4 ‖ω‖²_s`. -/
theorem sobolevNormSq_invLap_le {s : ℝ} {ω : L2} (h : MemSobolev s ω) :
    sobolevNormSq (s + 2) (invLap ω) ≤ 4 * sobolevNormSq s ω := by
  rw [sobolevNormSq, sobolevNormSq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (sobolevWeight_mul_fourierCoeff_invLap_le s ω) h.invLap
    (h.mul_left 4)

/-- The stream function `ψ = Δ⁻¹ω` of any `ω ∈ L²` is in `H²`. -/
theorem memSobolev_two_invLap (ω : L2) : MemSobolev 2 (invLap ω) := by
  simpa using (memSobolev_zero ω).invLap

/-! ### Derivatives -/

theorem frequencyComponent_sq_le (k : ℤ × ℤ) (j : Fin 2) :
    ((frequencyComponent k j : ℤ) : ℝ) ^ 2 ≤ normSq k := by
  unfold frequencyComponent normSq
  split_ifs <;> push_cast <;> nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]

theorem norm_sq_fourierCoeff_of_hasFourierPartial {j : Fin 2} {g h : L2}
    (hd : HasFourierPartial j g h) (k : ℤ × ℤ) :
    ‖fourierCoeff h k‖ ^ 2 = ((frequencyComponent k j : ℤ) : ℝ) ^ 2 * ‖fourierCoeff g k‖ ^ 2 := by
  rw [hd k, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow, sq_abs]

/-- Coefficientwise, `∂_j` loses one derivative with constant `1`. -/
theorem sobolevWeight_mul_fourierCoeff_partial_le (s : ℝ) {j : Fin 2} {g h : L2}
    (hd : HasFourierPartial j g h) (k : ℤ × ℤ) :
    sobolevWeight s k * ‖fourierCoeff h k‖ ^ 2 ≤
      sobolevWeight (s + 1) k * ‖fourierCoeff g k‖ ^ 2 := by
  rw [norm_sq_fourierCoeff_of_hasFourierPartial hd, sobolevWeight_add_one]
  have hw := (sobolevWeight_pos s k).le
  have hc := sq_nonneg ‖fourierCoeff g k‖
  have hq := frequencyComponent_sq_le k j
  have : ((frequencyComponent k j : ℤ) : ℝ) ^ 2 ≤ 1 + normSq k := by linarith
  calc sobolevWeight s k * (((frequencyComponent k j : ℤ) : ℝ) ^ 2 * ‖fourierCoeff g k‖ ^ 2)
      = (sobolevWeight s k * ‖fourierCoeff g k‖ ^ 2) *
          ((frequencyComponent k j : ℤ) : ℝ) ^ 2 := by ring
    _ ≤ (sobolevWeight s k * ‖fourierCoeff g k‖ ^ 2) * (1 + normSq k) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- `∂_j : Hˢ⁺¹ → Hˢ`. -/
theorem MemSobolev.of_hasFourierPartial {s : ℝ} {j : Fin 2} {g h : L2}
    (hg : MemSobolev (s + 1) g) (hd : HasFourierPartial j g h) : MemSobolev s h :=
  Summable.of_nonneg_of_le (fun k ↦ by have := sobolevWeight_pos s k; positivity)
    (sobolevWeight_mul_fourierCoeff_partial_le s hd) hg

/-- `∂_j : Hˢ⁺¹ → Hˢ` is bounded: `‖∂_j g‖²_s ≤ ‖g‖²_{s+1}`. -/
theorem sobolevNormSq_partial_le {s : ℝ} {j : Fin 2} {g h : L2}
    (hg : MemSobolev (s + 1) g) (hd : HasFourierPartial j g h) :
    sobolevNormSq s h ≤ sobolevNormSq (s + 1) g :=
  Summable.tsum_le_tsum (sobolevWeight_mul_fourierCoeff_partial_le s hd)
    (hg.of_hasFourierPartial hd) hg

/-- Functions in `H¹` have both Fourier partial derivatives in `L²`. -/
theorem MemSobolev.exists_hasFourierPartial {g : L2} (hg : MemSobolev 1 g) (j : Fin 2) :
    ∃ h, HasFourierPartial j g h := by
  have hs : Summable fun k ↦ ‖(I * frequencyComponent k j) * fourierCoeff g k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun k ↦ ?_) hg
    have hq := frequencyComponent_sq_le k j
    calc ‖(I * frequencyComponent k j) * fourierCoeff g k‖ ^ 2
        = ((frequencyComponent k j : ℤ) : ℝ) ^ 2 * ‖fourierCoeff g k‖ ^ 2 := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow, sq_abs]
      _ ≤ (1 + normSq k) * ‖fourierCoeff g k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = sobolevWeight 1 k * ‖fourierCoeff g k‖ ^ 2 := by rw [sobolevWeight, Real.rpow_one]
  obtain ⟨h, hh⟩ := exists_fourierCoeff _ hs
  exact ⟨h, fun k ↦ hh k⟩

/-- `g ∈ Hˢ⁺¹` if `g` and both its Fourier partial derivatives are in `Hˢ`. -/
theorem memSobolev_add_one_of_hasFourierPartial {s : ℝ} {g h₀ h₁ : L2} (hg : MemSobolev s g)
    (hd₀ : HasFourierPartial 0 g h₀) (hd₁ : HasFourierPartial 1 g h₁)
    (h₀s : MemSobolev s h₀) (h₁s : MemSobolev s h₁) : MemSobolev (s + 1) g := by
  refine (Summable.add (Summable.add hg h₀s) h₁s).congr fun k ↦ ?_
  rw [norm_sq_fourierCoeff_of_hasFourierPartial hd₀,
    norm_sq_fourierCoeff_of_hasFourierPartial hd₁, sobolevWeight_add_one]
  simp only [frequencyComponent, normSq]
  push_cast
  ring

/-! ### Sobolev embeddings (`lem:sobolev-embedding`, stated) -/

section Embedding

open MeasureTheory
open scoped NNReal ENNReal

/-- `H²(𝕋²) ⊂ C^{0,α}(𝕋²)` for every `α < 1`, continuously. -/
theorem exists_holderWith_of_memSobolev_two {α : ℝ≥0} (hα : α < 1) :
    ∃ C : ℝ≥0, ∀ g : L2, MemSobolev 2 g → ∃ u : Torus → ℂ, (g : Torus → ℂ) =ᵐ[volume] u ∧
      HolderWith (C * Real.toNNReal √(sobolevNormSq 2 g)) α u ∧
      ∀ t, ‖u t‖ ≤ C * √(sobolevNormSq 2 g) := by
  sorry

/-- `H¹(𝕋²) ⊂ Lᵖ(𝕋²)` for every `p < ∞`, continuously. -/
theorem memLp_of_memSobolev_one {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    ∃ C : ℝ, ∀ g : L2, MemSobolev 1 g → MemLp (g : Torus → ℂ) p ∧
      eLpNorm (g : Torus → ℂ) p volume ≤ ENNReal.ofReal (C * √(sobolevNormSq 1 g)) := by
  sorry

end Embedding

end NoEmbeddedEigenvalues
