import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.PSeries
import NoEmbeddedEigenvalues.Setup.Derivatives

/-! # Fourier Sobolev spaces on the torus -/

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

end NoEmbeddedEigenvalues
