import NoEmbeddedEigenvalues.Analysis.TorusSobolev.TorusElliptic

/-! # Continuous representatives of torus H² functions -/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex

/-! ### The continuous representative of an `H²` function -/

section ContinuousRep

open MeasureTheory

/-- The Fourier series `∑ ĝ_k e_k`, summed in the sup norm. For `g ∈ H²` it converges
    absolutely and represents `g` (`continuousRep_toLp`); otherwise it is the junk value `0`. -/
def continuousRep (g : L2) : C(Torus, ℂ) := ∑' k, fourierCoeff g k • char k

theorem norm_char_le (k : ℤ × ℤ) : ‖char k‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun t ↦ ?_
  change ‖fourier k.1 t.1 * fourier k.2 t.2‖ ≤ 1
  rw [norm_mul]
  have h1 := (fourier k.1 : C(AddCircle (2 * Real.pi), ℂ)).norm_coe_le_norm t.1
  have h2 := (fourier k.2 : C(AddCircle (2 * Real.pi), ℂ)).norm_coe_le_norm t.2
  rw [fourier_norm] at h1 h2
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `∑_ℤ (1 + n²)⁻¹ < ∞`. -/
theorem summable_inv_one_add_sq : Summable fun n : ℤ ↦ (1 + (n : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.2 one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ hpos (by linarith)

/-- `∑_{ℤ²} (1 + |k|²)⁻² < ∞`, the reason why `H² ⊂ C⁰` in two dimensions. -/
theorem summable_inv_sobolevWeight_two : Summable fun k : ℤ × ℤ ↦ (sobolevWeight 2 k)⁻¹ := by
  refine (summable_inv_one_add_sq.mul_of_nonneg summable_inv_one_add_sq (fun _ ↦ by positivity)
    (fun _ ↦ by positivity)).of_nonneg_of_le (fun k ↦ (inv_pos.2 (sobolevWeight_pos 2 k)).le)
    fun k ↦ ?_
  have ha : (0 : ℝ) ≤ (k.1 : ℝ) ^ 2 := sq_nonneg _
  have hb : (0 : ℝ) ≤ (k.2 : ℝ) ^ 2 := sq_nonneg _
  rw [sobolevWeight, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← mul_inv]
  apply inv_anti₀ (by positivity)
  simp only [normSq]
  push_cast
  nlinarith [mul_nonneg ha hb]

/-- For `g ∈ H²` the Fourier coefficients are absolutely summable:
    `|ĝ_k| ≤ ½((1 + |k|²)² |ĝ_k|² + (1 + |k|²)⁻²)`. -/
theorem MemSobolev.summable_norm_fourierCoeff {g : L2} (hg : MemSobolev 2 g) :
    Summable fun k ↦ ‖fourierCoeff g k‖ := by
  refine (((show Summable _ from hg).add summable_inv_sobolevWeight_two).div_const 2)
    |>.of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun k ↦ ?_
  have hw := sobolevWeight_pos 2 k
  set w := sobolevWeight 2 k
  set c := ‖fourierCoeff g k‖
  rw [le_div_iff₀ two_pos]
  have : 0 ≤ (w * c - 1) ^ 2 := sq_nonneg _
  have h : w * (c * 2) ≤ w * (w * c ^ 2 + w⁻¹) := by
    rw [mul_add, mul_inv_cancel₀ hw.ne']
    nlinarith
  exact le_of_mul_le_mul_left h hw

theorem MemSobolev.summable_fourier_char {g : L2} (hg : MemSobolev 2 g) :
    Summable fun k ↦ fourierCoeff g k • char k :=
  Summable.of_norm_bounded hg.summable_norm_fourierCoeff fun k ↦ by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_char_le k)

/-- For `g ∈ H²` the continuous Fourier sum is a representative of `g`. -/
theorem continuousRep_toLp {g : L2} (hg : MemSobolev 2 g) :
    ContinuousMap.toLp 2 volume ℂ (continuousRep g) = g := by
  have h := (hg.summable_fourier_char.hasSum).mapL (ContinuousMap.toLp 2 volume ℂ)
  simp only [map_smul] at h
  exact h.unique (hasSum_fourier_series g)

theorem coeFn_eq_continuousRep {g : L2} (hg : MemSobolev 2 g) :
    (g : Torus → ℂ) =ᵐ[volume] continuousRep g := by
  have := ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (continuousRep g)
  rwa [continuousRep_toLp hg] at this

/-- The stream function `ψ = Δ⁻¹ω` of every `ω ∈ L²` has the continuous representative `ψ̃`. -/
theorem coeFn_invLap_eq_continuousRep (ω : L2) :
    (invLap ω : Torus → ℂ) =ᵐ[volume] continuousRep (invLap ω) :=
  coeFn_eq_continuousRep (memSobolev_two_invLap ω)

end ContinuousRep

end NoEmbeddedEigenvalues
