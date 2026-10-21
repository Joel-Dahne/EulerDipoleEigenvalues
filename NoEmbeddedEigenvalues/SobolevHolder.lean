import NoEmbeddedEigenvalues.SobolevTorus
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Hölder Sobolev embedding on the torus

Blueprint: `lem:sobolev-holder`.

The Fourier sum is the existing continuous representative. Character increments
are bounded by interpolation between their uniform and Lipschitz bounds;
weighted Cauchy–Schwarz closes the estimate for every exponent below one.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory
open scoped Topology NNReal

/-- The one-dimensional lattice weight is summable above the critical decay. -/
theorem summable_one_add_int_sq_rpow {s : ℝ} (hs : s < -(1 / 2 : ℝ)) :
    Summable (fun n : ℤ ↦ (1 + (n : ℝ) ^ 2) ^ s) := by
  have hp : 1 < -(2 * s) := by linarith
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hp) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    _ ≤ ((n : ℝ) ^ 2) ^ s :=
      Real.rpow_le_rpow_of_nonpos hn2 (by linarith) (by linarith)
    _ = |(n : ℝ)| ^ (-(-(2 * s))) := by
      rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg _) 2]
      congr 1
      ring

/-- In two dimensions, `(1 + |k|²)^s` is summable whenever `s < -1`. -/
theorem summable_sobolevWeight_of_lt_neg_one {s : ℝ} (hs : s < -1) :
    Summable (sobolevWeight s) := by
  have hhalf : s / 2 < -(1 / 2 : ℝ) := by linarith
  have hsum := summable_one_add_int_sq_rpow hhalf
  refine (hsum.mul_of_nonneg hsum (fun _ ↦ by positivity) (fun _ ↦ by positivity)).of_nonneg_of_le
    (fun k ↦ (sobolevWeight_pos s k).le) (fun k ↦ ?_)
  have hq : 0 < 1 + (normSq k : ℝ) := by linarith [normSq_nonneg' k]
  have hprod : (1 + (k.1 : ℝ) ^ 2) * (1 + (k.2 : ℝ) ^ 2) ≤
      (1 + (normSq k : ℝ)) ^ 2 := by
    simp only [normSq]
    push_cast
    nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ),
      mul_nonneg (sq_nonneg (k.1 : ℝ)) (sq_nonneg (k.2 : ℝ))]
  calc
    sobolevWeight s k = ((1 + (normSq k : ℝ)) ^ 2) ^ (s / 2) := by
      rw [← Real.rpow_natCast_mul hq.le 2]
      congr 1
      ring
    _ ≤ ((1 + (k.1 : ℝ) ^ 2) * (1 + (k.2 : ℝ) ^ 2)) ^ (s / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hprod (by linarith)
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

/-- Weighted absolute Fourier summability and its quantitative Cauchy–Schwarz bound. -/
theorem MemSobolev.weighted_fourier_bound {g : L2} (hg : MemSobolev 2 g)
    {α : ℝ} (hα : α < 1) :
    Summable (fun k ↦ ‖fourierCoeff g k‖ * sobolevWeight (α / 2) k) ∧
      (∑' k, ‖fourierCoeff g k‖ * sobolevWeight (α / 2) k) ≤
        √(sobolevNormSq 2 g) * √(∑' k, sobolevWeight (α - 2) k) := by
  let f := fun k ↦ (1 + (normSq k : ℝ)) * ‖fourierCoeff g k‖
  let v := fun k ↦ sobolevWeight (α / 2 - 1) k
  have hf : ∀ k, 0 ≤ f k := fun k ↦ mul_nonneg (by linarith [normSq_nonneg' k]) (norm_nonneg _)
  have hv : ∀ k, 0 ≤ v k := fun k ↦ (sobolevWeight_pos _ k).le
  have hf2 : ∀ k, f k ^ (2 : ℝ) = sobolevWeight 2 k * ‖fourierCoeff g k‖ ^ 2 := by
    intro k
    simp only [f, Real.rpow_two, mul_pow, sobolevWeight]
  have hv2 : ∀ k, v k ^ (2 : ℝ) = sobolevWeight (α - 2) k := by
    intro k
    dsimp only [v, sobolevWeight]
    rw [← Real.rpow_mul (by linarith [normSq_nonneg' k])]
    congr 1
    ring
  have hfv : ∀ k, f k * v k = ‖fourierCoeff g k‖ * sobolevWeight (α / 2) k := by
    intro k
    have hq : 0 < 1 + (normSq k : ℝ) := by linarith [normSq_nonneg' k]
    dsimp only [f, v, sobolevWeight]
    calc
      _ = ‖fourierCoeff g k‖ * ((1 + (normSq k : ℝ)) ^ (α / 2 - 1) *
          (1 + (normSq k : ℝ))) := by ring
      _ = _ := by rw [← Real.rpow_add_one hq.ne']; congr 2; ring
  have hfs : Summable (fun k ↦ f k ^ (2 : ℝ)) := by simp_rw [hf2]; exact hg
  have hvs : Summable (fun k ↦ v k ^ (2 : ℝ)) := by
    simp_rw [hv2]
    exact summable_sobolevWeight_of_lt_neg_one (by linarith)
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf hv hfs hvs
  simpa only [hfv, hf2, hv2, ← Real.sqrt_eq_rpow, sobolevNormSq] using h

/-- The circle character has the expected unit angular speed. The quotient norm
is the infimum over real representatives, so the real exponential estimate descends. -/
theorem norm_fourier_sub_one_le (n : ℤ) (x : AddCircle (2 * Real.pi)) :
    ‖fourier (T := 2 * Real.pi) n x - 1‖ ≤ |(n : ℝ)| * ‖x‖ := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnpos : 0 < |(n : ℝ)| := abs_pos.2 hn0
  suffices h : ‖fourier (T := 2 * Real.pi) n x - 1‖ / |(n : ℝ)| ≤ ‖x‖ by
    nlinarith [(div_le_iff₀ hnpos).1 h]
  apply QuotientAddGroup.le_norm_iff.2
  intro t ht
  rw [← ht, div_le_iff₀ hnpos, Real.norm_eq_abs]
  have he : fourier (T := 2 * Real.pi) n (t : AddCircle (2 * Real.pi)) = exp (I * (n * t)) := by
    rw [fourier_coe_apply]
    congr 1
    field_simp
    push_cast
    ring
  rw [he]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (n : ℝ) * t)
  simpa only [Complex.ofReal_mul, Complex.ofReal_intCast, Real.norm_eq_abs, abs_mul, mul_comm]
    using hb

/-- Torus characters have pointwise norm one. -/
theorem norm_char_apply (k : ℤ × ℤ) (p : Torus) : ‖char k p‖ = 1 := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change ‖fourier k.1 p.1 * fourier k.2 p.2‖ = 1
  simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- Increment bound at the identity in terms of the coordinate norms. -/
theorem norm_char_sub_one_le (k : ℤ × ℤ) (p : Torus) :
    ‖char k p - 1‖ ≤ |(k.1 : ℝ)| * ‖p.1‖ + |(k.2 : ℝ)| * ‖p.2‖ := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  let z := fourier (T := 2 * Real.pi) k.1 p.1
  let w := fourier (T := 2 * Real.pi) k.2 p.2
  have hw : ‖w‖ = 1 := by simp [w, fourier_apply, Circle.norm_coe]
  have he : z * w - 1 = (z - 1) * w + (w - 1) := by ring
  change ‖z * w - 1‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(z - 1) * w‖ + ‖w - 1‖ := norm_add_le _ _
    _ = ‖z - 1‖ + ‖w - 1‖ := by rw [norm_mul, hw, mul_one]
    _ ≤ _ := add_le_add (norm_fourier_sub_one_le k.1 p.1) (norm_fourier_sub_one_le k.2 p.2)

/-- The character Lipschitz bound uses the product torus's max metric. -/
theorem norm_char_sub_le (k : ℤ × ℤ) (p q : Torus) :
    ‖char k p - char k q‖ ≤ 2 * √(1 + (normSq k : ℝ)) * dist p q := by
  have he : char k p - char k q = (char k (p - q) - 1) * char k q := by
    rw [sub_mul, one_mul, ← char_add_point, sub_add_cancel]
  rw [he, norm_mul, norm_char_apply, mul_one]
  have h1 : ‖(p - q).1‖ ≤ dist p q := by
    change AddCircle (2 * π) × AddCircle (2 * π) at p q
    change ‖p.1 - q.1‖ ≤ dist p q
    rw [Prod.dist_eq, dist_eq_norm]
    exact le_max_left _ _
  have h2 : ‖(p - q).2‖ ≤ dist p q := by
    change AddCircle (2 * π) × AddCircle (2 * π) at p q
    change ‖p.2 - q.2‖ ≤ dist p q
    simp only [dist_eq_norm]
    exact le_max_right _ _
  have hq : 0 ≤ 1 + (normSq k : ℝ) := by linarith [normSq_nonneg' k]
  have hsq := Real.sq_sqrt hq
  have hk (j : Fin 2) : |(frequencyComponent k j : ℝ)| ≤ √(1 + (normSq k : ℝ)) := by
    have h := frequencyComponent_sq_le k j
    have hs : 0 ≤ √(1 + (normSq k : ℝ)) := Real.sqrt_nonneg _
    nlinarith [sq_abs (frequencyComponent k j : ℝ)]
  have hsum : |(k.1 : ℝ)| + |(k.2 : ℝ)| ≤ 2 * √(1 + (normSq k : ℝ)) := by
    have h0 := hk 0
    have h1 := hk 1
    simp only [frequencyComponent, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at h0 h1
    linarith
  calc
    _ ≤ |(k.1 : ℝ)| * ‖(p - q).1‖ + |(k.2 : ℝ)| * ‖(p - q).2‖ := norm_char_sub_one_le k (p - q)
    _ ≤ (|(k.1 : ℝ)| + |(k.2 : ℝ)|) * dist p q := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum dist_nonneg

/-- Interpolate a bounded increment and a Lipschitz increment without excluding
the exponent zero or the zero-distance case. -/
theorem le_two_mul_rpow {v x α : ℝ} (hx : 0 ≤ x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hv : v ≤ 2) (hvx : v ≤ 2 * x) : v ≤ 2 * x ^ α := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge' hx hx1 hα0 hα1
    rw [Real.rpow_one] at h
    exact hvx.trans (mul_le_mul_of_nonneg_left h (by norm_num))
  · have h := Real.one_le_rpow (le_of_not_ge hx1) hα0
    linarith

/-- Fractional character increment bound for every exponent between zero and one. -/
theorem norm_char_sub_le_rpow {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (k : ℤ × ℤ) (p q : Torus) :
    ‖char k p - char k q‖ ≤ 2 * sobolevWeight (α / 2) k * dist p q ^ α := by
  have hb : ‖char k p - char k q‖ ≤ 2 := by
    have h := norm_sub_le (char k p) (char k q)
    simpa only [norm_char_apply, one_add_one_eq_two] using h
  have hi := le_two_mul_rpow (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg) hα0 hα1 hb
    (by simpa only [mul_assoc] using norm_char_sub_le k p q)
  rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by linarith [normSq_nonneg' k])] at hi
  simpa only [sobolevWeight, mul_div_assoc, div_mul_eq_mul_div, mul_one_div,
    one_mul, ← mul_assoc] using hi

/-- Evaluation of the sup-norm Fourier sum gives its pointwise Fourier series. -/
theorem MemSobolev.hasSum_continuousRep {g : L2} (hg : MemSobolev 2 g) (t : Torus) :
    HasSum (fun k ↦ fourierCoeff g k * char k t) (continuousRep g t) := by
  have h := hg.summable_fourier_char.hasSum.mapL (ContinuousMap.evalCLM (R := ℂ) t)
  simpa only [continuousRep, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using h

/-- Convert an ordinary metric increment bound to the extended-metric
form used by `HolderWith`. -/
theorem holderWith_of_dist_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C α : ℝ≥0} {u : X → Y}
    (h : ∀ p q, dist (u p) (u q) ≤ C * dist p q ^ (α : ℝ)) : HolderWith C α u := by
  intro p q
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal (h p q)

/-- `H²(𝕋²) ⊂ C^{0,α}(𝕋²)` for every `α < 1`, continuously. -/
theorem exists_holderWith_of_memSobolev_two {α : ℝ≥0} (hα : α < 1) :
    ∃ C : ℝ≥0, ∀ g : L2, MemSobolev 2 g → ∃ u : Torus → ℂ, (g : Torus → ℂ) =ᵐ[volume] u ∧
      HolderWith (C * Real.toNNReal √(sobolevNormSq 2 g)) α u ∧
      ∀ t, ‖u t‖ ≤ C * √(sobolevNormSq 2 g) := by
  let D := √(∑' k, sobolevWeight ((α : ℝ) - 2) k)
  let C : ℝ≥0 := Real.toNNReal (2 * D)
  have hC : (C : ℝ) = 2 * D := Real.coe_toNNReal _ (by positivity)
  have hαr : (α : ℝ) < 1 := by exact_mod_cast hα
  refine ⟨C, ?_⟩
  intro g hg
  obtain ⟨hws, hwb⟩ := hg.weighted_fourier_bound hαr
  let S := ∑' k, ‖fourierCoeff g k‖ * sobolevWeight ((α : ℝ) / 2) k
  have hSN : S ≤ √(sobolevNormSq 2 g) * D := hwb
  have hnorm : ∀ t, ‖continuousRep g t‖ ≤ S := by
    intro t
    apply (hg.hasSum_continuousRep t).norm_le_of_bounded hws.hasSum
    intro k
    rw [norm_mul, norm_char_apply, mul_one]
    have hw : 1 ≤ sobolevWeight ((α : ℝ) / 2) k := by
      simpa only [sobolevWeight_zero] using
        sobolevWeight_mono (show 0 ≤ (α : ℝ) / 2 by positivity) k
    exact le_mul_of_one_le_right (norm_nonneg _) hw
  have hdiff : ∀ p q, ‖continuousRep g p - continuousRep g q‖ ≤
      S * (2 * dist p q ^ (α : ℝ)) := by
    intro p q
    apply ((hg.hasSum_continuousRep p).sub (hg.hasSum_continuousRep q)).norm_le_of_bounded
      (hws.hasSum.mul_right (2 * dist p q ^ (α : ℝ)))
    intro k
    rw [← mul_sub, norm_mul]
    calc
      _ ≤ ‖fourierCoeff g k‖ *
          (2 * sobolevWeight ((α : ℝ) / 2) k * dist p q ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left (norm_char_sub_le_rpow α.coe_nonneg hαr.le k p q) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨continuousRep g, coeFn_eq_continuousRep hg, ?_, ?_⟩
  · apply holderWith_of_dist_bound
    intro p q
    rw [dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _), hC]
    calc
      _ ≤ S * (2 * dist p q ^ (α : ℝ)) := hdiff p q
      _ ≤ (√(sobolevNormSq 2 g) * D) * (2 * dist p q ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_right hSN (by positivity)
      _ = _ := by ring
  · intro t
    rw [hC]
    calc
      _ ≤ S := hnorm t
      _ ≤ √(sobolevNormSq 2 g) * D := hSN
      _ ≤ 2 * D * √(sobolevNormSq 2 g) := by
        have : 0 ≤ D := Real.sqrt_nonneg _
        nlinarith [Real.sqrt_nonneg (sobolevNormSq 2 g)]

end NoEmbeddedEigenvalues
