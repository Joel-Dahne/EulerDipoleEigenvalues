import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal
import NoEmbeddedEigenvalues.Virial.OriginalDomain.VirialFourier

/-! # Multiplication and weak transport tests on the torus -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex ComplexConjugate
open scoped Topology ContDiff InnerProductSpace Real

/-! ### Multiplication by continuous functions -/

section Multiplication

theorem mulL2_add_right (c : C(Torus, ℂ)) (u v : L2) :
    mulL2 c (u + v) = mulL2 c u + mulL2 c v := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (u + v), mulL2_ae c u, mulL2_ae c v, Lp.coeFn_add u v,
    Lp.coeFn_add (mulL2 c u) (mulL2 c v)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄, Pi.add_apply, h₁, h₂, h₃, Pi.add_apply, mul_add]

theorem mulL2_sub_right (c : C(Torus, ℂ)) (u v : L2) :
    mulL2 c (u - v) = mulL2 c u - mulL2 c v := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (u - v), mulL2_ae c u, mulL2_ae c v, Lp.coeFn_sub u v,
    Lp.coeFn_sub (mulL2 c u) (mulL2 c v)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄, Pi.sub_apply, h₁, h₂, h₃, Pi.sub_apply, mul_sub]

theorem mulL2_smul_right (c : C(Torus, ℂ)) (r : ℂ) (u : L2) :
    mulL2 c (r • u) = r • mulL2 c u := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (r • u), mulL2_ae c u, Lp.coeFn_smul r u,
    Lp.coeFn_smul r (mulL2 c u)] with t h h₁ h₂ h₃
  rw [h, h₃, Pi.smul_apply, h₁, h₂, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem norm_mulL2_le (c : C(Torus, ℂ)) (u : L2) : ‖mulL2 c u‖ ≤ ‖c‖ * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [mulL2_ae c u] with t h
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_right (c.norm_coe_le_norm t) (norm_nonneg _)

/-- Multiplication by a continuous function as a bounded operator on `L²`. -/
def mulL2CLM (c : C(Torus, ℂ)) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := mulL2 c, map_add' := mulL2_add_right c, map_smul' := mulL2_smul_right c }
    ‖c‖ (norm_mulL2_le c)

theorem mulL2CLM_apply (c : C(Torus, ℂ)) (u : L2) : mulL2CLM c u = mulL2 c u := rfl

/-- `sin y` on the torus. -/
def sinYTorus : C(Torus, ℂ) :=
  torusFunR (Real.continuous_sin.comp continuous_snd) isPeriodicLift_sin_snd

/-- `sin x` on the torus. -/
def sinXTorus : C(Torus, ℂ) :=
  torusFunR (Real.continuous_sin.comp continuous_fst) isPeriodicLift_sin_fst

theorem sinYTorus_torusProj (q : ℝ × ℝ) : sinYTorus (torusProj q) = Real.sin q.2 :=
  torusFunR_torusProj _ _ q

theorem sinXTorus_torusProj (q : ℝ × ℝ) : sinXTorus (torusProj q) = Real.sin q.1 :=
  torusFunR_torusProj _ _ q

theorem sinYTorus_apply (t : Torus) : sinYTorus t = (Real.Angle.sin t.2 : ℂ) := by
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  rw [sinYTorus_torusProj]
  simp [torusProj, Real.Angle.sin_coe]

theorem sinXTorus_apply (t : Torus) : sinXTorus t = (Real.Angle.sin t.1 : ℂ) := by
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  rw [sinXTorus_torusProj]
  simp [torusProj, Real.Angle.sin_coe]

end Multiplication

/-! ### Transport against `H¹` and `C¹` tests on the torus -/

section TorusTests

/-- `L₀eₖ = sin y ∂ₓeₖ - sin x ∂_yeₖ`. -/
theorem L0charLp_eq_mulL2 (k : ℤ × ℤ) :
    L0charLp k = mulL2 sinYTorus ((I * k.1) • charLp k) -
      mulL2 sinXTorus ((I * k.2) • charLp k) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (L0char k),
    Lp.coeFn_sub (mulL2 sinYTorus ((I * k.1) • charLp k))
      (mulL2 sinXTorus ((I * k.2) • charLp k)),
    mulL2_ae sinYTorus ((I * k.1) • charLp k), mulL2_ae sinXTorus ((I * k.2) • charLp k),
    Lp.coeFn_smul (I * k.1 : ℂ) (charLp k), Lp.coeFn_smul (I * k.2 : ℂ) (charLp k),
    charLp_ae_eq k] with t h1 h2 h3 h4 h5 h6 h7
  rw [L0charLp, h1, h2, Pi.sub_apply, h3, h4, h5, h6, Pi.smul_apply, Pi.smul_apply, h7,
    sinYTorus_apply, sinXTorus_apply]
  simp only [L0char, ContinuousMap.mul_apply, ContinuousMap.coe_mk, smul_eq_mul]
  ring

/-- The character-tested transport equation holds against every `u ∈ H¹(𝕋²)`:
`⟪u, h⟫ = -⟪sin y ∂ₓu - sin x ∂_yu, g⟫`. -/
theorem HasL0.inner_eq {g h u ux uy : L2} (hgh : HasL0 g h) (hx : HasFourierPartial 0 u ux)
    (hy : HasFourierPartial 1 u uy) :
    ⟪u, h⟫_ℂ = -⟪mulL2 sinYTorus ux - mulL2 sinXTorus uy, g⟫_ℂ := by
  set Lu := mulL2 sinYTorus ux - mulL2 sinXTorus uy
  have hterm (k : ℤ × ℤ) : fourierCoeff u k • L0charLp k =
      mulL2CLM sinYTorus (fourierCoeff ux k • charLp k) -
        mulL2CLM sinXTorus (fourierCoeff uy k • charLp k) := by
    rw [L0charLp_eq_mulL2, smul_sub, mulL2CLM_apply, mulL2CLM_apply, ← mulL2_smul_right,
      ← mulL2_smul_right, smul_smul, smul_smul, hx k, hy k]
    simp only [frequencyComponent]
    congr 3 <;> simp <;> ring
  have hL : HasSum (fun k ↦ fourierCoeff u k • L0charLp k) Lu := by
    simp only [hterm]
    exact ((hasSum_fourier_series ux).mapL (mulL2CLM sinYTorus)).sub
      ((hasSum_fourier_series uy).mapL (mulL2CLM sinXTorus))
  have hi : HasSum (fun k ↦ ⟪fourierCoeff u k • L0charLp k, g⟫_ℂ) ⟪Lu, g⟫_ℂ := by
    rw [← Complex.hasSum_conj']
    simpa only [innerSL_apply_apply, inner_conj_symm] using hL.mapL (innerSL ℂ g)
  refine (torusFourierBasis.hasSum_inner_mul_inner u h).unique (hi.neg.congr_fun fun k ↦ ?_)
  rw [inner_smul_left, ← mul_neg, ← hgh k, ← inner_conj_symm (𝕜 := ℂ) u (torusFourierBasis k)]
  simp only [← HilbertBasis.repr_apply_apply, torusFourierBasis_repr, fourierCoeff, map_mul,
    map_inv₀, map_pow, map_ofNat, conj_ofReal]
  field_simp

/-- The bilinear form for `C¹` tests: `∫ hΦ = -∫ g (sin y ∂ₓΦ - sin x ∂_yΦ)`. -/
theorem HasL0.integral_mul_eq {g h : L2} (hgh : HasL0 g h) {Φ Φx Φy : C(Torus, ℂ)}
    (hx : HasClassicalPartial 0 Φ Φx) (hy : HasClassicalPartial 1 Φ Φy) :
    ∫ t, h t * Φ t = -∫ t, g t * (sinYTorus t * Φx t - sinXTorus t * Φy t) := by
  have H := hgh.inner_eq hx.conj.hasFourierPartial hy.conj.hasFourierPartial
  rw [L2.inner_def, L2.inner_def] at H
  convert H using 1
  · apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (star Φ)] with t ht
    rw [ht, RCLike.inner_apply]
    simp
  · congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (mulL2 sinYTorus (ContinuousMap.toLp 2 volume ℂ (star Φx)))
        (mulL2 sinXTorus (ContinuousMap.toLp 2 volume ℂ (star Φy))),
      mulL2_ae sinYTorus (ContinuousMap.toLp 2 volume ℂ (star Φx)),
      mulL2_ae sinXTorus (ContinuousMap.toLp 2 volume ℂ (star Φy)),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (star Φx),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (star Φy)] with t h1 h2 h3 h4 h5
    rw [RCLike.inner_apply, h1, Pi.sub_apply, h2, h3, h4, h5]
    simp [sinYTorus_apply, sinXTorus_apply]

end TorusTests

end NoEmbeddedEigenvalues
