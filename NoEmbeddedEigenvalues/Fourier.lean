import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.Unique
import NoEmbeddedEigenvalues.TorusL2

/-!
# Fourier infrastructure on the `2π`-torus

The unit torus carries probability Haar measure. Scaling its coordinates by `2π`
identifies it with `Torus`, whose Lebesgue measure has mass `(2π)^2`.
We transport orthogonality and continuous-function density from Mathlib's unit
monomials, then construct the Hilbert basis `(2π)⁻¹ • charLp k` directly.
This avoids a separate `L²` scaling equivalence. We prove reconstruction,
Parseval, uniqueness and existence for prescribed square-summable coefficients
(blueprint: `def:torus-fourier-basis`, `lem:torus-fourier`).
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory
open scoped ENNReal InnerProductSpace lp

/-- Probability Haar measure on the physical torus. -/
def torusHaar : Measure Torus :=
  (AddCircle.haarAddCircle (T := 2 * π)).prod (AddCircle.haarAddCircle (T := 2 * π))

/-- Scaling a unit-circle coordinate to an angle. -/
def angleScale : UnitAddCircle ≃+ Angle :=
  AddCircle.equivAddCircle 1 (2 * π) one_ne_zero (by positivity)

theorem angleScale_coe (t : ℝ) : angleScale (t : UnitAddCircle) = (t * (2 * π) : ℝ) := by
  change (AddCircle.equivAddCircle (1 : ℝ) (2 * π) one_ne_zero (by positivity))
    (t : AddCircle (1 : ℝ)) = (t * (2 * π) : AddCircle (2 * π))
  simpa only [inv_one, one_mul] using
    (AddCircle.equivAddCircle_apply_mk (p := (1 : ℝ)) (q := 2 * π)
      one_ne_zero (by positivity) t)

theorem measurePreserving_angleScale :
    MeasurePreserving angleScale (AddCircle.haarAddCircle (T := 1))
      (AddCircle.haarAddCircle (T := 2 * π)) := by
  change MeasurePreserving (AddCircle.equivAddCircle 1 (2 * π) _ _)
    (AddCircle.haarAddCircle (T := 1)) (AddCircle.haarAddCircle (T := 2 * π))
  exact (AddCircle.equivAddCircle 1 (2 * π) _ _).toAddMonoidHom.measurePreserving
    (AddCircle.continuous_equivAddCircle ..)
    (AddCircle.equivAddCircle 1 (2 * π) _ _).surjective (by simp)

/-- Coordinates on the unit torus scaled to the physical `2π`-torus. -/
def torusScale : UnitAddTorus (Fin 2) ≃ₜ Torus :=
  (Homeomorph.piFinTwo fun _ => UnitAddCircle).trans
    ((AddCircle.homeomorphAddCircle 1 (2 * π) one_ne_zero (by positivity)).prodCongr
      (AddCircle.homeomorphAddCircle 1 (2 * π) one_ne_zero (by positivity)))

theorem torusScale_apply (t : UnitAddTorus (Fin 2)) :
    torusScale t = (angleScale (t 0), angleScale (t 1)) := rfl

/-- The explicit probability measure used by Mathlib's multivariate Fourier basis. -/
def unitTorusHaar : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi fun _ => AddCircle.haarAddCircle (T := 1)

theorem measurePreserving_torusScale :
    MeasurePreserving torusScale unitTorusHaar torusHaar := by
  exact (measurePreserving_angleScale.prod measurePreserving_angleScale).comp
    (measurePreserving_piFinTwo fun _ => AddCircle.haarAddCircle (T := 1))

/-- Lebesgue measure is `(2π)^2` times probability Haar measure. -/
theorem volume_eq_smul_torusHaar :
    (volume : Measure Torus) = ENNReal.ofReal ((2 * π) ^ 2) • torusHaar := by
  change (volume : Measure (AddCircle (2 * π) × AddCircle (2 * π))) = _
  rw [Measure.volume_eq_prod, AddCircle.volume_eq_smul_haarAddCircle,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [← ENNReal.ofReal_mul (by positivity), ← pow_two]
  rfl

/-- The Jacobian of coordinate scaling, expressed as a pushforward measure. -/
theorem map_torusScale :
    Measure.map torusScale unitTorusHaar =
      (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ • (volume : Measure Torus) := by
  rw [measurePreserving_torusScale.map_eq, volume_eq_smul_torusHaar, smul_smul,
    ENNReal.inv_mul_cancel (by positivity : ENNReal.ofReal ((2 * π) ^ 2) ≠ 0)
      (by simp), one_smul]

/-- Change of variables under scaling, with the Lebesgue Jacobian included. -/
theorem integral_torusScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus → E) :
    (∫ p, f p) = ((2 * π) ^ 2) • ∫ t, f (torusScale t) ∂unitTorusHaar := by
  rw [volume_eq_smul_torusHaar, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  rw [measurePreserving_torusScale.integral_comp
    torusScale.toMeasurableEquiv.measurableEmbedding]

/-- Frequency indices in product and finite-function notation. -/
def frequencyEquiv : (Fin 2 → ℤ) ≃ (ℤ × ℤ) := finTwoArrowEquiv ℤ

/-- Scaling the argument changes the period but not the character's frequency. -/
theorem fourier_angleScale (n : ℤ) (t : UnitAddCircle) :
    fourier (T := 2 * π) n (angleScale t) = fourier (T := 1) n t := by
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    rw [angleScale_coe]
    change fourier (T := 2 * π) n (t * (2 * π) : AddCircle (2 * π)) =
      fourier (T := 1) n (t : AddCircle (1 : ℝ))
    rw [fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    field_simp

/-- Our characters pull back to Mathlib's unit-torus monomials. -/
theorem char_torusScale (n : Fin 2 → ℤ) (t : UnitAddTorus (Fin 2)) :
    char (frequencyEquiv n) (torusScale t) = UnitAddTorus.mFourier n t := by
  change fourier (T := 2 * π) (n 0) (angleScale (t 0)) *
    fourier (T := 2 * π) (n 1) (angleScale (t 1)) = _
  rw [fourier_angleScale, fourier_angleScale]
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two]

/-- The characters span a dense subspace of continuous functions on the physical torus. -/
theorem span_char_closure_eq_top :
    (Submodule.span ℂ (Set.range char)).topologicalClosure = ⊤ := by
  let F := ContinuousMap.compCLM (R := ℂ) ℂ ⟨torusScale.symm, torusScale.symm.continuous⟩
  have hF : Function.Surjective F := by
    intro f
    refine ⟨f.comp ⟨torusScale, torusScale.continuous⟩, ?_⟩
    ext p
    exact congrArg f (torusScale.apply_symm_apply p)
  have hchar (n : Fin 2 → ℤ) : F (UnitAddTorus.mFourier n) = char (frequencyEquiv n) := by
    ext p
    have h := char_torusScale n (torusScale.symm p)
    simpa [F] using h.symm
  have hrange : Set.range (fun n => F (UnitAddTorus.mFourier n)) = Set.range char := by
    simp_rw [hchar]
    exact frequencyEquiv.surjective.range_comp char
  have hd := hF.denseRange.topologicalClosure_map_submodule
    (f := F) UnitAddTorus.span_mFourier_closure_eq_top
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← Set.range_comp,
    Function.comp_def, hrange] using hd

/-- Density of the characters in the physical `L²` space. -/
theorem span_charLp_closure_eq_top :
    (Submodule.span ℂ (Set.range charLp)).topologicalClosure = ⊤ := by
  change (Submodule.span ℂ (Set.range fun k =>
    ContinuousMap.toLp 2 (volume : Measure Torus) ℂ (char k))).topologicalClosure = ⊤
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← Set.range_comp,
    Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ (volume : Measure Torus) ℂ
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)).topologicalClosure_map_submodule span_char_closure_eq_top

/-- Orthogonality of the unnormalized characters for Lebesgue measure. -/
theorem inner_charLp (k l : ℤ × ℤ) :
    ⟪charLp k, charLp l⟫_ℂ = if k = l then ((2 * π : ℂ) ^ 2) else 0 := by
  obtain ⟨n, rfl⟩ := frequencyEquiv.surjective k
  obtain ⟨m, rfl⟩ := frequencyEquiv.surjective l
  have hunit := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) n m
  rw [ContinuousMap.inner_toLp] at hunit
  change (∫ t, inner ℂ (UnitAddTorus.mFourier n t) (UnitAddTorus.mFourier m t)
    ∂unitTorusHaar) = (if n = m then 1 else 0) at hunit
  change ⟪ContinuousMap.toLp 2 volume ℂ (char (frequencyEquiv n)),
    ContinuousMap.toLp 2 volume ℂ (char (frequencyEquiv m))⟫_ℂ = _
  rw [ContinuousMap.inner_toLp, integral_torusScale]
  simp_rw [char_torusScale]
  simp only [RCLike.inner_apply] at hunit
  rw [hunit]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> simp [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul]

/-- Normalized characters, of unit norm for Lebesgue measure. -/
def normalizedChar (k : ℤ × ℤ) : L2 := (2 * π : ℂ)⁻¹ • charLp k

theorem orthonormal_normalizedChar : Orthonormal ℂ normalizedChar := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [normalizedChar, inner_smul_left, inner_smul_right, inner_charLp]
  simp only [map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal]
  split_ifs <;> simp [pow_two]
  field_simp

/-- The normalized characters span densely, just as the unnormalized characters do. -/
theorem span_normalizedChar_closure_eq_top :
    (Submodule.span ℂ (Set.range normalizedChar)).topologicalClosure = ⊤ := by
  have hspan : Submodule.span ℂ (Set.range normalizedChar) =
      Submodule.span ℂ (Set.range charLp) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      have h := Submodule.smul_mem (Submodule.span ℂ (Set.range normalizedChar))
        (2 * π : ℂ) (Submodule.subset_span ⟨k, rfl⟩)
      have hne : (2 * π : ℂ) ≠ 0 := by
        exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
      rw [normalizedChar, smul_smul, mul_inv_cancel₀ hne, one_smul] at h
      exact h
  rw [hspan, span_charLp_closure_eq_top]

/-- Fourier Hilbert basis on the physical torus, indexed by `ℤ × ℤ`. -/
def torusFourierBasis : HilbertBasis (ℤ × ℤ) ℂ L2 :=
  HilbertBasis.mk orthonormal_normalizedChar span_normalizedChar_closure_eq_top.ge

theorem torusFourierBasis_apply (k : ℤ × ℤ) :
    torusFourierBasis k = normalizedChar k := congrFun (HilbertBasis.coe_mk _ _) k

/-- Hilbert coordinates differ from our Fourier coefficients by the factor `2π`. -/
theorem torusFourierBasis_repr (g : L2) (k : ℤ × ℤ) :
    torusFourierBasis.repr g k = (2 * π : ℂ) * fourierCoeff g k := by
  rw [HilbertBasis.repr_apply_apply, torusFourierBasis_apply]
  simp only [normalizedChar, inner_smul_left, fourierCoeff, map_inv₀, map_mul,
    map_ofNat, Complex.conj_ofReal]
  field_simp

/-- Fourier reconstruction is convergence in the `L²` norm, not pointwise convergence. -/
theorem hasSum_fourier_series (g : L2) :
    HasSum (fun k => fourierCoeff g k • charLp k) g := by
  have h := torusFourierBasis.hasSum_repr g
  simp_rw [torusFourierBasis_repr, torusFourierBasis_apply, normalizedChar,
    smul_smul] at h
  have heq (k : ℤ × ℤ) : (2 * π : ℂ) * fourierCoeff g k * (2 * π : ℂ)⁻¹ =
      fourierCoeff g k := by field_simp
  simpa only [heq] using h

/-- Fourier coefficients determine an `L²` function uniquely. -/
theorem fourierCoeff_ext {g h : L2} (heq : ∀ k, fourierCoeff g k = fourierCoeff h k) : g = h := by
  apply torusFourierBasis.repr.injective
  ext k
  simp only [torusFourierBasis_repr, heq]

/-- Parseval's identity, including the Lebesgue normalization. -/
theorem hasSum_sq_fourierCoeff (g : L2) :
    HasSum (fun k => (2 * π) ^ 2 * ‖fourierCoeff g k‖ ^ 2) (‖g‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (torusFourierBasis.repr g)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    torusFourierBasis_repr, norm_mul, mul_pow, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos] using h

/-- Fourier coefficients are square summable. -/
theorem summable_sq_fourierCoeff (g : L2) : Summable (fun k => ‖fourierCoeff g k‖ ^ 2) :=
  (summable_mul_left_iff (by positivity : (2 * π) ^ 2 ≠ 0)).mp
    (hasSum_sq_fourierCoeff g).summable

/-- Every square-summable sequence is the Fourier coefficient sequence of an `L²` function. -/
theorem exists_fourierCoeff (c : (ℤ × ℤ) → ℂ)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) : ∃ g : L2, ∀ k, fourierCoeff g k = c k := by
  have hcLp : Memℓp c 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hc
  let a : ℓ²(ℤ × ℤ, ℂ) := (2 * π : ℂ) • (⟨c, hcLp⟩ : ℓ²(ℤ × ℤ, ℂ))
  refine ⟨torusFourierBasis.repr.symm a, fun k => ?_⟩
  have h := congrArg (fun v : ℓ²(ℤ × ℤ, ℂ) => v k)
    (torusFourierBasis.repr.apply_symm_apply a)
  rw [torusFourierBasis_repr] at h
  change (2 * π : ℂ) * fourierCoeff (torusFourierBasis.repr.symm a) k = (2 * π : ℂ) * c k at h
  exact mul_left_cancel₀ (by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)) h

/-- A square-summable coefficient sequence defines a convergent series in `L²`. -/
theorem summable_fourier_series (c : (ℤ × ℤ) → ℂ)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    Summable (fun k => c k • charLp k) := by
  obtain ⟨g, hg⟩ := exists_fourierCoeff c hc
  simpa only [hg] using (hasSum_fourier_series g).summable

/-- The convergent Fourier series has exactly the prescribed coefficients. -/
theorem fourierCoeff_tsum (c : (ℤ × ℤ) → ℂ)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) (k : ℤ × ℤ) :
    fourierCoeff (∑' j, c j • charLp j) k = c k := by
  obtain ⟨g, hg⟩ := exists_fourierCoeff c hc
  have hs : HasSum (fun j => c j • charLp j) g := by
    simpa only [hg] using hasSum_fourier_series g
  rw [hs.tsum_eq]
  exact hg k

end NoEmbeddedEigenvalues
