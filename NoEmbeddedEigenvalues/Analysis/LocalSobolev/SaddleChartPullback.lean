module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.AxisReflectionJets
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.SaddleNormalForm
public import NoEmbeddedEigenvalues.Analysis.TorusSobolev.LiftPeriodization

/-!
# The affine jet interface in normalized saddle coordinates

Blueprint: `lem:saddle-chart-pullback`.

The explicit saddle chart is an affine equivalence of absolute determinant one.
Its disk pullback mixes the derivative indices and preserves each radial L²
condition. The chart's assigned values on the separatrix play no role.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Linear part of the normalized saddle chart. -/
def saddleLinearMap (P : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun q := ((q.1 - Real.cos P.1 * q.2) / Real.sqrt 2,
    (q.1 + Real.cos P.1 * q.2) / Real.sqrt 2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp <;> ring

@[simp] theorem saddleLinearMap_apply (P q : ℝ × ℝ) :
    saddleLinearMap P q = ((q.1 - Real.cos P.1 * q.2) / Real.sqrt 2,
      (q.1 + Real.cos P.1 * q.2) / Real.sqrt 2) := rfl

theorem det_saddleLinearMap (P : ℝ × ℝ) :
    LinearMap.det (saddleLinearMap P) = Real.cos P.1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, saddleLinearMap]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem abs_cos_saddle {P : ℝ × ℝ} (hP : P ∈ saddleSet) : |Real.cos P.1| = 1 := by
  obtain ⟨m, n, _, rfl⟩ := hP
  exact Real.abs_cos_int_mul_pi m

/-- The linear saddle chart as an equivalence. -/
def saddleLinear (P : ℝ × ℝ) (hP : P ∈ saddleSet) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ((saddleLinearMap P).equivOfDetNeZero (by
    rw [det_saddleLinearMap]
    have h := abs_cos_saddle hP
    intro hz
    simp [hz] at h)).toContinuousLinearEquiv

@[simp] theorem saddleLinear_apply (P : ℝ × ℝ) (hP : P ∈ saddleSet) (q : ℝ × ℝ) :
    saddleLinear P hP q = saddleLinearMap P q := rfl

theorem planeAffine_saddleLinear (P : ℝ × ℝ) (hP : P ∈ saddleSet) :
    (planeAffine (saddleLinear P hP) P : (ℝ × ℝ) → ℝ × ℝ) = saddleOrthoChart P := by
  funext q
  ext <;> simp [saddleLinearMap, saddleOrthoChart, add_comm]

theorem measurePreserving_saddleChart {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    MeasurePreserving (saddleOrthoChart P) := by
  rw [← planeAffine_saddleLinear P hP]
  apply measurePreserving_planeAffine
  change |LinearMap.det (saddleLinearMap P)| = 1
  rw [det_saddleLinearMap, abs_cos_saddle hP]

/-- Euclidean radius is preserved in the normalized chart. -/
theorem localRadius_saddleChart {P : ℝ × ℝ} (hP : P ∈ saddleSet) (q : ℝ × ℝ) :
    localRadius P (saddleOrthoChart P q) = localRadius 0 q := by
  have hsq : (Real.cos P.1) ^ 2 = 1 := (sq_abs (Real.cos P.1)).symm.trans
    (by rw [abs_cos_saddle hP]; norm_num)
  unfold localRadius saddleOrthoChart
  simp only [Prod.fst_zero, Prod.snd_zero, add_sub_cancel_left, sub_zero]
  congr 1
  simp only [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf
  rw [hsq]
  ring

/-- The full Sobolev/jet/radial data pull back on a saddle disk. -/
theorem saddle_chart_pullback {n : ℕ} {P : ℝ × ℝ} (hP : P ∈ saddleSet) {ρ : ℝ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hf : MemSobolevOn n (localDisk P ρ) f)
    (hD : HasWeakJetOn n (localDisk P ρ) f D) :
    ∃ E, MemSobolevOn n (localDisk 0 ρ) (f ∘ saddleOrthoChart P) ∧
      HasWeakJetOn n (localDisk 0 ρ) (f ∘ saddleOrthoChart P) E ∧
      ∀ k s, RadialJetLp k s (localDisk P ρ) P D →
        RadialJetLp k s (localDisk 0 ρ) 0 E := by
  have hmp : MeasurePreserving (planeAffine (saddleLinear P hP) P) := by
    simpa only [planeAffine_saddleLinear P hP] using measurePreserving_saddleChart hP
  have ho : IsOpen (localDisk P ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hr (q : ℝ × ℝ) : localRadius P (planeAffine (saddleLinear P hP) P q) =
      localRadius 0 q := by
    rw [planeAffine_saddleLinear P hP]
    exact localRadius_saddleChart hP q
  have hpre : planeAffine (saddleLinear P hP) P ⁻¹' localDisk P ρ = localDisk 0 ρ := by
    ext q
    exact Iff.of_eq (congrArg (fun r ↦ r < ρ) (hr q))
  refine ⟨affineJet (saddleLinear P hP) P D, ?_, ?_, fun k s hk ↦ ?_⟩
  · have hf' := hf.comp_planeAffine (saddleLinear P hP) P hmp ho
    rw [hpre] at hf'
    simpa only [planeAffine_saddleLinear P hP] using hf'
  · have hD' := hD.comp_planeAffine (saddleLinear P hP) P hmp ho
    rw [hpre] at hD'
    simpa only [planeAffine_saddleLinear P hP] using hD'
  · simpa only [hpre] using
      hk.comp_planeAffine (saddleLinear P hP) P hmp ho.measurableSet hr

/-- The inverse saddle chart transfers the full weighted weak jet back to
physical coordinates, including the Cartesian derivative indices. -/
theorem saddle_chart_pushforward {n : ℕ} {P : ℝ × ℝ} (hP : P ∈ saddleSet) {ρ : ℝ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n (localDisk 0 ρ) (f ∘ saddleOrthoChart P) D) :
    ∃ E, HasWeakJetOn n (localDisk P ρ) f E ∧
      ∀ k s, RadialJetLp k s (localDisk 0 ρ) 0 D →
        RadialJetLp k s (localDisk P ρ) P E := by
  let A := saddleLinear P hP
  let e := planeAffine A P
  have he : (e : (ℝ × ℝ) → ℝ × ℝ) = saddleOrthoChart P := planeAffine_saddleLinear P hP
  have hi : (e.symm : (ℝ × ℝ) → ℝ × ℝ) = planeAffine A.symm (-A.symm P) := by
    funext p
    change A.symm (p - P) = A.symm p + -A.symm P
    rw [map_sub, sub_eq_add_neg]
  have hm : MeasurePreserving e := he ▸ measurePreserving_saddleChart hP
  have hmi : MeasurePreserving (planeAffine A.symm (-A.symm P)) :=
    hi ▸ hm.symm e.toMeasurableEquiv
  have hr (p : ℝ × ℝ) : localRadius 0 (planeAffine A.symm (-A.symm P) p) =
      localRadius P p := by
    rw [← hi, ← localRadius_saddleChart hP, ← he, e.apply_symm_apply]
  have hpre : planeAffine A.symm (-A.symm P) ⁻¹' localDisk 0 ρ = localDisk P ρ := by
    ext p
    change localRadius 0 _ < ρ ↔ localRadius P p < ρ
    rw [hr]
  have hf : (f ∘ saddleOrthoChart P) ∘ planeAffine A.symm (-A.symm P) = f := by
    funext p
    simp only [← hi, ← he, Function.comp_apply, e.apply_symm_apply]
  refine ⟨affineJet A.symm (-A.symm P) D, ?_, fun k s hk ↦ ?_⟩
  · simpa only [hpre, hf] using
      hD.comp_planeAffine A.symm (-A.symm P) hmi (isOpen_localDisk 0 ρ)
  · simpa only [hpre] using hk.comp_planeAffine A.symm (-A.symm P) hmi
      (isOpen_localDisk 0 ρ).measurableSet hr

/-- Orthogonality preserves the trace of an arbitrary specified second jet.
No symmetry of its mixed entries is assumed or needed. -/
theorem affineJet_saddle_laplacian {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    affineJet (saddleLinear P hP) P D [0, 0] q +
      affineJet (saddleLinear P hP) P D [1, 1] q =
      D [0, 0] (saddleOrthoChart P q) + D [1, 1] (saddleOrthoChart P q) := by
  have hsq : (Real.cos P.1 : ℂ) ^ 2 = 1 := by
    have hr : Real.cos P.1 ^ 2 = 1 := by
      nlinarith [abs_cos_saddle hP, sq_abs (Real.cos P.1)]
    exact_mod_cast hr
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [← planeAffine_saddleLinear P hP]
  simp only [affineJet, affineCoeff, planeDirection, Fin.reduceEq, ↓reduceIte,
    saddleLinear_apply, saddleLinearMap_apply, axisCoord, Function.comp_apply,
    mul_zero, mul_one, sub_zero, zero_sub,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]
  field_simp
  ring_nf
  simp only [hsq, hsqrt, Complex.ofReal_one]
  ring

/-- A local axis reflection projects to the corresponding global separatrix
reflection at every lifted saddle, including its noncentral period copies. -/
theorem torusProj_saddleChart_axisReflect {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    (j : Fin 2) (q : ℝ × ℝ) :
    torusProj (saddleOrthoChart P (axisReflect j q)) =
      (if j = 0 then S₁ else S₂) (torusProj (saddleOrthoChart P q)) := by
  obtain ⟨m, n, ⟨k, hk⟩, rfl⟩ := hP
  have hkr : (m : ℝ) + (n : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
  fin_cases j
  all_goals
    simp only [axisReflect, Fin.mk_zero, Fin.mk_one, Fin.reduceEq, ↓reduceIte]
    apply Prod.ext
  all_goals
    dsimp only [torusProj, S₁, S₂, axisReflect]
    first | rw [← Real.Angle.coe_sub] | rw [← Real.Angle.coe_add]
  · apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨k, ?_⟩
    dsimp [saddleOrthoChart]
    linear_combination Real.pi * hkr
  · apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨k, ?_⟩
    dsimp [saddleOrthoChart]
    linear_combination Real.pi * hkr
  · apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨k - n, ?_⟩
    dsimp [saddleOrthoChart]
    push_cast
    linear_combination Real.pi * hkr
  · apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨n - k - 1, ?_⟩
    dsimp [saddleOrthoChart]
    push_cast
    linear_combination -Real.pi * hkr

/-- Torus reflection parities become the corresponding axis parities in the
orthonormal saddle chart, almost everywhere. -/
theorem saddle_chart_sector_parity {P : ℝ × ℝ} (hP : P ∈ saddleSet) {f : L2}
    {ε₁ ε₂ : Bool} (hf : InSector ε₁ ε₂ f) :
    ∀ j : Fin 2, ∀ᵐ q, liftL2 f (saddleOrthoChart P (axisReflect j q)) =
      paritySign (if j = 0 then ε₁ else ε₂) * liftL2 f (saddleOrthoChart P q) := by
  have h1 : ∀ᵐ t : Torus, f (S₁ t) = paritySign ε₁ * f t := by
    filter_upwards [ae_comp_of_pullback_eq hf.1, Lp.coeFn_smul (paritySign ε₁) f]
      with t ht hsm
    simpa only [symmetry₁, hsm, Pi.smul_apply, smul_eq_mul] using ht
  have h2 : ∀ᵐ t : Torus, f (S₂ t) = paritySign ε₂ * f t := by
    filter_upwards [ae_comp_of_pullback_eq hf.2, Lp.coeFn_smul (paritySign ε₂) f]
      with t ht hsm
    simpa only [symmetry₂, hsm, Pi.smul_apply, smul_eq_mul] using ht
  have hc1 := (measurePreserving_saddleChart hP).quasiMeasurePreserving.ae (ae_torusProj h1)
  have hc2 := (measurePreserving_saddleChart hP).quasiMeasurePreserving.ae (ae_torusProj h2)
  intro j
  filter_upwards [hc1, hc2] with q hq1 hq2
  change f (torusProj (saddleOrthoChart P (axisReflect j q))) =
    paritySign (if j = 0 then ε₁ else ε₂) * f (torusProj (saddleOrthoChart P q))
  rw [torusProj_saddleChart_axisReflect hP]
  fin_cases j
  · exact hq1
  · exact hq2

/-- Odd–odd specialization (`lem:saddle-chart-parity`). -/
theorem saddle_chart_parity {P : ℝ × ℝ} (hP : P ∈ saddleSet) {f : L2}
    (hf : InSector false false f) :
    ∀ j, ∀ᵐ q, liftL2 f (saddleOrthoChart P (axisReflect j q)) =
      -liftL2 f (saddleOrthoChart P q) := by
  intro j
  simpa [paritySign] using saddle_chart_sector_parity hP hf j

end NoEmbeddedEigenvalues
