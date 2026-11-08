import NoEmbeddedEigenvalues.AffineJets
import NoEmbeddedEigenvalues.Regularity.SaddleNormalForm

/-!
# The affine jet interface in normalized saddle coordinates

Blueprint: `lem:saddle-chart-pullback`.

The explicit saddle chart is an affine equivalence of absolute determinant one.
Its disk pullback mixes the derivative indices and preserves each radial L²
condition. The chart's assigned values on the separatrix play no role.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Linear part of the normalized saddle chart. -/
def saddleLinearMap (P : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun q := ((q.1 - Real.cos P.1 * q.2) / Real.sqrt 2,
    (q.1 + Real.cos P.1 * q.2) / Real.sqrt 2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp <;> ring

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

end NoEmbeddedEigenvalues
