import NoEmbeddedEigenvalues.Regularity.SaddleNormalForm
import NoEmbeddedEigenvalues.WeakJetOperations

/-!
# Cartesian jets of the saddle Taylor correction

The explicit dipole and its normalized quadratic differ by order four, including
all derivatives through order three. These geometric estimates have no
vorticity or eigenfunction hypotheses.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- The smooth Cartesian Taylor correction has finite radial jet norms
(`lem:saddle-taylor-correction`). -/
theorem saddle_taylor_correction {c : ℝ × ℝ} (hc : c ∈ saddleSet) (a : ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ E : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 3 (localDisk c ρ)
        (fun p ↦ saddleQuadratic c a p - a * (dipoleLift p : ℂ)) E ∧
      ∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c E := by
  sorry

/-- The normalized quadratic is harmonic in Cartesian coordinates. -/
theorem saddleQuadratic_harmonic (c : ℝ × ℝ) (a : ℂ) (p : ℝ × ℝ) :
    classicalComplexJet [0, 0] (saddleQuadratic c a) p +
      classicalComplexJet [1, 1] (saddleQuadratic c a) p = 0 := by
  let b : ℂ := a * (Real.cos c.1 : ℂ) / 2
  have hx : partialX (saddleQuadratic c a) =
      fun q ↦ b * (-2 * ((q.1 - c.1 : ℝ) : ℂ)) := by
    funext q
    have hd := ((((hasDerivAt_id q.1).sub_const c.1).pow 2).const_sub
      ((q.2 - c.2) ^ 2)).ofReal_comp.const_mul b
    convert hd.deriv using 1 <;> simp [partialX, saddleQuadratic, b]
  have hy : partialY (saddleQuadratic c a) =
      fun q ↦ b * (2 * ((q.2 - c.2 : ℝ) : ℂ)) := by
    funext q
    have hd := ((((hasDerivAt_id q.2).sub_const c.2).pow 2).sub_const
      ((q.1 - c.1) ^ 2)).ofReal_comp.const_mul b
    convert hd.deriv using 1 <;> simp [partialY, saddleQuadratic, b]
  simp only [classicalComplexJet, coordPartial, Fin.reduceEq, ↓reduceIte]
  rw [hx, hy]
  have hxx : partialX (fun q : ℝ × ℝ ↦ b * (-2 * ((q.1 - c.1 : ℝ) : ℂ))) p = b * (-2) := by
    have hd := (((hasDerivAt_id p.1).sub_const c.1).ofReal_comp.const_mul (-2 : ℂ)).const_mul b
    simpa [partialX] using hd.deriv
  have hyy : partialY (fun q : ℝ × ℝ ↦ b * (2 * ((q.2 - c.2 : ℝ) : ℂ))) p = b * 2 := by
    have hd := (((hasDerivAt_id p.2).sub_const c.2).ofReal_comp.const_mul (2 : ℂ)).const_mul b
    simpa [partialY] using hd.deriv
  rw [hxx, hyy]
  ring

/-- Distance to the saddle lattice is at most distance to any fixed saddle. -/
theorem saddleDist_le_localRadius {c : ℝ × ℝ} (hc : c ∈ saddleSet) (p : ℝ × ℝ) :
    saddleDist p ≤ localRadius c p :=
  (Metric.infDist_le_dist_of_mem hc).trans (dist_le_localRadius c p)

/-- The zero-distance set is null, even though the infimum uses the product metric. -/
theorem ae_saddleDist_ne_zero : ∀ᵐ p : ℝ × ℝ, saddleDist p ≠ 0 := by
  let S : Set (ℝ × ℝ) := {p | p.1 / Real.pi ∈ Set.range ((↑) : ℤ → ℝ)}
  have hS : IsClosed S := Real.isClosed_range_intCast.preimage (by fun_prop)
  have hsub : saddleSet ⊆ S := by
    rintro p ⟨m, n, _, rfl⟩
    exact ⟨m, by simp [Real.pi_ne_zero]⟩
  have hnull : volume S = 0 := by
    have heq : S = (Set.range fun m : ℤ ↦ (m : ℝ) * Real.pi) ×ˢ (univ : Set ℝ) := by
      ext p
      simp only [S, mem_ofPred_eq, mem_range, mem_prod, mem_univ, and_true]
      constructor
      · rintro ⟨m, hm⟩; exact ⟨m, by rw [hm]; field_simp⟩
      · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hm]; simp [Real.pi_ne_zero]⟩
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod]
    simp [(Set.countable_range (fun m : ℤ ↦ (m : ℝ) * Real.pi)).measure_zero volume]
  have hne : saddleSet.Nonempty := ⟨(0, Real.pi), 0, 1, by decide, by simp⟩
  have ha : ∀ᵐ p, p ∉ S := by rw [ae_iff]; simpa using hnull
  filter_upwards [ha] with p hp hz
  have hp' : p ∈ closure saddleSet := by
    by_contra hn
    have hh := (Metric.infDist_pos_iff_notMem_closure hne).mp hn
    exact (ne_of_gt hh) hz
  exact hp ((closure_minimal hsub hS) hp')

/-- Changing the lattice weight to a fixed-saddle Euclidean weight costs no constant. -/
theorem memLp_div_localRadius {c : ℝ × ℝ} (hc : c ∈ saddleSet)
    {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : MemLp (fun p ↦ f p / (saddleDist p : ℂ)) 2 (volume.restrict U)) :
    MemLp (fun p ↦ f p / (localRadius c p : ℂ)) 2 (volume.restrict U) := by
  have hm : Measurable (fun p ↦ ((saddleDist p / localRadius c p : ℝ) : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    apply Measurable.div (Metric.continuous_infDist_pt saddleSet).measurable
    exact (show Continuous (localRadius c) by unfold localRadius; fun_prop).measurable
  have hb : MemLp (fun p ↦ ((saddleDist p / localRadius c p : ℝ) : ℂ)) ⊤
      (volume.restrict U) := by
    apply memLp_top_of_bound hm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (show 0 ≤ saddleDist p from Metric.infDist_nonneg)
          (show 0 ≤ localRadius c p from Real.sqrt_nonneg _))]
      exact div_le_one_of_le₀ (saddleDist_le_localRadius hc p)
        (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)
  apply (hb.mul hf).ae_eq
  filter_upwards [ae_restrict_of_ae ae_saddleDist_ne_zero] with p hp
  have hd : (saddleDist p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  push_cast
  simp only [Pi.mul_apply, div_eq_mul_inv]
  calc _ = (f p * (localRadius c p : ℂ)⁻¹) *
        ((saddleDist p : ℂ) * (saddleDist p : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd, mul_one]

end NoEmbeddedEigenvalues
