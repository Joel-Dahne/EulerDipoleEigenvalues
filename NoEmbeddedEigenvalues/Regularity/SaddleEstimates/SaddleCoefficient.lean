import NoEmbeddedEigenvalues.Analysis.LocalSobolev.RadialNonintegrability
import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.SaddleStreamJet
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleChartPullback

/-!
# Uniqueness of the normalized quadratic saddle coefficient

Two admissible second remainder jets have a difference equal to the classical
quadratic difference by weak uniqueness. Its xx entry is constant. The genuine
L² Hessian weight rules out any nonzero constant, even on different disk sizes.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The pure xx entry of the original quadratic is its fixed constant Hessian. -/
theorem second_fst_saddleQuadratic (c : ℝ × ℝ) (a : ℂ) (p : ℝ × ℝ) :
    classicalComplexJet [0, 0] (saddleQuadratic c a) p =
      -(a * (Real.cos c.1 : ℂ)) := by
  have he : classicalComplexJet [0] (saddleQuadratic c a) =
      fun q ↦ -(a * (Real.cos c.1 : ℂ)) * ((q.1 - c.1 : ℝ) : ℂ) := by
    funext q
    simp [first_saddleQuadratic, axisCoord]
  change coordPartial 0 (classicalComplexJet [0] (saddleQuadratic c a)) p = _
  rw [he]
  have hd := (((hasDerivAt_id p.1).sub_const c.1).ofReal_comp).const_mul
    (-(a * (Real.cos c.1 : ℂ)))
  simpa [coordPartial, partialX] using hd.deriv

/-- The normalized coefficient is independent of the weak-jet representatives
and of the admissible disk radii. Only the weighted order-two entries are needed. -/
theorem saddle_coefficient_unique {c : ℝ × ℝ} (hc : c ∈ saddleSet)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) {F : ℝ × ℝ → ℂ} {a b : ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) (fun p ↦ F p - saddleQuadratic c a p) D)
    (hE : HasWeakJetOn 2 (localDisk c σ) (fun p ↦ F p - saddleQuadratic c b p) E)
    (hDw : RadialJetLp 2 2 (localDisk c ρ) c D)
    (hEw : RadialJetLp 2 2 (localDisk c σ) c E) : a = b := by
  let U := localDisk c (min ρ σ)
  have huD : U ⊆ localDisk c ρ := by
    intro p hp
    exact lt_of_lt_of_le (show localRadius c p < min ρ σ from hp) (min_le_left _ _)
  have huE : U ⊆ localDisk c σ := by
    intro p hp
    exact lt_of_lt_of_le (show localRadius c p < min ρ σ from hp) (min_le_right _ _)
  have hu : IsOpen U := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  let G := fun w p ↦ D w p - E w p
  have hG : HasWeakJetOn 2 U (saddleQuadratic c (b - a)) G := by
    refine ⟨?_, ?_⟩
    · funext p
      dsimp only [G]
      rw [congrFun hD.1 p, congrFun hE.1 p]
      simp only [saddleQuadratic]
      ring
    · intro w hw j
      simpa only [G, neg_one_mul, ← sub_eq_add_neg] using
        ((hD.mono huD).2 w hw j).add (((hE.mono huE).2 w hw j).const_mul (-1))
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (saddleQuadratic c (b - a)) := by
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (((contDiff_snd.sub contDiff_const).pow 2).sub
        ((contDiff_fst.sub contDiff_const).pow 2)))
  have he := hG.ae_eq hu (classicalComplexJet_weak hQ 2 U) [0, 0] (by simp)
  have hw : MemLp (fun p ↦ (-((b - a) * (Real.cos c.1 : ℂ))) /
      (localRadius c p ^ 2 : ℂ)) 2 (volume.restrict U) := by
    apply (((hDw.mono huD) [0, 0] (by simp)).sub
      ((hEw.mono huE) [0, 0] (by simp))).ae_eq
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hu.measurableSet] with p hp hpU
    dsimp only [Pi.sub_apply]
    rw [← sub_div]
    rw [show D [0, 0] p - E [0, 0] p =
      classicalComplexJet [0, 0] (saddleQuadratic c (b - a)) p from hp hpU,
      second_fst_saddleQuadratic]
  have hz := (memLp_const_div_sq_localRadius_iff c (lt_min hρ hσ) _).mp hw
  have hcos : (Real.cos c.1 : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.cos c.1 ≠ 0 from by
      intro h
      simpa [h] using abs_cos_saddle hc)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_right hcos)).symm

/-- Existence of the original weighted remainder jet already gives a unique
coefficient on that disk. No stronger regularity of the numerator is assumed. -/
theorem existsUnique_saddle_coefficient_iff {c : ℝ × ℝ} (hc : c ∈ saddleSet)
    {ρ : ℝ} (hρ : 0 < ρ) {F : ℝ × ℝ → ℂ} :
    (∃! a : ℂ, ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 (localDisk c ρ) (fun p ↦ F p - saddleQuadratic c a p) D ∧
      ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D) ↔
    (∃ a : ℂ, ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 (localDisk c ρ) (fun p ↦ F p - saddleQuadratic c a p) D ∧
      ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D) := by
  refine ⟨ExistsUnique.exists, ?_⟩
  rintro ⟨a, D, hD, hDw⟩
  refine ⟨a, ⟨D, hD, hDw⟩, ?_⟩
  rintro b ⟨E, hE, hEw⟩
  exact saddle_coefficient_unique hc hρ hρ hE hD (hEw 2 le_rfl) (hDw 2 le_rfl)

end NoEmbeddedEigenvalues
