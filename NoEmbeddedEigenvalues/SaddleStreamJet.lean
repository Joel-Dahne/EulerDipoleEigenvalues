import NoEmbeddedEigenvalues.SaddleTaylorJet
import NoEmbeddedEigenvalues.StreamJet

/-!
# Canonical stream and quadratic saddle jets

Blueprint: `lem:canonical-saddle-first-jet`, `lem:saddle-quadratic-first-jet`.

Weak uniqueness compares the original remainder jet with the fixed Fourier
stream derivatives. The explicit quadratic gradient grows linearly in the
Euclidean radius. These identities do not require logarithmic weights or
ordinary across-separatrix regularity.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The first classical quadratic jet, in the original Cartesian coordinates. -/
theorem first_saddleQuadratic (c : ℝ × ℝ) (a : ℂ) (j : Fin 2) (p : ℝ × ℝ) :
    classicalComplexJet [j] (saddleQuadratic c a) p =
      (if j = 0 then -1 else 1 : ℂ) * (a * (Real.cos c.1 : ℂ)) *
        ((axisCoord j p - axisCoord j c : ℝ) : ℂ) := by
  fin_cases j
  · have hd := ((((hasDerivAt_id p.1).sub_const c.1).pow 2).const_sub
        ((p.2 - c.2) ^ 2)).ofReal_comp.const_mul (a * (Real.cos c.1 : ℂ) / 2)
    convert hd.deriv using 1 <;>
      simp [classicalComplexJet, coordPartial, partialX, saddleQuadratic, axisCoord]
    ring
  · have hd := ((((hasDerivAt_id p.2).sub_const c.2).pow 2).sub_const
        ((p.1 - c.1) ^ 2)).ofReal_comp.const_mul (a * (Real.cos c.1 : ℂ) / 2)
    convert hd.deriv using 1 <;>
      simp [classicalComplexJet, coordPartial, partialY, saddleQuadratic, axisCoord]
    ring

/-- Linear growth of the fixed classical quadratic gradient. -/
theorem norm_first_saddleQuadratic_le (c : ℝ × ℝ) (a : ℂ) (j : Fin 2)
    (p : ℝ × ℝ) :
    ‖classicalComplexJet [j] (saddleQuadratic c a) p‖ ≤
      ‖a * (Real.cos c.1 : ℂ)‖ * localRadius c p := by
  have hcoord : |axisCoord j p - axisCoord j c| ≤ dist p c := by
    fin_cases j <;> simp [axisCoord, Prod.dist_eq, Real.dist_eq]
  have hsign : ‖(if j = 0 then -1 else 1 : ℂ)‖ = 1 := by split_ifs <;> norm_num
  rw [first_saddleQuadratic, norm_mul, norm_mul, hsign, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hcoord.trans (dist_le_localRadius c p)) (norm_nonneg _)

/-- Weak uniqueness identifies the original specified remainder entries with the
fixed canonical stream jet minus the same classical quadratic jet. -/
theorem HasWeakJetOn.canonical_saddle_first {ω : L2} {c : ℝ × ℝ} {ρ : ℝ} {a : ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ)
      (fun p ↦ contStream ω p - saddleQuadratic c a p) D) (j : Fin 2) :
    ∀ᵐ p, p ∈ localDisk c ρ → D [j] p = streamJet2 ω [j] p -
      classicalComplexJet [j] (saddleQuadratic c a) p := by
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (saddleQuadratic c a) := by
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (((contDiff_snd.sub contDiff_const).pow 2).sub
        ((contDiff_fst.sub contDiff_const).pow 2)))
  have hQjet := classicalComplexJet_weak hQ 2 (localDisk c ρ)
  have hsum : HasWeakJetOn 2 (localDisk c ρ) (contStream ω)
      (fun w p ↦ D w p + classicalComplexJet w (saddleQuadratic c a) p) := by
    refine ⟨?_, fun w hw j ↦ (hD.2 w hw j).add (hQjet.2 w hw j)⟩
    funext p
    dsimp only
    rw [congrFun hD.1 p]
    simp only [classicalComplexJet]
    ring
  filter_upwards [hsum.ae_eq hU (streamJet2_weak ω (localDisk c ρ)) [j] (by simp)]
    with p hp hpU
  exact (eq_sub_iff_add_eq).2 (hp hpU)

end NoEmbeddedEigenvalues
