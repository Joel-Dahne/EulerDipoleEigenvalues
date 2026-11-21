import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.SaddleQuadraticJet

/-! # Canonical first stream jet at a saddle -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

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
