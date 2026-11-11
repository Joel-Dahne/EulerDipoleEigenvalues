import NoEmbeddedEigenvalues.Regularity.OddOddSaddle
import NoEmbeddedEigenvalues.RadialWeakMultiplier
import NoEmbeddedEigenvalues.DipoleLogMultiplier
import NoEmbeddedEigenvalues.StreamJet

/-!
# Logarithmic mass of the saddle remainder gradient

Blueprint: `lem:log-radial-gradient`, `lem:dd-log-saddle-remainder`.

The two strongest positive-order saddle weights give H¹ of ∂ⱼR/r^(3/2)
through the center. The physical logarithmic multiplier then applies. Weak jet
uniqueness identifies these same derivatives with the fixed canonical Fourier
stream jet minus the classical quadratic jet.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Logarithmic remainder mass from a specified weighted second jet. -/
theorem HasWeakJetOn.log_radial_gradient {c : ℝ × ℝ} {ρ : ℝ}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) F D)
    (h₁ : RadialJetLp 1 3 (localDisk c ρ) c D)
    (h₂ : RadialJetLp 2 2 (localDisk c ρ) c D) (j : Fin 2) :
    MemSobolevLocOn 0 (localDisk c ρ) (fun p ↦
      (Real.sqrt (dipoleLogWeight p) : ℂ) * D [j] p /
        (Real.rpow (localRadius c p) (3 / 2) : ℂ)) := by
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  simpa only [mul_div_assoc] using
    (hD.radial_gradient_h1 h₁ h₂ j).memSobolevLocOn.log_dipole_mul hU

/-- The logarithmic saddle-remainder bound uses the same canonical first stream
jet as numerator differentiation, not an independent spatial representative. -/
theorem dd_log_saddle_remainder {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : ℂ, ∀ j : Fin 2,
      MemSobolevLocOn 0 (localDisk c ρ) (fun p ↦
        (Real.sqrt (dipoleLogWeight p) : ℂ) *
          (streamJet2 ω [j] p - classicalComplexJet [j] (saddleQuadratic c a) p) /
            (Real.rpow (localRadius c p) (3 / 2) : ℂ)) := by
  intro c hc
  obtain ⟨ρ, hρ, a, ⟨D, hD, hDw⟩, _⟩ := (saddle_dd hlam hω hs).2 c hc
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
  refine ⟨ρ, hρ, a, fun j ↦ ?_⟩
  have hl := hD.log_radial_gradient (hDw 1 (by norm_num)) (hDw 2 le_rfl) j
  have he := hsum.ae_eq hU (streamJet2_weak ω (localDisk c ρ)) [j] (by simp)
  apply hl.congr_ae_on
  filter_upwards [he] with p hp hpU
  have he' : D [j] p = streamJet2 ω [j] p -
      classicalComplexJet [j] (saddleQuadratic c a) p :=
    (eq_sub_iff_add_eq).2 (hp hpU)
  rw [he']

end NoEmbeddedEigenvalues
