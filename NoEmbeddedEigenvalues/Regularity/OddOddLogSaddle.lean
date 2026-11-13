import NoEmbeddedEigenvalues.Regularity.OddOddSaddle
import NoEmbeddedEigenvalues.RadialWeakMultiplier
import NoEmbeddedEigenvalues.DipoleLogMultiplier
import NoEmbeddedEigenvalues.SaddleStreamJet
import NoEmbeddedEigenvalues.SaddleLogarithmicMass
import NoEmbeddedEigenvalues.SaddleDistance

/-!
# Logarithmic mass of the saddle remainder gradient

Blueprint: `lem:log-radial-gradient`, `lem:dd-log-saddle-remainder`,
`lem:dd-log-saddle-gradient`, `lem:canonical-saddle-first-jet`,
`lem:dd-saddle-ray-quotients-h1`.

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
  refine ⟨ρ, hρ, a, fun j ↦ ?_⟩
  have hl := hD.log_radial_gradient (hDw 1 (by norm_num)) (hDw 2 le_rfl) j
  apply hl.congr_ae_on
  filter_upwards [hD.canonical_saddle_first j] with p hp hpU
  rw [hp hpU]

/-- Strong Cartesian H¹ quotients for ray traces, with the same quadratic
coefficient and canonical gradient entries as the bulk estimates. -/
theorem dd_saddle_ray_quotients_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : ℂ,
      MemSobolevOn 1 (localDisk c ρ) (fun p ↦
        (contStream ω p - saddleQuadratic c a p) / (Real.rpow (localRadius c p) 3 : ℂ)) ∧
      ∀ j : Fin 2, MemSobolevOn 1 (localDisk c ρ) (fun p ↦
        (streamJet2 ω [j] p - classicalComplexJet [j] (saddleQuadratic c a) p) /
          (Real.rpow (localRadius c p) 2 : ℂ)) := by
  intro c hc
  obtain ⟨ρ, hρ, a, ⟨D, hD, hDw⟩, _⟩ := (saddle_dd hlam hω hs).2 c hc
  have hQ := hD.radial_ray_quotients_h1 (hDw 0 (by norm_num))
    (hDw 1 (by norm_num)) (hDw 2 le_rfl)
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  refine ⟨ρ, hρ, a, hQ.1, fun j ↦ ?_⟩
  apply (hQ.2 j).congr_ae_on hU.measurableSet
  filter_upwards [hD.canonical_saddle_first j] with p hp hpU
  rw [hp hpU]

/-- The full saddle-weighted logarithmic gradient bound on one disk about each
saddle, with the lattice distance and the unchanged canonical stream jet. -/
theorem dd_log_saddle_gradient {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∀ j : Fin 2,
      MemSobolevLocOn 0 (localDisk c ρ) (fun p ↦
        (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω [j] p /
          (Real.rpow (saddleDist p) (3 / 2) : ℂ)) := by
  intro c hc
  obtain ⟨r, hr, a, hR⟩ := dd_log_saddle_remainder hlam hω hs c hc
  obtain ⟨q, hq, hQ⟩ := saddleQuadratic_log_gradient hc
  let ρ := min r (min q (Real.pi / 4))
  have hρ : 0 < ρ := lt_min hr (lt_min hq (by positivity))
  have hρr : ρ ≤ r := min_le_left _ _
  have hρq : ρ ≤ q := (min_le_right _ _).trans (min_le_left _ _)
  have hρpi : ρ ≤ Real.pi / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hsubr : localDisk c ρ ⊆ localDisk c r := fun _ hp ↦ lt_of_lt_of_le hp hρr
  have hsubq : localDisk c ρ ⊆ localDisk c q := fun _ hp ↦ lt_of_lt_of_le hp hρq
  have hball : localDisk c ρ ⊆ Metric.ball c (Real.pi / 2) := by
    intro p hp
    exact (dist_le_localRadius c p).trans_lt ((lt_of_lt_of_le hp hρpi).trans
      (by linarith [Real.pi_pos]))
  refine ⟨ρ, hρ, fun j ↦ ?_⟩
  have hQloc : MemSobolevLocOn 0 (localDisk c ρ) (fun p ↦
      (Real.sqrt (dipoleLogWeight p) : ℂ) *
        classicalComplexJet [j] (saddleQuadratic c a) p /
          (Real.rpow (localRadius c p) (3 / 2) : ℂ)) :=
    (show MemSobolevOn 0 (localDisk c q) _ from hQ a j).memSobolevLocOn.mono hsubq
  have hfull : MemSobolevLocOn 0 (localDisk c ρ) (fun p ↦
      (Real.sqrt (dipoleLogWeight p) : ℂ) * streamJet2 ω [j] p /
        (Real.rpow (localRadius c p) (3 / 2) : ℂ)) := by
    apply (((hR j).mono hsubr).add hQloc).congr_ae_on
    exact Filter.Eventually.of_forall fun p _ ↦ by ring
  exact hfull.div_saddleDist_of_radius hc hball (by norm_num)

end NoEmbeddedEigenvalues
