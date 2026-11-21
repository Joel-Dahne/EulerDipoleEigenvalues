module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierForcing
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderSignedInverse
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderJointParity

/-!
# Actual joint L² inverse candidate from the physical Poisson data

The original weighted forcing produces its own normalized signed spectrum and
allowed support. Its nonresonant quotient reconstructs a continuous, bounded,
parity-preserving function with genuine joint cylinder L² and exact Plancherel
mass. Its angular coefficients are the actual time inverse integrals. Spectral
multiplier equations do not yet assert weak derivatives or the physical PDE.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Original Poisson data supply every support premise of signed inversion. -/
theorem cylinder_forcing_signed_inverse_bounds {a ρ : ℝ} (ha : 1 ≤ a)
    {ε : Fin 2 → Bool} (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    let V := cylinderSignedInverse a (cylinderForcing_memLp hF)
    MemLp V 2 cylinderFourierMeasure ∧
      MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * V p) 2 cylinderFourierMeasure ∧
      Integrable V cylinderFourierMeasure ∧
      (∀ᵐ p ∂cylinderFourierMeasure,
        cylinderSymbol a p.1 p.2.natAbs * V p =
          cylinderFourierData (cylinderForcing_memLp hF) p) ∧
      ∀ᵐ p ∂cylinderFourierMeasure, ¬AllowedSaddleDegree ε p.2.natAbs → V p = 0 := by
  exact cylinderSignedInverse_bounds ha (M := {m | AllowedSaddleDegree ε m}) hgap
    (cylinderForcing_memLp hF) (cylinder_forcing_fourier_data hp hD hΔ hF).2.2

/-- The actual signed quotient retains the specified negative-mode sign. -/
theorem cylinder_forcing_signed_inverse_neg {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) (n : ℤ) :
    let V := cylinderSignedInverse a (cylinderForcing_memLp hF)
    (fun ξ ↦ V (ξ, -n)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ paritySign (ε 1) * V (ξ, n) := by
  filter_upwards [cylinder_forcing_fourier_neg hp hD hΔ hF n] with ξ hξ
  dsimp only [cylinderSignedInverse]
  rw [Int.natAbs_neg, hξ]
  ring

/-- Genuine joint L², coefficient identification and pointwise parity of the
actual physical forcing's inverse integral, without an extra reconstruction premise. -/
theorem cylinder_forcing_joint_inverse {a ρ : ℝ} (ha : 1 ≤ a) {ε : Fin 2 → Bool}
    (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    let V := cylinderSignedInverse a (cylinderForcing_memLp hF)
    let S := cylinderJointSynthesis V
    Continuous S ∧ MemLp S 2 logCylinderMeasure ∧
      (∫ q, ‖S q‖ ^ 2 ∂logCylinderMeasure) = ∫ p, ‖V p‖ ^ 2 ∂cylinderFourierMeasure ∧
      (∀ n : ℤ, ∀ t : ℝ, cylinderAngularCoeff S n t =
        cylinderTimeSynthesis (fun ξ ↦ V (ξ, n)) t) ∧
      (∀ t : ℝ, ∀ θ : AddCircle (2 * Real.pi),
        S (t, (Real.pi : AddCircle (2 * Real.pi)) - θ) = paritySign (ε 0) * S (t, θ) ∧
        S (t, -θ) = paritySign (ε 1) * S (t, θ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ q, ‖S q‖ ≤ C := by
  have hV := cylinder_forcing_signed_inverse_bounds ha hgap hp hD hΔ hF
  have h1 := hV.2.2.1
  refine ⟨continuous_cylinderJointSynthesis h1, cylinderJointSynthesis_memLp h1 hV.1,
    cylinderJointSynthesis_sq_mass h1 hV.1, cylinderJointSynthesis_coeff h1,
    cylinderJointSynthesis_parity h1 hV.2.2.2.2
      (cylinder_forcing_signed_inverse_neg hp hD hΔ hF), ?_⟩
  refine ⟨(∫ p, ‖cylinderSignedInverse a (cylinderForcing_memLp hF) p‖
    ∂cylinderFourierMeasure) + 1, ?_, ?_⟩
  · positivity
  · intro q
    exact (norm_cylinderJointSynthesis_le h1 q).trans (by linarith)

end NoEmbeddedEigenvalues
