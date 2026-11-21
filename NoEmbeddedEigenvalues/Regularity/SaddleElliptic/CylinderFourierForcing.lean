import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierData
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderForcing

/-!
# Normalized Fourier data from the physical Poisson forcing

The specified weak Laplacian and solution parity produce the spectral support.
The exact squared-mass normalization is inherited from logarithmic-polar
transport and the unitary real-line L² transform. No extra forcing parity,
mode support, or time L¹ hypothesis is assumed.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Physical forcing gives genuine normalized product-spectral L² data with
allowed support and the exact physical-area mass, from the original hypotheses. -/
theorem cylinder_forcing_fourier_data {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    let Φ := cylinderFourierData (cylinderForcing_memLp hF)
    MemLp Φ 2 cylinderFourierMeasure ∧
      (∫ p, ‖Φ p‖ ^ 2 ∂cylinderFourierMeasure) = (2 * Real.pi)⁻¹ *
        ∫ p in localDisk 0 ρ, ‖F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)‖ ^ 2 ∧
      ∀ᵐ p ∂cylinderFourierMeasure,
        ¬AllowedSaddleDegree ε p.2.natAbs → Φ p = 0 := by
  dsimp only
  refine ⟨cylinderFourierData_memLp _, ?_, ?_⟩
  · exact (cylinderFourierData_sq_mass _).trans (cylinderForcing_sq_mass hF)
  · exact cylinderFourierData_support _ fun n hn ↦
      (cylinder_forcing_modes hp hD hΔ hF n).2 hn

/-- The second reflection sign relates negative and positive signed spectral
modes, distinguishing cosine from sine reconstruction at the same allowed degree. -/
theorem cylinder_forcing_fourier_neg {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) (n : ℤ) :
    let Φ := cylinderFourierData (cylinderForcing_memLp hF)
    (fun ξ ↦ Φ (ξ, -n)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ paritySign (ε 1) * Φ (ξ, n) := by
  apply cylinderFourierData_smul_modes
  apply cylinderFourierMode_smul_of_coeff_ae
  filter_upwards [(cylinder_forcing_data hp hD hΔ hF).2] with t ht
  exact (ht.1.coeff_characters n).2

end NoEmbeddedEigenvalues
