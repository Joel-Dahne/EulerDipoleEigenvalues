import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTimeSynthesis
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTrigParity
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierForcing

/-!
# The actual physical forcing's trigonometric spectral candidate

The signed-mode folding and constant-mode identities are derived from the
original Poisson data, not imposed on a separate spectral forcing. Its allowed
spectral inverse has finite weighted L² and L¹ norms and a bounded continuous,
periodic synthesis with the original two pointwise reflection signs.
Identification of this synthesis with weak inverse Fourier derivatives remains
a separate analytic step.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- The original forcing supplies the signed pair needed by trigonometric folding. -/
theorem cylinder_forcing_trig_pair {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) {m : ℕ} (hm : m ≠ 0) :
    let hG := cylinderForcing_memLp hF
    let Φ := cylinderFourierData hG
    ∀ᵐ ξ ∂cylinderFrequencyMeasure, ∀ θ : ℝ,
      Complex.exp (Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) * Φ (ξ, (m : ℤ)) +
        Complex.exp (-Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) * Φ (ξ, -(m : ℤ)) =
      cylinderAngularMode (ε 1) m θ * cylinderTrigFourierData (ε 1) hG (ξ, m) := by
  apply cylinderTrigFourierData_pair (ε 1) (cylinderForcing_memLp hF) hm
  simpa only [paritySign] using cylinder_forcing_fourier_neg hp hD hΔ hF (m : ℤ)

/-- The even constant mode is used once; the odd constant mode is genuinely zero. -/
theorem cylinder_forcing_trig_constant {a ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    let hG := cylinderForcing_memLp hF
    ∀ᵐ ξ ∂cylinderFrequencyMeasure, ∀ θ : ℝ,
      cylinderAngularMode (ε 1) 0 θ * cylinderTrigFourierData (ε 1) hG (ξ, 0) =
        cylinderFourierData hG (ξ, 0) := by
  apply cylinderTrigFourierData_constant (ε 1) (cylinderForcing_memLp hF)
  simpa only [paritySign, neg_zero] using cylinder_forcing_fourier_neg hp hD hΔ hF 0

/-- Nonresonant inversion of the actual folded forcing produces finite spectral
norms and a bounded, continuous, periodic candidate with the original parity.
This does not assert its physical weak Poisson identity. -/
theorem cylinder_forcing_trig_inverse {a ρ : ℝ} (ha : 1 ≤ a) {ε : Fin 2 → Bool}
    (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    let hG := cylinderForcing_memLp hF
    let μ := cylinderAllowedFourierMeasure {m | AllowedSaddleDegree ε m}
    let V := cylinderTrigInverse a (ε 1) hG
    (∀ᵐ p ∂cylinderPositiveFourierMeasure,
      ¬AllowedSaddleDegree ε p.2 → cylinderTrigFourierData (ε 1) hG p = 0) ∧
      MemLp V 2 μ ∧
      MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ ∧
      Integrable V μ ∧
      (∀ᵐ p ∂μ, cylinderSymbol a p.1 p.2 * V p = cylinderTrigFourierData (ε 1) hG p) ∧
      Continuous (cylinderSynthesis (ε 1) μ V) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x, ‖cylinderSynthesis (ε 1) μ V x‖ ≤ C) ∧
      (∀ t, Function.Periodic (fun θ ↦ cylinderSynthesis (ε 1) μ V (t, θ)) (2 * Real.pi)) ∧
      ∀ t θ,
        cylinderSynthesis (ε 1) μ V (t, Real.pi - θ) =
          paritySign (ε 0) * cylinderSynthesis (ε 1) μ V (t, θ) ∧
        cylinderSynthesis (ε 1) μ V (t, -θ) =
          paritySign (ε 1) * cylinderSynthesis (ε 1) μ V (t, θ) := by
  dsimp only
  let M : Set ℕ := {m | AllowedSaddleDegree ε m}
  obtain ⟨hV, hWV, hL1, hσ, hCont, hBound⟩ :=
    cylinderTrigInverse_spectral_bounds ha (M := M) hgap (ε 1) (cylinderForcing_memLp hF)
  refine ⟨?_, hV, hWV, hL1, hσ, hCont, hBound,
    fun t ↦ cylinderSynthesis_periodic _ _ _ t, ?_⟩
  · apply cylinderTrigFourierData_support (ε 1) (cylinderForcing_memLp hF) (M := M)
    intro m hm
    apply (cylinder_forcing_modes hp hD hΔ hF (m : ℤ)).2
    change ¬AllowedSaddleDegree ε m at hm
    simpa only [Int.natAbs_natCast] using hm
  · intro t θ
    refine ⟨cylinderSynthesis_pi_sub (ae_mem_cylinderAllowedFourierMeasure M) _ t θ, ?_⟩
    simpa only [paritySign] using cylinderSynthesis_neg (ε 1)
      (cylinderAllowedFourierMeasure M) (cylinderTrigInverse a (ε 1) (cylinderForcing_memLp hF)) t θ

/-- Each allowed mode of the physical forcing's candidate has genuine time L²
and exact inverse Plancherel mass, with no extra mode-finiteness hypothesis. -/
theorem cylinder_forcing_trig_time_mode {a ρ : ℝ} (ha : 1 ≤ a) {ε : Fin 2 → Bool}
    (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {F : ℝ × ℝ → ℂ}
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) {m : ℕ} (hm : AllowedSaddleDegree ε m) :
    let f := fun ξ ↦ cylinderTrigInverse a (ε 1) (cylinderForcing_memLp hF) (ξ, m)
    MemLp (cylinderTimeSynthesis f) 2 volume ∧
      (∫ t, ‖cylinderTimeSynthesis f t‖ ^ 2) = ∫ ξ, ‖f ξ‖ ^ 2 ∂cylinderFrequencyMeasure := by
  exact ⟨(cylinderTrigInverse_time_modes ha (M := {m | AllowedSaddleDegree ε m})
    hgap (ε 1) (cylinderForcing_memLp hF) hm).1,
    cylinderTrigInverse_time_mass ha (M := {m | AllowedSaddleDegree ε m})
      hgap (ε 1) (cylinderForcing_memLp hF) hm⟩

end NoEmbeddedEigenvalues
