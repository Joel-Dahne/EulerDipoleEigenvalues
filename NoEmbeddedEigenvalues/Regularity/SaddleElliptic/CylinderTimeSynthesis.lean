module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTrigInverse
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.FourierL2Integral

/-!
# Normalized real-line inverse synthesis of actual cylinder modes

The integral uses `dξ / (2 * π)` and phase `exp (I * t * ξ)`. Returning its data
to cycle frequency identifies the actual integral with the unitary L² inverse.
In particular, every allowed mode of the bounded spectral candidate has genuine
real-line L² mass. This is modewise identification, not the whole cylinder PDE.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Actual angular-frequency inverse integral for a single mode. -/
def cylinderTimeSynthesis (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ξ, Complex.exp (Complex.I * ((t * ξ : ℝ) : ℂ)) * f ξ ∂cylinderFrequencyMeasure

/-- The same data, rescaled to cycles and inverted in real-line L². -/
def cylinderTimeInverseClass {f : ℝ → ℂ} (h2 : MemLp f 2 cylinderFrequencyMeasure) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  FourierTransform.fourierInv ((h2.comp_measurePreserving
    measurePreserving_cylinderAngularFrequency).toLp (fun η ↦ f ((2 * Real.pi) * η)))

/-- Forward frequency dilation is also an embedding for actual integrals. -/
theorem measurableEmbedding_cylinderAngularFrequency :
    MeasurableEmbedding (fun η : ℝ ↦ (2 * Real.pi) * η) := by
  have hp : 2 * Real.pi ≠ 0 := by positivity
  simpa only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀] using
    (Homeomorph.mulLeft₀ (2 * Real.pi) hp).toMeasurableEquiv.measurableEmbedding

/-- Exact normalization of the actual integral, before any L² identification. -/
theorem cylinderTimeSynthesis_eq_fourierInv (f : ℝ → ℂ) (t : ℝ) :
    cylinderTimeSynthesis f t =
      FourierTransform.fourierInv (fun η ↦ f ((2 * Real.pi) * η)) t := by
  calc
    _ = ∫ η, Complex.exp (Complex.I * ((t * ((2 * Real.pi) * η) : ℝ) : ℂ)) *
        f ((2 * Real.pi) * η) :=
      (measurePreserving_cylinderAngularFrequency.integral_comp
        measurableEmbedding_cylinderAngularFrequency _).symm
    _ = _ := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η ↦ by
        dsimp only
        rw [smul_eq_mul]
        congr 2
        change Complex.I * ((t * ((2 * Real.pi) * η) : ℝ) : ℂ) =
          ((2 * Real.pi * (t * η) : ℝ) : ℂ) * Complex.I
        push_cast
        ring

/-- Genuine L¹ ∩ L² frequency data give the specified L² inverse a.e. -/
theorem cylinderTimeSynthesis_ae_inverse {f : ℝ → ℂ}
    (h1 : Integrable f cylinderFrequencyMeasure) (h2 : MemLp f 2 cylinderFrequencyMeasure) :
    (cylinderTimeInverseClass h2 : ℝ → ℂ) =ᵐ[volume] cylinderTimeSynthesis f := by
  have ht := fourierInv_L2_ae_integral
    (measurePreserving_cylinderAngularFrequency.integrable_comp_of_integrable h1)
    (h2.comp_measurePreserving measurePreserving_cylinderAngularFrequency)
  filter_upwards [ht] with t ht
  exact ht.trans (cylinderTimeSynthesis_eq_fourierInv f t).symm

/-- Actual finite time mass follows from the L² representative identity. -/
theorem cylinderTimeSynthesis_memLp {f : ℝ → ℂ}
    (h1 : Integrable f cylinderFrequencyMeasure) (h2 : MemLp f 2 cylinderFrequencyMeasure) :
    MemLp (cylinderTimeSynthesis f) 2 volume :=
  (Lp.memLp (cylinderTimeInverseClass h2)).ae_eq (cylinderTimeSynthesis_ae_inverse h1 h2)

/-- Exact Plancherel mass of the actual normalized inverse integral. -/
theorem cylinderTimeSynthesis_sq_mass {f : ℝ → ℂ}
    (h1 : Integrable f cylinderFrequencyMeasure) (h2 : MemLp f 2 cylinderFrequencyMeasure) :
    (∫ t, ‖cylinderTimeSynthesis f t‖ ^ 2) = ∫ ξ, ‖f ξ‖ ^ 2 ∂cylinderFrequencyMeasure := by
  let k : Lp ℂ 2 (volume : Measure ℝ) :=
    (h2.comp_measurePreserving measurePreserving_cylinderAngularFrequency).toLp
      (fun η ↦ f ((2 * Real.pi) * η))
  calc
    _ = ∫ t, ‖cylinderTimeInverseClass h2 t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [cylinderTimeSynthesis_ae_inverse h1 h2] with t ht
      rw [ht]
    _ = ‖cylinderTimeInverseClass h2‖ ^ 2 := (cylinderRealL2_norm_sq _).symm
    _ = ‖k‖ ^ 2 := by
      change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm k‖ ^ 2 = ‖k‖ ^ 2
      rw [LinearIsometryEquiv.norm_map]
    _ = ∫ η, ‖k η‖ ^ 2 := cylinderRealL2_norm_sq k
    _ = ∫ η, ‖f ((2 * Real.pi) * η)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(h2.comp_measurePreserving
        measurePreserving_cylinderAngularFrequency).coeFn_toLp] with η hη
      rw [show k η = f ((2 * Real.pi) * η) from hη]
    _ = _ := measurePreserving_cylinderAngularFrequency.integral_comp
      measurableEmbedding_cylinderAngularFrequency (fun ξ ↦ ‖f ξ‖ ^ 2)

/-- Every allowed mode of the actual spectral candidate has an identified
real-line L² inverse. No extra mode integrability hypothesis is accepted. -/
theorem cylinderTrigInverse_time_modes {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    {m : ℕ} (hm : m ∈ M) :
    let f := fun ξ ↦ cylinderTrigInverse a even hG (ξ, m)
    MemLp (cylinderTimeSynthesis f) 2 volume ∧
      (cylinderTimeInverseClass (cylinderTrigInverse_mode_bounds ha hgap even hG hm).2 :
        ℝ → ℂ) =ᵐ[volume] cylinderTimeSynthesis f := by
  have hs := cylinderTrigInverse_mode_bounds ha hgap even hG hm
  exact ⟨cylinderTimeSynthesis_memLp hs.1 hs.2, cylinderTimeSynthesis_ae_inverse hs.1 hs.2⟩

/-- The actual time integral of each allowed candidate mode has exact finite mass. -/
theorem cylinderTrigInverse_time_mass {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    {m : ℕ} (hm : m ∈ M) :
    (∫ t, ‖cylinderTimeSynthesis (fun ξ ↦ cylinderTrigInverse a even hG (ξ, m)) t‖ ^ 2) =
      ∫ ξ, ‖cylinderTrigInverse a even hG (ξ, m)‖ ^ 2 ∂cylinderFrequencyMeasure := by
  have hs := cylinderTrigInverse_mode_bounds ha hgap even hG hm
  exact cylinderTimeSynthesis_sq_mass hs.1 hs.2

end NoEmbeddedEigenvalues
