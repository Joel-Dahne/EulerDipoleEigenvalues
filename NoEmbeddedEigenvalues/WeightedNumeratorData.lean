import NoEmbeddedEigenvalues.OrbitNumerators

/-!
# Weighted numerator data

The forcing uses a continuous representative and a specified second weak jet.
The jet only names derivatives already supplied by H²; it is not an H³ hypothesis.
Ray values of the gradient are canonical Sobolev traces. Fiber integrability is
explicit before any Bochner-defined orbit energy is used. The quantitative bounds
are exported for logarithmic summation rather than hidden in a qualitative proof.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Squared order-k derivative density in the base quarter coordinates. -/
def quarterJetDensity (k : ℕ) (s : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) : ℝ :=
  ∑ w : Fin k → Fin 2, ‖D (List.ofFn w) (dipoleOrbit q.1 q.2) /
    (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2

/-- Actual fiber integrability, separate from the default-valued integral. -/
def QuarterJetIntegrable (k : ℕ) (s : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : Prop :=
  IntegrableOn (fun t ↦ quarterJetDensity k s D (h, t)) (Ioo (-eighthPeriod h) (eighthPeriod h))

/-- Quarter energy, used together with `QuarterJetIntegrable`. -/
def quarterJetEnergy (k : ℕ) (s : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), quarterJetDensity k s D (h, t)

/-- Weak level derivative of the forcing, via the smooth orbit-map level vector. -/
def quarterForcingLevelDerivative (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  let V := deriv (fun h : ℝ ↦ dipoleOrbit h q.2) q.1
  (V.1 : ℂ) * D [0] (dipoleOrbit q.1 q.2) +
    (V.2 : ℂ) * D [1] (dipoleOrbit q.1 q.2)

def quarterEndpointValueEnergy (g : ℝ × ℝ → ℂ) (h : ℝ) : ℝ :=
  (∑ side : Bool, ‖g (quarterEndpointRay side (quarterEndpointRadius h))‖ ^ 2) / h ^ 2

def quarterEndpointGradientEnergy (T : Bool → Fin 2 → ℝ → ℂ) (h : ℝ) : ℝ :=
  (∑ side : Bool, ∑ j : Fin 2, ‖T side j (quarterEndpointRadius h)‖ ^ 2) / h

/-- Compatible weak differentiations, canonical ray traces and uniform bounds. -/
structure WeightedQuarterNumeratorData (lam : ℝ) (U : Set (ℝ × ℝ))
    (g : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (h₀ : ℝ) where
  first : ℝ → ℂ
  second : ℝ → ℂ
  halfFirst : ℝ → ℂ
  numerator_h2 : HasIntervalH2Loc 0 h₀ (quarterNumerator lam g) first second
  half_h1 : HasIntervalH1Loc 0 h₀ (quarterHalfNumerator lam g) halfFirst
  first_lp : MemLp first 2 (volume.restrict (Ioo 0 h₀))
  half_lp : MemLp halfFirst 2 (volume.restrict (Ioo 0 h₀))
  second_lp : MemLp (fun (h : ℝ) ↦ (h : ℂ) * second h) 2 (volume.restrict (Ioo 0 h₀))
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < 1
  endpoint_radius_lt : quarterEndpointRadius h₀ < radius
  gradientTrace : Bool → Fin 2 → ℝ → ℂ
  ray_trace : ∀ side j, HasQuarterRayTrace U radius 0 side (D [j]) (gradientTrace side j)
  endpoint_value_lp : ∀ side, MemLp (fun (h : ℝ) ↦
    g (quarterEndpointRay side (quarterEndpointRadius h)) / (h : ℂ)) 2
      (volume.restrict (Ioo 0 h₀))
  endpoint_gradient_lp : ∀ side j, MemLp (fun (h : ℝ) ↦
    gradientTrace side j (quarterEndpointRadius h) / (Real.sqrt h : ℂ)) 2
      (volume.restrict (Ioo 0 h₀))
  fibers_integrable : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)),
    QuarterJetIntegrable 1 (3 / 2) D h ∧ QuarterJetIntegrable 1 0 D h ∧
      QuarterJetIntegrable 2 0 D h ∧
      IntegrableOn (fun t ↦ quarterForcingLevelDerivative D (h, t))
        (Ioo (-eighthPeriod h) (eighthPeriod h))
  mass_integrable : IntegrableOn (quarterJetEnergy 1 (3 / 2) D) (Ioo 0 h₀) ∧
    IntegrableOn (quarterJetEnergy 1 0 D) (Ioo 0 h₀) ∧
    IntegrableOn (quarterJetEnergy 2 0 D) (Ioo 0 h₀)
  forcing_level_weak : HasWeakPartialOn (quarterOrbitStrip h₀) 0
    (fun q ↦ g (dipoleOrbit q.1 q.2)) (quarterForcingLevelDerivative D)
  bound : ℝ
  bound_pos : 0 < bound
  subinterval_bound : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∀ a b : ℝ,
    -eighthPeriod h ≤ a → a ≤ b → b ≤ eighthPeriod h →
      ‖∫ t in a..b, quarterForcingLevelDerivative D (h, t) *
        Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ ^ 2 ≤
          bound * quarterJetEnergy 1 (3 / 2) D h
  first_bound : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)),
    ‖first h‖ ^ 2 + ‖halfFirst h‖ ^ 2 ≤
      bound * (quarterJetEnergy 1 (3 / 2) D h + quarterEndpointValueEnergy g h)
  second_bound : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), h ^ 2 * ‖second h‖ ^ 2 ≤
    bound * (quarterJetEnergy 2 0 D h + quarterJetEnergy 1 0 D h +
      quarterEndpointGradientEnergy gradientTrace h + quarterEndpointValueEnergy g h)

end NoEmbeddedEigenvalues
