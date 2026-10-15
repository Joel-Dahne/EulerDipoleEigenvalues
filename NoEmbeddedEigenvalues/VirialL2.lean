import NoEmbeddedEigenvalues.VirialQuadratic
import NoEmbeddedEigenvalues.LiftTorus

/-!
# The virial identities on the `L²` domain

Blueprint: `lem:virial-l2` (stated).

For a `C^{2,1}` adapted field `W` with `C^{1,1}` coefficient `f`, the two smooth virial
identities (`VirialSmooth.lean`, `VirialQuadratic.lean`) hold for every eigenfunction
`ω ∈ L²`, with no further regularity. Derivatives of `ψ = Δ⁻¹ω` are the lifts of the
Fourier-defined ones, `Δψ = ω`, and `Δ(f - div W)` is the a.e. classical Laplacian of a
`C^{1,1}` function.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex

/-- The virial identities for an `L²` eigenfunction (`lem:virial-l2`):
    `Re⟨fω, ω + ψ⟩ = 2 Re⟨Dψ, ω⟩` with `D = W·∇ + ½ div W`, and the quadratic form
    `∫ f|ω|² + ∫ (2 sym DW - f I)∇ψ·∇ψ̄ + ½ ∫ Δ(f - div W)|ψ|² = 0`. -/
theorem virial_l2 {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₁L : ∃ K, LipschitzWith K (iteratedFDeriv ℝ 2 W₁))
    (hW₂ : ContDiff ℝ 2 W₂) (hW₂L : ∃ K, LipschitzWith K (iteratedFDeriv ℝ 2 W₂))
    (hf : ContDiff ℝ 1 f) (hfL : ∃ K, LipschitzWith K (fderiv ℝ f))
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) :
    (squarePairing (fun p ↦ f p • liftL2 ω p) (fun p ↦ liftL2 ω p + streamLift ω p)).re =
      2 * (squarePairing (fun p ↦ W₁ p • streamLiftX ω p + W₂ p • streamLiftY ω p +
        ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift ω p) (liftL2 ω)).re ∧
    (squarePairing (fun p ↦ f p • liftL2 ω p) (liftL2 ω)).re +
      2 * ((squarePairing (fun p ↦ partialX W₁ p • streamLiftX ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialX W₂ p • streamLiftY ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialY W₁ p • streamLiftX ω p) (streamLiftY ω)).re +
        (squarePairing (fun p ↦ partialY W₂ p • streamLiftY ω p) (streamLiftY ω)).re) -
      (squarePairing (fun p ↦ f p • streamLiftX ω p) (streamLiftX ω)).re -
      (squarePairing (fun p ↦ f p • streamLiftY ω p) (streamLiftY ω)).re +
      (1 / 2) * (squarePairing
        (fun p ↦ laplacian (fun q ↦ f q - divergence W₁ W₂ q) p • streamLift ω p)
        (streamLift ω)).re = 0 := by
  sorry

end NoEmbeddedEigenvalues
