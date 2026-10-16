import NoEmbeddedEigenvalues.VirialQuadratic
import NoEmbeddedEigenvalues.LiftTorus

/-!
# The virial identities on the `L²` domain

Blueprint: `lem:virial-exact-identity` (proved), `lem:virial-l2` (stated).

For a smooth adapted field `W` supported in a compact annulus `{2h₁ ≤ Ψ ≤ 2h₂}` of the
cells, `0 < h₁`, `h₂ < 1` (away from the separatrix and the centers), the two smooth virial
identities (`VirialSmooth.lean`, `VirialQuadratic.lean`) hold for every eigenfunction
`ω ∈ L²`, with no further regularity. Derivatives of `ψ = Δ⁻¹ω` are the lifts of the
Fourier-defined ones and `Δψ = ω`.

The planned proof (blueprint proof of `lem:virial-l2`) mollifies in the level variable of
action-angle coordinates (`lem:transversal-mollifier`) and uses the exact identity below with
`V = J_ε† D J_ε`; it needs no flow of `W`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex
open scoped InnerProductSpace

/-- The exact identity behind the virial argument (`lem:virial-exact-identity`): if
    `a = ω + ψ` and `Ha = λω` with `λ` real, then for every linear `V` defined on `ω` and `ψ`,
    `⟨Va, Ha⟩ - ⟨VHa, a⟩ = λ(⟨Vψ, ω⟩ - ⟨Vω, ψ⟩)`, because the two `⟨Vω, ω⟩` terms cancel.
    Mathlib's inner product is conjugate-linear in the first slot, so `⟨u, v⟩` here is
    `⟪v, u⟫`. -/
theorem inner_virial_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {M : Submodule ℂ E} (V : M →ₗ[ℂ] E) (ω ψ : M) (lam : ℝ) :
    ⟪(lam : ℂ) • (ω : E), V (ω + ψ)⟫_ℂ - ⟪((ω + ψ : M) : E), V ((lam : ℂ) • ω)⟫_ℂ =
      lam * (⟪(ω : E), V ψ⟫_ℂ - ⟪(ψ : E), V ω⟫_ℂ) := by
  simp only [map_add, map_smul, Submodule.coe_add, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_ofReal]
  ring

/-- Integration by parts for the stream function (`lem:stream-ibp`): for `ω ∈ L²` with mean
    zero, `ψ = Δ⁻¹ω ∈ H²` and smooth periodic real `φ`, with `K = |∇ψ|² + Re(ωψ̄)`,
    `½∫ Δφ |ψ|² = ∫ φK = -∫ Re(ψ̄ ∇φ·∇ψ)` over the period square. Both identities hold for
    trigonometric polynomials and are continuous in `H²`. -/
theorem stream_ibp {ω : L2} (hω : MeanZero ω) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hpφ : IsPeriodicLift φ) :
    (1 / 2) * (squarePairing (fun p ↦ laplacian φ p • streamLift ω p) (streamLift ω)).re =
      squareIntegral (fun p ↦ φ p * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 +
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) ∧
    squareIntegral (fun p ↦ φ p * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 +
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) =
      -squareIntegral (fun p ↦ (streamLift ω p * (starRingEnd ℂ)
        (partialX φ p • streamLiftX ω p + partialY φ p • streamLiftY ω p)).re) := by
  sorry

/-- The virial identities for an `L²` eigenfunction (`lem:virial-l2`), for a smooth adapted
    field supported in the annulus `{2h₁ ≤ Ψ ≤ 2h₂}`: `Re⟨fω, ω + ψ⟩ = 2 Re⟨Dψ, ω⟩` with
    `D = W·∇ + ½ div W`, and the quadratic form
    `∫ f|ω|² + ∫ (2 sym DW - f I)∇ψ·∇ψ̄ + ½ ∫ Δ(f - div W)|ψ|² = 0`. -/
theorem virial_l2 {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 3 W₁) (hW₂ : ContDiff ℝ 3 W₂) (hf : ContDiff ℝ 2 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₂1 : h₂ < 1)
    (hsupp : ∀ p, (W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0) →
      2 * h₁ ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * h₂)
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
