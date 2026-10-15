import NoEmbeddedEigenvalues.Sectors
import NoEmbeddedEigenvalues.NormalField
import NoEmbeddedEigenvalues.FlowBoundaryForm
import NoEmbeddedEigenvalues.Transport

/-!
# Even–even exclusion

The top-level statement of blueprint `thm:ee-exclusion`, and the statements of the lemmas
its proof uses: `lem:ee-neumann`, `lem:ee-truncated-virial`, `lem:ee-gradient-traces`,
`lem:ee-boundary-regularity`. Levels are handled in orbit coordinates: boundary terms are
flow-time integrals over almost every level, and limits are taken along levels outside a
null set. The analytic sector argument is not yet formalized.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set

/-- The normal derivative `ψₙ` of the stream function of `ω` (outward from `{Ψ > 2h}`). -/
abbrev streamNormal (ω : L2) : ℝ × ℝ → ℂ := normalDeriv (streamLiftX ω) (streamLiftY ω)

/-- The tangential derivative `ψₜ` of the stream function of `ω`. -/
abbrev streamTangent (ω : L2) : ℝ × ℝ → ℂ := tangentDeriv (streamLiftX ω) (streamLiftY ω)

/-- Neumann condition (`lem:ee-neumann`): in the even–even sector `ψₙ` is odd and `ψₜ` is even
    under the reflections `S₂(x, y) = (y + π, x + π)` and `S₁(x, y) = (π - y, π - x)` across
    the lines carrying the separatrix arcs. -/
theorem ee_neumann {ω : L2} (hω : InSector true true ω) :
    (∀ᵐ p, streamNormal ω (p.2 + Real.pi, p.1 + Real.pi) = -streamNormal ω p ∧
      streamTangent ω (p.2 + Real.pi, p.1 + Real.pi) = streamTangent ω p) ∧
    (∀ᵐ p, streamNormal ω (Real.pi - p.2, Real.pi - p.1) = -streamNormal ω p ∧
      streamTangent ω (Real.pi - p.2, Real.pi - p.1) = streamTangent ω p) := by
  sorry

/-- The truncated virial identity (`lem:ee-truncated-virial`): for almost every `ε ∈ (0, 2)`,
    `∫_{Ψ > ε} J = ∮ Re(ψ ψ̄ₙ) dℓ + (2 - ε) ∮ (|ψₙ|² - |ψₜ|² - Re(ω ψ̄)) dt` over the level
    `{Ψ = ε}`, with `dℓ = ρ dt`. -/
theorem ee_truncated_virial {lam : ℝ} {ω : L2} (hω : IsEigenSolution lam ω) :
    ∀ᵐ ε ∂(volume.restrict (Ioo 0 2)),
      ∫ p in {p | p ∈ cellSquare ∧ ε < dipoleLift p},
          eeDensity p (liftL2 ω p) (streamNormal ω p) (streamTangent ω p) =
        levelIntegral (ε / 2) (fun p ↦
            gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) +
          (2 - ε) * levelIntegral (ε / 2) (fun p ↦
            ‖streamNormal ω p‖ ^ 2 - ‖streamTangent ω p‖ ^ 2 -
              (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) := by
  sorry

/-- Weighted gradient traces (`lem:ee-gradient-traces`). For `ψ` even under both reflections,
    along levels `h → 0` outside a null set: `∮ |ψₙ|² dt → 0`,
    `∮ |ψₜ|² dt → ∑_γ ∫ ½ cosh² s |g_γ'(s)|² ds` with `g_γ = ψ̃ ∘ γ` the arc traces (on an arc
    `|ψₜ|² = ½ cosh² s |g'|²`), and `∮ Re(ψ ψ̄ₙ) dℓ → 0`. -/
theorem ee_gradient_traces {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω) :
    (∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamTangent ω p‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∑ k ∈ Finset.range 4,
          ∫ s, Real.cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2)) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦
          gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  sorry

/-- Regularity of the boundary unknown (`lem:ee-boundary-regularity`). For an even–even
    eigenfunction with rotation character `κ`, on each arc `γ` the canonical transport unknown
    `z` of `g = ψ̃ ∘ γ`, written `F(ξ) = z(artanh ξ)`, lies in the weighted domain, `G =
    -iwF' - λF ∈ H¹(-1, 1)`, its endpoint values are `-c±/λ` with `c±` the saddle values of
    `ψ̃` at the ends of the arc, and `c₊ = κ c₋`. -/
theorem ee_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) {k : ℕ} (hk : k < 4) :
    ∃ D E : ℝ → ℂ,
      HasWeightedBoundaryH2 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D E ∧
      MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ -
        lam * canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D 1 = -contStream ω (rotLift^[k] (0, -Real.pi)) / lam ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D (-1) = -contStream ω (rotLift^[k] (Real.pi, 0)) / lam ∧
      contStream ω (rotLift^[k] (0, -Real.pi)) =
        paritySign κ * contStream ω (rotLift^[k] (Real.pi, 0)) := by
  sorry

/-- An eigenfunction even under both separatrix reflections vanishes
at every nonzero real spectral parameter. Proof pending. -/
theorem even_even_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true true ω) : ω = 0 := by
  sorry

end NoEmbeddedEigenvalues
