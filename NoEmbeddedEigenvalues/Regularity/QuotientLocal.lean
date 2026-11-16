import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.TraceL2
import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.WeightedTransport
import NoEmbeddedEigenvalues.FirstTransportGain

/-!
# Local analytic interfaces for the quotient construction

Weak derivative jets specify derivatives rather than differentiating arbitrary Sobolev
representatives. Radial integrability is stated separately from energies, so a default
Bochner integral cannot stand in for a divergent norm. The radius is Euclidean: the
usual metric on a product of real normed spaces uses the maximum norm.

All division identities and parity hypotheses are a.e. identities on their domains.
The derivative jets in point removal are only required on the punctured disk.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- One-coordinate H³ division, including the uniform H² bound (`lem:odd-h3-division`). -/
theorem odd_h3_division {l r b : ℝ} (hlr : l < r) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (axisRectangle 1 b l r) R →
      HasWeakJetOn 3 (axisRectangle 1 b l r) R D →
      (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R (axisReflect 1 p) = -R p) →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (axisRectangle 1 b l r) V ∧
        HasWeakJetOn 2 (axisRectangle 1 b l r) V E ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R p = (p.2 : ℂ) * V p) ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), V (axisReflect 1 p) = V p) ∧
        weakJetEnergy 2 (axisRectangle 1 b l r) E ≤
          C * weakJetEnergy 3 (axisRectangle 1 b l r) D := by
  sorry

/-- Weighted double division (`lem:weighted-double-division`), in squared-energy form.
No fourth derivative and no weighted order-zero hypothesis on R is imposed. -/
theorem weighted_double_division {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (localDisk 0 ρ) R → HasWeakJetOn 3 (localDisk 0 ρ) R D →
      (∀ j, ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R (axisReflect j p) = -R p) →
      RadialJetLp 1 3 (localDisk 0 ρ) 0 D →
      RadialJetLp 2 2 (localDisk 0 ρ) 0 D →
      RadialJetLp 3 1 (localDisk 0 ρ) 0 D →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V ∧
        HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V E ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R p = ((p.1 * p.2 : ℝ) : ℂ) * V p) ∧
        RadialJetLp 0 2 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 1 1 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 2 0 (localDisk 0 ρ) 0 E ∧
        radialJetEnergy 0 2 (localDisk 0 ρ) 0 E +
          radialJetEnergy 1 1 (localDisk 0 ρ) 0 E +
          radialJetEnergy 2 0 (localDisk 0 ρ) 0 E ≤
          C * (radialJetEnergy 1 3 (localDisk 0 ρ) 0 D +
            radialJetEnergy 2 2 (localDisk 0 ρ) 0 D +
            radialJetEnergy 3 1 (localDisk 0 ρ) 0 D) := by
  sorry

/-- Weighted removal of a point, with a genuine continuous representative
(`lem:weighted-h2-point-removal`). No assigned raw value at zero is used. -/
theorem weighted_h2_point_removal {ρ : ℝ} (hρ : 0 < ρ) {V : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hV : MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V D)
    (h0 : RadialJetLp 0 2 (localDisk 0 ρ) 0 D)
    (h1 : RadialJetLp 1 1 (localDisk 0 ρ) 0 D)
    (h2 : RadialJetLp 2 0 (localDisk 0 ρ) 0 D) :
    MemSobolevOn 2 (localDisk 0 ρ) V ∧
      ∃ g : ℝ × ℝ → ℂ, ContinuousOn g (localDisk 0 ρ) ∧ g 0 = 0 ∧
        V =ᵐ[volume.restrict (localDisk 0 ρ)] g := by
  sorry

/-- Coordinate Hardy for either axis, using specified weak derivatives
(`lem:even-h2-axis-hardy`). -/
theorem even_h2_axis_hardy {j : Fin 2} {a l r : ℝ} (ha : 0 < a) (hlr : l < r)
    {F d dd : ℝ × ℝ → ℂ} (hF : MemSobolevOn 2 (axisRectangle j a l r) F)
    (he : ∀ᵐ p ∂(volume.restrict (axisRectangle j a l r)), F (axisReflect j p) = F p)
    (hd : HasWeakPartialOn (axisRectangle j a l r) j F d)
    (hdd : HasWeakPartialOn (axisRectangle j a l r) j d dd) :
    MemLp (fun p ↦ d p / (axisCoord j p : ℂ)) 2 (volume.restrict (axisRectangle j a l r)) ∧
      (∫ p in axisRectangle j a l r, ‖d p / (axisCoord j p : ℂ)‖ ^ 2) ≤
        4 * ∫ p in axisRectangle j a l r, ‖dd p‖ ^ 2 := by
  sorry

/-- Interior elliptic H³ regularity, with the Laplacian identified weakly
(the regularity part of `lem:elliptic-local`). -/
theorem elliptic_local_h3 {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u F : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hu : MemSobolevLocOn 2 U u)
    (hF : MemSobolevLocOn 1 U F) (hD : HasWeakJetOn 2 U u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict U), D [0, 0] p + D [1, 1] p = F p) :
    MemSobolevLocOn 3 U u := by
  sorry

/-- Uniform squared dyadic elliptic estimate (`lem:elliptic-dyadic`). -/
theorem elliptic_dyadic : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ × ℝ) (r : ℝ), 0 < r →
    ∀ (u F : ℝ × ℝ → ℂ) (D G : List (Fin 2) → ℝ × ℝ → ℂ),
      let A := {p | r < localRadius c p ∧ localRadius c p < 2 * r}
      let B := {p | r / 2 < localRadius c p ∧ localRadius c p < 4 * r}
      MemSobolevOn 2 B u → MemSobolevOn 1 B F →
      HasWeakJetOn 3 B u D → HasWeakJetOn 1 B F G →
      (∀ᵐ p ∂(volume.restrict B), D [0, 0] p + D [1, 1] p = F p) →
      RadialJetLp 3 0 A c D ∧
        radialJetEnergy 3 0 A c D ≤ C * (radialJetEnergy 1 0 B c G +
          r⁻¹ ^ 2 * radialJetEnergy 0 0 B c G + r⁻¹ ^ 6 * radialJetEnergy 0 0 B c D) := by
  sorry

/-- Second transport gain (`lem:transport-second-gain`), with an actual continuous
forcing representative and weak derivatives rather than pointwise derivatives. -/
theorem transport_second_gain {lam δ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / ((saddleDist p) ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
  sorry

end NoEmbeddedEigenvalues
