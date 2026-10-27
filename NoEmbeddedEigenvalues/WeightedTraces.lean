import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.TraceL2

/-!
# Canonical corner and crossing-edge trace interfaces

Traces are endpoint extensions of transverse ACL representatives, not evaluations
of arbitrary L² functions on null lines. Opposite-side traces are specified separately:
the matching condition does not assume an ACL representative across the interface.
The quadrant signs below are geometric signs (true means positive), not parity signs.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- A diagonal chart with tangential coordinate first and normal coordinate second. -/
def diagonalTraceChart (j : Fin 2) (q : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then diagInv (q.2, q.1) else diagInv q

/-- Zero Sobolev trace on separatrix lines inside U. The normal trace may be at an
endpoint or inside a transverse rectangle. The compact rectangle is contained in U. -/
def HasZeroSeparatrixTraceOn (U : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℂ) : Prop :=
  ∀ (j : Fin 2) (l r a b t : ℝ), l < r → a < b → t ∈ Icc a b → Real.cos t = 0 →
    diagonalTraceChart j '' (Icc l r ×ˢ Icc a b) ⊆ U →
    ∃ G D : ℝ × ℝ → ℂ,
      G =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo a b)] (fun q ↦ F (diagonalTraceChart j q)) ∧
      MemLp G 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) ∧
      MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) ∧
      HasACLSectionsOn (Ioo l r) (Ioo a b) G D ∧
      ∀ᵐ s ∂(volume.restrict (Ioo l r)), aclTrace a b G D t s = 0

/-- Canonical transverse H¹ trace in a chart, including normal endpoints. -/
def HasTransverseH1Trace (l r a b t : ℝ) (chart : ℝ × ℝ → ℝ × ℝ)
    (F : ℝ × ℝ → ℂ) (T : ℝ → ℂ) : Prop :=
  l < r ∧ a < b ∧ t ∈ Icc a b ∧ ∃ G D : ℝ × ℝ → ℂ,
    Measurable G ∧
    G =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo a b)] (fun q ↦ F (chart q)) ∧
    MemLp G 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) ∧
    MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) ∧
    HasACLSectionsOn (Ioo l r) (Ioo a b) G D ∧
    T =ᵐ[volume.restrict (Ioo l r)] aclTrace a b G D t

/-- Polar chart with radial coordinate first, angular coordinate second. -/
def polarTraceChart (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 * Real.cos q.2, q.1 * Real.sin q.2)

/-- Canonical trace along a fixed ray of the positive quadrant, on every compact
radial subinterval. Angular endpoints are included. -/
def HasRadialTrace (ρ : ℝ) (F : ℝ × ℝ → ℂ) (θ : ℝ) (T : ℝ → ℂ) : Prop :=
  θ ∈ Icc 0 (Real.pi / 2) ∧ ∀ a b, 0 < a → a < b → b < ρ →
    HasTransverseH1Trace a b 0 (Real.pi / 2) θ polarTraceChart F T

/-- An open signed quadrant of a Euclidean disk. -/
def quadrantDisk (ρ : ℝ) (σ : Fin 2 → Bool) : Set (ℝ × ℝ) :=
  {p | p ∈ localDisk 0 ρ ∧ ∀ j, 0 < (if σ j then axisCoord j p else -axisCoord j p)}

/-- Cartesian chart with tangential coordinate first, j-th coordinate normal. -/
def axisTraceChart (j : Fin 2) (q : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then (q.2, q.1) else q

/-- Matching canonical one-sided traces on every open half-axis. No trace at
the crossing point itself and no across-interface ACL hypothesis is imposed. -/
def HasMatchingAxisTraces (ρ : ℝ) (F : ℝ × ℝ → ℂ) : Prop :=
  ∀ (j : Fin 2) (l r a : ℝ), l < r → 0 < a → (r < 0 ∨ 0 < l) →
    axisTraceChart j '' (Icc l r ×ˢ Icc (-a) a) ⊆ localDisk 0 ρ →
    ∃ T : ℝ → ℂ,
      HasTransverseH1Trace l r (-a) 0 0 (axisTraceChart j) F T ∧
      HasTransverseH1Trace l r 0 a 0 (axisTraceChart j) F T

/-- The normal diagonal-coordinate value of a positive-cell edge. -/
def cellEdgeNormal (positive : Bool) : ℝ :=
  if positive then Real.pi / 2 else -Real.pi / 2

/-- Canonical trace from a cellwise region V onto one whole regular cell edge.
The open normal rectangle lies in V; the trace endpoint need not lie in V. -/
def HasCellEdgeTrace (V : Set (ℝ × ℝ)) (j : Fin 2) (positive : Bool)
    (F : ℝ × ℝ → ℂ) (T : ℝ → ℂ) : Prop :=
  ∀ (l r a b : ℝ), l < r → a < b →
    Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
    (if positive then b = cellEdgeNormal positive else a = cellEdgeNormal positive) →
    diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ V →
    HasTransverseH1Trace l r a b (cellEdgeNormal positive) (diagonalTraceChart j) F T

/-- Uniform weighted traces on the two sides and every fixed interior ray
(`lem:weighted-corner-trace`). Membership is separate from the integral estimates. -/
theorem weighted_corner_trace : ∃ K : ℝ, 0 < K ∧ ∀ (ρ : ℝ), 0 < ρ →
    ∀ (F : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      let Q := quadrantDisk ρ (fun _ ↦ true)
      MemSobolevOn 1 Q F → HasWeakJetOn 1 Q F D →
      MemLp (fun p ↦ F p / (localRadius 0 p : ℂ)) 2 (volume.restrict Q) →
      ∃ T : ℝ → ℝ → ℂ,
        (∀ θ ∈ Icc 0 (Real.pi / 2), HasRadialTrace ρ F θ (T θ) ∧
          MemLp (fun (r : ℝ) ↦ T θ r / (Real.sqrt r : ℂ)) 2
            (volume.restrict (Ioo 0 ρ))) ∧
        ((∫ r in Ioo 0 ρ, ‖T 0 r / (Real.sqrt r : ℂ)‖ ^ 2) +
          (∫ r in Ioo 0 ρ, ‖T (Real.pi / 2) r / (Real.sqrt r : ℂ)‖ ^ 2)) ≤
            K * (radialJetEnergy 0 1 Q 0 D + radialJetEnergy 1 0 Q 0 D) ∧
        (∀ θ ∈ Icc 0 (Real.pi / 2),
          (∫ r in Ioo 0 ρ, ‖T θ r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
            K * (radialJetEnergy 0 1 Q 0 D + radialJetEnergy 1 0 Q 0 D)) := by
  sorry

/-- Crossing-edge gluing with the specified quadrant derivatives
(`lem:h1-crossing-gluing`). The radial L² tail removes the crossing-point defect. -/
theorem h1_crossing_gluing {ρ : ℝ} (hρ : 0 < ρ) {F : ℝ × ℝ → ℂ}
    {D : Fin 2 → ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (localDisk 0 ρ)))
    (hq : ∀ σ : Fin 2 → Bool, MemSobolevOn 1 (quadrantDisk ρ σ) F)
    (hD : ∀ (σ : Fin 2 → Bool) j, HasWeakPartialOn (quadrantDisk ρ σ) j F (D j))
    (hm : HasMatchingAxisTraces ρ F)
    (hw : MemLp (fun p ↦ F p / (localRadius 0 p : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    MemSobolevOn 1 (localDisk 0 ρ) F ∧ ∀ j,
      HasWeakPartialOn (localDisk 0 ρ) j F (D j) ∧
      MemLp (D j) 2 (volume.restrict (localDisk 0 ρ)) := by
  sorry

end NoEmbeddedEigenvalues
