import NoEmbeddedEigenvalues.OddOdd.BoundaryForm.BoundaryData

/-! # Picone truncations, odd–odd finite parts, and ground-state current -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-! ### Truncations, finite parts and the ground-state current -/

/-- The lifted positive cell above the actual stream level `ε` (not the orbit parameter). -/
def ddTruncatedCell (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ cellSquare ∧ ε < dipoleLift p}

/-- The untransformed gradient/potential energy. -/
def ddRawEnergy (φ dx dy : L2) (p : ℝ × ℝ) : ℝ :=
  ddMatrixForm p (liftL2 dx p) (liftL2 dy p) - ddF p * ‖liftL2 φ p‖ ^ 2

/-- The truncated virial bulk, including the vorticity term. -/
def ddRawBulk (φ ν dx dy : L2) (ε : ℝ) : ℝ :=
  ∫ p in ddTruncatedCell ε, ddVorticityDensity ν p + ddRawEnergy φ dx dy p

/-- The three separate ordinary integrals after the Picone transformation. -/
def ddPiconeBulk (φ ν dx dy : L2) (ε : ℝ) : ℝ :=
  (∫ p in ddTruncatedCell ε, ddVorticityDensity ν p) +
    (∫ p in ddTruncatedCell ε, ddPiconeGradient φ dx dy p) +
    ∫ p in ddTruncatedCell ε, ddPiconePotential φ p

/-- The two actual saddle endpoint values of a lifted arc. -/
def ddArcEnd (φ : L2) (k : Fin 4) (positive : Bool) : ℂ :=
  continuousRep φ (torusProj (rotLift^[k.val]
    (if positive then (0, -Real.pi) else (Real.pi, 0))))

/-- Half the endpoint sum: each of the four lifted corners is incident to two arcs.
    The two torus saddles are counted with their lifted multiplicities. -/
def ddCornerMass (φ : L2) : ℝ :=
  (1 / 2 : ℝ) * ∑ k : Fin 4, (‖ddArcEnd φ k false‖ ^ 2 + ‖ddArcEnd φ k true‖ ^ 2)

/-- Arc value mass with its two endpoint constants removed. The choice at `t = 0`
    is immaterial for integration. -/
def ddArcValueRemainder (φ : L2) (k : Fin 4) (t : ℝ) : ℝ :=
  ‖ddArcTrace φ k t‖ ^ 2 -
    if t < 0 then ‖ddArcEnd φ k false‖ ^ 2 else ‖ddArcEnd φ k true‖ ^ 2

/-- The value finite part for truncation by `Ψ = ε`, including its `log 8` constant. -/
def ddValueFinitePart (φ : L2) : ℝ :=
  (∑ k : Fin 4, ∫ t, ddArcValueRemainder φ k t) + Real.log 8 * ddCornerMass φ

/-- The identical counterterm used for the virial bulk and the boundary current. -/
def ddLogCounterterm (φ : L2) (ε : ℝ) : ℝ :=
  (8 / 3 : ℝ) * ddCornerMass φ * Real.log (1 / ε)

/-- The comparison function restricted to `s = 0`. -/
def ddBoundaryGround (r : ℝ) : ℝ := 1 + r / 16 - r ^ 2 / 256 * Real.log (r / 2)

/-- The explicit boundary coefficient, in expanded rational/logarithmic form. -/
def ddBoundaryB (r : ℝ) : ℝ :=
  (5 * r / 16 + r / 256 * ((32 - 25 * r) * Real.log (r / 2) + 16 - 12 * r)) /
    ddBoundaryGround r

/-- The actual outward Picone current coefficient in flow time. The outward normal of
    `C_ε` is `-∇Ψ/|∇Ψ|`, so the coefficient has a minus sign. -/
def ddGroundCurrentCoeff (p : ℝ × ℝ) : ℝ :=
  -ddA p * (partialX dipoleLift p * partialX ddGround p +
    partialY dipoleLift p * partialY ddGround p) / ddGround p

/-- Level value mass. `levelIntegral h` is on `Ψ = 2h`, hence the argument `ε/2`. -/
def ddLevelMass (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- The `B`-weighted value mass on the same level. -/
def ddLevelBMass (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ddBoundaryB (gradSq dipoleLift p) *
    ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- The actual level current, using continuous values rather than raw L² representatives. -/
def ddGroundCurrent (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ddGroundCurrentCoeff p *
    ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- On a separatrix arc, `r = 2 sech² t`. -/
def ddArcCorrection (φ : L2) (k : Fin 4) (t : ℝ) : ℝ :=
  ddBoundaryB (2 / Real.cosh t ^ 2) * ‖ddArcTrace φ k t‖ ^ 2

end NoEmbeddedEigenvalues
