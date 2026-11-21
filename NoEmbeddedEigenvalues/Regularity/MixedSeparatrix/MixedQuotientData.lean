module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.AxisReflectionJets
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.BoundaryTraceH2
public import NoEmbeddedEigenvalues.Mixed.SecondOrderForm.ComparisonCoefficients
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeightedTraces
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedField
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.OrbitCoordinates
public import NoEmbeddedEigenvalues.Symmetry.Sectors
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SpecifiedJetLp

/-! # Weak jet and trace data for the mixed quotient -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- Edge value of a representative continuous on the closed diagonal cell. -/
def mixedEdgeValue (j : Fin 2) (positive : Bool) (φ : Plane → ℂ) (a : ℝ) : ℂ :=
  φ (axisTraceChart j (a, cellEdgeNormal positive))

/-- The four edge traces used here are in the tangential coordinate (not flow time). -/
def HasMixedEdgeTrace (j : Fin 2) (positive : Bool) (f : Plane → ℂ) (T : ℝ → ℂ) : Prop :=
  HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) (-Real.pi / 2) (Real.pi / 2)
    (cellEdgeNormal positive) (axisTraceChart j) f T

/-- Quotient operator `∂aa + ∂bb - 2 tan(a) ∂a` evaluated on a weak jet. -/
def mixedWeightedLaplacian (D : List (Fin 2) → Plane → ℂ) (q : Plane) : ℂ :=
  D [0, 0] q + D [1, 1] q - (2 * Real.tan q.1 : ℝ) • D [0] q

/-- The cell part of the odd–even quotient domain. The quotient has an actual
continuous representative at the corners and zero normal derivative on each
edge. The latter is a Sobolev trace, not an evaluation of the raw jet. -/
structure MixedQuotientData (ω : L2) where
  phi : Plane → ℂ
  jet : List (Fin 2) → Plane → ℂ
  h2 : MemSobolevOn 2 mixedOpenCell phi
  weakJet : HasWeakJetOn 2 mixedOpenCell phi jet
  continuous : ContinuousOn phi (closure mixedOpenCell)
  stream_eq : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
    liftL2 (invLap ω) (diagInv q) = (Real.cos q.1 : ℂ) * phi q
  vorticity_divided : MemLp (fun q ↦ liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)) 2
    (volume.restrict mixedOpenCell)
  laplace_eq : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
    mixedWeightedLaplacian jet q = 2 * (liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)) + phi q
  normal_zero : ∀ (j : Fin 2) (positive : Bool),
    HasMixedEdgeTrace j positive (jet [j]) (fun _ ↦ 0)
  central_odd : ∀ q ∈ closure mixedOpenCell, phi (-q) = -phi q

/-- The stream gradient in diagonal coordinates, computed by the product rule
from the quotient. -/
def MixedQuotientData.streamA {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℂ :=
  (Real.cos q.1 : ℂ) * d.jet [0] q - (Real.sin q.1 : ℂ) * d.phi q

/-- Second diagonal component of the stream gradient. -/
def MixedQuotientData.streamB {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℂ :=
  (Real.cos q.1 : ℂ) * d.jet [1] q

end NoEmbeddedEigenvalues
