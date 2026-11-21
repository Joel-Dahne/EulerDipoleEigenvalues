import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.OrbitCoordinates
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeightedTraces

/-!
# Recentered quarter domains and endpoint rays

The stream level is Ψ = 2h. The negative-time endpoint approaches (π,0),
the positive-time endpoint approaches (0,-π), and their Euclidean radius
from the saddle is 2 arcsin √h. Ray traces use transverse ACL extensions.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The positive-cell separatrix collar, with a cutoff on Ψ rather than h. -/
def cellSeparatrixStrip (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ cellSquare ∧ 0 < dipoleLift p ∧ dipoleLift p < ε}

/-- The base quarter's moving-endpoint coordinate domain. -/
def quarterOrbitStrip (h₀ : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ q.1 < h₀ ∧ -eighthPeriod q.1 < q.2 ∧ q.2 < eighthPeriod q.1}

/-- Each quarter is parametrized by its own recentered time, including rotations. -/
def recenteredQuarterMap (k : Fin 4) (q : ℝ × ℝ) : ℝ × ℝ :=
  rotLift^[k.val] (dipoleOrbit q.1 q.2)

/-- Euclidean endpoint-ray radius, not the saddle distance in the product metric. -/
def quarterEndpointRadius (h : ℝ) : ℝ := 2 * Real.arcsin (Real.sqrt h)

/-- The two fixed rays, parametrized by Euclidean radius from their saddles. -/
def quarterEndpointRay (positive : Bool) (r : ℝ) : ℝ × ℝ :=
  if positive then (0, -Real.pi + r) else (Real.pi - r, 0)

/-- Radial coordinate first, transverse coordinate second. -/
def quarterEndpointChart (positive : Bool) (q : ℝ × ℝ) : ℝ × ℝ :=
  if positive then (q.2, -Real.pi + q.1) else (Real.pi - q.1, q.2)

/-- Endpoint ray on the k-th recentered quarter. -/
def rotatedQuarterEndpointRay (k : Fin 4) (positive : Bool) (r : ℝ) : ℝ × ℝ :=
  rotLift^[k.val] (quarterEndpointRay positive r)

/-- The corresponding radial/transverse chart. -/
def rotatedQuarterEndpointChart (k : Fin 4) (positive : Bool) (q : ℝ × ℝ) : ℝ × ℝ :=
  rotLift^[k.val] (quarterEndpointChart positive q)

/-- Canonical interior trace along a quarter-endpoint ray. -/
def HasQuarterRayTrace (U : Set (ℝ × ℝ)) (ρ : ℝ) (k : Fin 4) (positive : Bool)
    (F : ℝ × ℝ → ℂ) (T : ℝ → ℂ) : Prop :=
  ∀ a b, 0 < a → a < b → b < ρ → ∀ w, 0 < w →
    rotatedQuarterEndpointChart k positive '' (Icc a b ×ˢ Icc (-w) w) ⊆ U →
    HasTransverseH1Trace a b (-w) w 0 (rotatedQuarterEndpointChart k positive) F T

end NoEmbeddedEigenvalues
