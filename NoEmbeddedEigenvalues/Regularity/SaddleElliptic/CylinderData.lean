module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets
public import NoEmbeddedEigenvalues.Symmetry.Sectors

/-! # Parity, angular degrees and classical harmonicity for cylinder inversion -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- The two prescribed coordinate reflection parities. -/
def HasAxisParityOn (ε : Fin 2 → Bool) (U : Set (ℝ × ℝ)) (u : ℝ × ℝ → ℂ) : Prop :=
  ∀ j, ∀ᵐ p ∂(volume.restrict U), u (axisReflect j p) = paritySign (ε j) * u p

/-- Allowed nonnegative harmonic angular degrees: even–even permits 0,2,…,
odd–odd permits 2,4,…, and either mixed parity permits 1,3,…. -/
def AllowedSaddleDegree (ε : Fin 2 → Bool) (m : ℕ) : Prop :=
  (Even m ↔ ε 0 = ε 1) ∧ (m = 0 → ε 0 = true ∧ ε 1 = true)

/-- Smooth harmonicity for the Euclidean plane, stated in Cartesian coordinates.
It does not posit an inner-product structure on the maximum-norm product. -/
def IsPlaneHarmonicOn (U : Set (ℝ × ℝ)) (h : ℝ × ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ h U ∧ ∀ p ∈ U,
    coordPartial 0 (coordPartial 0 h) p + coordPartial 1 (coordPartial 1 h) p = 0

end NoEmbeddedEigenvalues
