module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.LocalJets
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceL2

/-!
# Canonical transverse, separatrix and cell-edge traces

Traces are endpoint extensions of transverse ACL representatives, not evaluations
of arbitrary L² functions on null lines.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

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

/-- Cartesian chart with tangential coordinate first, j-th coordinate normal. -/
def axisTraceChart (j : Fin 2) (q : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then (q.2, q.1) else q

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

end EulerDipoleEigenvalues
