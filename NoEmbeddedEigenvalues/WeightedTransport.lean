import NoEmbeddedEigenvalues.WeightedTraces
import NoEmbeddedEigenvalues.ScalarDivision
import NoEmbeddedEigenvalues.Transport
import NoEmbeddedEigenvalues.QuarterCoordinates
import NoEmbeddedEigenvalues.WeightedNumerators
import NoEmbeddedEigenvalues.ZeroSaddleTransportGain
import NoEmbeddedEigenvalues.WeightedTransportH1Assembly

/-!
# Weighted cellwise transport regularity interfaces

The weak gradient of the forcing is specified, and weights use physical-area L².
Regularity and zero boundary trace are different conclusions. Only the latter uses
zero continuous forcing on the chosen whole edge and the weighted corner trace.

Quarter profiles use independent recentered time coordinates. Their h/t derivatives
carry weights d and 1/d respectively; no unweighted global H¹ norm on the quarter
coordinate domain is asserted. The physical stream level is Ψ = 2h.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Weighted forcing gives the second mass gain and cellwise physical H¹, together
with weak recentered quarter derivatives (`lem:weighted-transport-h1`). -/
theorem weighted_transport_h1 {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧
        MemSobolevOn 1 (cellSeparatrixStrip (2 * h₀)) v ∧
        ∃ A B : Fin 4 → ℝ × ℝ → ℂ, ∀ k,
          HasWeakPartialOn (quarterOrbitStrip h₀) 0
            (fun q ↦ v (recenteredQuarterMap k q)) (A k) ∧
          HasWeakPartialOn (quarterOrbitStrip h₀) 1
            (fun q ↦ v (recenteredQuarterMap k q)) (B k) ∧
          MemLp (fun q ↦ (saddleDist (recenteredQuarterMap k q) : ℂ) * A k q) 2
            (volume.restrict (quarterOrbitStrip h₀)) ∧
          MemLp (fun q ↦ B k q / (saddleDist (recenteredQuarterMap k q) : ℂ)) 2
            (volume.restrict (quarterOrbitStrip h₀)) := by
  refine ⟨weighted_transport_second_mass hp hb hcell hD hf hDf, ?_⟩
  obtain ⟨b, hpos, hhalf, A, B, hAB⟩ :=
    weighted_transport_quarter_derivatives hp hb hcell hD hf hDf
  exact ⟨b, hpos, hhalf,
    hp.cell_h1_of_weighted_quarter_derivatives hcell hpos hhalf hAB, A, B, hAB⟩

/-- Zero forcing on one whole regular edge forces its canonical cellwise trace
of v to vanish (`lem:transport-zero-edge-trace`). H¹ and the mass weight are inputs,
not inferred merely from the zero forcing values. -/
theorem transport_zero_edge_trace {lam ε : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U) (hε : 0 < ε)
    (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) v)
    (hw : MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2
      (volume.restrict (cellSeparatrixStrip ε)))
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (j : Fin 2) (positive : Bool)
    (hzero : ∀ s ∈ Ioo (-Real.pi / 2) (Real.pi / 2),
      g (diagonalTraceChart j (s, cellEdgeNormal positive)) = 0) :
    HasCellEdgeTrace (cellSeparatrixStrip ε) j positive v (fun _ ↦ 0) := by
  sorry

end NoEmbeddedEigenvalues
