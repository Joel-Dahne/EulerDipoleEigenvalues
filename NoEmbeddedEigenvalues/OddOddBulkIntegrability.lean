import NoEmbeddedEigenvalues.OddOddForms

/-!
# Forcing integrability for the odd–odd bulk

The weighted forcing estimate is independent of the quotient, its parity and
the equation. The torus-vorticity interface is a specialization after restricting
the weighted L² hypothesis to the cell.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- A supplied forcing with e/d ∈ L² has absolutely integrable weighted density.
No equation, periodicity or separate unweighted L² hypothesis is required. -/
theorem dd_forcing_density_integrable {e : ℝ × ℝ → ℂ}
    (he : MemLp (fun p ↦ e p / (saddleDist p : ℂ)) 2
      (volume.restrict cellSquare)) :
    IntegrableOn (fun p ↦ ddF p * ‖e p‖ ^ 2) cellSquare := by
  sorry

/-- Absolute integrability from `ν/d ∈ L²`, independently of the eigenvalue equation. -/
theorem dd_vorticityDensity_integrable (ν : L2)
    (hν : MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood)) :
    IntegrableOn (ddVorticityDensity ν) cellSquare := by
  exact dd_forcing_density_integrable (hν.mono_measure
    (Measure.restrict_mono (fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)) le_rfl))


end NoEmbeddedEigenvalues
