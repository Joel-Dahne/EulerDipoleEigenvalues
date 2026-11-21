module

public import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddPotentialMass
public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddGradientIntegrability

/-!
# Assembly of the renormalized odd–odd bulk limit

There are three separate analytic inputs: weighted forcing integrability,
even-H² gradient integrability, and the finite part of the weighted value mass.
Ordinary exhaustion combines them without a relation between the forcing and
the quotient and without exceptional levels.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

private theorem potential_mass_integrable_truncation (u : L2) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun p ↦ ddF p * ‖liftL2 u p‖ ^ 2) (ddTruncatedCell ε) := by
  have hb : Bornology.IsBounded (ddTruncatedCell ε) :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  have h := ddVirialDensity_integrable hε MemLp.zero (memLp_liftL2 u hb)
    MemLp.zero MemLp.zero
  apply h.congr_fun _ (isOpen_ddTruncatedCell ε).measurableSet
  intro p _
  simp [ddVirialDensity, ddMatrixForm, normalDeriv, tangentDeriv]

/-- Full renormalized bulk limit. The squared operator value can be any supplied
    function `e` with `e/d ∈ L²`; no equation for `e` is needed for this estimate. -/
theorem dd_renormalized_bulk {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) {e : ℝ × ℝ → ℂ}
    (he : MemLp (fun p ↦ e p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare)) :
    IntegrableOn (fun p ↦ ddF p * ‖e p‖ ^ 2) cellSquare ∧
      IntegrableOn (fun p ↦ ddMatrixForm p (liftL2 dx p) (liftL2 dy p)) cellSquare ∧
      ∃ J : ℝ, Tendsto (fun ε ↦
        (∫ p in ddTruncatedCell ε, ddVirialDensity (liftL2 u) e (liftL2 dx) (liftL2 dy) p) +
          ddLogCounterterm u ε) (𝓝[>] 0) (𝓝 J) := by
  have hf := dd_forcing_density_integrable he
  have hg := (dd_gradient_energies_integrable hu hs hx hy).1
  obtain ⟨V, hV⟩ := dd_potential_mass_finite_part hu
  have hlim := ((tendsto_ddTruncatedCell_integral hf).add
    (tendsto_ddTruncatedCell_integral hg)).sub hV
  refine ⟨hf, hg, _, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hsub : ddTruncatedCell ε ⊆ cellSquare := fun _ hp ↦ hp.1
  have hfi := hf.mono_set hsub
  have hgi := hg.mono_set hsub
  have hpi := potential_mass_integrable_truncation u hε
  have hid : (∫ p in ddTruncatedCell ε,
      ddVirialDensity (liftL2 u) e (liftL2 dx) (liftL2 dy) p) =
      (∫ p in ddTruncatedCell ε, ddF p * ‖e p‖ ^ 2) +
        (∫ p in ddTruncatedCell ε, ddMatrixForm p (liftL2 dx p) (liftL2 dy p)) -
          ∫ p in ddTruncatedCell ε, ddF p * ‖liftL2 u p‖ ^ 2 := by
    have hfun : ddVirialDensity (liftL2 u) e (liftL2 dx) (liftL2 dy) =
        ((fun p ↦ ddF p * ‖e p‖ ^ 2) +
          (fun p ↦ ddMatrixForm p (liftL2 dx p) (liftL2 dy p))) -
            (fun p ↦ ddF p * ‖liftL2 u p‖ ^ 2) := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, ddVirialDensity]
      ring
    rw [hfun]
    exact (integral_sub (hfi.add hgi) hpi).trans
      (congrArg (fun z : ℝ ↦ z - ∫ p in ddTruncatedCell ε, ddF p * ‖liftL2 u p‖ ^ 2)
        (integral_add hfi hgi))
  rw [hid]
  ring

end NoEmbeddedEigenvalues
