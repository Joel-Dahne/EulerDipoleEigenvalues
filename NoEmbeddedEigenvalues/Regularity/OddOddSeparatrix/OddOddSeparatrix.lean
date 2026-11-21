module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.OddOddPuncturedH1
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.StreamElliptic
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceWeakGluing
public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddEdgeTraces
public import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddRegularSeams
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.OddOddSobolevTraces

/-!
# Ordinary odd–odd regularity through the lifted separatrix

Blueprint: `prop:dd-separatrix-h1`.

The whole-lift endpoint is separated from the saddle/forcing inputs so that
cellwise transport, reflected periodic covering and elliptic completion can
precede its assembly, independently of logarithmic forcing.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- H¹ vorticity, zero Sobolev traces and H³ stream regularity across the separatrix
(`prop:dd-separatrix-h1`). The neighbourhood may be unbounded; the spaces are local. -/
theorem dd_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ {p | dipoleLift p = 0} ⊆ U ∧
      MemSobolevLocOn 1 U (liftL2 ω) ∧ HasZeroSeparatrixTraceOn U (liftL2 ω) ∧
      MemSobolevLocOn 3 U (contStream ω) := by
  obtain ⟨ε, hε, _, hF⟩ := dd_separatrix_vorticity_h1 hlam hω hs
  have hU : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  refine ⟨_, hU, ?_, hF, hF.oddOdd_collar_zero_traces hs,
    stream_h3_of_vorticity_h1 hω.1 hU hF⟩
  intro p hp
  change |dipoleLift p| < ε
  rw [hp, abs_zero]
  exact hε

end NoEmbeddedEigenvalues
