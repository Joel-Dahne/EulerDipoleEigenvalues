import NoEmbeddedEigenvalues.Regularity.OddOddPuncturedH1
import NoEmbeddedEigenvalues.Regularity.StreamElliptic
import NoEmbeddedEigenvalues.WeakPointRemoval
import NoEmbeddedEigenvalues.TraceWeakGluing

/-!
# Ordinary odd–odd regularity through the lifted separatrix

Blueprint: `prop:dd-separatrix-h1`.

The whole-lift endpoint is separated from the saddle/forcing inputs so that
cellwise transport, reflected periodic covering and elliptic completion can
precede its assembly, independently of logarithmic forcing.
-/

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
  sorry

end NoEmbeddedEigenvalues
