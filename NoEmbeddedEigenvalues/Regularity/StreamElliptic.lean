import NoEmbeddedEigenvalues.Regularity.QuotientLocal
import NoEmbeddedEigenvalues.StreamJet

/-!
# Elliptic completion of ordinary stream regularity

Blueprint: `lem:canonical-stream-poisson`, `lem:stream-h3-of-vorticity-h1`.

The Laplacian uses the fixed Fourier second jet. Mean zero removes the constant
mode. Ordinary torus H² supplies finite local lift norms before applying interior
elliptic regularity to the same continuous stream, on the same open domain.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The canonical second stream jet has the prescribed raw vorticity Laplacian. -/
theorem streamJet2_laplacian {ω : L2} (hω : MeanZero ω) :
    ∀ᵐ p, streamJet2 ω [0, 0] p + streamJet2 ω [1, 1] p = liftL2 ω p := by
  have he := ae_torusProj (Lp.coeFn_add
    (streamSecondPartial 0 0 ω) (streamSecondPartial 1 1 ω))
  rw [streamSecondPartial_add hω] at he
  filter_upwards [he] with p hp using hp.symm

/-- Local H¹ of the vorticity gives local H³ of its actual continuous stream.
The only elliptic input is the explicit interior H³ regularity interface. -/
theorem stream_h3_of_vorticity_h1 {ω : L2} (hω : MeanZero ω)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hF : MemSobolevLocOn 1 U (liftL2 ω)) :
    MemSobolevLocOn 3 U (contStream ω) := by
  have hu : MemSobolevLocOn 2 U (contStream ω) := by
    intro V _ hVc _
    exact (memSobolevOn_liftL2 (memSobolev_two_invLap ω)
      (hVc.isBounded.subset subset_closure)).congr_value (streamLift_ae_eq_contStream ω)
  exact elliptic_local_h3 hU hu hF (streamJet2_weak ω U)
    (ae_restrict_of_ae (streamJet2_laplacian hω))

end NoEmbeddedEigenvalues
