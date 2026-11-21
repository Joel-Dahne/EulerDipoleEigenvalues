import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets

/-!
# Specified second jet of the continuous stream

The entries are the existing Fourier multiplier derivatives, not classical
derivatives of raw L² representatives. Fixing this jet makes bulk, ray and
orbit estimates use identical derivative data.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

/-- Canonical order-two stream jet; higher entries are unused and set to zero. -/
def streamJet2 (ω : L2) : List (Fin 2) → ℝ × ℝ → ℂ
  | [] => contStream ω
  | [j] => liftL2 (streamPartial j ω)
  | [i, j] => liftL2 (streamSecondPartial i j ω)
  | _ => fun _ ↦ 0

/-- The packed jet follows from the first/second Fourier partial lift bridges. -/
theorem streamJet2_weak (ω : L2) (U : Set (ℝ × ℝ)) :
    HasWeakJetOn 2 U (contStream ω) (streamJet2 ω) := by
  refine ⟨rfl, fun w hw j ↦ ?_⟩
  cases w with
  | nil =>
    exact (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω j) U).congr_left
      (streamLift_ae_eq_contStream ω)
  | cons i w =>
    cases w with
    | nil =>
      exact hasWeakPartialOn_liftL2
        (hasFourierPartial_streamPartial_streamSecondPartial ω j i) U
    | cons k w => simp only [List.length_cons] at hw; omega

end NoEmbeddedEigenvalues
