module

public import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.FlowDerivatives

/-! # Continuity of the canonical transport profile -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory Set Filter Topology

/-- The canonical profile is continuous whenever its defining derivative is integrable. -/
theorem continuous_canonicalProfile {lam : ℝ} {g : ℝ → ℂ} (hg : Integrable (deriv g)) :
    Continuous (canonicalProfile lam g) := by
  have hc := (integrable_profileIntegrand (lam := lam) hg).continuous_primitive (0 : ℝ)
  have htail : Continuous (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) := by
    have heq : (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) =
        fun s ↦ (∫ t in Ioi 0, profileIntegrand lam g t) -
          ∫ t in (0 : ℝ)..s, profileIntegrand lam g t :=
      funext fun s ↦ integral_Ioi_profileIntegrand hg s
    rw [heq]
    exact continuous_const.sub hc
  exact (by fun_prop : Continuous fun s : ℝ ↦ Complex.exp (Complex.I * lam * s)).mul htail

end NoEmbeddedEigenvalues
