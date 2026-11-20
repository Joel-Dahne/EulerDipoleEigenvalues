import NoEmbeddedEigenvalues.MixedFlux
import NoEmbeddedEigenvalues.MixedCompletionCurrent
import NoEmbeddedEigenvalues.EvenEven

/-!
# Mixed exclusion

Blueprint: `thm:mixed-exclusion` and `cor:mixed-other-exclusion`.
The static identity and coercivity force zero stream mass in the positive
cell. Reflection gives global vanishing, and the Poisson relation recovers
the vorticity. The opposite mixed sector follows by quarter rotation.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory

/-- An eigenfunction odd under S₁ and even under S₂ vanishes
at every nonzero real spectral parameter. -/
theorem mixed_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false true ω) : ω = 0 := by
  obtain ⟨⟨d⟩, _⟩ := mixed_quotient_domain hlam hω hsector
  have ⟨hbound, hmass⟩ := mixed_static_coercivity d
  have hsign := (mixed_static_identity hlam hω hsector d).2
  rw [hmass] at hbound
  have hpos : 0 ≤ ∫ p in cellSquare, ‖liftL2 (invLap ω) p‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hzero : (∫ p in cellSquare, ‖liftL2 (invLap ω) p‖ ^ 2) = 0 := by linarith
  have hLp := (memLp_liftL2_periodBox (invLap ω)).mono_measure
    (Measure.restrict_mono cellSquare_subset_periodBox le_rfl)
  have hInt := hLp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hzeroAE := (integral_eq_zero_iff_of_nonneg (fun p ↦
    sq_nonneg ‖liftL2 (invLap ω) p‖) hInt).mp hzero
  have hstream : invLap ω = 0 := by
    apply hsector.invLap.eq_zero_of_lift_ae_zero_on_cellSquare
    filter_upwards [hzeroAE] with p hp
    change ‖liftL2 (invLap ω) p‖ ^ 2 = 0 at hp
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (liftL2 (invLap ω) p)])
  apply fourierCoeff_ext
  intro k
  simpa only [hstream, fourierCoeff_zero_fun, mul_zero] using
    hasFourierLaplacian_invLap ω hω.1 k

/-- The other mixed sector is excluded by quarter rotation. -/
theorem mixed_other_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true false ω) : ω = 0 := by
  apply rotate.injective
  rw [map_zero]
  exact mixed_exclusion lam hlam (rotate ω) hω.rotate hsector.rotate

end NoEmbeddedEigenvalues
