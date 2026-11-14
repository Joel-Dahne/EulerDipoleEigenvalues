import NoEmbeddedEigenvalues.Analysis.CylinderSpectralMass
import Mathlib.Tactic.FunProp

/-!
# Bounded continuous synthesis of cylinder spectral data

The angular factors are unnormalized cosine/sine modes. Their normalization and
identification with a unitary angular transform are separate from this dominated
integral construction. The logarithmic frequency is angular frequency, matching
`cylinderSymbol`. L¹ data make every displayed synthesis integral genuine.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- The angular mode selected by even/odd reflection in the second coordinate. -/
def cylinderAngularMode (even : Bool) (m : ℕ) (θ : ℝ) : ℂ :=
  if even then (Real.cos ((m : ℝ) * θ) : ℂ) else (Real.sin ((m : ℝ) * θ) : ℂ)

theorem norm_cylinderAngularMode_le (even : Bool) (m : ℕ) (θ : ℝ) :
    ‖cylinderAngularMode even m θ‖ ≤ 1 := by
  cases even <;>
    simp only [cylinderAngularMode, Bool.false_eq_true, ite_false, ite_true,
      Complex.norm_real, Real.norm_eq_abs]
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

theorem continuous_cylinderAngularMode (even : Bool) (m : ℕ) :
    Continuous (cylinderAngularMode even m) := by
  cases even
  · change Continuous (fun θ : ℝ ↦ (Real.sin ((m : ℝ) * θ) : ℂ))
    fun_prop
  · change Continuous (fun θ : ℝ ↦ (Real.cos ((m : ℝ) * θ) : ℂ))
    fun_prop

/-- Product of the logarithmic Fourier phase and one angular cosine/sine mode. -/
def cylinderSynthesisKernel (even : Bool) (x : ℝ × ℝ) (p : ℝ × ℕ) : ℂ :=
  Complex.exp (Complex.I * ((x.1 * p.1 : ℝ) : ℂ)) * cylinderAngularMode even p.2 x.2

theorem norm_cylinderSynthesisKernel_le (even : Bool) (x : ℝ × ℝ) (p : ℝ × ℕ) :
    ‖cylinderSynthesisKernel even x p‖ ≤ 1 := by
  rw [cylinderSynthesisKernel, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact norm_cylinderAngularMode_le _ _ _

theorem measurable_cylinderSynthesisKernel (even : Bool) (x : ℝ × ℝ) :
    Measurable (cylinderSynthesisKernel even x) := by
  have he : Measurable (fun p : ℝ × ℕ ↦
      Complex.exp (Complex.I * ((x.1 * p.1 : ℝ) : ℂ))) := by fun_prop
  exact he.mul ((measurable_of_countable (fun m ↦ cylinderAngularMode even m x.2)).comp
    measurable_snd)

theorem continuous_cylinderSynthesisKernel (even : Bool) (p : ℝ × ℕ) :
    Continuous (fun x ↦ cylinderSynthesisKernel even x p) := by
  have he : Continuous (fun x : ℝ × ℝ ↦
      Complex.exp (Complex.I * ((x.1 * p.1 : ℝ) : ℂ))) := by fun_prop
  exact he.mul ((continuous_cylinderAngularMode even p.2).comp continuous_snd)

/-- Synthesis on the unwrapped cylinder; integrability is asserted separately. -/
def cylinderSynthesis (even : Bool) (μ : Measure (ℝ × ℕ)) (V : ℝ × ℕ → ℂ)
    (x : ℝ × ℝ) : ℂ := ∫ p, cylinderSynthesisKernel even x p * V p ∂μ

theorem integrable_cylinderSynthesis {μ : Measure (ℝ × ℕ)} {V : ℝ × ℕ → ℂ}
    (hV : Integrable V μ) (even : Bool) (x : ℝ × ℝ) :
    Integrable (fun p ↦ cylinderSynthesisKernel even x p * V p) μ :=
  hV.bdd_mul (measurable_cylinderSynthesisKernel even x).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cylinderSynthesisKernel_le even x))

/-- Genuine L¹ data give a continuous synthesis with a uniform finite bound. -/
theorem continuous_cylinderSynthesis {μ : Measure (ℝ × ℕ)} {V : ℝ × ℕ → ℂ}
    (hV : Integrable V μ) (even : Bool) : Continuous (cylinderSynthesis even μ V) := by
  apply continuous_of_dominated (bound := fun p ↦ ‖V p‖)
  · intro x
    exact (integrable_cylinderSynthesis hV even x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun p ↦ by
      change ‖cylinderSynthesisKernel even x p * V p‖ ≤ ‖V p‖
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_cylinderSynthesisKernel_le even x p) (norm_nonneg (V p))
  · exact hV.norm
  · exact Filter.Eventually.of_forall fun p ↦
      (continuous_cylinderSynthesisKernel even p).mul continuous_const

theorem norm_cylinderSynthesis_le {μ : Measure (ℝ × ℕ)} {V : ℝ × ℕ → ℂ}
    (hV : Integrable V μ) (even : Bool) (x : ℝ × ℝ) :
    ‖cylinderSynthesis even μ V x‖ ≤ ∫ p, ‖V p‖ ∂μ := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (integrable_cylinderSynthesis hV even x).norm hV.norm
  intro p
  change ‖cylinderSynthesisKernel even x p * V p‖ ≤ ‖V p‖
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_cylinderSynthesisKernel_le even x p) (norm_nonneg (V p))

/-- Every angular mode is periodic, including the zero mode. -/
theorem cylinderAngularMode_periodic (even : Bool) (m : ℕ) :
    Function.Periodic (cylinderAngularMode even m) (2 * Real.pi) := by
  intro θ
  cases even <;>
    simp only [cylinderAngularMode, Bool.false_eq_true, ite_false, ite_true, mul_add,
      Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]

/-- Synthesis descends to the angular circle by actual pointwise periodicity. -/
theorem cylinderSynthesis_periodic (even : Bool) (μ : Measure (ℝ × ℕ))
    (V : ℝ × ℕ → ℂ) (t : ℝ) :
    Function.Periodic (fun θ ↦ cylinderSynthesis even μ V (t, θ)) (2 * Real.pi) := by
  intro θ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p ↦ by
    change Complex.exp (Complex.I * ((t * p.1 : ℝ) : ℂ)) *
      cylinderAngularMode even p.2 (θ + 2 * Real.pi) * V p = _
    rw [cylinderAngularMode_periodic even p.2 θ]
    rfl

/-- The spectral two-derivative norm supplies an actual bounded continuous
synthesis, with a positive constant uniform in both cylinder coordinates. -/
theorem cylinderSynthesis_of_memLp_weighted {μ : Measure (ℝ × ℕ)}
    (hμ : μ ≤ cylinderSpectralMeasure) {V : ℝ × ℕ → ℂ}
    (hV : AEStronglyMeasurable V μ)
    (hWV : MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ) (even : Bool) :
    Continuous (cylinderSynthesis even μ V) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x, ‖cylinderSynthesis even μ V x‖ ≤ C := by
  have hL1 := integrable_of_memLp_cylinderSobolevWeight hμ hV hWV
  have hn : 0 ≤ ∫ p, ‖V p‖ ∂μ := integral_nonneg fun p ↦ norm_nonneg _
  refine ⟨continuous_cylinderSynthesis hL1 even, ⟨(∫ p, ‖V p‖ ∂μ) + 1, by linarith, ?_⟩⟩
  intro x
  exact (norm_cylinderSynthesis_le hL1 even x).trans (by linarith)

end NoEmbeddedEigenvalues
