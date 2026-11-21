import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierData
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderSynthesis

/-!
# Folding signed Fourier data into cosine/sine amplitudes

Positive degrees acquire factor `2` for cosines and `2 * I` for sines.
The even constant mode has factor one; the odd constant mode is absent.
The positive-mode product measure retains the frequency density `dξ / (2 * π)`.
Finite joint mass is proved before these data are used in spectral inversion.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- Frequency measure for natural angular degrees, before support restriction. -/
def cylinderPositiveFourierMeasure : Measure (ℝ × ℕ) :=
  cylinderFrequencyMeasure.prod Measure.count

/-- Restricted measure used for inversion on a nonresonant set of degrees. -/
def cylinderAllowedFourierMeasure (M : Set ℕ) : Measure (ℝ × ℕ) :=
  cylinderPositiveFourierMeasure.restrict {p | p.2 ∈ M}

/-- Positive-mode normalization of the unnormalized trigonometric basis. -/
def cylinderFoldFactor (even : Bool) (m : ℕ) : ℂ :=
  if m = 0 then (if even then 1 else 0) else (if even then 2 else 2 * Complex.I)

theorem norm_cylinderFoldFactor_le (even : Bool) (m : ℕ) :
    ‖cylinderFoldFactor even m‖ ≤ 2 := by
  by_cases hm : m = 0 <;> cases even <;>
    simp [cylinderFoldFactor, hm]

/-- Exact pairing of a nonzero signed pair; there is no square-root normalization. -/
theorem cylinderFoldFactor_pair (even : Bool) {m : ℕ} (hm : m ≠ 0) (θ : ℝ) :
    cylinderFoldFactor even m * cylinderAngularMode even m θ =
      Complex.exp (Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) +
        (if even then (1 : ℂ) else -1) *
          Complex.exp (-Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) := by
  have hp := Complex.exp_ofReal_mul_I ((m : ℝ) * θ)
  have hn := Complex.exp_ofReal_mul_I (-((m : ℝ) * θ))
  rw [show -Complex.I * (((m : ℝ) * θ : ℝ) : ℂ) =
    ((-((m : ℝ) * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [mul_comm Complex.I, hp, hn]
  cases even <;> simp only [cylinderFoldFactor, hm, ite_false, ite_true,
    Bool.false_eq_true, cylinderAngularMode, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg] <;> ring

/-- The selected positive signed coefficients, without changing their amplitude. -/
def cylinderPositiveFourierData {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (p : ℝ × ℕ) : ℂ :=
  cylinderFourierData hG (p.1, (p.2 : ℤ))

/-- Amplitudes for the existing unnormalized cosine/sine synthesis. -/
def cylinderTrigFourierData (even : Bool) {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) (p : ℝ × ℕ) : ℂ :=
  cylinderFoldFactor even p.2 * cylinderPositiveFourierData hG p

theorem measurable_cylinderPositiveFourierData {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) : Measurable (cylinderPositiveFourierData hG) :=
  (measurable_cylinderFourierData hG).comp
    (measurable_fst.prodMk ((measurable_of_countable (fun m : ℕ ↦ (m : ℤ))).comp
      measurable_snd))

theorem measurable_cylinderTrigFourierData (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure) :
    Measurable (cylinderTrigFourierData even hG) :=
  ((measurable_of_countable (cylinderFoldFactor even)).comp measurable_snd).mul
    (measurable_cylinderPositiveFourierData hG)

/-- Restricting the signed summable mode masses to natural indices stays finite. -/
theorem cylinderPositiveFourierData_memLp {G : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hG : MemLp G 2 logCylinderMeasure) :
    MemLp (cylinderPositiveFourierData hG) 2 cylinderPositiveFourierMeasure := by
  apply memLp_two_prod_count_of_summable_mass
    (measurable_cylinderPositiveFourierData hG).aestronglyMeasurable
    (fun m ↦ cylinderFourierData_mode_memLp hG (m : ℤ))
  simp_rw [cylinderPositiveFourierData, cylinderFourierData_mode_mass]
  exact (cylinderFourierMode_hasSum_mass hG).summable.comp_injective Int.ofNat_injective

/-- The folding factors are uniformly bounded, so actual joint L² is retained. -/
theorem cylinderTrigFourierData_memLp (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure) :
    MemLp (cylinderTrigFourierData even hG) 2 cylinderPositiveFourierMeasure := by
  apply (cylinderPositiveFourierData_memLp hG).of_le_mul
    (measurable_cylinderTrigFourierData even hG).aestronglyMeasurable (c := 2)
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [cylinderTrigFourierData, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_cylinderFoldFactor_le even p.2) (norm_nonneg _)

/-- Genuine coefficient support gives joint support of the folded amplitudes. -/
theorem cylinderTrigFourierData_support (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    {M : Set ℕ} (hM : ∀ m, m ∉ M → cylinderAngularCoeff G (m : ℤ) =ᵐ[volume] 0) :
    ∀ᵐ p ∂cylinderPositiveFourierMeasure, p.2 ∉ M → cylinderTrigFourierData even hG p = 0 := by
  have hs : ∀ᵐ ξ ∂cylinderFrequencyMeasure,
      ∀ m : ℕ, m ∉ M → cylinderTrigFourierData even hG (ξ, m) = 0 := by
    apply ae_all_iff.mpr
    intro m
    by_cases hm : m ∈ M
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hm).elim
    · filter_upwards [cylinderFourierData_mode_eq_zero hG (hM m hm)] with ξ hξ
      simp only [cylinderTrigFourierData, cylinderPositiveFourierData, hξ, Pi.zero_apply,
        mul_zero, implies_true]
  exact (Measure.quasiMeasurePreserving_fst.ae hs).mono fun p hp ↦ hp p.2

/-- Folding combines an actual signed pair, assuming its specified reflection sign.
The exceptional frequency set is independent of the angular evaluation. -/
theorem cylinderTrigFourierData_pair (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    {m : ℕ} (hm : m ≠ 0)
    (hneg : (fun ξ ↦ cylinderFourierData hG (ξ, -(m : ℤ))) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ (if even then (1 : ℂ) else -1) * cylinderFourierData hG (ξ, (m : ℤ))) :
    ∀ᵐ ξ ∂cylinderFrequencyMeasure, ∀ θ : ℝ,
      Complex.exp (Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) *
          cylinderFourierData hG (ξ, (m : ℤ)) +
        Complex.exp (-Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) *
          cylinderFourierData hG (ξ, -(m : ℤ)) =
      cylinderAngularMode even m θ * cylinderTrigFourierData even hG (ξ, m) := by
  filter_upwards [hneg] with ξ hξ θ
  rw [hξ, cylinderTrigFourierData, cylinderPositiveFourierData]
  calc
    _ = (Complex.exp (Complex.I * (((m : ℝ) * θ : ℝ) : ℂ)) +
        (if even then (1 : ℂ) else -1) *
          Complex.exp (-Complex.I * (((m : ℝ) * θ : ℝ) : ℂ))) *
            cylinderFourierData hG (ξ, (m : ℤ)) := by ring
    _ = _ := by rw [← cylinderFoldFactor_pair even hm θ]; ring

/-- The constant mode is counted once, and disappears in odd parity. -/
theorem cylinderTrigFourierData_constant (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    (hzero : (fun ξ ↦ cylinderFourierData hG (ξ, 0)) =ᵐ[cylinderFrequencyMeasure]
      fun ξ ↦ (if even then (1 : ℂ) else -1) * cylinderFourierData hG (ξ, 0)) :
    ∀ᵐ ξ ∂cylinderFrequencyMeasure, ∀ θ : ℝ,
      cylinderAngularMode even 0 θ * cylinderTrigFourierData even hG (ξ, 0) =
        cylinderFourierData hG (ξ, 0) := by
  filter_upwards [hzero] with ξ hξ θ
  cases even
  · have hz : cylinderFourierData hG (ξ, 0) = 0 :=
      CharZero.eq_neg_self_iff.mp (by simpa only [Bool.false_eq_true, ite_false,
        neg_one_mul] using hξ)
    simp [cylinderAngularMode, cylinderTrigFourierData, hz]
  · simp [cylinderAngularMode, cylinderTrigFourierData, cylinderFoldFactor,
      cylinderPositiveFourierData]

/-- The support restriction belongs to the discrete factor of the product. -/
theorem cylinderAllowedFourierMeasure_eq_prod (M : Set ℕ) :
    cylinderAllowedFourierMeasure M =
      cylinderFrequencyMeasure.prod (Measure.count.restrict M) := by
  have hs : {p : ℝ × ℕ | p.2 ∈ M} = Set.univ ×ˢ M := by ext p; simp
  rw [cylinderAllowedFourierMeasure, cylinderPositiveFourierMeasure, hs,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- Counting measure has no exceptional allowed degree: every such mode is L¹. -/
theorem integrable_mode_cylinderAllowedFourierMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : Set ℕ} {f : ℝ × ℕ → E} (hf : Integrable f (cylinderAllowedFourierMeasure M))
    {m : ℕ} (hm : m ∈ M) : Integrable (fun ξ ↦ f (ξ, m)) cylinderFrequencyMeasure := by
  rw [cylinderAllowedFourierMeasure_eq_prod] at hf
  have hs := ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1
  exact (Measure.ae_count_iff.mp
    ((ae_restrict_iff' (Set.to_countable M).measurableSet).mp hs)) m hm

/-- The restricted normalized measure is small enough for bounded synthesis. -/
theorem cylinderAllowedFourierMeasure_le_spectral (M : Set ℕ) :
    cylinderAllowedFourierMeasure M ≤ cylinderSpectralMeasure :=
  Measure.restrict_le_self.trans (Measure.prod_mono cylinderFrequencyMeasure_le_volume le_rfl)

theorem ae_mem_cylinderAllowedFourierMeasure (M : Set ℕ) :
    ∀ᵐ p ∂cylinderAllowedFourierMeasure M, p.2 ∈ M :=
  ae_restrict_mem ((Set.to_countable M).measurableSet.preimage measurable_snd)

end NoEmbeddedEigenvalues
