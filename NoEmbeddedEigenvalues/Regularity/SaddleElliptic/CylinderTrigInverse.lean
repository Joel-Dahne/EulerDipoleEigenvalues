import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTrigData

/-!
# A bounded spectral candidate from the actual trigonometric forcing data

Division uses the nonvanishing symbol on the allowed measure. The two-derivative
spectral weight gives actual L¹ and a bounded continuous periodic synthesis.
These are spectral statements and a dominated integral construction, not yet
an identification of the inverse L² transform or physical weak derivatives.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- The particular spectral candidate with the prescribed trigonometric amplitude. -/
def cylinderTrigInverse (a : ℝ) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    (p : ℝ × ℕ) : ℂ :=
  cylinderTrigFourierData even hG p / cylinderSymbol a p.1 p.2

theorem measurable_cylinderTrigInverse (a : ℝ) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure) :
    Measurable (cylinderTrigInverse a even hG) :=
  (measurable_cylinderTrigFourierData even hG).div (measurable_cylinderSymbol a)

/-- Actual folded L² data produce a genuine spectral inverse and a bounded,
continuous integral candidate, on the original angular-frequency measure. -/
theorem cylinderTrigInverse_spectral_bounds {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure) :
    let μ := cylinderAllowedFourierMeasure M
    let V := cylinderTrigInverse a even hG
    MemLp V 2 μ ∧
      MemLp (fun p ↦ (cylinderSobolevWeight p : ℂ) * V p) 2 μ ∧
      Integrable V μ ∧
      (∀ᵐ p ∂μ, cylinderSymbol a p.1 p.2 * V p = cylinderTrigFourierData even hG p) ∧
      Continuous (cylinderSynthesis even μ V) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x, ‖cylinderSynthesis even μ V x‖ ≤ C := by
  obtain ⟨B, _, hInv⟩ := cylinder_spectral_inverse ha hgap
  have hΦ : MemLp (cylinderTrigFourierData even hG) 2 (cylinderAllowedFourierMeasure M) :=
    (cylinderTrigFourierData_memLp even hG).mono_measure Measure.restrict_le_self
  have hi := hInv (cylinderAllowedFourierMeasure M) (ae_mem_cylinderAllowedFourierMeasure M)
    (cylinderTrigFourierData even hG) hΦ
  have hμ := cylinderAllowedFourierMeasure_le_spectral M
  have hs := cylinderSynthesis_of_memLp_weighted hμ hi.1.aestronglyMeasurable hi.2.1 even
  exact ⟨hi.1, hi.2.1,
    integrable_of_memLp_cylinderSobolevWeight hμ hi.1.aestronglyMeasurable hi.2.1,
    hi.2.2.1, hs⟩

/-- Every allowed degree has actual real-frequency L¹ and L² data. -/
theorem cylinderTrigInverse_mode_bounds {a : ℝ} (ha : 1 ≤ a) {M : Set ℕ}
    (hgap : ∀ m ∈ M, a ≠ (m : ℝ)) (even : Bool)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    {m : ℕ} (hm : m ∈ M) :
    Integrable (fun ξ ↦ cylinderTrigInverse a even hG (ξ, m)) cylinderFrequencyMeasure ∧
      MemLp (fun ξ ↦ cylinderTrigInverse a even hG (ξ, m)) 2 cylinderFrequencyMeasure := by
  obtain ⟨hV, _, hL1, _⟩ := cylinderTrigInverse_spectral_bounds ha hgap even hG
  refine ⟨integrable_mode_cylinderAllowedFourierMeasure hL1 hm, ?_⟩
  have hs := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
  apply (memLp_two_iff_integrable_sq_norm
    ((measurable_cylinderTrigInverse a even hG).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
  exact integrable_mode_cylinderAllowedFourierMeasure hs hm

end NoEmbeddedEigenvalues
