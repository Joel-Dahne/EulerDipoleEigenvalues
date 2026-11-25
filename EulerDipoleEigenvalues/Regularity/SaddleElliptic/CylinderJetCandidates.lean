module

public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderL2Inverse
public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.CylinderSignedMass

/-!
# Finite L² candidate entries for the cylinder jet

Each ordered word multiplies the signed spectrum by its time/angular derivative
symbols. The quadratic spectral weight controls every word through order two.
The inverse entries are genuine joint L² functions, even when their spectra are
not L¹. The zeroth entry is kept pointwise equal to the actual continuous integral.
This construction alone does not assert any weak derivative identity.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory

/-- Angular-frequency derivative symbol: time is coordinate zero. -/
def cylinderDerivativeSymbol (j : Fin 2) (p : ℝ × ℤ) : ℂ :=
  Complex.I * ((if j = 0 then p.1 else (p.2 : ℝ)) : ℂ)

/-- Ordered finite derivative multiplier, with the outer derivative at the head. -/
def cylinderJetSymbol : List (Fin 2) → ℝ × ℤ → ℂ
  | [], _ => 1
  | j :: w, p => cylinderDerivativeSymbol j p * cylinderJetSymbol w p

/-- The actual candidate derivative spectrum. -/
def cylinderSpectralJet (w : List (Fin 2)) (H : ℝ × ℤ → ℂ) (p : ℝ × ℤ) : ℂ :=
  cylinderJetSymbol w p * H p

theorem measurable_cylinderDerivativeSymbol (j : Fin 2) :
    Measurable (cylinderDerivativeSymbol j) := by
  unfold cylinderDerivativeSymbol
  split_ifs <;> fun_prop

theorem measurable_cylinderJetSymbol (w : List (Fin 2)) :
    Measurable (cylinderJetSymbol w) := by
  induction w with
  | nil => exact measurable_const
  | cons j w ih => exact (measurable_cylinderDerivativeSymbol j).mul ih

private theorem cylinderSignedWeight_eq (p : ℝ × ℤ) :
    cylinderSignedWeight p = 1 + p.1 ^ 2 + (p.2 : ℝ) ^ 2 := by
  simp [cylinderSignedWeight, cylinderSobolevWeight, Nat.cast_natAbs]

private theorem cylinderDerivativeSymbol_sq_le (j : Fin 2) (p : ℝ × ℤ) :
    ‖cylinderDerivativeSymbol j p‖ ^ 2 ≤ p.1 ^ 2 + (p.2 : ℝ) ^ 2 := by
  rw [cylinderDerivativeSymbol, norm_mul, Complex.norm_I, one_mul]
  split_ifs <;> rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] <;>
    nlinarith [sq_nonneg p.1, sq_nonneg (p.2 : ℝ)]

/-- One common quadratic weight controls every ordered multiplier through order two. -/
theorem norm_cylinderJetSymbol_le {w : List (Fin 2)} (hw : w.length ≤ 2) (p : ℝ × ℤ) :
    ‖cylinderJetSymbol w p‖ ≤ cylinderSignedWeight p := by
  rw [cylinderSignedWeight_eq]
  cases w with
  | nil =>
    simpa only [cylinderJetSymbol, norm_one] using
      (show (1 : ℝ) ≤ 1 + p.1 ^ 2 + (p.2 : ℝ) ^ 2 by
        nlinarith [sq_nonneg p.1, sq_nonneg (p.2 : ℝ)])
  | cons j w =>
    cases w with
    | nil =>
      simp only [cylinderJetSymbol, mul_one]
      have h := cylinderDerivativeSymbol_sq_le j p
      nlinarith [sq_nonneg (‖cylinderDerivativeSymbol j p‖ - 1)]
    | cons k w =>
      have he : w = [] := by simpa using hw
      subst w
      simp only [cylinderJetSymbol, mul_one, norm_mul]
      have hj := cylinderDerivativeSymbol_sq_le j p
      have hk := cylinderDerivativeSymbol_sq_le k p
      nlinarith [sq_nonneg
        (‖cylinderDerivativeSymbol j p‖ - ‖cylinderDerivativeSymbol k p‖)]

/-- Candidate derivative spectra have genuine L², without an L¹ premise. -/
theorem cylinderSpectralJet_memLp {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {w : List (Fin 2)} (hw : w.length ≤ 2) :
    MemLp (cylinderSpectralJet w H) 2 cylinderFourierMeasure := by
  apply hWH.of_le_mul ((measurable_cylinderJetSymbol w).aestronglyMeasurable.mul hH) (c := 1)
  exact Filter.Eventually.of_forall fun p ↦ by
    change ‖cylinderJetSymbol w p * H p‖ ≤ 1 * ‖(cylinderSignedWeight p : ℂ) * H p‖
    simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((one_le_cylinderSignedWeight p).trans' zero_le_one)]
    exact mul_le_mul_of_nonneg_right (norm_cylinderJetSymbol_le hw p) (norm_nonneg (H p))

/-- The spectral zeroth entry is the original function, with no representative change. -/
theorem cylinderSpectralJet_nil (H : ℝ × ℤ → ℂ) : cylinderSpectralJet [] H = H := by
  funext p
  simp only [cylinderSpectralJet, cylinderJetSymbol, one_mul]

/-- Joint inverse entries; the nil entry is the actual integral, not an L² choice. -/
def cylinderInverseJetEntries {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    (w : List (Fin 2)) : ℝ × AddCircle (2 * Real.pi) → ℂ :=
  if w = [] then cylinderJointSynthesis H else
    if hw : w.length ≤ 2 then
      cylinderInverseL2 ((cylinderSpectralJet_memLp hH hWH hw).toLp (cylinderSpectralJet w H))
    else 0

theorem cylinderInverseJetEntries_nil {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure) :
    cylinderInverseJetEntries hH hWH [] = cylinderJointSynthesis H := by
  simp [cylinderInverseJetEntries]

/-- Every specified candidate entry through order two has genuine finite joint mass. -/
theorem cylinderInverseJetEntries_memLp {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {w : List (Fin 2)} (hw : w.length ≤ 2) :
    MemLp (cylinderInverseJetEntries hH hWH w) 2 logCylinderMeasure := by
  by_cases h0 : w = []
  · subst w
    rw [cylinderInverseJetEntries_nil]
    have h2 : MemLp H 2 cylinderFourierMeasure := by
      simpa only [cylinderSpectralJet_nil] using cylinderSpectralJet_memLp hH hWH hw
    exact cylinderJointSynthesis_memLp (integrable_of_memLp_cylinderSignedWeight hH hWH) h2
  · simp only [cylinderInverseJetEntries, ite_eq_right h0, dite_eq_left hw]
    exact cylinderInverseL2_memLp _

/-- The actual nil entry and the chosen derivative entries represent one L² inverse family. -/
theorem cylinderInverseJetEntries_ae {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {w : List (Fin 2)} (hw : w.length ≤ 2) :
    cylinderInverseJetEntries hH hWH w =ᵐ[logCylinderMeasure]
      (cylinderInverseL2
        ((cylinderSpectralJet_memLp hH hWH hw).toLp (cylinderSpectralJet w H)) :
          ℝ × AddCircle (2 * Real.pi) → ℂ) := by
  by_cases h0 : w = []
  · subst w
    rw [cylinderInverseJetEntries_nil]
    have h1 := integrable_of_memLp_cylinderSignedWeight hH hWH
    have h2 := cylinderSpectralJet_memLp hH hWH hw
    simpa only [cylinderSpectralJet_nil] using
      (cylinderInverseL2_ae_integral
        (by simpa only [cylinderSpectralJet_nil] using h1) h2).symm
  · simp only [cylinderInverseJetEntries, ite_eq_right h0, dite_eq_left hw]
    exact Filter.EventuallyEq.rfl

/-- Exact finite mass of every candidate entry, including the actual nil integral. -/
theorem cylinderInverseJetEntries_sq_mass {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {w : List (Fin 2)} (hw : w.length ≤ 2) :
    (∫ q, ‖cylinderInverseJetEntries hH hWH w q‖ ^ 2 ∂logCylinderMeasure) =
      ∫ p, ‖cylinderSpectralJet w H p‖ ^ 2 ∂cylinderFourierMeasure := by
  calc
    _ = ∫ q, ‖cylinderInverseL2
        ((cylinderSpectralJet_memLp hH hWH hw).toLp (cylinderSpectralJet w H)) q‖ ^ 2
          ∂logCylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [cylinderInverseJetEntries_ae hH hWH hw] with q hq
      rw [hq]
    _ = _ := cylinderInverseL2_sq_mass (cylinderSpectralJet_memLp hH hWH hw)

end EulerDipoleEigenvalues
