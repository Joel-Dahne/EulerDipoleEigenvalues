module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderTimeSynthesis

/-!
# Joint inverse synthesis on the logarithmic cylinder

Signed complex angular modes use probability Haar, and real angular frequency uses
`dξ / (2 * π)`. Genuine spectral L¹ makes the integral continuous and permits
angular coefficient extraction by Fubini. Spectral L² then supplies finite joint
cylinder mass by the actual modewise inverse integrals and angular Parseval.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SigmaFinite cylinderFourierMeasure := by
  unfold cylinderFourierMeasure
  infer_instance

/-- Signed Fourier synthesis kernel on the actual angular circle. -/
def cylinderJointKernel (q : ℝ × AddCircle (2 * Real.pi)) (p : ℝ × ℤ) : ℂ :=
  Complex.exp (Complex.I * ((q.1 * p.1 : ℝ) : ℂ)) * _root_.fourier p.2 q.2

/-- Actual joint inverse integral; its integrability is established separately. -/
def cylinderJointSynthesis (H : ℝ × ℤ → ℂ) (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  ∫ p, cylinderJointKernel q p * H p ∂cylinderFourierMeasure

theorem norm_cylinderJointKernel (q : ℝ × AddCircle (2 * Real.pi)) (p : ℝ × ℤ) :
    ‖cylinderJointKernel q p‖ = 1 := by
  simp only [cylinderJointKernel, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    _root_.fourier_apply, Circle.norm_coe]

theorem continuous_cylinderJointKernel :
    Continuous (fun z : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℤ) ↦
      cylinderJointKernel z.1 z.2) := by
  have hc : Continuous (fun z : ℤ × AddCircle (2 * Real.pi) ↦ _root_.fourier z.1 z.2) :=
    continuous_eval.comp
      (((continuous_of_discreteTopology : Continuous
        (_root_.fourier : ℤ → C(AddCircle (2 * Real.pi), ℂ))).comp continuous_fst).prodMk
          continuous_snd)
  exact (by fun_prop : Continuous (fun z : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℤ) ↦
    Complex.exp (Complex.I * ((z.1.1 * z.2.1 : ℝ) : ℂ)))).mul
      (hc.comp ((continuous_snd.snd).prodMk continuous_fst.snd))

theorem integrable_cylinderJointSynthesis {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (q : ℝ × AddCircle (2 * Real.pi)) :
    Integrable (fun p ↦ cylinderJointKernel q p * H p) cylinderFourierMeasure :=
  hH.bdd_mul (continuous_cylinderJointKernel.comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ (norm_cylinderJointKernel q p).le)

theorem continuous_cylinderJointSynthesis {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) : Continuous (cylinderJointSynthesis H) := by
  apply continuous_of_dominated (bound := fun p ↦ ‖H p‖)
  · intro q
    exact (integrable_cylinderJointSynthesis hH q).aestronglyMeasurable
  · intro q
    exact Filter.Eventually.of_forall fun p ↦ by
      change ‖cylinderJointKernel q p * H p‖ ≤ ‖H p‖
      rw [norm_mul, norm_cylinderJointKernel, one_mul]
  · exact hH.norm
  · exact Filter.Eventually.of_forall fun p ↦
      (continuous_cylinderJointKernel.comp
        (continuous_id.prodMk continuous_const)).mul continuous_const

theorem norm_cylinderJointSynthesis_le {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (q : ℝ × AddCircle (2 * Real.pi)) :
    ‖cylinderJointSynthesis H q‖ ≤ ∫ p, ‖H p‖ ∂cylinderFourierMeasure := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (integrable_cylinderJointSynthesis hH q).norm hH.norm
  intro p
  change ‖cylinderJointKernel q p * H p‖ ≤ ‖H p‖
  rw [norm_mul, norm_cylinderJointKernel, one_mul]

theorem cylinderJointSynthesis_slice_memLp {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (t : ℝ) :
    MemLp (fun θ ↦ cylinderJointSynthesis H (t, θ)) 2 AddCircle.haarAddCircle :=
  MemLp.of_bound ((continuous_cylinderJointSynthesis hH).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (∫ p, ‖H p‖ ∂cylinderFourierMeasure)
    (Filter.Eventually.of_forall fun θ ↦ norm_cylinderJointSynthesis_le hH (t, θ))

/-- Counting measure leaves no exceptional signed mode. -/
theorem cylinderFourierMeasure_mode_integrable {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (n : ℤ) :
    Integrable (fun ξ ↦ H (ξ, n)) cylinderFrequencyMeasure :=
  Measure.ae_count_iff.mp hH.prod_left_ae n

theorem cylinderFourierMeasure_mode_memLp {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) (n : ℤ) :
    MemLp (fun ξ ↦ H (ξ, n)) 2 cylinderFrequencyMeasure := by
  have hm := Measure.ae_count_iff.mp hH.aestronglyMeasurable.prodMk_right n
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact Measure.ae_count_iff.mp
    ((memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH).prod_left_ae n

/-- Extracting the angular coefficient of the actual integral gives its actual
normalized time inverse, not just a class chosen independently. -/
theorem cylinderJointSynthesis_coeff {H : ℝ × ℤ → ℂ}
    (hH : Integrable H cylinderFourierMeasure) (n : ℤ) (t : ℝ) :
    cylinderAngularCoeff (cylinderJointSynthesis H) n t =
      cylinderTimeSynthesis (fun ξ ↦ H (ξ, n)) t := by
  have hc : Continuous (fun z : AddCircle (2 * Real.pi) × (ℝ × ℤ) ↦
      _root_.fourier (-n) z.1 * cylinderJointKernel (t, z.1) z.2) :=
    ((_root_.fourier (-n)).continuous.comp continuous_fst).mul
      (continuous_cylinderJointKernel.comp
        ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
  have hi : Integrable (fun z : AddCircle (2 * Real.pi) × (ℝ × ℤ) ↦
      _root_.fourier (-n) z.1 * (cylinderJointKernel (t, z.1) z.2 * H z.2))
        (AddCircle.haarAddCircle.prod cylinderFourierMeasure) := by
    have hb : ∀ z : AddCircle (2 * Real.pi) × (ℝ × ℤ),
        ‖_root_.fourier (-n) z.1 * cylinderJointKernel (t, z.1) z.2‖ ≤ 1 := by
      intro z
      rw [norm_mul, norm_cylinderJointKernel, _root_.fourier_apply, Circle.norm_coe, one_mul]
    simpa only [mul_assoc] using (hH.comp_snd AddCircle.haarAddCircle).bdd_mul
      hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hinner (p : ℝ × ℤ) :
      (∫ θ, _root_.fourier (-n) θ * (cylinderJointKernel (t, θ) p * H p)
        ∂AddCircle.haarAddCircle) =
      if p.2 = n then Complex.exp (Complex.I * ((t * p.1 : ℝ) : ℂ)) * H p else 0 := by
    have hf : (∫ θ : AddCircle (2 * Real.pi),
        _root_.fourier (-n) θ * _root_.fourier p.2 θ ∂AddCircle.haarAddCircle) =
        if p.2 = n then (1 : ℂ) else 0 := by
      change _root_.fourierCoeff (_root_.fourier p.2) n = _
      rw [_root_.fourierCoeff_fourier]
      simp [Pi.single_apply, eq_comm]
    calc
      _ = (Complex.exp (Complex.I * ((t * p.1 : ℝ) : ℂ)) * H p) *
          ∫ θ : AddCircle (2 * Real.pi), _root_.fourier (-n) θ * _root_.fourier p.2 θ
            ∂AddCircle.haarAddCircle := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun θ ↦ by dsimp [cylinderJointKernel]; ring
      _ = _ := by rw [hf]; split_ifs <;> simp
  have hj := hi.integral_prod_right.congr (Filter.Eventually.of_forall hinner)
  change (∫ θ : AddCircle (2 * Real.pi), _root_.fourier (-n) θ *
    (∫ p, cylinderJointKernel (t, θ) p * H p ∂cylinderFourierMeasure)
      ∂AddCircle.haarAddCircle) = _
  calc
    _ = ∫ θ : AddCircle (2 * Real.pi), ∫ p, _root_.fourier (-n) θ *
        (cylinderJointKernel (t, θ) p * H p) ∂cylinderFourierMeasure
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ ↦ (integral_const_mul _ _).symm
    _ = ∫ p, ∫ θ : AddCircle (2 * Real.pi), _root_.fourier (-n) θ *
        (cylinderJointKernel (t, θ) p * H p) ∂AddCircle.haarAddCircle
          ∂cylinderFourierMeasure := integral_integral_swap hi
    _ = ∫ p, (if p.2 = n then Complex.exp (Complex.I * ((t * p.1 : ℝ) : ℂ)) * H p
        else 0) ∂cylinderFourierMeasure := integral_congr_ae
          (Filter.Eventually.of_forall hinner)
    _ = _ := by
      rw [cylinderFourierMeasure, integral_prod _ hj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ ↦ by
        have hs : (fun m : ℤ ↦ if m = n then
            Complex.exp (Complex.I * ((t * ξ : ℝ) : ℂ)) * H (ξ, m) else 0) =
            ({n} : Set ℤ).indicator
              (fun m ↦ Complex.exp (Complex.I * ((t * ξ : ℝ) : ℂ)) * H (ξ, m)) := by
          ext m
          simp [Set.indicator]
        dsimp only
        rw [hs, integral_indicator (measurableSet_singleton n), integral_singleton]
        simp

end NoEmbeddedEigenvalues
