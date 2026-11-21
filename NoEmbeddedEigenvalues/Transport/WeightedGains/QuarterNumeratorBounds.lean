module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitNumeratorDerivative
public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals

/-!
# Elementary estimates for quarter-numerator derivatives

Complex Cauchy–Schwarz, the two-term norm inequality and continuity of the
fixed-time level vector are shared by weighted and unweighted numerator bounds.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real
open scoped Topology ContDiff

/-- Integral Cauchy–Schwarz with explicit L² hypotheses. -/
theorem norm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℂ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    ‖∫ x, F x * G x ∂μ‖ ^ 2 ≤ (∫ x, ‖F x‖ ^ 2 ∂μ) * ∫ x, ‖G x‖ ^ 2 ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp F (ENNReal.ofReal 2) μ by simpa using hF)
    (show MemLp G (ENNReal.ofReal 2) μ by simpa using hG)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  have hn := (norm_integral_le_integral_norm (f := fun x ↦ F x * G x)).trans
    (by simpa only [norm_mul] using hh)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  rw [mul_pow, sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),
    sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))] at hs
  exact hs

/-- A nonsharp two-term square-norm bound. -/
theorem norm_add_sq_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

/-- The fixed-time orbit-level derivative is continuous in time. -/
theorem continuous_orbit_level_derivative {h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun t ↦ deriv (fun x ↦ dipoleOrbit x t) h) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦
      fderiv ℝ (fun p : ℝ × ℝ ↦ dipoleOrbit p.1 p.2) q (1, 0)) (h, t) :=
    ((contDiffAt_orbitMap (t := t) hh).fderiv_right (m := ∞)
      (by simp)).clm_apply contDiffAt_const
  have he : ∀ t, deriv (fun x ↦ dipoleOrbit x t) h =
      fderiv ℝ (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) (h, t) (1, 0) := by
    intro t
    have hd := ((contDiffAt_orbitMap (t := t) hh).differentiableAt (by simp)).hasFDerivAt
    exact (hd.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h t))).deriv
  simp_rw [he]
  exact hs.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt

end NoEmbeddedEigenvalues
