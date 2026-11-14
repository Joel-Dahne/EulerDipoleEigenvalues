import NoEmbeddedEigenvalues.Analysis.RadialMeanKernel
import NoEmbeddedEigenvalues.Analysis.WeakLaplacian
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# A fixed radial smoothing reproduces a classical harmonic function

The polar-coordinate Fubini integrals are genuinely integrable on a bounded
rectangle before the angular mean-value identity is applied. Complex Euclidean
harmonicity is bridged to the actual Cartesian coordinate trace; no inner
product is placed on the product maximum-norm carrier.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Metric InnerProductSpace
open scoped ContDiff Topology

/-- A smooth Cartesian zero trace gives native Euclidean harmonicity. -/
theorem harmonicOnNhd_complex_of_plane {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hΔ : ∀ p ∈ V, planeLaplacian g p = 0) :
    HarmonicOnNhd (g ∘ Complex.equivRealProdCLM) (Complex.equivRealProdCLM ⁻¹' V) := by
  intro z hz
  refine ⟨(hg.comp Complex.equivRealProdCLM.contDiff).contDiffAt.of_le (by simp), ?_⟩
  filter_upwards [(hV.preimage Complex.equivRealProdCLM.continuous).mem_nhds hz] with w hw
  exact (laplacian_complex_of_plane hg w).trans (hΔ _ hw)

private theorem polar_integrable_of_upper_support {R : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) (hzero : ∀ p, R < p.1 → F p = 0) :
    IntegrableOn F (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  let K := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hi : Integrable (K.indicator F) :=
    (hF.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  apply hi.integrableOn.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  by_cases hR : p.1 ≤ R
  · rw [indicator_of_mem (show p ∈ K from ⟨⟨hp.1.le, hR⟩, hp.2.1.le, hp.2.2.le⟩)]
  · rw [hzero p (lt_of_not_ge hR), indicator_apply_eq_zero.mpr]
    intro _
    exact hzero p (lt_of_not_ge hR)

private theorem radialPlaneKernel_polar (R : ℝ) (q : ℝ × ℝ) :
    radialPlaneKernel R (polarCoord.symm q) = radialPlaneKernel R (q.1, 0) := by
  apply radialPlaneKernel_norm_eq R
  change ‖Complex.polarCoord.symm q‖ = ‖Complex.equivRealProdCLM.symm (q.1, 0)‖
  simp only [Complex.norm_polarCoord_symm, Complex.equivRealProdCLM_symm_apply,
    Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs]

private theorem radialPlaneKernel_real_zero {R r : ℝ} (hR : 0 < R) (hr : R < r) :
    radialPlaneKernel R (r, 0) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  have hn := tsupport_radialPlaneKernel hR hp
  change ‖Complex.equivRealProdCLM.symm (r, 0)‖ ≤ R at hn
  simp only [Complex.equivRealProdCLM_symm_apply, Complex.ofReal_zero, zero_mul,
    add_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR.trans hr)] at hn
  exact (not_le_of_gt hr) hn

/-- The angular circle identity in exactly the polar strip used by change of variables. -/
theorem harmonic_integral_polar_angle {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {g : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hH : HarmonicOnNhd (g ∘ Complex.equivRealProdCLM)
      (closedBall (Complex.equivRealProdCLM.symm x) R)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, g (x - polarCoord.symm (r, θ))) =
      ∫ _θ in Ioo (-Real.pi) Real.pi, g x := by
  have hm := (hH.mono (closedBall_subset_closedBall
    (show |(-r)| ≤ R by simpa [abs_of_pos hr] using hrR))).circleAverage_eq
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right
      (fun θ ↦ (g ∘ Complex.equivRealProdCLM)
        (circleMap (Complex.equivRealProdCLM.symm x) (-r) θ)) (-Real.pi)] at hm
  have hend : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simp only [zero_add, hend, intervalIntegral.integral_of_le
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at hm
  have hcircle (θ : ℝ) :
      Complex.equivRealProdCLM (circleMap (Complex.equivRealProdCLM.symm x) (-r) θ) =
        x - polarCoord.symm (r, θ) := by
    apply Complex.equivRealProdCLM.symm.injective
    change circleMap (Complex.equivRealProdCLM.symm x) (-r) θ =
      Complex.equivRealProdCLM.symm x - Complex.polarCoord.symm (r, θ)
    simp [circleMap, Complex.exp_mul_I, Complex.polarCoord_symm_apply]
    ring
  simp_rw [hcircle] at hm
  calc
    _ = (2 * Real.pi) • ((2 * Real.pi)⁻¹ •
        ∫ θ in Ioo (-Real.pi) Real.pi, g (x - polarCoord.symm (r, θ))) := by
      rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    _ = (2 * Real.pi) • g x := by rw [hm]
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
        (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), intervalIntegral.integral_const]
      congr 1
      ring

/-- A fixed normalized Euclidean radial kernel reproduces the center value of
an actual classical harmonic function on its whole closed support disk. -/
theorem integral_radialPlaneKernel_mul_harmonic {R : ℝ} (hR : 0 < R)
    {g : ℝ × ℝ → ℂ} (hg : Continuous g) (x : ℝ × ℝ)
    (hH : HarmonicOnNhd (g ∘ Complex.equivRealProdCLM)
      (closedBall (Complex.equivRealProdCLM.symm x) R)) :
    (∫ y, radialPlaneKernel R y * g (x - y)) = g x := by
  let B (q : ℝ × ℝ) : ℂ :=
    q.1 • (radialPlaneKernel R (polarCoord.symm q) * g (x - polarCoord.symm q))
  let B0 (q : ℝ × ℝ) : ℂ :=
    q.1 • (radialPlaneKernel R (polarCoord.symm q) * g x)
  have hKc := (contDiff_radialPlaneKernel R).continuous
  have hBc : Continuous B := continuous_fst.smul
    ((hKc.comp continuous_polarCoord_symm).mul
      (hg.comp (continuous_const.sub continuous_polarCoord_symm)))
  have hB0c : Continuous B0 := continuous_fst.smul
    ((hKc.comp continuous_polarCoord_symm).mul continuous_const)
  have hB : IntegrableOn B (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    apply polar_integrable_of_upper_support (R := R) hBc
    intro q hq
    simp only [B, radialPlaneKernel_polar, radialPlaneKernel_real_zero hR hq,
      zero_mul, smul_zero]
  have hB0 : IntegrableOn B0 (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    apply polar_integrable_of_upper_support (R := R) hB0c
    intro q hq
    simp only [B0, radialPlaneKernel_polar, radialPlaneKernel_real_zero hR hq,
      zero_mul, smul_zero]
  have hang (r : ℝ) (hr : 0 < r) :
      (∫ θ in Ioo (-Real.pi) Real.pi, B (r, θ)) =
        ∫ θ in Ioo (-Real.pi) Real.pi, B0 (r, θ) := by
    by_cases hrR : r ≤ R
    · simp only [B, B0, radialPlaneKernel_polar, Complex.real_smul, ← mul_assoc]
      rw [integral_const_mul, integral_const_mul, harmonic_integral_polar_angle hr hrR hH]
    · simp only [B, B0, radialPlaneKernel_polar,
        radialPlaneKernel_real_zero hR (lt_of_not_ge hrR), zero_mul, smul_zero, integral_zero]
  calc
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, B q :=
      (integral_comp_polarCoord_symm _).symm
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, B (r, θ) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod _ hB
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, B0 (r, θ) :=
      setIntegral_congr_fun measurableSet_Ioi hang
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, B0 q := by
      rw [Measure.volume_eq_prod]
      exact (setIntegral_prod _ hB0).symm
    _ = ∫ y, radialPlaneKernel R y * g x :=
      integral_comp_polarCoord_symm (fun y ↦ radialPlaneKernel R y * g x)
    _ = g x := by rw [integral_mul_const, integral_radialPlaneKernel hR, one_mul]

end NoEmbeddedEigenvalues
