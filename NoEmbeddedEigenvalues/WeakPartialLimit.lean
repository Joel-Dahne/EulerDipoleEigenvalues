import NoEmbeddedEigenvalues.SobolevLocal
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak partial derivatives are closed under joint L² convergence

Both the value and its specified derivative converge strongly on the same
domain. Compact test pairings are continuous by the L² inner product. This
does not require Sobolev density, pointwise convergence, or boundary traces.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

theorem tendsto_integral_mul_of_L2 {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {f : ι → α → ℂ} {F ψ : α → ℂ}
    (hf : ∀ i, MemLp (f i) 2 μ) (hF : MemLp F 2 μ) (hψ : MemLp ψ 2 μ)
    (hlim : Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 (hF.toLp F))) :
    Tendsto (fun i ↦ ∫ p, f i p * ψ p ∂μ) l (𝓝 (∫ p, F p * ψ p ∂μ)) := by
  let v := hψ.star.toLp (star ψ)
  have he (u : α → ℂ) (hu : MemLp u 2 μ) :
      inner ℂ v (hu.toLp u) = ∫ p, u p * ψ p ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ.star.coeFn_toLp, hu.coeFn_toLp] with p hv hu
    simp only [RCLike.inner_apply, v, hv, hu, Pi.star_apply, starRingEnd_apply, star_star]
  have hc : Tendsto (fun _ : ι ↦ v) l (𝓝 v) := tendsto_const_nhds
  simpa only [he] using hc.inner (𝕜 := ℂ) hlim

/-- Strong L² limits of a specified weak pair retain that same weak derivative. -/
theorem HasWeakPartialOn.of_tendsto_L2 {U : Set (ℝ × ℝ)} {j : Fin 2}
    {f d : ℕ → ℝ × ℝ → ℂ} {F D : ℝ × ℝ → ℂ}
    (hweak : ∀ N, HasWeakPartialOn U j (f N) (d N))
    (hf : ∀ N, MemLp (f N) 2 (volume.restrict U))
    (hd : ∀ N, MemLp (d N) 2 (volume.restrict U))
    (hF : MemLp F 2 (volume.restrict U)) (hD : MemLp D 2 (volume.restrict U))
    (hflim : Tendsto (fun N ↦ (hf N).toLp (f N)) atTop (𝓝 (hF.toLp F)))
    (hdlim : Tendsto (fun N ↦ (hd N).toLp (d N)) atTop (𝓝 (hD.toLp D))) :
    HasWeakPartialOn U j F D := by
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hD.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  have hφ2 : MemLp φ 2 (volume.restrict U) :=
    (hφ.contDiff.continuous.memLp_of_hasCompactSupport hφ.hasCompactSupport).restrict U
  have hφd2 : MemLp (coordPartial j φ) 2 (volume.restrict U) :=
    ((hφ.continuous_coordPartial j).memLp_of_hasCompactSupport
      (hφ.hasCompactSupport_coordPartial j)).restrict U
  have he {ψ : ℝ × ℝ → ℂ} (hψ : tsupport ψ ⊆ U) (a : ℝ × ℝ → ℂ) :
      (∫ p in U, a p * ψ p) = ∫ p, a p * ψ p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hψ h)), mul_zero]
  have hleft : Tendsto (fun N ↦ ∫ p, f N p * coordPartial j φ p) atTop
      (𝓝 (∫ p, F p * coordPartial j φ p)) := by
    simpa only [he ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset)] using
      tendsto_integral_mul_of_L2 hf hF hφd2 hflim
  have hright : Tendsto (fun N ↦ -(∫ p, d N p * φ p)) atTop
      (𝓝 (-(∫ p, D p * φ p))) := by
    simpa only [he hφ.tsupport_subset] using
      (tendsto_integral_mul_of_L2 hd hD hφ2 hdlim).neg
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun N ↦ ((hweak N).2.2 φ hφ).symm))

end NoEmbeddedEigenvalues
