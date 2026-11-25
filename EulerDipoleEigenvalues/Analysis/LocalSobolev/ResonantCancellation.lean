module

public import EulerDipoleEigenvalues.Analysis.Inequalities.ScalarDivision

/-!
# Integrable quotients cancel at differentiable divisor zeros

Blueprint: `lem:integrable-divisor-cancellation`.

A nonzero continuous numerator and a divisor differentiable at its zero force
a reciprocal-distance lower bound on the quotient. This contradicts local L¹
integrability. Neither simplicity of the zero nor a value of the quotient at
the exceptional point is required.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- An a.e. integrable quotient forces a continuous numerator to vanish at every
interior differentiable divisor zero, even when that zero is not simple. -/
theorem eq_zero_of_integrable_divisor {a b z : ℝ} {N D E : ℝ → ℂ}
    (hz : z ∈ Ioo a b) (hN : ContinuousAt N z) (hD : DifferentiableAt ℝ D z)
    (hDz : D z = 0) (hE : IntegrableOn E (Ioo a b))
    (hrel : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ‖D x‖ * ‖E x‖ = ‖N x‖) : N z = 0 := by
  by_contra hne
  obtain ⟨C, hC⟩ := hD.hasDerivAt.isBigO_sub.bound
  let C' := max C 1
  have hC' : 0 < C' := lt_max_of_lt_right one_pos
  let m := ‖N z‖ / 2
  have hm : 0 < m := by dsimp [m]; exact half_pos (norm_pos_iff.2 hne)
  have hNm : ∀ᶠ x in 𝓝 z, m < ‖N x‖ := hN.norm.eventually
    (lt_mem_nhds (by dsimp [m]; linarith [norm_pos_iff.2 hne]))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (hC.and (hNm.and (Ioo_mem_nhds hz.1 hz.2)))
  let ε := min δ 1 / 2
  have hε : 0 < ε := by positivity
  have hεδ : ε < δ := by have := min_le_left δ 1; dsimp [ε]; linarith
  have hnear (x : ℝ) (hx : x ∈ Ioc z (z + ε)) : dist x z < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
    linarith [hx.2]
  have hsub : Ioc z (z + ε) ⊆ Ioo a b := fun x hx ↦ (hball (hnear x hx)).2.2
  have hlow : ∀ᵐ x ∂(volume.restrict (Ioc z (z + ε))),
      ENNReal.ofReal (m / C') * ENNReal.ofReal (x - z)⁻¹ ≤ ‖E x‖ₑ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hrel,
      ae_restrict_mem measurableSet_Ioc] with x hxrel hx
    obtain ⟨hL, hNx, -⟩ := hball (hnear x hx)
    have hpos : 0 < x - z := sub_pos.2 hx.1
    have hL' : ‖D x‖ ≤ C' * (x - z) := by
      rw [hDz, sub_zero, Real.norm_eq_abs, abs_of_pos hpos] at hL
      exact hL.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
    have hprod : m ≤ C' * (x - z) * ‖E x‖ := by
      calc m ≤ ‖N x‖ := hNx.le
        _ = ‖D x‖ * ‖E x‖ := hxrel.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hL' (norm_nonneg _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, div_le_iff₀ hC', ← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith [hprod]
  have hfin : ∫⁻ x in Ioo a b, ‖E x‖ₑ < ⊤ :=
    (hasFiniteIntegral_iff_eNorm).1 hE.2
  have hI : ∫⁻ x in Ioc z (z + ε), ENNReal.ofReal (x - z)⁻¹ < ⊤ := by
    have h1 : ENNReal.ofReal (m / C') *
        ∫⁻ x in Ioc z (z + ε), ENNReal.ofReal (x - z)⁻¹ < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ((lintegral_mono_ae hlow).trans (lintegral_mono_set hsub)).trans_lt hfin
    exact (ENNReal.mul_lt_top_iff.1 h1).elim (fun h ↦ h.2) (fun h ↦ h.elim
      (fun h0 ↦ absurd h0 (by simp only [ENNReal.ofReal_eq_zero, not_le]; positivity))
      (fun h0 ↦ by rw [h0]; exact ENNReal.zero_lt_top))
  have hint : IntervalIntegrable (fun x ↦ (x - z)⁻¹) volume z (z + ε) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    refine ⟨(measurable_id.sub_const _).inv.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hI
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact inv_nonneg.2 (by linarith [hx.1])
  rw [intervalIntegrable_sub_inv_iff] at hint
  rcases hint with h | h
  · linarith
  · exact h (left_mem_uIcc)

end EulerDipoleEigenvalues
