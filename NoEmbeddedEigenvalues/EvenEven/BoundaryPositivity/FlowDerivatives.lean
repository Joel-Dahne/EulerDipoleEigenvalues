import NoEmbeddedEigenvalues.EvenEven.BoundaryPositivity.FlowBoundaryForm
import NoEmbeddedEigenvalues.Transport.CanonicalProfile.CanonicalProfile

/-! # Weighted boundary derivatives in flow time -/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory Set Filter Topology

/-- Pullback by `tanh` preserves almost-everywhere statements. Its inverse is differentiable
    on `(-1,1)`, so preimages of null sets are images of null sets under `artanh`. -/
theorem ae_comp_tanh {P : ℝ → Prop} (hP : ∀ᵐ x, P x) : ∀ᵐ s, P (Real.tanh s) := by
  have hd : DifferentiableOn ℝ Real.artanh (Ioo (-1) 1) := by
    intro x hx
    have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
    have hq : DifferentiableAt ℝ (fun x : ℝ ↦ (1 + x) / (1 - x)) x :=
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).differentiableAt.div
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).differentiableAt
        (by linarith [hx.2])
    exact ((hq.sqrt hp.ne').log (Real.sqrt_pos.2 hp).ne').differentiableWithinAt
  rw [ae_iff] at hP ⊢
  have hn : volume ({x | ¬P x} ∩ Ioo (-1 : ℝ) 1) = 0 :=
    measure_mono_null inter_subset_left hP
  have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hd.mono inter_subset_right) hn
  have heq : {s | ¬P (Real.tanh s)} =
      Real.artanh '' ({x | ¬P x} ∩ Ioo (-1 : ℝ) 1) := by
    ext s
    constructor
    · intro hs
      exact ⟨Real.tanh s, ⟨hs, ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩⟩,
        Real.artanh_tanh s⟩
    · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
      change ¬P (Real.tanh (Real.artanh x))
      rw [Real.tanh_artanh hxi]
      exact hx
  rw [heq]
  exact him

/-- The first weighted derivative is the derivative of the flow-time value a.e. -/
theorem HasWeightedBoundaryH2.ae_hasDerivAt_flowValue {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) :
    ∀ᵐ s, HasDerivAt (flowValue F) (flowFirst D s) s := by
  filter_upwards [ae_comp_tanh h.h1.hasDerivAt_ae] with s hs
  exact hasDerivAt_flowValue (hs ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)

/-- The second weighted derivative is the derivative of the first flow derivative a.e. -/
theorem HasWeightedBoundaryH2.ae_hasDerivAt_flowFirst {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) :
    ∀ᵐ s, HasDerivAt (flowFirst D) (flowSecond D E s) s := by
  filter_upwards [ae_comp_tanh h.hasDerivAt_first_ae] with s hs
  exact hasDerivAt_flowFirst (hs ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)

/-- The first flow derivative is continuous; only interior continuity of `D` is needed. -/
theorem HasWeightedBoundaryH2.continuous_flowFirst {F D E : ℝ → ℂ}
    (h : HasWeightedBoundaryH2 F D E) : Continuous (flowFirst D) := by
  have hD : ContinuousOn D (Ioo (-1) 1) := by
    intro x hx
    have hac := h.locally_absolutelyContinuous_first ((x - 1) / 2) ((x + 1) / 2)
      (by linarith [hx.1]) (by linarith) (by linarith [hx.2])
    have hc := hac.continuousOn
    rw [uIcc_of_le (by linarith : (x - 1) / 2 ≤ (x + 1) / 2)] at hc
    exact (hc.continuousAt (Icc_mem_nhds (by linarith [hx.1])
      (by linarith [hx.2]))).continuousWithinAt
  have ht : Continuous Real.tanh := continuous_iff_continuousAt.mpr
    (fun s ↦ (hasDerivAt_tanh s).continuousAt)
  have hcomp : Continuous (fun s ↦ D (Real.tanh s)) :=
    hD.comp_continuous ht (fun s ↦ ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩)
  exact (continuous_ofReal.comp (continuous_const.sub (ht.pow 2))).mul hcomp

end NoEmbeddedEigenvalues
