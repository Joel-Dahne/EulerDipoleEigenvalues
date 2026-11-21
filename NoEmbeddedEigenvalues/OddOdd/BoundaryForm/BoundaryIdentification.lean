module

public import NoEmbeddedEigenvalues.OddOdd.Picone.CharacterVirialLimit

/-! # Identification of the odd–odd boundary form -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- The explicit expanded boundary coefficient has exactly the normalization used in β. -/
theorem ddBoundaryB_two_weight (x : ℝ) :
    ddBoundaryB (2 * boundaryWeight x) = boundaryWeight x * correctedBoundaryBeta x := by
  have h : 2 * boundaryWeight x / 2 = boundaryWeight x := by ring
  dsimp only [ddBoundaryB, ddBoundaryGround, correctedBoundaryBeta]
  rw [h]
  ring_nf

/-- The arc correction in flow time is the Jacobian-weighted interval correction. -/
theorem ddBoundaryB_cosh (t : ℝ) : ddBoundaryB (2 / Real.cosh t ^ 2) =
    (1 / Real.cosh t ^ 2) * correctedBoundaryBeta (Real.tanh t) := by
  rw [show 2 / Real.cosh t ^ 2 = 2 * boundaryWeight (Real.tanh t) by
    rw [boundaryWeight_tanh]; ring, ddBoundaryB_two_weight, boundaryWeight_tanh]

/-- Renormalizing the actual current uses the very same counterterm as the virial bulk. -/
theorem dd_ground_current_limit {φ : L2} (hφ : MemSobolev 2 φ) :
    Tendsto (fun ε ↦ ddGroundCurrent φ ε + ddLogCounterterm φ ε) (𝓝[>] 0)
      (𝓝 (-(8 / 3 : ℝ) * (ddValueFinitePart φ -
        ∑ k : Fin 4, ∫ t, ddArcCorrection φ k t))) := by
  have h := ((dd_current_remainder_limit hφ).sub
    ((dd_value_finite_part hφ).2.const_mul (8 / 3 : ℝ))).add
      ((dd_boundaryB_trace_limit hφ).2.const_mul (8 / 3 : ℝ))
  convert h using 1
  · funext ε
    dsimp only [ddLogCounterterm]
    ring
  · congr 1
    ring

/-- Changing variables in the correction preserves absolute integrability and identifies
    the actual canonical forcing supplied by the boundary data. No positivity is used. -/
theorem dd_boundary_correction_eq {lam : ℝ} {κ : Bool} {φ : L2}
    (b : DDBoundaryData lam κ φ) (k : Fin 4) :
    IntegrableOn (correctedBoundaryTerm lam (ddBoundaryUnknown lam φ k) (b.first k))
      (Ioo (-1) 1) ∧
      (∫ t, ddArcCorrection φ k t) =
        ∫ x in (-1 : ℝ)..1, correctedBoundaryTerm lam
          (ddBoundaryUnknown lam φ k) (b.first k) x := by
  have ha := ae_comp_tanh ((ae_restrict_iff' measurableSet_Ioo).1 (b.trace_eq k))
  have ht : ∀ᵐ t, correctedBoundaryTrace lam (ddBoundaryUnknown lam φ k) (b.first k)
      (Real.tanh t) = ddArcTrace φ k t := by
    filter_upwards [ha] with t ht
    simpa only [Real.artanh_tanh] using ht ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  have he : (fun t ↦ (1 / Real.cosh t ^ 2) • correctedBoundaryTerm lam
      (ddBoundaryUnknown lam φ k) (b.first k) (Real.tanh t)) =ᵐ[volume] ddArcCorrection φ k := by
    filter_upwards [ht] with t ht
    simp only [smul_eq_mul, correctedBoundaryTerm, ht, ddArcCorrection, ddBoundaryB_cosh]
    ring
  refine ⟨(b.regular k).integrable_correctedBoundaryTerm lam, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_tanh_subst]
  exact (integral_congr_ae he).symm

/-- The canonical arc form is the uncorrected interval form for the specified derivatives. -/
theorem DDQuotientData.canonicalArcForm_eq_boundaryForm {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hlam : lam ≠ 0) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (b : DDBoundaryData lam κ q.phi) (k : Fin 4) :
    canonicalArcForm lam (ddArcTrace q.phi k) =
      boundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  have hg := (q.arc_melnikov hκ k.val).1
  have he := (even_sobolev_arc_regularity q.regular q.even k.isLt).2.2
  have hArc : ddArcTrace q.phi k =
      (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) := rfl
  rw [← hArc] at hg he
  have hUnknown : ddBoundaryUnknown lam q.phi k =
      (fun ξ ↦ canonicalUnknown lam (ddArcTrace q.phi k) (Real.artanh ξ)) := rfl
  have hw := b.regular k
  rw [hUnknown] at hw ⊢
  exact (canonicalArcForm_eq_flowBoundaryForm hlam hg he hw).trans (hw.flowBoundaryForm_eq lam)

/-- Identification with the corrected interval form for arbitrary supplied boundary data. -/
theorem DDQuotientData.correctedBoundaryForm_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hlam : lam ≠ 0) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (b : DDBoundaryData lam κ q.phi) (k : Fin 4) :
    canonicalArcForm lam (ddArcTrace q.phi k) + (∫ t, ddArcCorrection q.phi k t) =
      correctedBoundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  rw [q.canonicalArcForm_eq_boundaryForm hlam hκ b k,
    (dd_boundary_correction_eq b k).2]
  rfl

end NoEmbeddedEigenvalues
