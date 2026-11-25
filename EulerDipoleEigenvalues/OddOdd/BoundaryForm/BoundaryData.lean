module

public import EulerDipoleEigenvalues.OddOdd.Picone.PiconeDensities

/-! # Odd–odd boundary data and regularity -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology

/-- Continuous quotient trace on an oriented cell edge. -/
def ddArcTrace (φ : L2) (k : Fin 4) (t : ℝ) : ℂ :=
  continuousRep φ (torusProj (cellArc k t))

/-- Canonical boundary unknown in the interval coordinate. -/
def ddBoundaryUnknown (lam : ℝ) (φ : L2) (k : Fin 4) (x : ℝ) : ℂ :=
  canonicalUnknown lam (ddArcTrace φ k) (Real.artanh x)

/-- Boundary domains, endpoint characters and the identification of the transformed
    boundary forcing with the actual quotient trace. No energy inequality is a field. -/
structure DDBoundaryData (lam : ℝ) (κ : Bool) (φ : L2) where
  first : Fin 4 → ℝ → ℂ
  second : Fin 4 → ℝ → ℂ
  regular : ∀ k, HasWeightedBoundaryH2 (ddBoundaryUnknown lam φ k) (first k) (second k)
  endpoints : ∀ k, intervalH1Extension (-1) 1 (ddBoundaryUnknown lam φ k) (first k) 1 =
    paritySign κ * intervalH1Extension (-1) 1 (ddBoundaryUnknown lam φ k) (first k) (-1)
  trace_eq : ∀ k, ∀ᵐ x ∂(volume.restrict (Ioo (-1) 1)),
    correctedBoundaryTrace lam (ddBoundaryUnknown lam φ k) (first k) x =
      ddArcTrace φ k (Real.artanh x)

/-- The quotient multiplication identity holds pointwise for the continuous representatives. -/
theorem DDQuotientData.contStream_eq {lam : ℝ} {ω : L2} (q : DDQuotientData lam ω)
    (p : ℝ × ℝ) :
    contStream ω p = (dipoleLift p : ℂ) * continuousRep q.phi (torusProj p) := by
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  have ha : contStream ω =ᵐ[volume]
      (fun p ↦ (dipoleLift p : ℂ) * continuousRep q.phi (torusProj p)) := by
    filter_upwards [ae_torusProj q.stream_eq,
      ae_torusProj (coeFn_eq_continuousRep q.regular), streamLift_ae_eq_contStream ω]
      with p hp hφ hψ
    change invLap ω (torusProj p) = contStream ω p at hψ
    rw [← hψ, hp, hφ, Ψ_torusProj]
  exact congrFun (Measure.eq_of_ae_eq ha (continuous_contStream ω)
    ((Complex.continuous_ofReal.comp (by unfold dipoleLift; fun_prop)).mul hc)) p

/-- Division by the rotation-invariant dipole preserves the character, including on
    the separatrix by continuity. No pointwise division by zero is used. -/
theorem DDQuotientData.continuousRep_rotLift {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) (p : ℝ × ℝ) :
    continuousRep q.phi (torusProj (rotLift p)) =
      paritySign κ * continuousRep q.phi (torusProj p) := by
  have hn : ∀ᵐ p : ℝ × ℝ, dipoleLift p ≠ 0 := by
    have hm := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (0, Real.pi)
    have h := hm.quasiMeasurePreserving.ae ae_cos_fst_ne_cos_snd
    filter_upwards [h] with p hp
    simp only [Prod.fst_add, Prod.snd_add, add_zero, Real.cos_add_pi] at hp
    unfold dipoleLift
    intro hz
    apply hp
    linarith
  have hprod (p : ℝ × ℝ) : (dipoleLift p : ℂ) *
      continuousRep q.phi (torusProj (rotLift p)) =
      (dipoleLift p : ℂ) * (paritySign κ * continuousRep q.phi (torusProj p)) := by
    have h := contStream_rotLift hκ p
    rw [q.contStream_eq, q.contStream_eq] at h
    have hR : dipoleLift (rotLift p) = dipoleLift p := by
      simp [dipoleLift, rotLift, Real.cos_neg, add_comm]
    rw [hR] at h
    linear_combination h
  have ha : (fun p ↦ continuousRep q.phi (torusProj (rotLift p))) =ᵐ[volume]
      (fun p ↦ paritySign κ * continuousRep q.phi (torusProj p)) := by
    filter_upwards [hn] with p hp
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hp) (hprod p)
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  exact congrFun (Measure.eq_of_ae_eq ha (hc.comp (by unfold rotLift; fun_prop))
    (continuous_const.mul hc)) p

/-- Pointwise iteration of the quotient's rotation character. -/
theorem DDQuotientData.continuousRep_iterate_rotLift {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) (k : ℕ)
    (p : ℝ × ℝ) : continuousRep q.phi (torusProj (rotLift^[k] p)) =
      paritySign κ ^ k * continuousRep q.phi (torusProj p) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply, ih, q.continuousRep_rotLift hκ, pow_succ]
    ring

/-- The supplied quotient transport pair has zero Melnikov integral on every cell arc. -/
theorem DDQuotientData.arc_melnikov {lam : ℝ} {ω : L2} (q : DDQuotientData lam ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) (k : ℕ) :
    Integrable (deriv (fun s ↦ continuousRep q.phi (torusProj (cellArc k s)))) ∧
      (∫ t, profileIntegrand lam
        (fun s ↦ continuousRep q.phi (torusProj (cellArc k s))) t) = 0 := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hfR : ∀ p ∈ cellNeighbourhood, continuousRep q.phi (torusProj (p.2, -p.1)) =
      c * continuousRep q.phi (torusProj p) := by
    intro p _
    rw [hcc]
    exact q.continuousRep_rotLift hκ p
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  obtain ⟨hg, hM⟩ := melnikov q.transport closure_cellSquare_subset_cellNeighbourhood hc hUR hfR
    ((continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous).continuousOn
  simp only [Function.comp_def] at hg hM
  have hArc : (fun s ↦ continuousRep q.phi (torusProj (cellArc k s))) =
      fun s ↦ paritySign κ ^ k * continuousRep q.phi (torusProj (separatrixArc s)) :=
    funext fun s ↦ q.continuousRep_iterate_rotLift hκ k (separatrixArc s)
  rw [hArc]
  refine ⟨by simpa only [deriv_const_mul_field'] using hg.const_mul (paritySign κ ^ k), ?_⟩
  simp only [profileIntegrand, deriv_const_mul_field', mul_assoc, integral_const_mul]
  simp only [profileIntegrand, mul_assoc] at hM
  rw [hM, mul_zero]

/-- The canonical profiles of the quotient have the interval domain needed for corrected
    positivity; this is a separate input from the Picone current identity. -/
theorem dd_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) :
    Nonempty (DDBoundaryData lam κ q.phi) := by
  classical
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  let cp (k : Fin 4) := continuousRep q.phi (torusProj (rotLift^[k.val] (0, -Real.pi)))
  let cm (k : Fin 4) := continuousRep q.phi (torusProj (rotLift^[k.val] (Real.pi, 0)))
  have hRc (k : Fin 4) : Continuous
      (fun p ↦ continuousRep q.phi (torusProj (rotLift^[k.val] p))) :=
    hc.comp (Continuous.iterate (by unfold rotLift; fun_prop) k.val)
  have hgp (k : Fin 4) : Tendsto (ddArcTrace q.phi k) atTop (𝓝 (cp k)) :=
    ((hRc k).tendsto _).comp tendsto_separatrixArc_atTop
  have hgm (k : Fin 4) : Tendsto (ddArcTrace q.phi k) atBot (𝓝 (cm k)) :=
    ((hRc k).tendsto _).comp tendsto_separatrixArc_atBot
  have ha (k : Fin 4) := even_sobolev_arc_regularity q.regular q.even k.isLt
  have hm (k : Fin 4) := q.arc_melnikov hκ k.val
  have hr (k : Fin 4) := canonical_boundary_regularity hlam (ha k).1 (ha k).2.1
    (hm k).1 (ha k).2.2 (fun s ↦ (continuousRep q.phi).norm_coe_le_norm _)
    (hm k).2 (hgp k) (hgm k)
  choose D E hW hG ht hp hm using hr
  have hchar (k : Fin 4) : cp k = paritySign κ * cm k := by
    dsimp only [cp, cm]
    rw [show ((0 : ℝ), -Real.pi) = rotLift (Real.pi, 0) by simp [rotLift],
      ← Function.iterate_succ_apply, Function.iterate_succ_apply', q.continuousRep_rotLift hκ]
  have hArc (k : Fin 4) : ddArcTrace q.phi k =
      (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) := rfl
  have hUnknown (k : Fin 4) : ddBoundaryUnknown lam q.phi k =
      (fun ξ ↦ canonicalUnknown lam
        (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) (Real.artanh ξ)) := by
    funext ξ
    rw [ddBoundaryUnknown, hArc]
  refine ⟨⟨D, E, ?_, ?_, ?_⟩⟩
  · intro k
    rw [hUnknown k]
    exact hW k
  · intro k
    rw [hUnknown k, hp k, hm k, hchar k]
    ring
  · intro k
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ by
      simp only [correctedBoundaryTrace, hUnknown k, hArc k]
      exact ht k x hx

end EulerDipoleEigenvalues
