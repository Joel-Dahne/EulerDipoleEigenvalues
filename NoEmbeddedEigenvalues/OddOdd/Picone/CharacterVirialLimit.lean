import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddPicone
import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddCoercivity
import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddBoundaryTrace
import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddCurrentRemainder
import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddRenormalizedBulk
import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddValueFinitePart
import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddGradientTraces

/-! # Odd–odd character virial limit and boundary ground state -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- Character-wise renormalized virial for supplied quotient data. This is a full bulk
    limit; pairing convergence along good levels is sufficient to identify it. -/
theorem dd_character_virial_limit {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    Tendsto (fun ε ↦ ddRawBulk q.phi q.nu dx dy ε + ddLogCounterterm q.phi ε)
      (𝓝[>] 0) (𝓝 (-(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) + ddValueFinitePart q.phi))) := by
  classical
  -- Existence is a full positive-level bulk limit, independent of the pairing sequence.
  have he := q.weighted_nu.mono_measure
    (Measure.restrict_mono (subset_closure.trans
      closure_cellSquare_subset_cellNeighbourhood) le_rfl)
  obtain ⟨-, -, J, hJ⟩ := dd_renormalized_bulk q.regular q.even hdx hdy he
  have hbulk : Tendsto
      (fun ε ↦ ddRawBulk q.phi q.nu dx dy ε + ddLogCounterterm q.phi ε)
      (𝓝[>] 0) (𝓝 J) := by
    convert hJ using 1
    funext ε
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ by
      dsimp only [ddVirialDensity, ddVorticityDensity, ddRawEnergy]
      ring
  obtain ⟨-, Ng, hNg, hN, hT, hM⟩ :=
    dd_quotient_gradient_traces q.regular q.even hdx hdy
  -- Put every exceptional set in the same orbit parameter h = ε/2.
  let P : ℝ → Prop := fun h ↦ ddRawBulk q.phi q.nu dx dy (2 * h) =
    (8 - (2 * h) ^ 3) / 3 *
      (levelIntegral h (fun p ↦ ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
        levelIntegral h (fun p ↦ ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
        ddLevelMass q.phi (2 * h) -
        levelIntegral h (fun p ↦
          (liftL2 q.nu p * (starRingEnd ℂ) (continuousRep q.phi (torusProj p))).re)) -
      (2 * h) ^ 2 * levelIntegral h (fun p ↦ gradNorm p *
        ((starRingEnd ℂ) (continuousRep q.phi (torusProj p)) *
          ddInwardNormal (liftL2 dx) (liftL2 dy) p).re)
  have hPae : ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)), P h := by
    filter_upwards [q.ae_truncated_virial hlam hω hs hdx hdy,
      dd_virial_level_split q.regular q.nu dx dy] with h hv hb
    exact hv.trans hb
  let Nv : Set ℝ := {h | h ∈ Ioo 0 1 ∧ ¬P h}
  have hNv : volume Nv = 0 := by
    simpa only [ae_iff, not_imp] using
      (ae_restrict_iff' measurableSet_Ioo).mp hPae
  let Nr : Set ℝ := (fun h : ℝ ↦ 2 * h) ⁻¹' Ng
  have hNr : volume Nr = 0 := by
    rw [Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0), hNg, mul_zero]
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hfR : ∀ p ∈ cellNeighbourhood,
      continuousRep q.phi (torusProj (p.2, -p.1)) =
        c * continuousRep q.phi (torusProj p) := by
    intro p _
    have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
    rw [hcc]
    exact q.continuousRep_rotLift hκ p
  obtain ⟨seq, hseq, hlim, hpair⟩ := pairing_limit q.transport
    closure_cellSquare_subset_cellNeighbourhood hc
    (fun _ hp ↦ rotLift_mem_cellNeighbourhood hp) hfR
    ((continuousRep q.phi).continuous.comp
      isOpenQuotientMap_torusProj.continuous).continuousOn
    (hN := measure_union_null hNv hNr)
  have hP (j : ℕ) : P (seq j) := by
    by_contra hj
    exact (hseq j).2.1 (Or.inl ⟨(hseq j).1, hj⟩)
  have hscaled : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 : ℝ)
  have hpos : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hscaled, Eventually.of_forall fun j ↦
      mul_pos two_pos (hseq j).1.1⟩
  have hwithin : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝[Ioi 0 \ Ng] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hscaled, Eventually.of_forall fun j ↦
      ⟨mul_pos two_pos (hseq j).1.1, fun hj ↦ (hseq j).2.1 (Or.inr hj)⟩⟩
  have hpair' : Tendsto (fun j ↦ levelIntegral (seq j) (fun p ↦
      (liftL2 q.nu p * (starRingEnd ℂ) (continuousRep q.phi (torusProj p))).re)) atTop
      (𝓝 (∑ k : Fin 4, ∫ t,
        (canonicalProfile lam (ddArcTrace q.phi k) t *
          (starRingEnd ℂ) (ddArcTrace q.phi k t)).re)) := by
    convert hpair using 1
    simp only [← Fin.sum_univ_eq_sum_range]
    rfl
  have hn := hN.comp hwithin
  have ht := hT.comp hwithin
  have hm := hM.comp hwithin
  simp only [Function.comp_def, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    at hn ht hm
  have hv := (dd_value_finite_part q.regular).2.comp hpos
  have hfactor : Tendsto (fun j ↦ (8 - (2 * seq j) ^ 3) / 3) atTop (𝓝 (8 / 3 : ℝ)) := by
    simpa using (hscaled.pow 3).const_sub 8 |>.div_const 3
  -- The coefficient error against the logarithmic counterterm is ε³ log(1/ε)/3.
  have hlog : Tendsto (fun ε : ℝ ↦ ε ^ 3 * Real.log (1 / ε))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 3) (by norm_num)).neg
    simpa only [one_div, Real.log_inv, Real.rpow_ofNat, neg_mul, mul_neg, mul_comm,
      neg_zero] using h
  have herr := ((hlog.comp hpos).const_mul (ddCornerMass q.phi)).div_const 3
  have hlimB := (hfactor.mul (((hn.sub ht).sub hv).sub hpair')).sub
    ((hscaled.pow 2).mul hm) |>.add herr
  have htarget : Tendsto
      (fun j ↦ ddRawBulk q.phi q.nu dx dy (2 * seq j) +
        ddLogCounterterm q.phi (2 * seq j)) atTop
      (𝓝 (-(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
          ddValueFinitePart q.phi))) := by
    convert hlimB using 1
    · funext j
      dsimp only [Function.comp_def]
      dsimp only [P] at hP
      rw [hP j]
      unfold ddLogCounterterm
      ring
    · simp only [canonicalArcForm, Finset.sum_add_distrib, zero_sub,
        mul_zero, sub_zero, zero_div, add_zero]
      ring
  have hident := tendsto_nhds_unique (hbulk.comp hpos) htarget
  exact hident ▸ hbulk

/-- The boundary comparison function is positive on the geometric range of `r`. -/
theorem ddBoundaryGround_pos {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    0 < ddBoundaryGround r := by
  have hl : Real.log (r / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hmul : r ^ 2 / 256 * Real.log (r / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hl
  unfold ddBoundaryGround
  linarith

/-- Explicit derivative of the one-dimensional boundary comparison function. -/
theorem hasDerivAt_ddBoundaryGround {r : ℝ} (hr : 0 < r) :
    HasDerivAt ddBoundaryGround
      (1 / 16 - r / 128 * Real.log (r / 2) - r / 256) r := by
  have hlog := ((hasDerivAt_id r).div_const 2).log (by positivity : r / 2 ≠ 0)
  have h := ((hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).div_const 16)).sub
    ((((hasDerivAt_id r).pow 2).div_const 256).mul hlog)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    field_simp [hr.ne']
    ring

/-- The expanded coefficient agrees with the derivative formula for the boundary current. -/
theorem ddBoundaryB_eq {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ddBoundaryB r = 1 - 4 * (r / 8 + (4 - 3 * r) * deriv ddBoundaryGround r) /
      ddBoundaryGround r := by
  rw [(hasDerivAt_ddBoundaryGround hr).deriv]
  dsimp only [ddBoundaryB]
  field_simp [(ddBoundaryGround_pos hr hr2).ne']
  unfold ddBoundaryGround
  ring

end NoEmbeddedEigenvalues
