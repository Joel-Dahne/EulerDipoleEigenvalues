import NoEmbeddedEigenvalues.OddOddPicone
import NoEmbeddedEigenvalues.OddOddCoercivity
import NoEmbeddedEigenvalues.OddOddBoundaryTrace

/-!
# Odd–odd exclusion and renormalized current assembly

The analytic forms and boundary data are defined in `OddOddForms`.
The weighted virial inputs are in `OddOddVirial`.
-/

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

/-- The error in replacing the actual current coefficient by `-(8/3)(1-B)` integrates
    to zero: the uniform `O(ε)` coefficient error times the logarithmic period vanishes. -/
theorem dd_current_remainder_limit {φ : L2} (hφ : MemSobolev 2 φ) :
    Tendsto (fun ε ↦ ddGroundCurrent φ ε + (8 / 3 : ℝ) * ddLevelMass φ ε -
      (8 / 3 : ℝ) * ddLevelBMass φ ε) (𝓝[>] 0) (𝓝 0) := by
  sorry

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

/-- Integrable functions converge under exhaustion by the actual stream levels. This is
    dominated convergence and does not assume any sign of the integrand. -/
theorem tendsto_ddTruncatedCell_integral {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f cellSquare) :
    Tendsto (fun ε ↦ ∫ p in ddTruncatedCell ε, f p) (𝓝[>] 0)
      (𝓝 (∫ p in cellSquare, f p)) := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hm (ε : ℝ) : MeasurableSet {p : ℝ × ℝ | ε < dipoleLift p} :=
    measurableSet_lt measurable_const (by unfold dipoleLift; fun_prop)
  have hrep (ε : ℝ) : (∫ p in ddTruncatedCell ε, f p) =
      ∫ p in cellSquare, {p | ε < dipoleLift p}.indicator f p := by
    rw [setIntegral_indicator (hm ε)]
    rfl
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict cellSquare)
    (F := fun ε ↦ {p | ε < dipoleLift p}.indicator f) (f := f) (fun p ↦ ‖f p‖)
    (Eventually.of_forall fun ε ↦ hf.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ {p | ε < dipoleLift p}
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp, norm_zero]
        exact norm_nonneg _)
    hf.norm (by
      filter_upwards [ae_restrict_mem hcell] with p hp
      have hs : 0 < dipoleLift p := by
        simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < dipoleLift p :=
        nhdsWithin_le_nhds (Iio_mem_nhds hs)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with ε hε
      rw [indicator_of_mem (show p ∈ {p | ε < dipoleLift p} from hε)])
  exact h.congr' (Eventually.of_forall fun ε ↦ (hrep ε).symm)

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

/-- Ordinary-integral Picone identity after cancellation of the corner finite parts. -/
theorem dd_picone_current {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω)
    (b : DDBoundaryData lam κ q.phi) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    IntegrableOn (ddVorticityDensity q.nu) cellSquare ∧
      IntegrableOn (ddPiconeGradient q.phi dx dy) cellSquare ∧
      IntegrableOn (ddPiconePotential q.phi) cellSquare ∧
      (∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
        (∫ p in cellSquare, ddPiconePotential q.phi p) =
      -(8 / 3 : ℝ) * ∑ k : Fin 4,
        correctedBoundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  have hv := dd_vorticityDensity_integrable q.nu q.weighted_nu
  obtain ⟨_, hg⟩ := dd_gradient_energies_integrable q.regular q.even hdx hdy
  have hp := dd_piconePotential_integrable q.regular
  refine ⟨hv, hg, hp, ?_⟩
  have hBulk : Tendsto (ddPiconeBulk q.phi q.nu dx dy) (𝓝[>] 0)
      (𝓝 ((∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
          ∫ p in cellSquare, ddPiconePotential q.phi p)) :=
    ((tendsto_ddTruncatedCell_integral hv).add
      (tendsto_ddTruncatedCell_integral hg)).add (tendsto_ddTruncatedCell_integral hp)
  have h := (dd_character_virial_limit hlam hω hs q hκ hdx hdy).sub
    (dd_ground_current_limit q.regular)
  have hLevel := h.congr' (f₂ := ddPiconeBulk q.phi q.nu dx dy) (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with ε hε
    obtain ⟨hr, _, _, _, ht⟩ := dd_truncated_picone q.regular hdx hdy hε
    have hvε := hv.mono_set (show ddTruncatedCell ε ⊆ cellSquare from fun _ hp ↦ hp.1)
    dsimp only [ddRawBulk, ddPiconeBulk]
    rw [integral_add hvε hr, ht]
    ring)
  have hforms : (∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
      (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t) =
      ∑ k : Fin 4, correctedBoundaryForm lam
        (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ q.correctedBoundaryForm_eq hlam hκ b k
  calc
    _ = -(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) + ddValueFinitePart q.phi) -
        (-(8 / 3 : ℝ) * (ddValueFinitePart q.phi -
          ∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := tendsto_nhds_unique hBulk hLevel
    _ = -(8 / 3 : ℝ) * ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
        (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := by ring
    _ = _ := by rw [hforms]

/-- Bulk coercivity on the finite-energy domain. Integrability is a hypothesis, so the
    default value of a divergent Bochner integral cannot masquerade as an energy. -/
theorem dd_bulk_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    (hc : centralInversion φ = φ)
    (hmean : (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 φ p) = 0)
    (hgrad : IntegrableOn (ddPiconeGradient φ dx dy) cellSquare)
    (hpot : IntegrableOn (ddPiconePotential φ) cellSquare) :
    (25 / 54 : ℝ) * (∫ p in cellSquare, ddMassDensity φ p) ≤
      (∫ p in cellSquare, ddPiconeGradient φ dx dy p) +
        ∫ p in cellSquare, ddPiconePotential φ p := by
  have hg := dd_bulk_gradient_bound hφ hdx hdy hc hmean hgrad
  have hp := dd_bulk_potential_bound φ hpot
  linarith

/-- Nonnegativity of the retained vorticity term. -/
theorem ddVorticityDensity_nonneg {p : ℝ × ℝ} (hp : p ∈ cellSquare) (ν : L2) :
    0 ≤ ddVorticityDensity ν p := by
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hle : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
  have hcube : dipoleLift p ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le hle 3
  have h8 : 0 ≤ 8 - dipoleLift p ^ 3 := by linarith
  unfold ddVorticityDensity ddF
  positivity

/-- Zero weighted mass gives zero quotient in the even sector. -/
theorem dd_eq_zero_of_mass_eq_zero {φ : L2} (hs : InSector true true φ)
    (hmass : (∫ p in cellSquare, ddMassDensity φ p) = 0) : φ = 0 := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hn : 0 ≤ᵐ[volume.restrict cellSquare] ddMassDensity φ :=
    Eventually.of_forall fun p ↦ by unfold ddMassDensity ddWeight; positivity
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (integrableOn_ddMassDensity φ)).1 hmass
  apply hs.eq_zero_of_lift_ae_zero_on_cellSquare
  filter_upwards [hz, ae_restrict_mem hcell] with p hp hpc
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hpc
  change dipoleLift p ^ 2 * ‖liftL2 φ p‖ ^ 2 = 0 at hp
  have hsq : ‖liftL2 φ p‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hpos.ne')
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (liftL2 φ p)])

/-- Recovering the vorticity from a vanishing quotient uses only the Poisson relation. -/
theorem DDQuotientData.vorticity_eq_zero {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hm : MeanZero ω) (hz : q.phi = 0) : ω = 0 := by
  have hφ := Lp.eq_zero_iff_ae_eq_zero.mp hz
  have hψ : invLap ω = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [q.stream_eq, hφ] with t ht hzt
    simp only [Pi.zero_apply] at hzt ⊢
    rw [ht, hzt, mul_zero]
  apply fourierCoeff_ext
  intro k
  simpa only [hψ, fourierCoeff_zero_fun, mul_zero] using hasFourierLaplacian_invLap ω hm k

/-- Final contradiction in one rotation character, conditional on the analytic interfaces. -/
theorem odd_odd_character_exclusion {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) : ω = 0 := by
  obtain ⟨q⟩ := dd_exclusion_domain hlam hω hs
  obtain ⟨hmean, hc⟩ := dd_orthogonality hlam hω hs q
  obtain ⟨b⟩ := dd_boundary_regularity hlam q hκ
  have h1 : MemSobolev 1 q.phi := q.regular.mono (by norm_num)
  obtain ⟨dx, hdx⟩ := h1.exists_hasFourierPartial 0
  obtain ⟨dy, hdy⟩ := h1.exists_hasFourierPartial 1
  obtain ⟨hv, hg, hp, hid⟩ := dd_picone_current hlam hω hs q hκ b hdx hdy
  have hbulk := dd_bulk_picone q.regular hdx hdy hc hmean hg hp
  have hsum : 0 ≤ ∑ k : Fin 4, correctedBoundaryForm lam
      (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) :=
    Finset.sum_nonneg fun k _ ↦
      (correctedBoundaryForm_nonneg hlam (b.regular k) (b.endpoints k)).2
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hν : 0 ≤ ∫ p in cellSquare, ddVorticityDensity q.nu p :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem hcell fun p hp ↦
      ddVorticityDensity_nonneg hp q.nu)
  have hmass : (∫ p in cellSquare, ddMassDensity q.phi p) = 0 := by
    have hn : 0 ≤ ∫ p in cellSquare, ddMassDensity q.phi p :=
      integral_nonneg fun p ↦ by unfold ddMassDensity ddWeight; positivity
    nlinarith
  exact q.vorticity_eq_zero hω.1 (dd_eq_zero_of_mass_eq_zero q.even hmass)

/-- An eigenfunction odd under both separatrix reflections vanishes
    at every nonzero real spectral parameter. -/
theorem odd_odd_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false false ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, odd_odd_character_exclusion hlam hep hsp hkp,
    odd_odd_character_exclusion hlam hem hsm hkm, add_zero]

end NoEmbeddedEigenvalues
