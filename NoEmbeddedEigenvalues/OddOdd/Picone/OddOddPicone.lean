import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddPiconeCutoff

/-!
# Picone on every positive stream truncation

Blueprint: `lem:dd-truncated-picone`.

The value current is continuous on regular levels. Choose good annular endpoints
approaching a prescribed lower level from above and the center from below.
Bulk dominated convergence and the full center-current limit recover the identity
at every positive level, without exceptional boundary gradient values.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- The value-only current is continuous at every regular stream level. -/
theorem continuousAt_ddGroundCurrent_level (φ : L2) {h₀ : ℝ}
    (hh₀ : h₀ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun h ↦ ddGroundCurrent φ (2 * h)) h₀ := by
  let c := fun h : ℝ ↦ max (h₀ / 2) (min ((h₀ + 1) / 2) h)
  have hc : Continuous c := by fun_prop
  have hcI (h : ℝ) : c h ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact (show 0 < h₀ / 2 by linarith [hh₀.1]).trans_le (le_max_left _ _)
    · apply (max_le (by linarith [hh₀.2]) (min_le_left _ _)).trans_lt
      linarith [hh₀.2]
  have hcnear : ∀ᶠ h in 𝓝 h₀, c h = h := by
    filter_upwards [Ioo_mem_nhds (show h₀ / 2 < h₀ by linarith [hh₀.1])
      (show h₀ < (h₀ + 1) / 2 by linarith [hh₀.2])] with h hh
    simp only [c, min_eq_right hh.2.le, max_eq_right hh.1.le]
  have hT : Continuous (fun h ↦ orbitPeriod (c h)) :=
    continuousOn_orbitPeriod.comp_continuous hc hcI
  let B := fun p ↦ ddGroundCurrentCoeff p * ‖continuousRep φ (torusProj p)‖ ^ 2
  have ho : Continuous (fun q : ℝ × ℝ ↦ dipoleOrbit (c q.1) q.2) :=
    continuous_dipoleOrbit.comp (f := fun q : ℝ × ℝ ↦ (c q.1, q.2))
      ((hc.comp continuous_fst).prodMk continuous_snd)
  have hF : Continuous (fun q : ℝ × ℝ ↦ B (dipoleOrbit (c q.1) q.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hs := dipoleLift_dipoleOrbit (hcI q.1).1 (hcI q.1).2 q.2
    have hs0 : 0 < dipoleLift (dipoleOrbit (c q.1) q.2) := by rw [hs]; linarith [(hcI q.1).1]
    have hs2 : dipoleLift (dipoleOrbit (c q.1) q.2) < 2 := by rw [hs]; linarith [(hcI q.1).2]
    exact ((continuousAt_ddGroundCurrentCoeff hs0.ne'
      (gradSq_dipoleLift_pos hs0 hs2).ne').mul
        (((continuousRep φ).continuous.comp
          isOpenQuotientMap_torusProj.continuous).continuousAt.norm.pow 2)).comp
          (f := fun r : ℝ × ℝ ↦ dipoleOrbit (c r.1) r.2) ho.continuousAt
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun h t ↦ B (dipoleOrbit (c h) t)) (a₀ := 0) (μ := volume) hF hT
  apply hcont.continuousAt.congr
  filter_upwards [hcnear] with h hh
  rw [hh]
  simp only [ddGroundCurrent, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

/-- Sobolev Picone on every positive truncation, with bulk and current integrability.
    The center is included; its removal and limiting argument belong to this input. -/
theorem dd_truncated_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconePotential φ) (ddTruncatedCell ε) ∧
      IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
        ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
        volume 0 (orbitPeriod (ε / 2)) ∧
      (∫ p in ddTruncatedCell ε, ddRawEnergy φ dx dy p) =
        (∫ p in ddTruncatedCell ε, ddPiconeGradient φ dx dy p) +
          (∫ p in ddTruncatedCell ε, ddPiconePotential φ p) + ddGroundCurrent φ ε := by
  obtain ⟨hr, hg, hp, hc⟩ := dd_truncated_picone_integrability hφ dx dy hε
  refine ⟨hr, hg, hp, hc, ?_⟩
  let J := fun p ↦ ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p
  let A := ddTruncatedCell ε
  have hi : IntegrableOn J A := (hr.sub hg).sub hp
  obtain ⟨N, hN, hann⟩ := ddPicone_annular hφ hdx hdy
  have hDense : Dense Nᶜ := MeasureTheory.Measure.dense_of_ae (measure_eq_zero_iff_ae_notMem.mp hN)
  let h : ℝ := ε / 2
  let b : ℝ := (h + 1) / 2
  have hh : h ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [h]; linarith [hε.1],
    by dsimp [h]; linarith [hε.2]⟩
  have hhb : h < b := by dsimp [b]; linarith [hh.2]
  have hb1 : b < 1 := by dsimp [b]; linarith [hh.2]
  have h2h : 2 * h = ε := by dsimp [h]; ring
  obtain ⟨lo, _, hlo, htlo⟩ := hDense.exists_seq_strictAnti_tendsto_of_lt hhb
  obtain ⟨up, _, hup, htup⟩ := hDense.exists_seq_strictMono_tendsto_of_lt hb1
  let S (n : ℕ) : Set (ℝ × ℝ) := {p | 2 * lo n < dipoleLift p ∧ dipoleLift p < 2 * up n}
  have hm (n : ℕ) : MeasurableSet (S n) := by
    have hms : Measurable dipoleLift := by unfold dipoleLift; fun_prop
    exact (measurableSet_lt measurable_const hms).inter (measurableSet_lt hms measurable_const)
  have hset (n : ℕ) : {p | p ∈ cellSquare ∧
      2 * lo n < dipoleLift p ∧ dipoleLift p < 2 * up n} = S n ∩ A := by
    ext p
    constructor
    · intro hp
      refine ⟨hp.2, hp.1, ?_⟩
      linarith [(hlo n).1.1, hp.2.1]
    · rintro ⟨hs, hp⟩
      exact ⟨hp.1, hs⟩
  have hind (n : ℕ) : (∫ p in {p | p ∈ cellSquare ∧
      2 * lo n < dipoleLift p ∧ dipoleLift p < 2 * up n}, J p) =
      ∫ p in A, (S n).indicator J p := by
    rw [integral_indicator (hm n), Measure.restrict_restrict (hm n), hset]
  have hlt2 : ∀ᵐ p : ℝ × ℝ, dipoleLift p < 2 := by
    filter_upwards [ae_cos_fst_ne_cos_snd] with p hp
    by_contra hge
    apply hp
    unfold dipoleLift at hge
    linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
  have htbulk : Tendsto (fun n ↦ ∫ p in {p | p ∈ cellSquare ∧
      2 * lo n < dipoleLift p ∧ dipoleLift p < 2 * up n}, J p)
      atTop (𝓝 (∫ p in A, J p)) := by
    simp_rw [hind]
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖J p‖)
    · exact fun n ↦ hi.aestronglyMeasurable.indicator (hm n)
    · exact hi.norm
    · intro n
      filter_upwards with p
      by_cases hp : p ∈ S n <;> simp [hp]
    · filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell ε).measurableSet,
        ae_restrict_of_ae hlt2] with p hp hp2
      apply tendsto_const_nhds.congr'
      have hl : h < dipoleLift p / 2 := by linarith [hp.2]
      have hu : dipoleLift p / 2 < 1 := by linarith
      filter_upwards [htlo.eventually (gt_mem_nhds hl), htup.eventually (lt_mem_nhds hu)]
        with n hnlo hnup
      exact (indicator_of_mem (show p ∈ S n from ⟨by linarith, by linarith⟩) J).symm
  have htloI : Tendsto (fun n ↦ ddGroundCurrent φ (2 * lo n)) atTop
      (𝓝 (ddGroundCurrent φ ε)) := by
    have ht := (continuousAt_ddGroundCurrent_level φ hh).tendsto.comp htlo
    rw [h2h] at ht
    exact ht
  have htup2 : Tendsto (fun n ↦ 2 * up n) atTop (𝓝[<] (2 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · simpa using htup.const_mul 2
    · change 2 * up n < 2
      linarith [(hup n).1.2]
  have htupI := (tendsto_ddGroundCurrent_center φ).comp htup2
  have htrhs := htloI.sub htupI
  rw [sub_zero] at htrhs
  have hid (n : ℕ) : (∫ p in {p | p ∈ cellSquare ∧
      2 * lo n < dipoleLift p ∧ dipoleLift p < 2 * up n}, J p) =
      ddGroundCurrent φ (2 * lo n) - ddGroundCurrent φ (2 * up n) := by
    exact hann (lo n) (up n) (hh.1.trans (hlo n).1.1)
      ((hlo n).1.2.trans (hup n).1.1) (hup n).1.2 (hlo n).2 (hup n).2
  have heq : (∫ p in A, J p) = ddGroundCurrent φ ε :=
    tendsto_nhds_unique htbulk (htrhs.congr fun n ↦ (hid n).symm)
  change (∫ p in ddTruncatedCell ε,
    ddRawEnergy φ dx dy p - ddPiconeGradient φ dx dy p - ddPiconePotential φ p) = _ at heq
  have hsplt := integral_sub (hr.sub hg) hp
  simp only [Pi.sub_apply, integral_sub hr hg] at hsplt
  rw [hsplt] at heq
  linarith

end NoEmbeddedEigenvalues
