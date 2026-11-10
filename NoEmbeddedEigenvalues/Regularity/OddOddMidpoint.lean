import NoEmbeddedEigenvalues.Regularity.OddOddLogarithmic
import NoEmbeddedEigenvalues.LogarithmicMidpoint
import NoEmbeddedEigenvalues.QuarterReconstruction
import NoEmbeddedEigenvalues.WeakQuarterReconstruction

/-!
# Logarithmic phase division and the odd–odd midpoint coefficient

All data use the same continuous stream and canonical jet. The numerator data
remain available on their original interval; the phase quotient and midpoint
coefficient are constructed on a smaller complete-cell interval and identified
with orbitwise ACL midpoint values. Weak differentiation of the joint reconstruction
identifies the square-integrable level derivative of the actual transport-unknown
pullback on the recentered quarter strip.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Compatible logarithmically weighted phase quotient and midpoint coefficient
(`lem:dd-log-midpoint`). The original numerator data are retained for reconstruction. -/
theorem dd_log_midpoint {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧
      ∃ d : WeightedQuarterNumeratorData lam cellNeighbourhood (contStream ω) (streamJet2 ω) h₀,
        IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 (3 / 2) (streamJet2 ω) h)
          (Ioo 0 h₀) ∧
        ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam (paritySign κ) h₁ ∧
          ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
            (∀ h ∈ Ioo 0 h₁, quarterDivisor lam (paritySign κ) h * Q h =
              quarterNumerator lam (contStream ω) h) ∧
            MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q h / (h : ℂ)) 2
              (volume.restrict (Ioo 0 h₁)) ∧
            MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * Q₁ h) 2
              (volume.restrict (Ioo 0 h₁)) ∧
            HasIntervalH1Loc 0 h₁ (quarterMidpoint lam Q (contStream ω))
              (quarterMidpointDerivative lam Q Q₁ d.halfFirst) ∧
            MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) *
              quarterMidpointDerivative lam Q Q₁ d.halfFirst h) 2
              (volume.restrict (Ioo 0 h₁)) ∧
            HasWeakPartialOn (quarterOrbitStrip h₁) 0
              (fun q ↦ transportUnknown lam (liftL2 ω) (contStream ω) (dipoleOrbit q.1 q.2))
              (quarterReconstructionLevel lam (quarterMidpointDerivative lam Q Q₁ d.halfFirst)
                (quarterForcingLevelDerivative (streamJet2 ω))) ∧
            MemLp (quarterReconstructionLevel lam
              (quarterMidpointDerivative lam Q Q₁ d.halfFirst) (quarterForcingLevelDerivative
                (streamJet2 ω))) 2 (volume.restrict (quarterOrbitStrip h₁)) ∧
            ∀ᵐ h ∂(volume.restrict (Ioo 0 h₁)), ∃ Z : ℝ → ℂ,
              (∀ᵐ t, Z t = transportUnknown lam (liftL2 ω) (contStream ω) (dipoleOrbit h t)) ∧
              (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
              (∀ᵐ t, HasDerivAt Z
                (Complex.I * ((lam : ℂ) * Z t + contStream ω (dipoleOrbit h t))) t) ∧
              Z 0 = quarterMidpoint lam Q (contStream ω) h ∧
              ∀ t, Z t = Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ)) *
                  quarterMidpoint lam Q (contStream ω) h +
                Complex.I * ∫ u in 0..t,
                  Complex.exp (Complex.I * ((lam * (t - u) : ℝ) : ℂ)) *
                    contStream ω (dipoleOrbit h u) := by
  obtain ⟨h₀, hh₀, hh₀half, d, hK, hN₁, hB₁, hN₂⟩ := dd_log_numerators hlam hω hs hκ
  have hh₀1 : h₀ < 1 := by linarith
  have hp := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hA : orbitAnnulus 0 h₀ ⊆ cellNeighbourhood := fun _ hx ↦
    closure_cellSquare_subset_cellNeighbourhood (subset_closure hx.1.1)
  have hvκ : HasQuarterCharacterOn (paritySign κ) (orbitAnnulus 0 h₀) (liftL2 ω) :=
    ae_restrict_of_ae (liftL2_rotLift_ae hκ)
  have hfκ : HasQuarterCharacterOn (paritySign κ) (orbitAnnulus 0 h₀) (contStream ω) :=
    Filter.Eventually.of_forall (contStream_rotLift hκ)
  have hκ4 : paritySign κ ^ 4 = 1 := by cases κ <;> norm_num [paritySign]
  have hz := (numerator_zeros hκ4 hp hh₀ hh₀1 hA
    (continuous_contStream ω).continuousOn (Filter.Eventually.of_forall fun _ ↦ rfl) hvκ hfκ).2
  obtain ⟨c, C, η, hc, _, hη, _, hperiod⟩ := eighthPeriod_derivative_bounds
  obtain ⟨ρ, hρ, _, hneρ⟩ := exists_ae_quarterDivisor_ne_zero hlam hκ4 hh₀
  let δ := min h₀ (min η ρ)
  have hδ : 0 < δ := lt_min hh₀ (lt_min hη hρ)
  have hδ₀ : δ ≤ h₀ := min_le_left _ _
  have hδ1 : δ < 1 := hδ₀.trans_lt hh₀1
  have hsubδ : Ioo 0 δ ⊆ Ioo 0 h₀ := fun _ hx ↦ ⟨hx.1, hx.2.trans_le hδ₀⟩
  have hNloc : HasIntervalH2Loc 0 δ (quarterNumerator lam (contStream ω)) d.first d.second :=
    fun a b ha hab hb ↦ d.numerator_h2 a b ha hab (hb.trans_le hδ₀)
  have hzδ : ∀ h ∈ Ioo 0 δ, quarterDivisor lam (paritySign κ) h = 0 →
      quarterNumerator lam (contStream ω) h = 0 := fun h hh ↦ hz h (hsubδ hh)
  obtain ⟨h₁, hh₁, hh₁δ, hend, Q, Q₁, hQ, hdiv, hQw, hQ₁w, _⟩ :=
    log_phase_cell_division hlam hκ4 hδ hδ1 hNloc hzδ
      (hN₁.mono_measure (Measure.restrict_mono hsubδ le_rfl))
      (hN₂.mono_measure (Measure.restrict_mono hsubδ le_rfl))
  have hh₁₀ : h₁ < h₀ := hh₁δ.trans_le hδ₀
  have hh₁η : h₁ < η := hh₁δ.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hsub : Ioo 0 h₁ ⊆ Ioo 0 h₀ := fun _ hx ↦ ⟨hx.1, hx.2.trans hh₁₀⟩
  have hBl : HasIntervalH1Loc 0 h₁ (quarterHalfNumerator lam (contStream ω)) d.halfFirst :=
    fun a b ha hab hb ↦ d.half_h1 a b ha hab (hb.trans hh₁₀)
  have hphase : ∀ h ∈ Ioo 0 h₁, |h * deriv eighthPeriod h| ≤ C := by
    intro h hh
    obtain ⟨hl, hu, _⟩ := hperiod h ⟨hh.1, hh.2.trans hh₁η⟩
    rw [abs_of_nonpos (by linarith : h * deriv eighthPeriod h ≤ 0)]
    linarith
  obtain ⟨hAl, hAw⟩ := log_midpoint_gain (hh₁₀.trans hh₀1) hQ hBl hphase hQw hQ₁w
    (hB₁.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hh₁ρ : h₁ < ρ := hh₁δ.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsubρ : Ioo 0 h₁ ⊆ Ioo 0 ρ := fun _ hx ↦ ⟨hx.1, hx.2.trans hh₁ρ⟩
  have hne : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₁)), quarterDivisor lam (paritySign κ) h ≠ 0 :=
    hneρ.filter_mono (ae_mono (Measure.restrict_mono hsubρ le_rfl))
  have hA₁ : orbitAnnulus 0 h₁ ⊆ cellNeighbourhood := fun _ hx ↦
    closure_cellSquare_subset_cellNeighbourhood (subset_closure hx.1.1)
  have hvκ₁ : HasQuarterCharacterOn (paritySign κ) (orbitAnnulus 0 h₁) (liftL2 ω) :=
    ae_restrict_of_ae (liftL2_rotLift_ae hκ)
  have hfκ₁ : HasQuarterCharacterOn (paritySign κ) (orbitAnnulus 0 h₁) (contStream ω) :=
    Filter.Eventually.of_forall (contStream_rotLift hκ)
  have hprof := quarter_midpoint_reconstruction hκ4 hp hh₁ (hh₁₀.trans hh₀1) hA₁
    (continuous_contStream ω) hvκ₁ hfκ₁ hdiv hne
  have hlevel := d.reconstruction_level_memLp hh₀half hh₁₀.le hAw
    (hK.mono_set hsub)
  have hsubS : quarterOrbitStrip h₁ ⊆ quarterOrbitStrip h₀ := fun q hq ↦
    ⟨hq.1, hq.2.1.trans hh₁₀, hq.2.2⟩
  have hweak := quarterReconstruction_weak_of_intervalH1Loc (hh₁₀.trans hh₀1).le hAl
    (d.forcing_level_weak.mono hsubS) lam
  have hRaw : AEStronglyMeasurable (fun q : ℝ × ℝ ↦
      transportUnknown lam (liftL2 ω) (contStream ω) (dipoleOrbit q.1 q.2))
      (volume.restrict (quarterOrbitStrip h₁)) := by
    have hv : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    have hf := (continuous_contStream ω).measurable
    have hm : Measurable (transportUnknown lam (liftL2 ω) (contStream ω)) := by
      unfold transportUnknown
      fun_prop
    exact (hm.comp continuous_dipoleOrbit.measurable).aestronglyMeasurable
  have heq := ae_eq_quarterStrip_of_ae_sections hweak.1.aestronglyMeasurable hRaw (by
    filter_upwards [hprof] with h hh
    obtain ⟨Z, hzeq, _, _, _, hrec⟩ := hh
    filter_upwards [ae_restrict_of_ae hzeq] with t ht
    rw [quarterReconstruction_eq]
    exact (hrec t).symm.trans ht)
  have hweakRaw := hweak.congr_ae_on (measurableSet_quarterOrbitStrip h₁)
    ((ae_restrict_iff' (measurableSet_quarterOrbitStrip h₁)).1 heq)
    (Filter.Eventually.of_forall fun _ _ ↦ rfl)
  exact ⟨h₀, hh₀, hh₀half, d, hK, h₁, hh₁, hh₁₀, hend, Q, Q₁, hQ, hdiv, hQw,
    hQ₁w, hAl, hAw, hweakRaw, hlevel, hprof⟩

end NoEmbeddedEigenvalues
