module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterSecondMass
public import NoEmbeddedEigenvalues.Transport.WeightedGains.SubcriticalQuotientMass
public import NoEmbeddedEigenvalues.Transport.WeightedGains.ExponentialTransportDecay

/-!
# Subcritical base-quarter reconstruction and second mass

Blueprint: `lem:subcritical-quarter-mass`.

The original forcing's corner growth gives exp(-(2-δ)|t|) decay. Integrate
the specified canonical ACL unknown from the nearer endpoint; both endpoint
norms are the original scalar quotient norm. Transfer a.e. to the original
raw spatial unknown before applying the second-mass profile criterion.
No jointly measurable choice of canonical orbit representatives is required.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

/-- The original transport pair, continuous forcing and supplied first weak
gradient give actual second saddle-distance mass on one base quarter. -/
theorem IsTransportPair.subcritical_quarter_memLp
    {lam δ : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hbU : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧ η < 1 / 2 ∧
      MemLp (fun q : ℝ × ℝ ↦ v (dipoleOrbit q.1 q.2) /
        ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip η)) := by
  obtain ⟨rQ, hrQ, hrQr, hrQh, _, hQ, hne⟩ :=
    hp.subcritical_quarterQuotient_memLp hκ hbU hcell hδ1 hg hfg hbound hD hw hr hvκ hfκ
  have hs : 0 < 2 - δ := by linarith
  obtain ⟨K, hK, hglobal⟩ := exists_cell_forcing_rpow_bound hbU hcell hg hs hbound
  obtain ⟨C, rF, hC, hrF, _, hdecay, _⟩ := forcing_rpow_orbit_bounds hs hK hglobal
  obtain ⟨c, _, rD, hc, hrD, hdist⟩ := saddleDist_dipoleOrbit
  let b := min rQ (min rF rD) / 2
  have hm : 0 < min rQ (min rF rD) := lt_min hrQ (lt_min hrF hrD)
  have hb : 0 < b := half_pos hm
  have hbmin : b < min rQ (min rF rD) := half_lt_self hm
  have hbQ : b < rQ := hbmin.trans_le (min_le_left _ _)
  have hbF : b < rF :=
    hbmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbD : b < rD :=
    hbmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbr : b < r := hbQ.trans hrQr
  have hbh : b < 1 / 2 := hbQ.trans hrQh
  have hb1 : b < 1 := hbh.trans (by norm_num)
  have hsubQ : Ioo (0 : ℝ) b ⊆ Ioo 0 rQ := Ioo_subset_Ioo le_rfl hbQ.le
  have hAr : orbitAnnulus 0 b ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans hbr⟩
  have hA : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  obtain ⟨Em, Ep, _, hprof⟩ := quarter_endpoint_formula hκ hp hb hb1 hA hg hfg
    (ae_restrict_of_ae_restrict_of_subset hAr hvκ)
    (ae_restrict_of_ae_restrict_of_subset hAr hfκ)
  have hfgOrb := ae_orbit_congr hb1.le (ae_restrict_of_ae_restrict_of_subset hA hfg)
  have hκnorm : ‖κ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hκ (by decide)
  let B := (|lam| / (2 - δ) + 1) * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hV : MemLp (fun q : ℝ × ℝ ↦ v (dipoleOrbit q.1 q.2)) 2
      (volume.restrict (quarterOrbitStrip b)) :=
    memLp_comp_quarterOrbitStrip_of_memLp hb1.le
      (hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
  refine ⟨b, hb, hbr, hbh, ?_⟩
  apply memLp_quarter_div_saddleDist_sq_of_exp_bound hb hb1 hc (abs_nonneg lam) hB hδ0 hδ1
    hV.aestronglyMeasurable (hQ.mono_measure (Measure.restrict_mono_set _ hsubQ))
    (fun h hh t ht ↦ (hdist h ⟨hh.1, hh.2.trans hbD⟩ t ht).1)
  filter_upwards [hprof, hfgOrb, ae_restrict_of_ae_restrict_of_subset hsubQ hne,
    ae_restrict_mem measurableSet_Ioo] with h hZ hfg_h hn hh
  obtain ⟨Z, hzeq, _, hac, hode, hEm, hEp, hchar, _, hnorm⟩ := hZ
  have hh1 : h < 1 := hh.2.trans hb1
  have hgc : Continuous (fun t ↦ g (dipoleOrbit h t)) := by
    apply hg.comp_continuous
      (continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt)
    intro t
    have hm : dipoleOrbit h t ∈ puncturedCell := by
      simpa only [actionAngleInv,
        div_mul_cancel₀ t (orbitPeriod_pos hh.1 hh1).ne'] using
        actionAngleInv_mem_puncturedCell hh.1 hh1 (t / orbitPeriod h)
    exact hA ⟨hm, (levelCoord_dipoleOrbit hh.1 hh1 t).symm ▸ hh⟩
  have hleft : ‖Z (-eighthPeriod h)‖ ≤ ‖quarterQuotient lam κ g h‖ := by
    rw [hEm, hnorm hn]
  have hright : ‖Z (eighthPeriod h)‖ ≤ ‖quarterQuotient lam κ g h‖ := by
    rw [hEp, hchar, norm_mul, hκnorm, one_mul, hnorm hn]
  have hZbound := norm_transport_le_endpoints_of_exp_decay
    (eighthPeriod_pos hh.1 hh1).le hC.le hs hgc.continuousOn
    (hdecay h ⟨hh.1, hh.2.trans hbF⟩) hac hode hleft hright
  filter_upwards [ae_restrict_of_ae hzeq, ae_restrict_of_ae hfg_h,
    ae_restrict_mem measurableSet_Ioo] with t hzt hfgt htI
  have ht : |t| ≤ eighthPeriod h := abs_le.2 ⟨htI.1.le, htI.2.le⟩
  have hv : v (dipoleOrbit h t) = -((lam : ℂ) * Z t + g (dipoleOrbit h t)) := by
    dsimp only [transportUnknown] at hzt
    rw [hfgt] at hzt
    have he := (eq_div_iff (Complex.ofReal_ne_zero.mpr hp.ne_zero)).1 hzt
    linear_combination he
  calc ‖v (dipoleOrbit h t)‖ ≤ |lam| * ‖Z t‖ + ‖g (dipoleOrbit h t)‖ := by
        rw [hv, norm_neg]
        convert norm_add_le ((lam : ℂ) * Z t) (g (dipoleOrbit h t)) using 1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
       _ ≤ |lam| * (‖quarterQuotient lam κ g h‖ + (C / (2 - δ)) * exp (-(2 - δ) * |t|)) +
          C * exp (-(2 - δ) * |t|) :=
        add_le_add (mul_le_mul_of_nonneg_left (hZbound t ht) (abs_nonneg lam))
          (hdecay h ⟨hh.1, hh.2.trans hbF⟩ t ht)
       _ = |lam| * ‖quarterQuotient lam κ g h‖ + B * exp (-(2 - δ) * |t|) := by
        dsimp only [B]
        ring

end NoEmbeddedEigenvalues
