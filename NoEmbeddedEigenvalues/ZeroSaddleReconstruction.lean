import NoEmbeddedEigenvalues.QuarterFirstMass
import NoEmbeddedEigenvalues.ZeroSaddleQuotientMass

/-!
# Zero-saddle base-quarter reconstruction

Blueprint: `lem:transport-endpoint-decay`, `lem:zero-saddle-quarter-mass`.

Integrate the canonical ACL transport unknown from the nearer time endpoint.
Both endpoint norms are the scalar quotient norm, and the forcing tail decays
as exp(-|t|/2). The resulting estimate is transferred a.e. to the original
spatial unknown before applying the weighted moving-strip mass criterion.
No raw endpoint values of the spatial unknown are used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

private theorem norm_transport_le_endpoint {lam a b : ℝ} {W F : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval W a b) (hF : IntervalIntegrable F volume a b)
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t) :
    ‖W b‖ ≤ ‖W a‖ +
      ‖∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ))‖ := by
  have hi := transport_integratingFactor hac hF (hd.mono fun _ ht _ ↦ ht)
  have hint : (∫ s in a..b, Complex.exp (-(Complex.I * (lam : ℂ) * (s : ℂ))) * F s) =
      ∫ s in a..b, F s * Complex.exp (-Complex.I * ((lam * s : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show -(Complex.I * (lam : ℂ) * (s : ℂ)) =
      -Complex.I * ((lam * s : ℝ) : ℂ) by push_cast; ring, mul_comm]
  rw [hint] at hi
  calc ‖W b‖ = ‖Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b‖ := by
        rw [norm_mul, norm_exp_neg_I_mul, one_mul]
       _ = ‖(Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b -
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a) +
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ := by
        rw [sub_add_cancel]
       _ ≤ ‖Complex.exp (-(Complex.I * (lam : ℂ) * (b : ℂ))) * W b -
          Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ +
          ‖Complex.exp (-(Complex.I * (lam : ℂ) * (a : ℂ))) * W a‖ := norm_add_le _ _
       _ = _ := by
        rw [hi, norm_mul, Complex.norm_I, one_mul, norm_mul, norm_exp_neg_I_mul, one_mul]
        ring

/-- Integrating from the nearer endpoint preserves exponential forcing decay,
for either sign of the real transport frequency. The endpoints belong to the
specified ACL representative, not to raw a.e. spatial data. -/
theorem norm_transport_le_endpoints_of_decay {lam L C A : ℝ} {W F : ℝ → ℂ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hF : ContinuousOn F (Icc (-L) L))
    (hdecay : ∀ t, |t| ≤ L → ‖F t‖ ≤ C * exp (-|t| / 2))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval W a b)
    (hd : ∀ᵐ t, HasDerivAt W (Complex.I * ((lam : ℂ) * W t + F t)) t)
    (hleft : ‖W (-L)‖ ≤ A) (hright : ‖W L‖ ≤ A) :
    ∀ t, |t| ≤ L → ‖W t‖ ≤ A + 2 * C * exp (-|t| / 2) := by
  obtain ⟨hneg, hpos⟩ := forcing_decay_tail_bounds hL hC hF hdecay lam
  intro t ht
  have htI := abs_le.1 ht
  rcases le_total t 0 with ht0 | ht0
  · have hiF : IntervalIntegrable F volume (-L) t :=
      (hF.mono (Icc_subset_Icc le_rfl htI.2)).intervalIntegrable_of_Icc htI.1
    have hn := norm_transport_le_endpoint (hac (-L) t) hiF hd
    have hb := hn.trans (add_le_add hleft (hneg t ⟨htI.1, ht0⟩).2)
    simpa only [abs_of_nonpos ht0, neg_neg] using hb
  · have hiF : IntervalIntegrable F volume L t :=
      ((hF.mono (Icc_subset_Icc htI.1 le_rfl)).intervalIntegrable_of_Icc htI.2).symm
    have hn := norm_transport_le_endpoint (hac L t) hiF hd
    rw [intervalIntegral.integral_symm, norm_neg] at hn
    have hb := hn.trans (add_le_add hright (hpos t ⟨ht0, htI.2⟩).2)
    simpa only [abs_of_nonneg ht0] using hb

/-- A zero-saddle character component has the first weighted mass gain on the
base quarter of a sufficiently small separatrix collar, with its original
spatial unknown and supplied continuous forcing representative. -/
theorem IsTransportPair.zero_saddle_quarter_memLp
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g)
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0)
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧ η < 1 / 2 ∧
      MemLp (fun q : ℝ × ℝ ↦ v (dipoleOrbit q.1 q.2) /
        (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
        (volume.restrict (quarterOrbitStrip η)) := by
  obtain ⟨rQ, hrQ, hrQr, hrQh, _, hQ, hne⟩ :=
    hp.zero_saddle_quarterQuotient_memLp hκ hcell hg hfg hz hr hvκ hfκ
  obtain ⟨C, rF, hC, hrF, _, hdecay, _⟩ :=
    hp.zero_saddle_forcing_decay hcell hg hfg hz
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
  let B := (2 * |lam| + 1) * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hV : MemLp (fun q : ℝ × ℝ ↦ v (dipoleOrbit q.1 q.2)) 2
      (volume.restrict (quarterOrbitStrip b)) :=
    memLp_comp_quarterOrbitStrip_of_memLp hb1.le
      (hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
  refine ⟨b, hb, hbr, hbh, ?_⟩
  apply memLp_quarter_div_saddleDist_of_exp_bound hb hb1 hc (abs_nonneg lam) hB
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
  have hZbound := norm_transport_le_endpoints_of_decay
    (eighthPeriod_pos hh.1 hh1).le hC.le hgc.continuousOn
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
       _ ≤ |lam| * (‖quarterQuotient lam κ g h‖ + 2 * C * exp (-|t| / 2)) +
          C * exp (-|t| / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hZbound t ht) (abs_nonneg lam))
          (hdecay h ⟨hh.1, hh.2.trans hbF⟩ t ht)
       _ = |lam| * ‖quarterQuotient lam κ g h‖ + B * exp (-|t| / 2) := by
        dsimp only [B]
        ring

end NoEmbeddedEigenvalues
