module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.LogarithmicMidpoint
public import NoEmbeddedEigenvalues.Transport.WeightedGains.WeightedQuarterGradient
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1LocalToGlobal
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.PeriodDerivativeBounds
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeakQuarterReconstruction

/-!
# Ordinary midpoint data and distance-weighted reconstruction

Blueprint: `lem:ordinary-midpoint-gain`, `lem:quarter-reconstruction-raw-ae`,
`lem:quarter-weighted-level-bound`.

The midpoint is constructed from the original continuous half numerator and
an interval H¹ quotient. Its phase derivative costs Q/h, without a logarithmic
weight. Orbitwise ACL witnesses identify the single raw transport pullback;
no measurable selection of witnesses is used.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

private theorem restrict_h1 {a b c d : ℝ} {F G : ℝ → ℂ}
    (h : HasIntervalH1 a b F G) (hac : a ≤ c) (hdb : d ≤ b) :
    HasIntervalH1 c d F G := by
  have hs : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono_set _ hs),
    h.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hs),
    fun u v hu huv hv ↦ h.locally_absolutelyContinuous u v
      (hac.trans_lt hu) huv (hv.trans_le hdb),
    h.hasDerivAt_ae.mono fun x hx hxI ↦ hx (hs hxI)⟩

/-- Ordinary quotient and half-numerator data give actual global H¹ of the
same midpoint, with its specified derivative, on a smaller positive collar. -/
theorem ordinary_midpoint_h1 {lam r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {Q Q₁ B₁ : ℝ → ℂ} {g : ℝ × ℝ → ℂ}
    (hQ : HasIntervalH1 0 r Q Q₁)
    (hQh : MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 r)))
    (hB : HasIntervalH1 0 r (quarterHalfNumerator lam g) B₁) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧
      HasIntervalH1 0 b (quarterMidpoint lam Q g) (quarterMidpointDerivative lam Q Q₁ B₁) := by
  obtain ⟨c, C, s, hc, _, hs, _, hL⟩ := eighthPeriod_derivative_bounds
  let b := min r s / 2
  have hb : 0 < b := half_pos (lt_min hr hs)
  have hbr : b < r := by dsimp [b]; linarith [min_le_left r s]
  have hbs : b < s := by dsimp [b]; linarith [min_le_right r s]
  have hb1 : b < 1 := hbr.trans hr1
  have hQB := restrict_h1 hQ le_rfl hbr.le
  have hBB := restrict_h1 hB le_rfl hbr.le
  have hBloc : HasIntervalH1Loc 0 b (quarterHalfNumerator lam g) B₁ :=
    fun u v hu _ hv ↦ restrict_h1 hBB hu.le hv.le
  have hK (h : ℝ) (hh : h ∈ Ioo 0 b) : |h * deriv eighthPeriod h| ≤ C := by
    have hp := hL h ⟨hh.1, hh.2.trans hbs⟩
    have hn : h * deriv eighthPeriod h ≤ 0 := by nlinarith [hp.1]
    rw [abs_of_nonpos hn]
    nlinarith [hp.2.1]
  obtain ⟨hlocal, hderiv⟩ := midpoint_gain hb1 hQB hBloc hK
    (hQh.mono_measure (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hbr.le)))
    hBB.memLp_derivative
  refine ⟨b, hb, hbr, hasIntervalH1_of_local_derivative hb hderiv ?_⟩
  intro x hx
  let u := x / 2
  let v := (x + b) / 2
  have hu : 0 < u := half_pos hx.1
  have hux : u < x := by dsimp [u]; linarith [hx.1]
  have hxv : x < v := by dsimp [v]; linarith [hx.2]
  have hv : v < b := by dsimp [v]; linarith [hx.2]
  exact ⟨u, v, hu.le, hv.le, ⟨hux, hxv⟩, hlocal u v hu (hux.trans hxv) hv⟩

/-- The exact scalar midpoint reconstruction agrees jointly a.e. with the raw
transport unknown. All norms and measurability are for the actual raw fields. -/
theorem IsTransportPair.quarterReconstruction_ae {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 b) f)
    {Q A₁ : ℝ → ℂ} (hA : HasIntervalH1 0 b (quarterMidpoint lam Q g) A₁)
    (hdiv : ∀ h ∈ Ioo 0 b, quarterDivisor lam κ h * Q h = quarterNumerator lam g h)
    (hne : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), quarterDivisor lam κ h ≠ 0) :
    (quarterReconstruction lam (quarterMidpoint lam Q g)
      (fun q ↦ g (dipoleOrbit q.1 q.2))) =ᵐ[volume.restrict (quarterOrbitStrip b)]
      (fun q ↦ transportUnknown lam v f (dipoleOrbit q.1 q.2)) := by
  have hAnn : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  have hfgLp : MemLp g 2 (volume.restrict U) := hp.memSobolevOn.memLp.ae_eq hfg
  have hgp := memLp_comp_quarterOrbitStrip_of_memLp hb1.le
    (hfgLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
  have hphase : Measurable (fun q : ℝ × ℝ ↦
      Complex.exp (-Complex.I * ((lam * q.2 : ℝ) : ℂ))) := by fun_prop
  have hP := aestronglyMeasurable_quarterPrimitive
    (hgp.aestronglyMeasurable.mul hphase.aestronglyMeasurable)
  have hM := aestronglyMeasurable_level_quarterStrip hA.memLp_value.aestronglyMeasurable
  have hR : AEStronglyMeasurable
      (quarterReconstruction lam (quarterMidpoint lam Q g)
        (fun q ↦ g (dipoleOrbit q.1 q.2))) (volume.restrict (quarterOrbitStrip b)) := by
    unfold quarterReconstruction quarterDuhamel
    exact (hM.mul (by fun_prop)).add ((hP.mul (by fun_prop)).const_mul Complex.I)
  have hZ : MemLp (transportUnknown lam v f) 2 (volume.restrict U) := by
    convert ((hp.memLp.add hp.memSobolevOn.memLp).neg.const_mul (lam : ℂ)⁻¹) using 1
    funext p
    simp only [transportUnknown, div_eq_mul_inv, mul_comm, Pi.neg_apply, Pi.add_apply]
  have hZp := memLp_comp_quarterOrbitStrip_of_memLp hb1.le
    (hZ.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
  apply ae_eq_quarterStrip_of_ae_sections hR hZp.aestronglyMeasurable
  have hprofile := quarter_midpoint_reconstruction_with_rep hκ hp hb hb1 hAnn hg hfg
    hvκ hfκ hdiv hne
  filter_upwards [hprofile] with h hh
  obtain ⟨Z, hzeq, _, _, _, hz⟩ := hh
  filter_upwards [ae_restrict_of_ae hzeq] with t ht
  exact (quarterReconstruction_eq lam (quarterMidpoint lam Q g)
    (fun q ↦ g (dipoleOrbit q.1 q.2)) (h, t)).trans ((hz t).symm.trans ht)

/-- A uniform distance-square time moment integrates a levelwise square bound
without a period or logarithmic loss. The conclusion is a genuine joint norm. -/
theorem memLp_saddleDist_mul_of_level_bound {b C : ℝ} (hb : b < 1)
    {F : ℝ × ℝ → ℂ} {E : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b)))
    (hE : IntegrableOn E (Ioo 0 b))
    (hEpos : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), 0 ≤ E h)
    (hMoment : ∀ h ∈ Ioo 0 b,
      (∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ 2) ≤ C)
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ᵐ t ∂(volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))),
        ‖F (h, t)‖ ^ 2 ≤ E h) :
    MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * F q) 2
      (volume.restrict (quarterOrbitStrip b)) := by
  have hd : Continuous (fun q : ℝ × ℝ ↦ saddleDist (dipoleOrbit q.1 q.2)) :=
    (Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit
  have hW : AEStronglyMeasurable
      (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) * F q)
      (volume.restrict (quarterOrbitStrip b)) :=
    (Complex.continuous_ofReal.comp hd).aestronglyMeasurable.mul hF
  apply memLp_quarterStrip_of_integral_bound hW (hE.const_mul C)
  filter_upwards [hbound, hEpos, aestronglyMeasurable_quarterStrip_sections hW,
    ae_restrict_mem measurableSet_Ioo] with h hh hpos hm hI
  have hL := eighthPeriod_pos hI.1 (hI.2.trans hb)
  have hw : IntegrableOn (fun t ↦ saddleDist (dipoleOrbit h t) ^ 2)
      (Ioo (-eighthPeriod h) (eighthPeriod h)) :=
    (((hd.comp (continuous_const.prodMk continuous_id)).pow 2).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have he : (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
      saddleDist (dipoleOrbit h t) ^ 2) ≤ C := by
    rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -eighthPeriod h ≤ eighthPeriod h)]
    exact hMoment h hI
  have hi : IntegrableOn
      (fun t ↦ ‖(saddleDist (dipoleOrbit h t) : ℂ) * F (h, t)‖ ^ 2)
      (Ioo (-eighthPeriod h) (eighthPeriod h)) := by
    apply (hw.const_mul (E h)).mono' (hm.norm.pow 2)
    filter_upwards [hh] with t ht
    simp only [Pi.pow_apply] at *
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (mul_comm _ _)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        E h * saddleDist (dipoleOrbit h t) ^ 2 := by
      apply integral_mono_ae hi (hw.const_mul (E h))
      filter_upwards [hh] with t ht
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (mul_comm _ _)
    _ = E h * ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h),
        saddleDist (dipoleOrbit h t) ^ 2 := integral_const_mul _ _
    _ ≤ E h * C := mul_le_mul_of_nonneg_left he hpos
    _ = C * E h := mul_comm _ _

/-- Actual midpoint integrals and an integrable level majorant give the
physical-distance-weighted reconstruction norm with no logarithmic weight. -/
theorem quarterReconstructionLevel_weighted_memLp {lam b C : ℝ} (hb : b < 1)
    {A₁ : ℝ → ℂ} {G : ℝ × ℝ → ℂ} {E : ℝ → ℝ}
    (hA : MemLp A₁ 2 (volume.restrict (Ioo 0 b)))
    (hG : AEStronglyMeasurable G (volume.restrict (quarterOrbitStrip b)))
    (hE : IntegrableOn E (Ioo 0 b))
    (hEpos : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), 0 ≤ E h)
    (hMoment : ∀ h ∈ Ioo 0 b,
      (∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ 2) ≤ C)
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      ∀ t ∈ Ioo (-eighthPeriod h) (eighthPeriod h),
        IntervalIntegrable (fun u ↦ G (h, u) *
          Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))) volume 0 t ∧
        ‖∫ u in 0..t, G (h, u) *
          Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ))‖ ^ 2 ≤ E h) :
    MemLp (fun q ↦ (saddleDist (dipoleOrbit q.1 q.2) : ℂ) *
      quarterReconstructionLevel lam A₁ G q) 2 (volume.restrict (quarterOrbitStrip b)) := by
  have hphase : Measurable (fun q : ℝ × ℝ ↦
      Complex.exp (-Complex.I * ((lam * q.2 : ℝ) : ℂ))) := by fun_prop
  have hP := aestronglyMeasurable_quarterPrimitive (hG.mul hphase.aestronglyMeasurable)
  have hR : AEStronglyMeasurable (quarterReconstructionLevel lam A₁ G)
      (volume.restrict (quarterOrbitStrip b)) :=
    (show AEStronglyMeasurable (fun q : ℝ × ℝ ↦
      Complex.exp (Complex.I * ((lam * q.2 : ℝ) : ℂ))) _ from (by fun_prop)).mul
      ((aestronglyMeasurable_level_quarterStrip hA.aestronglyMeasurable).add
        (hP.const_mul Complex.I))
  have hAE : IntegrableOn (fun h ↦ ‖A₁ h‖ ^ 2) (Ioo 0 b) :=
    hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have htotal : IntegrableOn (fun h ↦ 2 * ‖A₁ h‖ ^ 2 + 2 * E h) (Ioo 0 b) := by
    exact (hAE.const_mul (2 : ℝ)).add (hE.const_mul (2 : ℝ))
  apply memLp_saddleDist_mul_of_level_bound (E := fun h ↦ 2 * ‖A₁ h‖ ^ 2 + 2 * E h) hb hR htotal
    (hEpos.mono fun h hh ↦ add_nonneg (by positivity) (mul_nonneg (by norm_num) hh)) hMoment
  filter_upwards [hbound] with h hh
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hint := (hh t ht).2
  have he : ‖Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  dsimp [quarterReconstructionLevel]
  rw [norm_mul, he, one_mul]
  have hs := norm_add_sq_le (A₁ h) (Complex.I * ∫ u in 0..t,
    G (h, u) * Complex.exp (-Complex.I * ((lam * u : ℝ) : ℂ)))
  simp only [norm_mul, Complex.norm_I, one_mul] at hs
  nlinarith only [hs, hint]

end NoEmbeddedEigenvalues
