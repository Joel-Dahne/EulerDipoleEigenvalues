import NoEmbeddedEigenvalues.Transport.WeightedForcing.SaddleEndpointEnergy
import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals
import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterCellMass
import NoEmbeddedEigenvalues.Transport.WeightedGains.PhaseCellSecondMass
import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterTransportProjections

/-!
# Weighted transport mass from the scalar quotient

Blueprint: `lem:weighted-quarter-mass`, `lem:weighted-character-mass`,
`lem:weighted-transport-mass-data`.

Actual forcing/d² mass and quotient/h mass control the original raw unknown.
Canonical ACL solutions are used only inside an almost-everywhere fiber proof;
no jointly measurable selection of these solutions is required. Exponential
endpoint energy and the period bound give an integrable level majorant without
pointwise forcing decay or a logarithmic loss.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real

private theorem exp_four_eighthPeriod_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    exp (4 * eighthPeriod h) ≤ exp 8 / h ^ 2 := by
  have hp := pow_le_pow_left₀
    (mul_nonneg (exp_pos (eighthPeriod h)).le (sqrt_nonneg h))
    (exp_eighthPeriod_mul_sqrt_le hh hh1) 4
  have he (x : ℝ) : exp x ^ 4 = exp (4 * x) := by
    rw [← exp_nat_mul]
    norm_num
  have hs : (sqrt h) ^ 4 = h ^ 2 := by
    calc _ = ((sqrt h) ^ 2) ^ 2 := by ring
         _ = _ := by rw [sq_sqrt hh.le]
  rw [mul_pow, he, hs, he] at hp
  norm_num at hp
  exact (le_div_iff₀ (sq_pos_of_pos hh)).2 hp

/-- For one supplied quarter character, actual forcing/d² mass and the
ordinary scalar quotient/h norm give raw second mass on a smaller base quarter.
The scalar quotient norm is an input, not inferred from the forcing norm alone. -/
theorem IsTransportPair.weighted_quarter_memLp_of_quotient
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f)
    (hQ : MemLp (fun h ↦ quarterQuotient lam κ g h / (h : ℂ)) 2
      (volume.restrict (Ioo 0 r))) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧ b < 1 / 2 ∧
      MemLp (fun q : ℝ × ℝ ↦ v (dipoleOrbit q.1 q.2) /
        ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨c, C, rD, hc, hrD, hdist⟩ := saddleDist_dipoleOrbit
  obtain ⟨b, hb, hbmin, hne⟩ := exists_ae_quarterDivisor_ne_zero hp.ne_zero hκ
    (lt_min hr (lt_min hrD (by norm_num : (0 : ℝ) < 1 / 2)))
  have hbr : b < r := hbmin.trans_le (min_le_left _ _)
  have hbD : b < rD := hbmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbh : b < 1 / 2 := hbmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : b < 1 := hbh.trans (by norm_num)
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 r := Ioo_subset_Ioo le_rfl hbr.le
  have hAr : orbitAnnulus 0 b ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans hbr⟩
  have hA : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  obtain ⟨Em, Ep, _, hprof⟩ := quarter_endpoint_formula hκ hp hb hb1 hA hg hfg
    (ae_restrict_of_ae_restrict_of_subset hAr hvκ)
    (ae_restrict_of_ae_restrict_of_subset hAr hfκ)
  have hfgOrb := ae_orbit_congr hb1.le (ae_restrict_of_ae_restrict_of_subset hA hfg)
  have hfgCell := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hcell) hfg
  have hgf : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply hf.ae_eq
    filter_upwards [hfgCell] with p hp
    rw [hp]
  let F : ℝ × ℝ → ℂ := fun q ↦ g (dipoleOrbit q.1 q.2) /
    ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)
  let V : ℝ × ℝ → ℂ := fun q ↦ v (dipoleOrbit q.1 q.2) /
    ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)
  have hF : MemLp F 2 (volume.restrict (quarterOrbitStrip b)) :=
    memLp_comp_quarterOrbitStrip_of_memLp hb1.le hgf
  have hv := memLp_comp_quarterOrbitStrip_of_memLp hb1.le
    (hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell)))
  have hdm : Continuous (fun q : ℝ × ℝ ↦
      ((saddleDist (dipoleOrbit q.1 q.2)) ^ 2 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit)).pow 2
  have hVm : AEStronglyMeasurable V (volume.restrict (quarterOrbitStrip b)) :=
    hv.aestronglyMeasurable.div₀ hdm.aestronglyMeasurable
  let E := fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖F (h, t)‖ ^ 2
  have hE : IntegrableOn E (Ioo 0 b) :=
    (integrable_quarterStrip_sections (hF.integrable_norm_pow (by norm_num))).1
  let K₁ := 2 * lam ^ 2 * exp 8 / c ^ 4
  let K₂ := lam ^ 2 * C ^ 4 / (2 * c ^ 4) + 2
  let B := fun h ↦ K₁ * ‖quarterQuotient lam κ g h / (h : ℂ)‖ ^ 2 + K₂ * E h
  have hB : IntegrableOn B (Ioo 0 b) :=
    (((hQ.mono_measure (Measure.restrict_mono_set _ hsub)).integrable_norm_pow
      (by norm_num)).const_mul K₁).add (hE.const_mul K₂)
  refine ⟨b, hb, hbr, hbh, memLp_quarterStrip_of_integral_bound hVm hB ?_⟩
  filter_upwards [hprof, hfgOrb, hne, memLp_quarterStrip_sections hF,
    ae_restrict_mem measurableSet_Ioo] with h hZ hfg_h hn hFh hh
  obtain ⟨Z, hzeq, _, hac, hode, hEm, hEp, hchar, _, hnorm⟩ := hZ
  have hh1 : h < 1 := hh.2.trans hb1
  have hL := (eighthPeriod_pos hh.1 hh1).le
  have hκnorm : ‖κ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hκ (by decide)
  have hleft : ‖Z (-eighthPeriod h)‖ ≤ ‖quarterQuotient lam κ g h‖ := by
    rw [hEm, hnorm hn]
  have hright : ‖Z (eighthPeriod h)‖ ≤ ‖quarterQuotient lam κ g h‖ := by
    rw [hEp, hchar, norm_mul, hκnorm, one_mul, hnorm hn]
  have hdc : Continuous (fun t : ℝ ↦ saddleDist (dipoleOrbit h t)) :=
    (Metric.continuous_infDist_pt saddleSet).comp
      (continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt)
  have hFi : MemLp (fun t ↦ g (dipoleOrbit h t) /
      ((saddleDist (dipoleOrbit h t)) ^ 2 : ℂ)) 2
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hFh
  obtain ⟨hVi, hbound⟩ := transport_saddle_vorticity_energy hL hc hdc.measurable
    (fun t ht ↦ (hdist h ⟨hh.1, hh.2.trans hbD⟩ t (abs_le.2 ht)).1)
    (fun t ht ↦ (hdist h ⟨hh.1, hh.2.trans hbD⟩ t (abs_le.2 ht)).2)
    hac hFi hode hleft hright
  rw [← restrict_Ioo_eq_restrict_Icc] at hVi
  have heq : (fun t ↦ -((lam : ℂ) * Z t + g (dipoleOrbit h t)) /
      ((saddleDist (dipoleOrbit h t)) ^ 2 : ℂ)) =ᵐ[
        volume.restrict (Ioo (-eighthPeriod h) (eighthPeriod h))]
      (fun t ↦ V (h, t)) := by
    filter_upwards [ae_restrict_of_ae hzeq, ae_restrict_of_ae hfg_h] with t hzt hfgt
    have he : v (dipoleOrbit h t) = -((lam : ℂ) * Z t + g (dipoleOrbit h t)) := by
      dsimp only [transportUnknown] at hzt
      rw [hfgt] at hzt
      have he := (eq_div_iff (Complex.ofReal_ne_zero.mpr hp.ne_zero)).1 hzt
      linear_combination he
    dsimp only [V]
    rw [he]
  have hraw := hVi.ae_eq heq
  have hIe := integral_congr_ae (heq.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
  dsimp only [Function.comp_def] at hIe
  simp only [integral_Icc_eq_integral_Ioo] at hbound
  rw [hIe] at hbound
  have hqn : ‖quarterQuotient lam κ g h / (h : ℂ)‖ ^ 2 =
      ‖quarterQuotient lam κ g h‖ ^ 2 / h ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh.1, div_pow]
  have hcoef : (2 * lam ^ 2 * exp (4 * eighthPeriod h) / c ^ 4) *
      ‖quarterQuotient lam κ g h‖ ^ 2 ≤ K₁ * ‖quarterQuotient lam κ g h / (h : ℂ)‖ ^ 2 := by
    rw [hqn]
    calc _ = (2 * lam ^ 2 / c ^ 4 * ‖quarterQuotient lam κ g h‖ ^ 2) *
          exp (4 * eighthPeriod h) := by ring
         _ ≤ (2 * lam ^ 2 / c ^ 4 * ‖quarterQuotient lam κ g h‖ ^ 2) * (exp 8 / h ^ 2) :=
          mul_le_mul_of_nonneg_left (exp_four_eighthPeriod_le hh.1 hh1) (by positivity)
         _ = _ := by dsimp only [K₁]; ring
  refine ⟨hraw.integrable_norm_pow (by norm_num), ?_⟩
  exact hbound.trans (add_le_add hcoef le_rfl)

/-- A second-distance collar norm extends to the cell using the original
unweighted L² norm. No first transport gain or bounded ambient domain is needed. -/
theorem memLp_div_saddleDist_sq_of_cell_collar {b : ℝ} (hb : 0 < b)
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict cellSquare))
    (hw : MemLp (fun p ↦ F p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict (cellSeparatrixStrip (2 * b)))) :
    MemLp (fun p ↦ F p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  let W := fun p ↦ F p / (saddleDist p ^ 2 : ℂ)
  have hm : AEStronglyMeasurable W (volume.restrict cellSquare) :=
    hF.aestronglyMeasurable.div₀
      ((Complex.continuous_ofReal.comp
        (Metric.continuous_infDist_pt saddleSet)).pow 2).aestronglyMeasurable
  have hsub : cellSquare \ cellSeparatrixStrip (2 * b) ⊆ cellSquare := sdiff_subset
  have hi := hF.mono_measure (Measure.restrict_mono_set _ hsub)
  have hout : MemLp W 2 (volume.restrict (cellSquare \ cellSeparatrixStrip (2 * b))) := by
    apply hi.of_le_mul (c := (b ^ 2)⁻¹) (hm.mono_measure (Measure.restrict_mono_set _ hsub))
    filter_upwards [ae_restrict_mem
      (isOpen_cellSquare.measurableSet.diff (isOpen_cellSeparatrixStrip _).measurableSet)]
      with p hp
    have hpos : 0 < dipoleLift p := by
      rw [dipoleLift_eq_diag]
      exact mul_pos (mul_pos (by norm_num) (cos_pos_of_mem_Ioo (abs_lt.mp hp.1.1)))
        (cos_pos_of_mem_Ioo (abs_lt.mp hp.1.2))
    have hlevel : b ≤ levelCoord p := by
      have hn : ¬dipoleLift p < 2 * b := fun ht ↦ hp.2 ⟨hp.1, hpos, ht⟩
      dsimp only [levelCoord]
      linarith [not_lt.mp hn]
    have hd := hlevel.trans (levelCoord_le_saddleDist hp.1)
    have hd0 : 0 < saddleDist p := hb.trans_le hd
    dsimp only [W]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    calc ‖F p‖ / saddleDist p ^ 2 ≤ ‖F p‖ / b ^ 2 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hb)
            (pow_le_pow_left₀ hb.le hd 2)
         _ = (b ^ 2)⁻¹ * ‖F p‖ := by ring
  have hi₁ : IntegrableOn (fun p ↦ ‖W p‖ ^ 2) (cellSeparatrixStrip (2 * b)) :=
    hw.integrable_norm_pow (by norm_num)
  have hi₂ : IntegrableOn (fun p ↦ ‖W p‖ ^ 2) (cellSquare \ cellSeparatrixStrip (2 * b)) :=
    hout.integrable_norm_pow (by norm_num)
  have hu : MemLp W 2 (volume.restrict
      (cellSeparatrixStrip (2 * b) ∪ (cellSquare \ cellSeparatrixStrip (2 * b)))) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_union_iff.2
      ⟨hw.aestronglyMeasurable, hout.aestronglyMeasurable⟩)).2 (hi₁.union hi₂)
  apply hu.mono_measure (Measure.restrict_mono_set _ ?_)
  intro p hp
  by_cases h : p ∈ cellSeparatrixStrip (2 * b)
  · exact Or.inl h
  · exact Or.inr ⟨hp, h⟩

/-- Reverse the quarter chart and use the quarter character on a full collar.
Original unweighted cell mass controls its interior complement. -/
theorem IsTransportPair.weighted_character_memLp_of_quotient
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f)
    (hQ : MemLp (fun h ↦ quarterQuotient lam κ g h / (h : ℂ)) 2
      (volume.restrict (Ioo 0 r))) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨b, hb, hbr, hbh, hq⟩ := hp.weighted_quarter_memLp_of_quotient
    hκ hcell hg hfg hf hr hvκ hfκ hQ
  have hb1 : b < 1 := hbh.trans (by norm_num)
  have hκ0 : κ ≠ 0 := by
    intro hz
    simp [hz] at hκ
  have hsub : cellSeparatrixStrip (2 * b) ⊆ orbitAnnulus 0 r := by
    rw [cellSeparatrixStrip_eq_orbitAnnulus hb1.le]
    exact fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.trans hbr⟩
  have hchar : HasQuarterCharacterOn κ (cellSeparatrixStrip (2 * b))
      (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvκ] with p hp
    rw [saddleDist_rotLift, hp, mul_div_assoc]
  have hColl := memLp_cell_collar_of_quarter_character hb1.le hκ0 hchar hq
  exact memLp_div_saddleDist_sq_of_cell_collar hb
    (hp.memLp.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell))) hColl

/-- Only the compatible first numerator derivative and its actual L² norm
are needed to supply scalar second mass. No second numerator jet is required. -/
theorem IsTransportPair.weighted_character_memLp_of_numerator
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    {r : ℝ} (hr : 0 < r)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 r) f)
    {N₁ : ℝ → ℂ} (hN : HasIntervalH1Loc 0 r (quarterNumerator lam g) N₁)
    (hN₁ : MemLp N₁ 2 (volume.restrict (Ioo 0 r))) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  let b := min r (1 / 2)
  have hb : 0 < b := lt_min hr (by norm_num)
  have hbr : b ≤ r := min_le_left _ _
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 r := Ioo_subset_Ioo le_rfl hbr
  have hAr : orbitAnnulus 0 b ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans_le hbr⟩
  have hA : orbitAnnulus 0 b ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  have hz := (numerator_zeros hκ hp hb hb1 hA hg hfg
    (ae_restrict_of_ae_restrict_of_subset hAr hvκ)
    (ae_restrict_of_ae_restrict_of_subset hAr hfκ)).2
  have hNb : HasIntervalH1Loc 0 b (quarterNumerator lam g) N₁ :=
    fun c d hc hcd hd ↦ hN c d hc hcd (hd.trans_le hbr)
  obtain ⟨η, hη, hηb, _, hQ, _⟩ := phase_cell_second_mass_division hp.ne_zero hκ hb hNb hz
    (hN₁.mono_measure (Measure.restrict_mono_set _ hsub))
  have hηr : η < r := hηb.trans_le hbr
  have hηA : orbitAnnulus 0 η ⊆ orbitAnnulus 0 r := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans hηr⟩
  exact hp.weighted_character_memLp_of_quotient hκ hcell hg hfg hf hη
    (ae_restrict_of_ae_restrict_of_subset hηA hvκ)
    (ae_restrict_of_ae_restrict_of_subset hηA hfκ) hQ

/-- The existing numerator-data interface supplies exactly the first-derivative
premises used by physical weighted mass. Its second derivative, half numerator
and ray traces are not used. This does not construct the supplied data. -/
theorem WeightedQuarterNumeratorData.character_memLp
    {lam h₀ : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1) (hh₀ : 0 < h₀)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (d : WeightedQuarterNumeratorData lam U g D h₀)
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) f) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) :=
  hp.weighted_character_memLp_of_numerator hκ hcell hg hfg hf hh₀ hvκ hfκ
    (fun c e hc hce he ↦ (d.numerator_h2 c e hc hce he).1) d.first_lp

/-- Finite character projections preserve actual cell Lp membership for every
exponent and every complex coefficient. No forcing regularity is used. -/
theorem memLp_quarterCharacterProjection {p : ENNReal} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F p (volume.restrict cellSquare)) (κ : ℂ) :
    MemLp (quarterCharacterProjection κ F) p (volume.restrict cellSquare) := by
  have hcell : rotLift ⁻¹' cellSquare = cellSquare := by
    ext q
    exact (rotLift_cell_level q).1
  have hm : MeasurePreserving rotLift (volume.restrict cellSquare)
      (volume.restrict cellSquare) := by
    simpa only [hcell] using measurePreserving_rotLift.restrict_preimage
      isOpen_cellSquare.measurableSet
  have h1 := hF.comp_measurePreserving hm
  have h2 := h1.comp_measurePreserving hm
  have h3 := h2.comp_measurePreserving hm
  exact (((hF.add (h1.const_mul (κ ^ 3))).add (h2.const_mul (κ ^ 2))).add
    (h3.const_mul κ)).const_mul (1 / 4)

/-- Saddle-distance invariance makes weighted value mass commute with the
same quarter projection applied to the original raw forcing. -/
theorem memLp_quarterCharacterProjection_div_saddleDist_pow
    {p : ENNReal} {n : ℕ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp (fun q ↦ F q / (saddleDist q : ℂ) ^ n) p
      (volume.restrict cellSquare)) (κ : ℂ) :
    MemLp (fun q ↦ quarterCharacterProjection κ F q / (saddleDist q : ℂ) ^ n) p
      (volume.restrict cellSquare) := by
  have he : quarterCharacterProjection κ (fun q ↦ F q / (saddleDist q : ℂ) ^ n) =
      (fun q ↦ quarterCharacterProjection κ F q / (saddleDist q : ℂ) ^ n) := by
    funext q
    simp only [quarterCharacterProjection, saddleDist_rotLift]
    ring
  rw [← he]
  exact memLp_quarterCharacterProjection hF κ

/-- First numerator data for the four projected continuous forcings suffice
for raw second mass on the whole cell. This separates mass reconstruction from
the producer of numerator regularity and from the stronger H¹ conclusion. -/
theorem weighted_transport_mass_of_first_numerators
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hbU : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    (hN : ∀ κ : ℂ, κ ^ 4 = 1 → ∃ r : ℝ, 0 < r ∧ ∃ N₁ : ℝ → ℂ,
      HasIntervalH1Loc 0 r (quarterNumerator lam (quarterCharacterProjection κ g)) N₁ ∧
        MemLp N₁ 2 (volume.restrict (Ioo 0 r))) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨V, hV, _, hVU, hcellV, hRV⟩ :=
    exists_rotationInvariant_transport_neighbourhood hp.isOrbitUnion hbU hcell
  have hpV := hp.mono hV hVU
  have hgV := hg.mono hVU
  have hfgV := ae_restrict_of_ae_restrict_of_subset hVU hfg
  have hchar (κ : ℂ) (hκ : κ ^ 4 = 1) :
      MemLp (fun p ↦ quarterCharacterProjection κ v p / (saddleDist p ^ 2 : ℂ)) 2
        (volume.restrict cellSquare) := by
    obtain ⟨r, hr, N₁, hNl, hN₁⟩ := hN κ hκ
    exact (hpV.quarterCharacterProjection hRV κ).weighted_character_memLp_of_numerator
      hκ hcellV (continuousOn_quarterCharacterProjection hgV hRV κ)
      (quarterCharacterProjection_congr_ae hV.1.measurableSet hRV hfgV κ)
      (memLp_quarterCharacterProjection_div_saddleDist_pow hf κ) hr
      (Eventually.of_forall (quarterCharacterProjection_rotLift hκ v))
      (Eventually.of_forall (quarterCharacterProjection_rotLift hκ f)) hNl hN₁
  have hsum := (((hchar 1 (by norm_num)).add (hchar (-1) (by norm_num))).add
    (hchar Complex.I (by norm_num))).add (hchar (-Complex.I) (by
      calc (-Complex.I) ^ 4 = Complex.I ^ 4 := by ring
           _ = 1 := by norm_num))
  apply hsum.ae_eq
  exact Eventually.of_forall fun p ↦ by
    simp only [Pi.add_apply, ← add_div, quarterCharacterProjection_sum]

end NoEmbeddedEigenvalues
