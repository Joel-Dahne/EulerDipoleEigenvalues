module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.WeightedConeTrace

/-!
# Canonical weighted traces without continuous planar representatives

Blueprint: `lem:cone-band-energy`, `lem:canonical-weighted-cone-trace`.

The trace is fixed by interior continuous-section germs, not raw ray values.
A radius-sized transverse rectangle controls its r⁻¹ mass by F/r and the
unweighted transverse weak derivative. Disjoint bands then sum actual energies.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- A common integrable cone density sums radius-sized band estimates. -/
theorem memLp_two_of_cone_band_energy {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    {W : ℝ → ℂ} {G : ℝ × ℝ → ℝ}
    (hGi : IntegrableOn G (cartesianRayCone R))
    (hpos : ∀ q ∈ cartesianRayCone R, 0 ≤ G q)
    (hBand : ∀ a : ℝ, 0 < a → 2 * a ≤ R →
      MemLp W 2 (volume.restrict (Ioo a (2 * a))) ∧
      (∫ r in Ioo a (2 * a), ‖W r‖ ^ 2) ≤
        K * ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a, G q) :
    MemLp W 2 (volume.restrict (Ioo 0 R)) ∧
      (∫ r in Ioo 0 R, ‖W r‖ ^ 2) ≤ K * ∫ q in cartesianRayCone R, G q := by
  let Q := cartesianRayCone R
  let H := Q.indicator G
  let E := fun r : ℝ ↦ ∫ t : ℝ, H (r, t)
  have hQ : MeasurableSet Q :=
    (measurable_fst measurableSet_Ioo).inter
      (measurableSet_lt continuous_snd.abs.measurable measurable_fst)
  have hG : IntegrableOn G Q := hGi
  have hH : Integrable H volume := (integrable_indicator_iff hQ).2 hG
  have hHp : Integrable H (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hH
  have hE : Integrable E volume := hHp.integral_prod_left
  have hHpos (q : ℝ × ℝ) : 0 ≤ H q := by
    exact indicator_nonneg hpos q
  have hEpos (r : ℝ) : 0 ≤ E r := integral_nonneg (fun t ↦ hHpos (r, t))
  let e := fun n : ℕ ↦ R * (1 / 2 : ℝ) ^ n
  have hepos (n : ℕ) : 0 < e n := mul_pos hR (pow_pos (by norm_num) _)
  have he : StrictAnti e := fun i j hij ↦ mul_lt_mul_of_pos_left
    (pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hij) hR
  have het : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
  have hstep (n : ℕ) : 2 * e (n + 1) = e n := by dsimp only [e]; rw [pow_succ]; ring
  let s := fun n ↦ Ioo (e (n + 1)) (e n)
  let B := fun n ↦ s n ×ˢ Ioo (-e (n + 1)) (e (n + 1))
  have hsub (n : ℕ) : B n ⊆ Q := by
    intro q hq
    refine ⟨⟨(hepos _).trans hq.1.1, hq.1.2.trans_le ?_⟩, ?_⟩
    · exact (he.antitone (Nat.zero_le n)).trans_eq (by simp [e])
    · exact (abs_lt.mpr hq.2).trans hq.1.1
  have hband (n : ℕ) : MemLp W 2 (volume.restrict (s n)) ∧
      (∫ r in s n, ‖W r‖ ^ 2) ≤ K * ∫ q in B n, G q := by
    have htop : 2 * e (n + 1) ≤ R := by
      rw [hstep n]
      exact (he.antitone (Nat.zero_le n)).trans_eq (by simp [e])
    simpa only [hstep n] using hBand (e (n + 1)) (hepos _) htop
  have hbound (n : ℕ) : (∫ r in s n, ‖W r‖ ^ 2) ≤ K * ∫ r in s n, E r := by
    apply (hband n).2.trans
    apply mul_le_mul_of_nonneg_left _ hK
    have hm : (volume.restrict (s n)).prod volume =
        (volume : Measure (ℝ × ℝ)).restrict (s n ×ˢ univ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    have hHi : Integrable H ((volume.restrict (s n)).prod volume) := by
      rw [hm]
      exact hH.integrableOn
    calc
      _ = ∫ q in B n, H q := setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
        (fun q hq ↦ (indicator_of_mem (hsub n hq) G).symm)
      _ ≤ ∫ q in s n ×ˢ univ, H q := setIntegral_mono_set hH.integrableOn
        (Eventually.of_forall hHpos) (Eventually.of_forall fun q hq ↦ ⟨hq.1, mem_univ _⟩)
      _ = ∫ r in s n, E r := by simpa only [hm] using integral_prod H hHi
  have hdis := descending_cells_disjoint he
  have hW := memLp_two_of_cell_energy (fun _ ↦ measurableSet_Ioo) hdis hK
    hE.integrableOn (fun r _ ↦ hEpos r) (fun n ↦ (hband n).1) hbound
  have hcover : (⋃ n, s n) =ᵐ[volume] Ioo 0 R := by
    simpa only [e, pow_zero, mul_one] using descending_cells_ae_cover he hepos het
  have hmeasure := Measure.restrict_congr_set hcover
  refine ⟨by rwa [← hmeasure], ?_⟩
  have hsW := hasSum_integral_iUnion (fun _ ↦ measurableSet_Ioo) hdis
    (hW.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hsE := hasSum_integral_iUnion (fun _ ↦ measurableSet_Ioo) hdis hE.integrableOn
  calc
    _ = ∑' n, ∫ r in s n, ‖W r‖ ^ 2 := by
      rw [← hmeasure]
      exact hsW.tsum_eq.symm
    _ ≤ ∑' n, K * ∫ r in s n, E r :=
      hsW.summable.tsum_le_tsum hbound (hsE.mul_left K).summable
    _ = K * ∫ r in ⋃ n, s n, E r := (hsE.mul_left K).tsum_eq
    _ ≤ K * ∫ r, E r := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hE (Eventually.of_forall hEpos)) hK
    _ = _ := by
      congr 1
      rw [← integral_prod H hHp, ← Measure.volume_eq_prod]
      exact integral_indicator hQ


/-- The rectangle estimate controls the canonical interior trace without
requiring a continuous planar representative. -/
theorem HasWeakPartialOn.canonical_rectangle_trace
    {a b w : ℝ} (hab : a < b) (hw : 0 < w) {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo (-w) w) 1 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo (-w) w)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo (-w) w))) :
    MemLp (interiorChartTrace id F) 2 (volume.restrict (Ioo a b)) ∧
      (∫ r in Ioo a b, ‖interiorChartTrace id F r‖ ^ 2) ≤
        (1 / w) * (∫ q in Ioo a b ×ˢ Ioo (-w) w, ‖F q‖ ^ 2) +
          (4 * w) * ∫ q in Ioo a b ×ˢ Ioo (-w) w, ‖D q‖ ^ 2 := by
  obtain ⟨G, hGm, hGF, hACL, _, htrace⟩ := hd.exists_l2_trace isOpen_Ioo
    ordConnected_Ioo (nonempty_Ioo.mpr hab) (by linarith) hF hD
  have ht : HasTransverseH1Trace a b (-w) w 0 id F (aclTrace (-w) w G D 0) :=
    ⟨hab, by linarith, ⟨by linarith, hw.le⟩, G, D, hGm, hGF,
      hF.ae_eq hGF.symm, hD, hACL, EventuallyEq.rfl⟩
  have he := ht.ae_eq_interiorChartTrace (by linarith) hw
  obtain ⟨hTL, hT⟩ := htrace 0 ⟨by linarith, hw.le⟩
  refine ⟨hTL.ae_eq he, ?_⟩
  have hi := integral_congr_ae (he.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
  dsimp only [Function.comp_def] at hi
  rw [← hi]
  convert hT using 1
  field_simp
  ring

/-- A radius-sized rectangle controls the r⁻¹ canonical ray mass. -/
theorem canonical_weighted_band_trace {a : ℝ} (ha : 0 < a)
    {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo a (2 * a) ×ˢ Ioo (-a) a) 1 F D)
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ)) 2
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)))
    (hD : MemLp D 2 (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a))) :
    MemLp (fun r ↦ interiorChartTrace id F r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) ∧
    (∫ r in Ioo a (2 * a), ‖interiorChartTrace id F r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      4 * ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
  let T := interiorChartTrace id F
  have hX : MemLp (fun q : ℝ × ℝ ↦ (q.1 : ℂ)) ⊤
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)) := by
    apply memLp_top_of_bound (by fun_prop) (2 * a)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans hq.1.1)]
      using hq.1.2.le
  have hF0 : MemLp F 2 (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)) := by
    apply (hX.mul hF).ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ha.trans hq.1.1).ne')
  obtain ⟨hT, hTb⟩ := hd.canonical_rectangle_trace (by linarith) ha hF0 hD
  have hWm := hT.aestronglyMeasurable.div₀
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
  have hW : MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) := by
    apply hT.of_le_mul hWm (c := 1 / Real.sqrt a)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    change ‖T r / (Real.sqrt r : ℂ)‖ ≤ (1 / Real.sqrt a) * ‖T r‖
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [one_div, inv_mul_eq_div] using
      div_le_div_of_nonneg_left (norm_nonneg _) (Real.sqrt_pos.mpr ha)
        (Real.sqrt_le_sqrt hr.1.le)
  have hsq (r : ℝ) (hr : r ∈ Ioo a (2 * a)) :
      ‖T r / (Real.sqrt r : ℂ)‖ ^ 2 = ‖T r‖ ^ 2 / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (ha.trans hr.1).le]
  have hA : (∫ r in Ioo a (2 * a), ‖T r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      (1 / a) * ∫ r in Ioo a (2 * a), ‖T r‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hW.integrable_norm_pow (by norm_num))
      ((hT.integrable_norm_pow (by norm_num)).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hsq r hr]
    simpa only [one_div, inv_mul_eq_div] using
      div_le_div_of_nonneg_left (sq_nonneg ‖T r‖) ha hr.1.le
  have hiF := hF0.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiD := hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hE := (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add hiD
  refine ⟨hW, hA.trans ((mul_le_mul_of_nonneg_left hTb (by positivity)).trans ?_)⟩
  calc
    _ = ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        ((1 / a ^ 2) * ‖F q‖ ^ 2 + 4 * ‖D q‖ ^ 2) := by
      rw [integral_add (hiF.const_mul _) (hiD.const_mul _), integral_const_mul,
        integral_const_mul]
      field_simp
    _ ≤ 4 * ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_ae ((hiF.const_mul _).add (hiD.const_mul _)) (hE.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
      have hx : 0 < q.1 := ha.trans hq.1.1
      have h2 : q.1 ^ 2 ≤ 4 * a ^ 2 := by
        have := pow_le_pow_left₀ hx.le hq.1.2.le 2
        nlinarith
      have hi2 : 1 / a ^ 2 ≤ 4 / q.1 ^ 2 :=
        (div_le_div_iff₀ (sq_pos_of_pos ha) (sq_pos_of_pos hx)).2 (by nlinarith)
      have hb := add_le_add (mul_le_mul_of_nonneg_right hi2 (sq_nonneg ‖F q‖))
        (le_refl (4 * ‖D q‖ ^ 2))
      simp only [Pi.add_apply, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx, div_pow]
      convert hb using 1
      ring

/-- Canonical interior traces have finite critical ray mass. No continuity or
pointwise value of the planar Sobolev representative on the ray is assumed. -/
theorem canonical_weighted_cone_trace {R : ℝ} (hR : 0 < R) {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (cartesianRayCone R) 1 F D)
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ)) 2
      (volume.restrict (cartesianRayCone R)))
    (hD : MemLp D 2 (volume.restrict (cartesianRayCone R))) :
    MemLp (fun r ↦ interiorChartTrace id F r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 R)) ∧
    (∫ r in Ioo 0 R, ‖interiorChartTrace id F r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      4 * ∫ q in cartesianRayCone R, (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
  apply memLp_two_of_cone_band_energy hR (by norm_num)
    ((hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
    (fun _ _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
  intro a ha haR
  have hsub : Ioo a (2 * a) ×ˢ Ioo (-a) a ⊆ cartesianRayCone R := by
    intro q hq
    exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans_le haR⟩, (abs_lt.mpr hq.2).trans hq.1.1⟩
  exact canonical_weighted_band_trace ha (hd.mono hsub)
    (hF.mono_measure (Measure.restrict_mono_set _ hsub))
    (hD.mono_measure (Measure.restrict_mono_set _ hsub))

end EulerDipoleEigenvalues
