module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTrace
public import NoEmbeddedEigenvalues.Analysis.Inequalities.CountableCellEnergy
public import NoEmbeddedEigenvalues.Transport.WeightedGains.DescendingIntervalPartition

/-!
# Weighted traces in a Cartesian cone

Blueprint: `def:cartesian-ray-cone`, `lem:weighted-band-trace`,
`lem:weighted-cone-trace`.

Disjoint radial bands allow the elementary rectangle trace estimate to use
transverse widths comparable to radius. The value energy has weight r⁻⁴ and
the transverse derivative energy weight r⁻². Continuity identifies the raw
interior ray values with canonical ACL traces; no raw Sobolev ray assignment
is used.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Identify the interior trace of a continuous forcing before estimating it. -/
theorem HasWeakPartialOn.continuous_rectangle_trace
    {a b w : ℝ} (hab : a < b) (hw : 0 < w) {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo (-w) w) 1 F D)
    (hc : ContinuousOn F (Ioo a b ×ˢ Ioo (-w) w))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo (-w) w)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo (-w) w))) :
    MemLp (fun r ↦ F (r, 0)) 2 (volume.restrict (Ioo a b)) ∧
      (∫ r in Ioo a b, ‖F (r, 0)‖ ^ 2) ≤
        (1 / w) * (∫ q in Ioo a b ×ˢ Ioo (-w) w, ‖F q‖ ^ 2) +
          (4 * w) * ∫ q in Ioo a b ×ˢ Ioo (-w) w, ‖D q‖ ^ 2 := by
  obtain ⟨G, hGm, hGF, hACL, _, htrace⟩ := hd.exists_l2_trace isOpen_Ioo
    ordConnected_Ioo (nonempty_Ioo.mpr hab) (by linarith) hF hD
  have ht : HasTransverseH1Trace a b (-w) w 0 id F (aclTrace (-w) w G D 0) :=
    ⟨hab, by linarith, ⟨by linarith, hw.le⟩, G, D, hGm, hGF,
      hF.ae_eq hGF.symm, hD, hACL, EventuallyEq.rfl⟩
  have he : (aclTrace (-w) w G D 0) =ᵐ[volume.restrict (Ioo a b)] (fun r ↦ F (r, 0)) := by
    filter_upwards [ht.ae_eq_interiorChartTrace (by linarith) hw,
      ae_restrict_mem measurableSet_Ioo] with r hr hri
    apply hr.trans
    exact interiorSectionTrace_eq (by linarith) hw
      (hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht ↦ ⟨hri, ht⟩)) EventuallyEq.rfl
  obtain ⟨hTL, hT⟩ := htrace 0 ⟨by linarith, hw.le⟩
  refine ⟨hTL.ae_eq he, ?_⟩
  have hi := integral_congr_ae (he.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
  dsimp only [Function.comp_def] at hi
  rw [← hi]
  convert hT using 1
  field_simp
  ring

/-- Recover unweighted values from a weighted L² representative on a bounded
radial rectangle, without imposing any global measurability on the raw values. -/
private theorem memLp_rectangle_unweight {a : ℝ} (ha : 0 < a)
    {F : ℝ × ℝ → ℂ} {n : ℕ}
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ) ^ n) 2
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a))) :
    MemLp F 2 (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)) := by
  have hc : MemLp (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ n) ⊤
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)) := by
    apply memLp_top_of_bound (by fun_prop) ((2 * a) ^ n)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans hq.1.1)]
    exact pow_le_pow_left₀ (ha.trans hq.1.1).le hq.1.2.le n
  apply (hc.mul hF).ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
  exact mul_div_cancel₀ _ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr (ha.trans hq.1.1).ne'))

/-- Squared weighted ray values are controlled by weighted bulk energies on
one radial band. The constant is independent of the scale a. -/
theorem weighted_band_trace {a : ℝ} (ha : 0 < a) {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo a (2 * a) ×ˢ Ioo (-a) a) 1 F D)
    (hc : ContinuousOn F (Ioo a (2 * a) ×ˢ Ioo (-a) a))
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ) ^ 2) 2
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a)))
    (hD : MemLp (fun q ↦ D q / (q.1 : ℂ)) 2
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo (-a) a))) :
    MemLp (fun r ↦ F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) ∧
    (∫ r in Ioo a (2 * a), ‖F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      16 * ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        (‖F q / (q.1 : ℂ) ^ 2‖ ^ 2 + ‖D q / (q.1 : ℂ)‖ ^ 2) := by
  have hF0 := memLp_rectangle_unweight ha hF
  have hD0 := memLp_rectangle_unweight (n := 1) ha (by simpa using hD)
  obtain ⟨hT, hTb⟩ := hd.continuous_rectangle_trace (by linarith) ha hc hF0 hD0
  have hWm := hT.aestronglyMeasurable.div₀ Complex.measurable_ofReal.aestronglyMeasurable
    |>.div₀ (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
  have hw (r : ℝ) (hr : r ∈ Ioo a (2 * a)) :
      ‖F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)‖ ≤
        (1 / (a * Real.sqrt a)) * ‖F (r, 0)‖ := by
    have hr0 := ha.trans hr.1
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hr0), div_div]
    calc _ ≤ ‖F (r, 0)‖ / (a * Real.sqrt a) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
            (mul_le_mul hr.1.le (Real.sqrt_le_sqrt hr.1.le) (Real.sqrt_nonneg _) hr0.le)
         _ = _ := by ring
  have hW : MemLp (fun r ↦ F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) := hT.of_le_mul hWm
        ((ae_restrict_mem measurableSet_Ioo).mono fun r hr ↦ hw r hr)
  have hsq (r : ℝ) (hr : r ∈ Ioo a (2 * a)) :
      ‖F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)‖ ^ 2 = ‖F (r, 0)‖ ^ 2 / r ^ 3 := by
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ha.trans hr.1), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (ha.trans hr.1)), div_pow, div_pow,
      Real.sq_sqrt (ha.trans hr.1).le, div_div]
    congr 1
  have hA : (∫ r in Ioo a (2 * a), ‖F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      (1 / a ^ 3) * ∫ r in Ioo a (2 * a), ‖F (r, 0)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hW.integrable_norm_pow (by norm_num))
      ((hT.integrable_norm_pow (by norm_num)).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hsq r hr]
    simpa only [one_div, inv_mul_eq_div] using
      div_le_div_of_nonneg_left (sq_nonneg ‖F (r, 0)‖) (pow_pos ha 3)
        (pow_le_pow_left₀ ha.le hr.1.le 3)
  have hiF := hF0.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiD := hD0.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hE := (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
    (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨hW, hA.trans ((mul_le_mul_of_nonneg_left hTb (by positivity)).trans ?_)⟩
  calc
    _ = ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        ((1 / a ^ 4) * ‖F q‖ ^ 2 + (4 / a ^ 2) * ‖D q‖ ^ 2) := by
      rw [integral_add (hiF.const_mul _) (hiD.const_mul _), integral_const_mul,
        integral_const_mul]
      field_simp
    _ ≤ 16 * ∫ q in Ioo a (2 * a) ×ˢ Ioo (-a) a,
        (‖F q / (q.1 : ℂ) ^ 2‖ ^ 2 + ‖D q / (q.1 : ℂ)‖ ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_ae ((hiF.const_mul _).add (hiD.const_mul _)) (hE.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
      have hx : 0 < q.1 := ha.trans hq.1.1
      have h2 : q.1 ^ 2 ≤ 4 * a ^ 2 := by
        have := pow_le_pow_left₀ hx.le hq.1.2.le 2
        nlinarith
      have h4 : q.1 ^ 4 ≤ 16 * a ^ 4 := by
        have := pow_le_pow_left₀ hx.le hq.1.2.le 4
        nlinarith
      have hi2 : 4 / a ^ 2 ≤ 16 / q.1 ^ 2 :=
        (div_le_div_iff₀ (sq_pos_of_pos ha) (sq_pos_of_pos hx)).2 (by nlinarith)
      have hi4 : 1 / a ^ 4 ≤ 16 / q.1 ^ 4 :=
        (div_le_div_iff₀ (pow_pos ha 4) (pow_pos hx 4)).2 (by nlinarith)
      have hb := add_le_add (mul_le_mul_of_nonneg_right hi4 (sq_nonneg ‖F q‖))
        (mul_le_mul_of_nonneg_right hi2 (sq_nonneg ‖D q‖))
      simp only [Pi.add_apply, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx, div_pow]
      convert hb using 1
      ring

/-- A radial cone with an interior horizontal ray and radius measured by the
first coordinate. It is the affine shape of a small positive-cell corner. -/
def cartesianRayCone (R : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioo 0 R ∧ |q.2| < q.1}

/-- Shrinking rectangles give an actual weighted interior ray norm, using only
weighted bulk L² and a specified weak transverse derivative. -/
theorem weighted_cone_trace {R : ℝ} (hR : 0 < R) {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (cartesianRayCone R) 1 F D)
    (hc : ContinuousOn F (cartesianRayCone R))
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ) ^ 2) 2
      (volume.restrict (cartesianRayCone R)))
    (hD : MemLp (fun q ↦ D q / (q.1 : ℂ)) 2
      (volume.restrict (cartesianRayCone R))) :
    MemLp (fun r ↦ F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 R)) ∧
    (∫ r in Ioo 0 R, ‖F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      16 * ∫ q in cartesianRayCone R,
        (‖F q / (q.1 : ℂ) ^ 2‖ ^ 2 + ‖D q / (q.1 : ℂ)‖ ^ 2) := by
  let Q := cartesianRayCone R
  let G := fun q : ℝ × ℝ ↦ ‖F q / (q.1 : ℂ) ^ 2‖ ^ 2 + ‖D q / (q.1 : ℂ)‖ ^ 2
  let H := Q.indicator G
  let E := fun r : ℝ ↦ ∫ t : ℝ, H (r, t)
  let W := fun r ↦ F (r, 0) / (r : ℂ) / (Real.sqrt r : ℂ)
  have hQ : MeasurableSet Q :=
    (measurable_fst measurableSet_Ioo).inter
      (measurableSet_lt continuous_snd.abs.measurable measurable_fst)
  have hG : IntegrableOn G Q :=
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hH : Integrable H volume := (integrable_indicator_iff hQ).2 hG
  have hHp : Integrable H (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hH
  have hE : Integrable E volume := hHp.integral_prod_left
  have hHpos (q : ℝ × ℝ) : 0 ≤ H q := by
    exact indicator_nonneg (fun p _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) q
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
      (∫ r in s n, ‖W r‖ ^ 2) ≤ 16 * ∫ q in B n, G q := by
    have hw := hd.mono (hsub n)
    have hc' := hc.mono (hsub n)
    have hF' := hF.mono_measure (Measure.restrict_mono_set _ (hsub n))
    have hD' := hD.mono_measure (Measure.restrict_mono_set _ (hsub n))
    change HasWeakPartialOn (Ioo (e (n + 1)) (e n) ×ˢ Ioo (-e (n + 1)) (e (n + 1))) 1 F D at hw
    dsimp only [B, s] at hc' hF' hD'
    rw [← hstep n] at hw hc' hF' hD'
    simpa only [hstep n] using weighted_band_trace (hepos (n + 1)) hw hc' hF' hD'
  have hbound (n : ℕ) : (∫ r in s n, ‖W r‖ ^ 2) ≤ 16 * ∫ r in s n, E r := by
    apply (hband n).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
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
  have hW := memLp_two_of_cell_energy (fun _ ↦ measurableSet_Ioo) hdis (by norm_num : (0 : ℝ) ≤ 16)
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
      change (∫ r, ‖W r‖ ^ 2 ∂volume.restrict (Ioo 0 R)) = _
      rw [← hmeasure]
      exact hsW.tsum_eq.symm
    _ ≤ ∑' n, 16 * ∫ r in s n, E r :=
      hsW.summable.tsum_le_tsum hbound (hsE.mul_left 16).summable
    _ = 16 * ∫ r in ⋃ n, s n, E r := (hsE.mul_left 16).tsum_eq
    _ ≤ 16 * ∫ r, E r := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hE (Eventually.of_forall hEpos)) (by norm_num)
    _ = _ := by
      congr 1
      rw [← integral_prod H hHp, ← Measure.volume_eq_prod]
      exact integral_indicator hQ

end NoEmbeddedEigenvalues
