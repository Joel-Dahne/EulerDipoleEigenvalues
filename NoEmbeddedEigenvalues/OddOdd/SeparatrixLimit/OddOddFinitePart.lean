module

public import NoEmbeddedEigenvalues.OddOdd.WeightedVirial.OddOddVirial
public import NoEmbeddedEigenvalues.OddOdd.SeparatrixLimit.OddOddBulkIntegrability

/-!
# Scalar finite part of the odd–odd bulk coefficient

The annular normal-field divergence gives the exact truncated coefficient
integral. Removing the center and then using the leading period asymptotic
isolates the logarithmic finite part.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

private def massFlux (s : ℝ) : ℝ := (8 - s ^ 3) / 3

private def normalFactor (s : ℝ) : ℝ := (s ^ 2 + 2 * s + 4) / 3

private theorem coefficient_factor (p : ℝ × ℝ) :
    ddF p = normalFactor (dipoleLift p) * normalCoeff p := by
  unfold ddF normalFactor normalCoeff
  ring

private theorem continuous_integrable_cell {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f cellSquare :=
  (hf.continuousOn.integrableOn_compact
    (isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)).isCompact_closure).mono_set
        subset_closure

/-- The potential coefficient is integrable on every positive truncation. -/
theorem ddF_integrable_truncation {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn ddF (ddTruncatedCell ε) := by
  have hb : Bornology.IsBounded (ddTruncatedCell ε) :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  have : IsFiniteMeasure (volume.restrict (ddTruncatedCell ε)) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have h := ddVirialDensity_integrable hε (u := 0) (e := fun _ ↦ (1 : ℂ))
    (ux := 0) (uy := 0) MemLp.zero (memLp_const _) MemLp.zero MemLp.zero
  apply h.congr_fun _ (isOpen_ddTruncatedCell ε).measurableSet
  intro p _
  simp [ddVirialDensity, ddMatrixForm, normalDeriv, tangentDeriv]

private theorem total_integrable_truncation {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun p ↦ ddF p + ddWeight p) (ddTruncatedCell ε) :=
  (ddF_integrable_truncation hε).add
    ((continuous_integrable_cell (by unfold ddWeight dipoleLift; fun_prop)).mono_set
      (fun _ hp ↦ hp.1))

private theorem coefficient_cutoff_identity {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    (∫ p in cellSquare, φ (dipoleLift p / 2) * (ddF p + ddWeight p)) =
      ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * massFlux (dipoleLift p) := by
  let χ := fun s ↦ φ (s / 2) * normalFactor s
  have hχ : ContDiff ℝ ∞ χ := by
    dsimp [χ, normalFactor]
    exact (hφ.comp (contDiff_id.div_const 2)).mul (by fun_prop)
  have hχs : ∀ s, χ s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b := by
    intro s hs
    have hs' : φ (s / 2) ≠ 0 := fun hz ↦ hs (by simp [χ, hz])
    obtain ⟨hL, hU⟩ := hsupp _ hs'
    constructor <;> linarith
  obtain ⟨hX, hY, -, hpX, hpY, -, -⟩ :=
    annularCutoff_normalField hχ (by linarith : 0 < 2 * a) (by linarith : 2 * b < 2) hχs
  let X := fun p ↦ χ (dipoleLift p) * normalField₁ p
  let Y := fun p ↦ χ (dipoleLift p) * normalField₂ p
  have hd : Continuous (divergence X Y) :=
    (contDiff_partialX (hX.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞))).continuous.add
      (contDiff_partialY (hY.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞))).continuous
  have hzero : squareIntegral (divergence X Y) = 0 := by
    unfold squareIntegral divergence
    rw [integral_add
      (integrableOn_periodSquare (contDiff_partialX (n := 0) (hX.of_le (by simp))).continuous)
      (integrableOn_periodSquare (contDiff_partialY (n := 0) (hY.of_le (by simp))).continuous)]
    change squareIntegral (partialX X) + squareIntegral (partialY Y) = 0
    rw [squareIntegral_partialX (hX.of_le (by simp)) hpX,
      squareIntegral_partialY (hY.of_le (by simp)) hpY, add_zero]
  have hvan : ∀ p, dipoleLift p ≤ 0 → divergence X Y p = 0 := by
    intro p hp
    have hev : ∀ᶠ q in 𝓝 p, χ (dipoleLift q) = 0 := by
      have hn : {q | dipoleLift q < 2 * a} ∈ 𝓝 p :=
        (isOpen_lt (by unfold dipoleLift; fun_prop) continuous_const).mem_nhds (by
          change dipoleLift p < 2 * a
          linarith)
      filter_upwards [hn] with q hq
      by_contra he
      linarith [(hχs _ he).1]
    have heX : ∀ᶠ q in 𝓝 p, X q = 0 := hev.mono fun q hq ↦ by simp [X, hq]
    have heY : ∀ᶠ q in 𝓝 p, Y q = 0 := hev.mono fun q hq ↦ by simp [Y, hq]
    simp [divergence, partialX_eq_zero_of_eventually heX, partialY_eq_zero_of_eventually heY]
  have hDivCell : (∫ p in cellSquare, divergence X Y p) = 0 := by
    exact (squareIntegral_eq_setIntegral_cellSquare (F := divergence X Y)
      (hpX.partialX.add hpY.partialY) hd.measurable hvan).symm.trans hzero
  have hχd (s : ℝ) :
      deriv χ s = deriv φ (s / 2) / 2 * normalFactor s +
        φ (s / 2) * ((2 * s + 2) / 3) := by
    have hf := ((hφ.differentiable (by simp) (s / 2)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2))
    have hg : HasDerivAt normalFactor ((2 * s + 2) / 3) s := by
      convert ((((hasDerivAt_id s).pow 2).add
        ((hasDerivAt_id s).const_mul 2)).add_const 4).div_const 3 using 1
      · funext t; dsimp [normalFactor]
      · simp
    change deriv ((φ ∘ fun x : ℝ ↦ x / 2) * normalFactor) s = _
    simpa [div_eq_mul_inv] using (hf.mul hg).deriv
  have hid (p : ℝ × ℝ) :
      φ (dipoleLift p / 2) * (ddF p + ddWeight p) =
        divergence X Y p + deriv φ (dipoleLift p / 2) / 2 * massFlux (dipoleLift p) := by
    have h := (cutoff_normalField_algebra hχ
      (by linarith : 0 < 2 * a) (by linarith : 2 * b < 2) hχs p).1
    change χ (dipoleLift p) * normalCoeff p - divergence X Y p =
      -χ (dipoleLift p) - (dipoleLift p - 2) * deriv χ (dipoleLift p) at h
    rw [hχd] at h
    rw [coefficient_factor]
    dsimp [χ, normalFactor, massFlux, ddWeight] at h ⊢
    linear_combination h
  have hi : IntegrableOn (fun p ↦ deriv φ (dipoleLift p / 2) / 2 *
      massFlux (dipoleLift p)) cellSquare :=
    continuous_integrable_cell (by
      have hc := hφ.continuous_deriv (by simp)
      unfold massFlux dipoleLift
      fun_prop)
  calc _ = ∫ p in cellSquare, divergence X Y p +
      deriv φ (dipoleLift p / 2) / 2 * massFlux (dipoleLift p) :=
        setIntegral_congr_fun isOpen_cellSquare.measurableSet fun p _ ↦ hid p
       _ = _ := by
         rw [integral_add (continuous_integrable_cell hd) hi, hDivCell, zero_add]

private theorem level_massFlux {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    levelIntegral h (fun p ↦ massFlux (dipoleLift p)) =
      massFlux (2 * h) * orbitPeriod h := by
  unfold levelIntegral
  simp_rw [dipoleLift_dipoleOrbit h0 h1]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_comm]

private theorem massFlux_center :
    Tendsto (fun h ↦ massFlux (2 * h) * orbitPeriod h) (𝓝[<] 1) (𝓝 0) := by
  have hlim : Tendsto (fun h : ℝ ↦ 16 * |massFlux (2 * h)|) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ ↦ 16 * |massFlux (2 * h)|) := by
      unfold massFlux; fun_prop
    convert (hc.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ))) using 1
    norm_num [massFlux]
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with h hh
  have h0 : 0 < h := by linarith [hh.1]
  have hp := orbitPeriod_pos h0 hh.2
  have hb : orbitPeriod h ≤ 16 := by
    unfold orbitPeriod
    have hi := eighthPeriod_le_inv h0 hh.2
    have hi' : 1 / h ≤ 2 := (div_le_iff₀ h0).mpr (by linarith [hh.1])
    linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp.le]
  nlinarith [abs_nonneg (massFlux (2 * h))]

private theorem coefficient_annular :
    ∃ N : Set ℝ, volume N = 0 ∧
      ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
        (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'},
          ddF p + ddWeight p) =
        massFlux (2 * h) * orbitPeriod h - massFlux (2 * h') * orbitPeriod h' := by
  obtain ⟨N, hN, hann⟩ := annular_virial_of_cutoff_identity
    (J := fun p ↦ ddF p + ddWeight p) (B := fun p ↦ massFlux (dipoleLift p))
    (fun a b ha _ ↦ (total_integrable_truncation ha).mono_set fun p hp ↦
      ⟨hp.1, by linarith [hp.2.1]⟩)
    (fun _ _ _ _ ↦ (continuous_integrable_cell (by unfold massFlux dipoleLift; fun_prop)).mono_set
      (fun _ hp ↦ hp.1))
    (fun φ hφ a b ha hb hsupp ↦ coefficient_cutoff_identity hφ ha hb hsupp)
  refine ⟨N, hN, fun h h' h0 hhh' h'1 hn h'n ↦ ?_⟩
  rw [← level_massFlux h0 (hhh'.trans h'1), ← level_massFlux (h0.trans hhh') h'1]
  exact hann h h' h0 hhh' h'1 hn h'n

private theorem ae_dipole_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ, dipoleLift p ≠ c := by
  have hcos (z : ℝ) : {y : ℝ | cos y = z}.Countable := by
    by_cases he : ∃ y : ℝ, cos y = z
    · obtain ⟨x, hx⟩ := he
      apply ((Set.countable_range (fun k : ℤ ↦ 2 * k * π + x)).union
        (Set.countable_range (fun k : ℤ ↦ 2 * k * π - x))).mono
      intro y hy
      obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.mp (hx.trans hy.symm)
      · exact Or.inl ⟨k, hk.symm⟩
      · exact Or.inr ⟨k, hk.symm⟩
    · have : {y : ℝ | cos y = z} = ∅ := by
        ext y
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hy ↦ he ⟨y, hy⟩
      rw [this]
      exact countable_empty
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae (by unfold dipoleLift; measurability)).mpr
  exact Eventually.of_forall fun x ↦ by
    rw [ae_iff]
    have hnull := (hcos (c - cos x)).measure_zero volume
    apply measure_mono_null _ hnull
    intro y hy
    change ¬ dipoleLift (x, y) ≠ c at hy
    change cos y = c - cos x
    push Not at hy
    unfold dipoleLift at hy
    linarith

private theorem continuousAt_truncated_integral {f : ℝ × ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : IntegrableOn f (ddTruncatedCell (a / 2))) :
    ContinuousAt (fun ε ↦ ∫ p in ddTruncatedCell ε, f p) a := by
  let A := ddTruncatedCell (a / 2)
  have hm (ε : ℝ) : MeasurableSet {p | ε < dipoleLift p} :=
    measurableSet_lt measurable_const (by unfold dipoleLift; fun_prop)
  have heq : ∀ᶠ ε in 𝓝 a,
      (∫ p in A, {p | ε < dipoleLift p}.indicator f p) = ∫ p in ddTruncatedCell ε, f p := by
    filter_upwards [Ioi_mem_nhds (by linarith : a / 2 < a)] with ε hε
    rw [integral_indicator (hm ε), Measure.restrict_restrict (hm ε)]
    have hset : {p | ε < dipoleLift p} ∩ A = ddTruncatedCell ε := by
      ext p
      change (ε < dipoleLift p ∧ p ∈ cellSquare ∧ a / 2 < dipoleLift p) ↔
        p ∈ cellSquare ∧ ε < dipoleLift p
      constructor
      · exact fun hp ↦ ⟨hp.2.1, hp.1⟩
      · exact fun hp ↦ ⟨hp.2, hp.1, lt_trans hε hp.2⟩
    rw [hset]
  have hlim : Tendsto (fun ε ↦ ∫ p in A, {p | ε < dipoleLift p}.indicator f p)
      (𝓝 a) (𝓝 (∫ p in A, {p | a < dipoleLift p}.indicator f p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p ↦ ‖f p‖)
    · exact Eventually.of_forall fun ε ↦ hf.aestronglyMeasurable.indicator (hm ε)
    · apply Eventually.of_forall
      intro ε
      exact Eventually.of_forall fun p ↦ norm_indicator_le_norm_self f p
    · exact hf.norm
    · filter_upwards [ae_restrict_of_ae (ae_dipole_ne a)] with p hp
      rcases hp.lt_or_gt with hp | hp
      · rw [indicator_of_notMem (show p ∉ {p | a < dipoleLift p} from not_lt.mpr hp.le)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_nhds hp] with ε hε
        change dipoleLift p < ε at hε
        exact (indicator_of_notMem (show p ∉ {p | ε < dipoleLift p} from not_lt.mpr hε.le) f).symm
      · rw [indicator_of_mem (show p ∈ {p | a < dipoleLift p} from hp)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Iio_mem_nhds hp] with ε hε
        exact (indicator_of_mem (show p ∈ {p | ε < dipoleLift p} from hε) f).symm
  change Tendsto (fun ε ↦ ∫ p in ddTruncatedCell ε, f p) (𝓝 a)
    (𝓝 (∫ p in ddTruncatedCell a, f p))
  rw [← heq.self_of_nhds]
  exact hlim.congr' heq

private theorem truncated_total_integral :
    ∀ h ∈ Ioo (0 : ℝ) 1, (∫ p in ddTruncatedCell (2 * h), ddF p + ddWeight p) =
      massFlux (2 * h) * orbitPeriod h := by
  obtain ⟨N, hN, hann⟩ := coefficient_annular
  obtain ⟨seq, hseq, hlim, -⟩ := exists_seq_one_sub_mul_tendsto_zero
    (g := fun _ ↦ 0) (by simp) hN
  have hseq' : Tendsto seq atTop (𝓝[<] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun j ↦ (hseq j).1.2⟩
  have hflux := massFlux_center.comp hseq'
  have hlt2 : ∀ᵐ p : ℝ × ℝ, dipoleLift p < 2 := by
    filter_upwards [ae_dipole_ne 2] with p hp
    have hb : dipoleLift p ≤ 2 := by
      unfold dipoleLift
      linarith [cos_le_one p.1, cos_le_one p.2]
    exact lt_of_le_of_ne hb hp
  have hgood : ∀ h ∈ Ioo (0 : ℝ) 1, h ∉ N →
      (∫ p in ddTruncatedCell (2 * h), ddF p + ddWeight p) =
        massFlux (2 * h) * orbitPeriod h := by
    intro h hh hn
    let A := ddTruncatedCell (2 * h)
    let J := fun p ↦ ddF p + ddWeight p
    have hi := total_integrable_truncation (mul_pos (by norm_num : (0 : ℝ) < 2) hh.1)
    have hm (b : ℝ) : MeasurableSet {p | dipoleLift p < 2 * b} :=
      measurableSet_lt (by unfold dipoleLift; fun_prop) measurable_const
    have hset (j : ℕ) : {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧
        dipoleLift p < 2 * seq j} = A ∩ {p | dipoleLift p < 2 * seq j} := by
      ext p
      simp only [A, ddTruncatedCell, mem_ofPred_eq, mem_inter_iff, and_assoc]
    have hev : ∀ᶠ j in atTop, h < seq j := hlim.eventually (Ioi_mem_nhds hh.2)
    have hlim1 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < 2 * seq j}, J p)
        atTop (𝓝 (massFlux (2 * h) * orbitPeriod h)) := by
      have hd := (tendsto_const_nhds (x := massFlux (2 * h) * orbitPeriod h)).sub hflux
      rw [sub_zero] at hd
      apply hd.congr'
      filter_upwards [hev] with j hj
      rw [← hset]
      exact (hann h (seq j) hh.1 hj (hseq j).1.2 hn (hseq j).2).symm
    have hlim2 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < 2 * seq j}, J p)
        atTop (𝓝 (∫ p in A, J p)) := by
      have hind (j : ℕ) : (∫ p in A ∩ {p | dipoleLift p < 2 * seq j}, J p) =
          ∫ p in A, {p | dipoleLift p < 2 * seq j}.indicator J p := by
        rw [Set.inter_comm A, ← Measure.restrict_restrict (hm _), integral_indicator (hm _)]
      simp_rw [hind]
      apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖J p‖)
      · exact fun j ↦ hi.aestronglyMeasurable.indicator (hm _)
      · exact hi.norm
      · exact fun j ↦ Eventually.of_forall fun p ↦ norm_indicator_le_norm_self J p
      · filter_upwards [ae_restrict_of_ae hlt2] with p hp
        apply tendsto_const_nhds.congr'
        have h2 : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝 2) := by
          simpa using hlim.const_mul 2
        filter_upwards [h2.eventually (Ioi_mem_nhds hp)] with j hj
        exact (indicator_of_mem (show p ∈ {p | dipoleLift p < 2 * seq j} from hj) J).symm
    exact tendsto_nhds_unique hlim2 hlim1
  have hA : ContinuousOn (fun h ↦ ∫ p in ddTruncatedCell (2 * h), ddF p + ddWeight p)
      (Ioo (0 : ℝ) 1) := by
    intro h hh
    have hc := continuousAt_truncated_integral (a := 2 * h)
      (by linarith [hh.1] : 0 < 2 * h)
      (total_integrable_truncation (by linarith [hh.1] : 0 < 2 * h / 2))
    exact (hc.comp (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hB : ContinuousOn (fun h ↦ massFlux (2 * h) * orbitPeriod h) (Ioo (0 : ℝ) 1) :=
    (show Continuous (fun h : ℝ ↦ massFlux (2 * h)) by unfold massFlux; fun_prop).continuousOn.mul
      continuousOn_orbitPeriod
  have hae : (fun h ↦ ∫ p in ddTruncatedCell (2 * h), ddF p + ddWeight p) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] fun h ↦ massFlux (2 * h) * orbitPeriod h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hN)] with h hh hn
    exact hgood h hh hn
  exact volume.eqOn_open_of_ae_eq hae isOpen_Ioo hA hB

/-- The exact positive-truncation coefficient integral, before taking its finite part. -/
theorem ddF_integral_truncation {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    (∫ p in ddTruncatedCell ε, ddF p) =
      (8 - ε ^ 3) / 3 * orbitPeriod (ε / 2) -
        ∫ p in ddTruncatedCell ε, ddWeight p := by
  have hiW := (continuous_integrable_cell (f := ddWeight)
    (by unfold ddWeight dipoleLift; fun_prop)).mono_set
    (show ddTruncatedCell ε ⊆ cellSquare from fun _ hp ↦ hp.1)
  have h := truncated_total_integral (ε / 2) ⟨by linarith [hε.1], by linarith [hε.2]⟩
  rw [show 2 * (ε / 2) = ε by ring, integral_add (ddF_integrable_truncation hε.1) hiW] at h
  dsimp [massFlux] at h
  linarith

/-- Exact truncated coefficient integral and its scalar finite part. -/
theorem dd_finite_part :
    (∀ ε ∈ Ioo (0 : ℝ) 2,
      (∫ p in ddTruncatedCell ε, ddF p) =
        (8 - ε ^ 3) / 3 * orbitPeriod (ε / 2) -
          ∫ p in ddTruncatedCell ε, ddWeight p) ∧
    Tendsto (fun ε ↦ (∫ p in ddTruncatedCell ε, ddF p) -
      (32 / 3 : ℝ) * Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 ((32 / 3 : ℝ) * Real.log 8 - 2 * Real.pi ^ 2)) := by
  refine ⟨fun _ hε ↦ ddF_integral_truncation hε, ?_⟩
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hscale : Tendsto (fun ε : ℝ ↦ ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hid.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change (0 : ℝ) < ε / 2
      exact div_pos hε (by norm_num)
  have hP : Tendsto (fun ε ↦ orbitPeriod (ε / 2) - 4 * log (8 / ε))
      (𝓝[>] 0) (𝓝 0) := by
    apply (orbitPeriod_leading_asymptotic.comp hscale).congr'
    exact Eventually.of_forall fun ε ↦ by
      simp only [Function.comp_apply]
      congr 3
      ring
  have hK : Tendsto massFlux (𝓝[>] 0) (𝓝 (8 / 3)) := by
    have hc : Continuous massFlux := by unfold massFlux; fun_prop
    simpa [massFlux] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun ε : ℝ ↦ ε ^ 3 * log ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [rpow_ofNat, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 3) (by norm_num))
  have hsmall : Tendsto (fun ε : ℝ ↦ ε ^ 3 * log (8 / ε)) (𝓝[>] 0) (𝓝 0) := by
    have hh := ((hid.pow 3).const_mul (log 8)).sub hlog
    simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero, sub_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [log_div (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hε)]
    ring
  have hW : Tendsto (fun ε ↦ ∫ p in ddTruncatedCell ε, ddWeight p)
      (𝓝[>] 0) (𝓝 (2 * π ^ 2)) := by
    rw [← integral_cellSquare_ddWeight]
    exact tendsto_ddTruncatedCell_integral
      (continuous_integrable_cell (by unfold ddWeight dipoleLift; fun_prop))
  have hlim : Tendsto (fun ε ↦
      massFlux ε * (orbitPeriod (ε / 2) - 4 * log (8 / ε)) -
        (4 / 3 : ℝ) * (ε ^ 3 * log (8 / ε)) + (32 / 3 : ℝ) * log 8 -
          ∫ p in ddTruncatedCell ε, ddWeight p) (𝓝[>] 0)
      (𝓝 ((32 / 3 : ℝ) * log 8 - 2 * π ^ 2)) := by
    simpa only [mul_zero, zero_sub, zero_add, sub_zero] using
      (((hK.mul hP).sub (hsmall.const_mul (4 / 3))).add_const ((32 / 3 : ℝ) * log 8)).sub hW
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with ε hε
  rw [ddF_integral_truncation hε, log_div (by norm_num : (8 : ℝ) ≠ 0) hε.1.ne',
    one_div, log_inv]
  unfold massFlux
  ring

end NoEmbeddedEigenvalues
