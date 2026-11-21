module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.CanonicalConeTrace
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceWeakGluing
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Critical one-sided traces at a Cartesian corner

Blueprint: `def:cartesian-half-cone`, `lem:half-cone-band-energy`,
`lem:one-sided-trace-energy`, `lem:boundary-weighted-band-trace`,
`lem:boundary-weighted-cone-trace`, `lem:critical-boundary-mode`.

A radius-sized rectangle adjacent to a boundary controls the canonical endpoint
trace by F/r and the unweighted normal derivative. Disjoint radial bands sum
these genuine energies. A trace with constant modulus therefore vanishes.
The trace is supplied as a canonical ACL trace on the bands; no raw boundary
values or continuous planar representative are assumed.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- An endpoint or interior trace estimate with the specified normal derivative. -/
theorem HasTransverseH1Trace.l2_estimate_of_weak_snd {l r a b t : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t chart F T)
    (hd : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 (F ∘ chart) D)
    (hD : MemLp D 2 (volume.restrict (Ioo l r ×ˢ Ioo a b))) :
    MemLp T 2 (volume.restrict (Ioo l r)) ∧
      (∫ s in Ioo l r, ‖T s‖ ^ 2) ≤
        (2 / (b - a)) * (∫ q in Ioo l r ×ˢ Ioo a b, ‖F (chart q)‖ ^ 2) +
          2 * (b - a) * ∫ q in Ioo l r ×ˢ Ioo a b, ‖D q‖ ^ 2 := by
  obtain ⟨G, hGm, hGF, hG, hGD, hT⟩ := h.with_weak_snd hd hD
  obtain ⟨hTL, hTb⟩ := hGD.l2_trace h.2.1 hGm hG hD t h.2.2.1
  refine ⟨hTL.ae_eq hT.symm, ?_⟩
  have hiT := integral_congr_ae (hT.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
  have hiF := integral_congr_ae (hGF.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
  dsimp only [Function.comp_def] at hiT hiF
  rw [hiT, ← hiF]
  exact hTb

/-- The positive-normal half of a Cartesian ray cone. -/
def cartesianHalfCone (R : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioo 0 R ∧ q.2 ∈ Ioo 0 q.1}

/-- A common half-cone density sums estimates on one-sided radial bands. -/
theorem memLp_two_of_half_cone_band_energy {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    {W : ℝ → ℂ} {E : ℝ × ℝ → ℝ}
    (hE : IntegrableOn E (cartesianHalfCone R))
    (hpos : ∀ q ∈ cartesianHalfCone R, 0 ≤ E q)
    (hBand : ∀ a : ℝ, 0 < a → 2 * a ≤ R →
      MemLp W 2 (volume.restrict (Ioo a (2 * a))) ∧
      (∫ r in Ioo a (2 * a), ‖W r‖ ^ 2) ≤
        K * ∫ q in Ioo a (2 * a) ×ˢ Ioo 0 a, E q) :
    MemLp W 2 (volume.restrict (Ioo 0 R)) ∧
      (∫ r in Ioo 0 R, ‖W r‖ ^ 2) ≤
        K * ∫ q in cartesianHalfCone R, E q := by
  let Q := cartesianHalfCone R
  let G := Q.indicator E
  have hQ : MeasurableSet Q :=
    (measurable_fst measurableSet_Ioo).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst))
  have hsub : Q ⊆ cartesianRayCone R := by
    intro q hq
    exact ⟨hq.1, by simpa only [abs_of_pos hq.2.1] using hq.2.2⟩
  have hG : Integrable G volume := (integrable_indicator_iff hQ).2 hE
  have h := memLp_two_of_cone_band_energy (W := W) hR hK hG.integrableOn
    (fun q _ ↦ indicator_nonneg hpos q) ?_
  · simpa only [G, setIntegral_indicator hQ, inter_eq_right.mpr hsub] using h
  intro a ha haR
  have hb : Ioo a (2 * a) ×ˢ Ioo 0 a ⊆ Q := by
    intro q hq
    exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans_le haR⟩, ⟨hq.2.1, hq.2.2.trans hq.1.1⟩⟩
  have heq : (Ioo a (2 * a) ×ˢ Ioo (-a) a) ∩ Q =
      Ioo a (2 * a) ×ˢ Ioo 0 a := by
    ext q
    constructor
    · rintro ⟨hq, hqQ⟩
      exact ⟨hq.1, hqQ.2.1, hq.2.2⟩
    · intro hq
      exact ⟨⟨hq.1, by linarith [hq.2.1], hq.2.2⟩, hb hq⟩
  simpa only [G, setIntegral_indicator hQ, heq] using hBand a ha haR

/-- The critical endpoint trace estimate on one radial band. -/
theorem boundary_weighted_band_trace {a : ℝ} (ha : 0 < a)
    {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo a (2 * a) ×ˢ Ioo 0 a) 1 F D)
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ)) 2
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo 0 a)))
    (hD : MemLp D 2 (volume.restrict (Ioo a (2 * a) ×ˢ Ioo 0 a)))
    (hT : HasTransverseH1Trace a (2 * a) 0 a 0 id F T) :
    MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) ∧
    (∫ r in Ioo a (2 * a), ‖T r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      8 * ∫ q in Ioo a (2 * a) ×ˢ Ioo 0 a,
        (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
  have hX : MemLp (fun q : ℝ × ℝ ↦ (q.1 : ℂ)) ⊤
      (volume.restrict (Ioo a (2 * a) ×ˢ Ioo 0 a)) := by
    apply memLp_top_of_bound (by fun_prop) (2 * a)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans hq.1.1)]
      using hq.1.2.le
  have hF0 : MemLp F 2 (volume.restrict (Ioo a (2 * a) ×ˢ Ioo 0 a)) := by
    apply (hX.mul hF).ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ha.trans hq.1.1).ne')
  obtain ⟨hTL, hTb⟩ := hT.l2_estimate_of_weak_snd (by simpa using hd) hD
  simp only [sub_zero, id_eq] at hTb
  have hWm := hTL.aestronglyMeasurable.div₀
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
  have hW : MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo a (2 * a))) := by
    apply hTL.of_le_mul hWm (c := 1 / Real.sqrt a)
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
      ((hTL.integrable_norm_pow (by norm_num)).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hsq r hr]
    simpa only [one_div, inv_mul_eq_div] using
      div_le_div_of_nonneg_left (sq_nonneg ‖T r‖) ha hr.1.le
  have hiF := hF0.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiD := hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hE := (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add hiD
  refine ⟨hW, hA.trans ((mul_le_mul_of_nonneg_left hTb (by positivity)).trans ?_)⟩
  calc
    _ = ∫ q in Ioo a (2 * a) ×ˢ Ioo 0 a,
        ((2 / a ^ 2) * ‖F q‖ ^ 2 + 2 * ‖D q‖ ^ 2) := by
      rw [integral_add (hiF.const_mul _) (hiD.const_mul _), integral_const_mul,
        integral_const_mul]
      field_simp
    _ ≤ 8 * ∫ q in Ioo a (2 * a) ×ˢ Ioo 0 a,
        (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_ae ((hiF.const_mul _).add (hiD.const_mul _)) (hE.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
      have hx : 0 < q.1 := ha.trans hq.1.1
      have h2 : q.1 ^ 2 ≤ 4 * a ^ 2 := by
        have := pow_le_pow_left₀ hx.le hq.1.2.le 2
        nlinarith
      have hi2 : 2 / a ^ 2 ≤ 8 / q.1 ^ 2 :=
        (div_le_div_iff₀ (sq_pos_of_pos ha) (sq_pos_of_pos hx)).2 (by nlinarith)
      have hb := add_le_add (mul_le_mul_of_nonneg_right hi2 (sq_nonneg ‖F q‖))
        (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 8) (sq_nonneg ‖D q‖))
      simp only [Pi.add_apply, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx, div_pow]
      convert hb using 1
      ring

/-- Specified canonical one-sided traces have finite critical boundary mass. -/
theorem boundary_weighted_cone_trace {R : ℝ} (hR : 0 < R)
    {F D : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hd : HasWeakPartialOn (cartesianHalfCone R) 1 F D)
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ)) 2
      (volume.restrict (cartesianHalfCone R)))
    (hD : MemLp D 2 (volume.restrict (cartesianHalfCone R)))
    (hT : ∀ a : ℝ, 0 < a → 2 * a ≤ R →
      HasTransverseH1Trace a (2 * a) 0 a 0 id F T) :
    MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 R)) ∧
    (∫ r in Ioo 0 R, ‖T r / (Real.sqrt r : ℂ)‖ ^ 2) ≤
      8 * ∫ q in cartesianHalfCone R,
        (‖F q / (q.1 : ℂ)‖ ^ 2 + ‖D q‖ ^ 2) := by
  apply memLp_two_of_half_cone_band_energy hR (by norm_num : (0 : ℝ) ≤ 8)
    ((hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
    (fun q _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
  intro a ha haR
  have hb : Ioo a (2 * a) ×ˢ Ioo 0 a ⊆ cartesianHalfCone R := by
    intro q hq
    exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans_le haR⟩, ⟨hq.2.1, hq.2.2.trans hq.1.1⟩⟩
  exact boundary_weighted_band_trace ha (hd.mono hb)
    (hF.mono_measure (Measure.restrict_mono_set _ hb))
    (hD.mono_measure (Measure.restrict_mono_set _ hb)) (hT a ha haR)

/-- Critical boundary mass excludes a nonzero constant-modulus mode. -/
theorem constant_modulus_eq_zero_of_critical_memLp {R c : ℝ} (hR : 0 < R)
    {T : ℝ → ℂ}
    (hT : MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 R)))
    (hc : ∀ᵐ r ∂(volume.restrict (Ioo 0 R)), ‖T r‖ = c) : c = 0 := by
  have hi : IntegrableOn (fun r ↦ c ^ 2 / r) (Ioo 0 R) := by
    apply (hT.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with r hr hri
    simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hri.1.le, hr]
  by_contra hz
  have hci : c ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hi' : IntegrableOn (fun r : ℝ ↦ r ^ (-1 : ℝ)) (Ioo 0 R) := by
    apply (hi.const_mul (c ^ 2)⁻¹).congr
    filter_upwards [] with r
    simp only [Real.rpow_neg_one]
    field_simp
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hR).1 hi'
  norm_num at this

/-- A common nonzero modulus is impossible even when canonical trace witnesses
are supplied separately on each radial band. No joint ACL family is selected. -/
theorem constant_modulus_boundary_trace_eq_zero {R : ℝ} (hR : 0 < R)
    {F D : ℝ × ℝ → ℂ} {z : ℂ}
    (hd : HasWeakPartialOn (cartesianHalfCone R) 1 F D)
    (hF : MemLp (fun q ↦ F q / (q.1 : ℂ)) 2
      (volume.restrict (cartesianHalfCone R)))
    (hD : MemLp D 2 (volume.restrict (cartesianHalfCone R)))
    (hBand : ∀ a : ℝ, 0 < a → 2 * a ≤ R → ∃ T : ℝ → ℂ,
      HasTransverseH1Trace a (2 * a) 0 a 0 id F T ∧
        ∀ᵐ r ∂(volume.restrict (Ioo a (2 * a))), ‖T r‖ = ‖z‖) : z = 0 := by
  have hm : MemLp (fun r ↦ z / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 R)) := by
    apply (memLp_two_of_half_cone_band_energy hR (by norm_num : (0 : ℝ) ≤ 8)
      ((hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
        (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
      (fun q _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) ?_).1
    intro a ha haR
    have hb : Ioo a (2 * a) ×ˢ Ioo 0 a ⊆ cartesianHalfCone R := by
      intro q hq
      exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans_le haR⟩, ⟨hq.2.1, hq.2.2.trans hq.1.1⟩⟩
    obtain ⟨T, hT, hTN⟩ := hBand a ha haR
    obtain ⟨hTL, hTB⟩ := boundary_weighted_band_trace ha (hd.mono hb)
      (hF.mono_measure (Measure.restrict_mono_set _ hb))
      (hD.mono_measure (Measure.restrict_mono_set _ hb)) hT
    have hWL : MemLp (fun r ↦ z / (Real.sqrt r : ℂ)) 2
        (volume.restrict (Ioo a (2 * a))) := by
      apply hTL.of_le_mul
        (measurable_const.div (Complex.measurable_ofReal.comp
          Real.continuous_sqrt.measurable)).aestronglyMeasurable (c := 1)
      filter_upwards [hTN] with r hr
      change ‖z / (Real.sqrt r : ℂ)‖ ≤ 1 * ‖T r / (Real.sqrt r : ℂ)‖
      simp only [norm_div, hr, one_mul, le_refl]
    refine ⟨hWL, ?_⟩
    have he : (∫ r in Ioo a (2 * a), ‖z / (Real.sqrt r : ℂ)‖ ^ 2) =
        ∫ r in Ioo a (2 * a), ‖T r / (Real.sqrt r : ℂ)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hTN] with r hr
      simp only [norm_div, hr]
    exact he ▸ hTB
  exact norm_eq_zero.mp (constant_modulus_eq_zero_of_critical_memLp hR hm
    (Eventually.of_forall fun _ ↦ rfl))

end NoEmbeddedEigenvalues
