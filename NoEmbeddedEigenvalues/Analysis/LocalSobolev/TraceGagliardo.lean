module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceH2
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.HardyAverage

/-!
# Fractional traces by averaged rectangular paths

Blueprint: `lem:trace-gagliardo`.

The direct route compares trace values through horizontal slices at heights
proportional to their separation. Hardy's averaging inequality controls the
vertical increments; horizontal increments are controlled by the tangential
energy. This avoids extension and smooth-density prerequisites. The parallelogram
identity cancels the diagonal Jacobian, giving the uniform constant
`36 * (b₂ - b₀) / (a₁ - a₀) + 12 * (a₁ - a₀) / (b₂ - b₀)`.
The final theorem retains the original global representative and a.e. transverse
ACL/derivative guarantees; line values are not freely reassigned.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval

/-- Rewrite a double integral in terms of its horizontal displacement. -/
theorem lintegral_pair_eq_shift {K : ℝ × ℝ → ℝ≥0∞} (hK : Measurable K) :
    (∫⁻ x, ∫⁻ y, K (x, y)) = ∫⁻ r, ∫⁻ x, K (x, x + r) := by
  calc
    _ = ∫⁻ x, ∫⁻ r, K (x, x + r) := by
      congr 1
      funext x
      exact (lintegral_add_left_eq_self (fun y ↦ K (x, y)) x).symm
    _ = _ := lintegral_lintegral_swap (by fun_prop)

/-- Integrating an even function over the line is twice its positive-half integral. -/
theorem lintegral_eq_two_Ioi_of_even {f : ℝ → ℝ≥0∞} (hf : ∀ r, f (-r) = f r) :
    (∫⁻ r, f r) = 2 * ∫⁻ r in Ioi 0, f r := by
  have hn : (∫⁻ r in Iio 0, f r) = ∫⁻ r in Ioi 0, f r := by
    rw [← lintegral_indicator measurableSet_Iio,
      ← lintegral_neg_eq_self (fun r ↦ (Iio 0).indicator f r),
      ← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext r
    by_cases hr : 0 < r
    · simp [hr, hf r]
    · simp [hr]
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi,
    ← setLIntegral_congr Iio_ae_eq_Iic, hn, two_mul]

/-- Symmetry of a pair kernel reduces its displacement integral to positive shifts. -/
theorem lintegral_pair_eq_two_pos_shifts {K : ℝ × ℝ → ℝ≥0∞} (hK : Measurable K)
    (hKs : ∀ x y, K (y, x) = K (x, y)) :
    (∫⁻ x, ∫⁻ y, K (x, y)) = 2 * ∫⁻ r in Ioi 0, ∫⁻ x, K (x, x + r) := by
  rw [lintegral_pair_eq_shift hK]
  apply lintegral_eq_two_Ioi_of_even
  intro r
  calc
    _ = ∫⁻ x, K (x + r, x + r + -r) :=
      (lintegral_add_right_eq_self (fun x ↦ K (x, x + -r)) r).symm
    _ = _ := by simp only [add_neg_cancel_right, hKs]

/-- Fubini for a moving interval: every point is covered by a set of starting
points of length `r`. -/
theorem lintegral_moving_interval {E : ℝ → ℝ≥0∞} (hE : Measurable E)
    {r : ℝ} :
    (∫⁻ a, ∫⁻ t in Ioo a (a + r), E t) = ENNReal.ofReal r * ∫⁻ t, E t := by
  let A : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 < p.1 + r}
  have hAm : MeasurableSet A := by
    exact (isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd (continuous_fst.add continuous_const)).measurableSet
  calc
    _ = ∫⁻ a, ∫⁻ t, A.indicator (fun p ↦ E p.2) (a, t) := by
      congr 1
      funext a
      rw [← lintegral_indicator measurableSet_Ioo]
      rfl
    _ = ∫⁻ t, ∫⁻ a, A.indicator (fun p ↦ E p.2) (a, t) :=
      lintegral_lintegral_swap ((hE.comp measurable_snd).indicator hAm).aemeasurable
    _ = ∫⁻ t, ∫⁻ a in Ioo (t - r) t, E t := by
      congr 1
      funext t
      rw [← lintegral_indicator measurableSet_Ioo]
      congr 1
      funext a
      have he : (a, t) ∈ A ↔ a ∈ Ioo (t - r) t := by
        change (a < t ∧ t < a + r) ↔ t - r < a ∧ a < t
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      simp only [indicator_apply, he]
    _ = _ := by
      simp_rw [setLIntegral_const, Real.volume_Ioo, sub_sub_cancel]
      rw [lintegral_mul_const _ hE, mul_comm]

/-- Integrated horizontal increments cost `r²` times the derivative energy.
Only interior values of the interval representative are used. -/
theorem HasIntervalH1.lintegral_sq_sub_translate_le {a₀ a₁ r : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a₀ a₁ F D) (ha : a₀ < a₁) (hr : 0 < r) :
    (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖F (a + r) - F a‖ ^ 2)) ≤
      ENNReal.ofReal (r ^ 2) * ∫⁻ t in Ioo a₀ a₁, ENNReal.ofReal (‖D t‖ ^ 2) := by
  let D₀ := intervalZeroExtension a₀ a₁ D
  have hD₀ : MemLp D₀ 2 volume := memLp_intervalZeroExtension h.memLp_derivative
  let M := hD₀.aestronglyMeasurable.mk D₀
  have hM : Measurable M := hD₀.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : D₀ =ᵐ[volume] M := hD₀.aestronglyMeasurable.ae_eq_mk
  have hML : MemLp M 2 volume := hD₀.ae_eq he
  have hE : (∫⁻ t, ENNReal.ofReal (‖M t‖ ^ 2)) =
      ∫⁻ t in Ioo a₀ a₁, ENNReal.ofReal (‖D t‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards [he] with t ht
    rw [← ht]
    by_cases hti : t ∈ Ioo a₀ a₁ <;> simp [D₀, intervalZeroExtension, hti]
  have hpoint : ∀ a ∈ Ioo a₀ (a₁ - r),
      ENNReal.ofReal (‖F (a + r) - F a‖ ^ 2) ≤
        ENNReal.ofReal r * ∫⁻ t in Ioo a (a + r), ENNReal.ofReal (‖M t‖ ^ 2) := by
    intro a haI
    have ha0 : a ∈ Ioo a₀ a₁ := ⟨haI.1, by linarith [haI.2]⟩
    have har : a + r ∈ Ioo a₀ a₁ := ⟨by linarith [haI.1], by linarith [haI.2]⟩
    have hsub : Ioo a (a + r) ⊆ Ioo a₀ a₁ :=
      Ioo_subset_Ioo ha0.1.le har.2.le
    have hi := h.extension_sub_sq_le ha (Ioo_subset_Icc_self ha0)
      (Ioo_subset_Icc_self har) (by linarith : a ≤ a + r)
    rw [h.extension_eq ha ha0, h.extension_eq ha har,
      intervalIntegral.integral_of_le (by linarith : a ≤ a + r),
      integral_Ioc_eq_integral_Ioo, add_sub_cancel_left] at hi
    have hchange : (∫ t in Ioo a (a + r), ‖D t‖ ^ 2) =
        ∫ t in Ioo a (a + r), ‖M t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioo] with t ht hti
      have heD : D₀ t = D t := indicator_of_mem (hsub hti) D
      rw [← ht, heD]
    rw [hchange] at hi
    calc
      _ ≤ ENNReal.ofReal (r * ∫ t in Ioo a (a + r), ‖M t‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hi
      _ = _ := by
        rw [ENNReal.ofReal_mul hr.le,
          ofReal_integral_eq_lintegral_ofReal hML.norm.integrable_sq.restrict
            (Eventually.of_forall (fun t ↦ sq_nonneg ‖M t‖))]
  calc
    _ ≤ ∫⁻ a in Ioo a₀ (a₁ - r),
        ENNReal.ofReal r * ∫⁻ t in Ioo a (a + r), ENNReal.ofReal (‖M t‖ ^ 2) :=
      setLIntegral_mono' measurableSet_Ioo hpoint
    _ ≤ ∫⁻ a, ENNReal.ofReal r *
        ∫⁻ t in Ioo a (a + r), ENNReal.ofReal (‖M t‖ ^ 2) :=
      setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_moving_interval (by fun_prop),
        ← mul_assoc, ← pow_two, ← ENNReal.ofReal_pow hr.le, hE]

/-- A one-sided vertical increment has finite Hardy energy, controlled by
the derivative on that side of the trace line. -/
theorem HasIntervalH1.lintegral_sq_sub_div_sq_le {b₁ b₂ b₀ : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 b₁ b₂ F D) (hb₀ : b₀ ∈ Ioo b₁ b₂) :
    (∫⁻ t in Ioo 0 (b₂ - b₀), ENNReal.ofReal (‖F (b₀ + t) - F b₀‖ ^ 2 / t ^ 2)) ≤
      4 * ∫⁻ b in Ioo b₀ b₂, ENNReal.ofReal (‖D b‖ ^ 2) := by
  let D₀ := intervalZeroExtension b₀ b₂ D
  have hDL : MemLp D 2 (volume.restrict (Ioo b₀ b₂)) :=
    h.memLp_derivative.mono_measure (Measure.restrict_mono
      (Ioo_subset_Ioo hb₀.1.le le_rfl) le_rfl)
  have hDi : Integrable D₀ := integrable_intervalZeroExtension hDL
  let E := fun t ↦ D₀ (b₀ + t)
  have hEi : Integrable E := hDi.comp_add_left b₀
  have hprim : ∀ t ∈ Ioo 0 (b₂ - b₀),
      (∫ s in (0 : ℝ)..t, E s) = F (b₀ + t) - F b₀ := by
    intro t ht
    have hbt : b₀ + t ∈ Ioo b₁ b₂ := ⟨by linarith [hb₀.1, ht.1], by linarith [ht.2]⟩
    change (∫ s in (0 : ℝ)..t, D₀ (b₀ + s)) = _
    rw [intervalIntegral.integral_comp_add_left, add_zero]
    rw [show (∫ s in b₀..b₀ + t, D₀ s) = ∫ s in b₀..b₀ + t, D s from
      intervalIntegral_intervalZeroExtension D ⟨le_rfl, hb₀.2.le⟩
        ⟨by linarith [ht.1], hbt.2.le⟩]
    exact h.integral_eq_sub hb₀ hbt
  have hDE : (∫⁻ t, ENNReal.ofReal (‖E t‖ ^ 2)) =
      ∫⁻ b in Ioo b₀ b₂, ENNReal.ofReal (‖D b‖ ^ 2) := by
    change (∫⁻ t, ENNReal.ofReal (‖D₀ (b₀ + t)‖ ^ 2)) = _
    rw [lintegral_add_left_eq_self (fun t ↦ ENNReal.ofReal (‖D₀ t‖ ^ 2)) b₀,
      ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext t
    by_cases ht : t ∈ Ioo b₀ b₂ <;> simp [D₀, intervalZeroExtension, ht]
  calc
    _ = ∫⁻ t in Ioo 0 (b₂ - b₀),
        ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, E s‖ ^ 2 / t ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [hprim t ht]
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, E s‖ ^ 2 / t ^ 2) :=
      lintegral_mono_set (fun _ ht ↦ ht.1)
    _ ≤ 4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (‖E t‖ ^ 2) :=
      lintegral_sq_primitive_div_sq_le_of_integrable hEi
    _ ≤ 4 * ∫⁻ t, ENNReal.ofReal (‖E t‖ ^ 2) := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by rw [hDE]

/-- The squared distance between endpoints is controlled by the three sides
of a rectangular comparison path. -/
theorem norm_sub_sq_le_three (u v x y : ℂ) :
    ‖u - v‖ ^ 2 ≤ 3 * (‖u - x‖ ^ 2 + ‖x - y‖ ^ 2 + ‖y - v‖ ^ 2) := by
  have he : u - v = (u - x) + (x - y) + (y - v) := by abel
  have hn : ‖u - v‖ ≤ ‖u - x‖ + ‖x - y‖ + ‖y - v‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  nlinarith [sq_nonneg (‖u - x‖ - ‖x - y‖),
    sq_nonneg (‖u - x‖ - ‖y - v‖), sq_nonneg (‖x - y‖ - ‖y - v‖)]

/-- Translation of the shorter interval stays inside the original interval. -/
theorem lintegral_translate_interval_le (f : ℝ → ℝ≥0∞) {a₀ a₁ r : ℝ} (hr : 0 < r) :
    (∫⁻ a in Ioo a₀ (a₁ - r), f (a + r)) ≤ ∫⁻ a in Ioo a₀ a₁, f a := by
  have hsub : Ioo a₀ (a₁ - r) ⊆ (fun a ↦ a + r) ⁻¹' Ioo a₀ a₁ := by
    intro a ha
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  exact (lintegral_mono_set hsub).trans_eq
    ((measurePreserving_add_right volume r).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addRight r).measurableEmbedding f (Ioo a₀ a₁))

/-- Null-set changes of a line representative do not alter its integrated
horizontal increments, including the shifted endpoint. -/
theorem lintegral_sq_sub_translate_congr {a₀ a₁ r : ℝ} {F G : ℝ → ℂ} (hr : 0 < r)
    (hFG : F =ᵐ[volume.restrict (Ioo a₀ a₁)] G) :
    (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖F (a + r) - F a‖ ^ 2)) =
      ∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖G (a + r) - G a‖ ^ 2) := by
  have h0 := (ae_restrict_iff' measurableSet_Ioo).1 hFG
  have hshift := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae h0
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae h0, ae_restrict_of_ae hshift,
    ae_restrict_mem measurableSet_Ioo] with a ha har haI
  rw [ha ⟨haI.1, by linarith [haI.2]⟩,
    har ⟨by linarith [haI.1], by linarith [haI.2]⟩]

/-- On almost every horizontal line, any a.e. representative satisfies the
integrated translation bound for its tangential weak derivative. -/
theorem HasWeakPartialOn.ae_horizontal_translate_le {a₀ a₁ b₁ b₂ : ℝ}
    {F A G : ℝ × ℝ → ℂ} (ha : a₀ < a₁) (hb : b₁ < b₂)
    (hd : HasWeakPartialOn (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) 0 F A)
    (hF : MemLp F 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hA : MemLp A 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hGF : G =ᵐ[volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)] F) :
    ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)), ∀ r, 0 < r →
      (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖G (a + r, b) - G (a, b)‖ ^ 2)) ≤
        ENNReal.ofReal (r ^ 2) * ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b)‖ ^ 2) := by
  have hs : Prod.swap ⁻¹' (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) = Ioo b₁ b₂ ×ˢ Ioo a₀ a₁ := by
    ext p; simp only [mem_preimage, mem_prod, Prod.fst_swap, Prod.snd_swap, and_comm]
  have hFo : IsOpen (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) := isOpen_Ioo.prod isOpen_Ioo
  have hFs := memLp_comp_swap hFo.measurableSet hF
  have hAs := memLp_comp_swap hFo.measurableSet hA
  have hds := hd.comp_swap_fst hFo
  rw [hs] at hFs hAs hds
  obtain ⟨K, -, hKF, hK⟩ := hds.exists_acl_sections isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 ha)
  have hKL := hFs.ae_eq hKF.symm
  have hGFp : G =ᵐ[(volume.restrict (Ioo a₀ a₁)).prod (volume.restrict (Ioo b₁ b₂))] F := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hGF
  have hGFs : (G ∘ Prod.swap) =ᵐ[volume.restrict (Ioo b₁ b₂ ×ˢ Ioo a₀ a₁)]
      (F ∘ Prod.swap) := by
    have h := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hGFp
    change ∀ᵐ p ∂(volume.restrict (Ioo b₁ b₂ ×ˢ Ioo a₀ a₁)), G p.swap = F p.swap
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Function.comp_apply] using h
  have hKGp : K =ᵐ[(volume.restrict (Ioo b₁ b₂)).prod (volume.restrict (Ioo a₀ a₁))]
      (G ∘ Prod.swap) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hKF.trans hGFs.symm
  filter_upwards [hK.ae_hasIntervalH1 hKL hAs, Measure.ae_ae_of_ae_prod hKGp] with b hbK hbKG
  intro r hr
  have hbKG' : (fun a ↦ K (b, a)) =ᵐ[volume.restrict (Ioo a₀ a₁)] (fun a ↦ G (a, b)) := hbKG
  rw [lintegral_sq_sub_translate_congr hr hbKG'.symm]
  exact hbK.lintegral_sq_sub_translate_le ha hr

/-- The interval-restricted displacement formula for a symmetric kernel. -/
theorem lintegral_interval_pair_eq_two_pos_shifts {K : ℝ × ℝ → ℝ≥0∞}
    (hK : Measurable K) (hKs : ∀ x y, K (y, x) = K (x, y)) (a₀ a₁ : ℝ) :
    (∫⁻ x in Ioo a₀ a₁, ∫⁻ y in Ioo a₀ a₁, K (x, y)) =
      2 * ∫⁻ r in Ioi 0, ∫⁻ x in Ioo a₀ (a₁ - r), K (x, x + r) := by
  let P := (Ioo a₀ a₁ ×ˢ Ioo a₀ a₁).indicator K
  have hP : Measurable P := hK.indicator (measurableSet_Ioo.prod measurableSet_Ioo)
  have hPs : ∀ x y, P (y, x) = P (x, y) := by
    intro x y
    by_cases hx : x ∈ Ioo a₀ a₁ <;> by_cases hy : y ∈ Ioo a₀ a₁ <;>
      simp [P, hx, hy, hKs]
  have hleft : (∫⁻ x in Ioo a₀ a₁, ∫⁻ y in Ioo a₀ a₁, K (x, y)) =
      ∫⁻ x, ∫⁻ y, P (x, y) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo a₀ a₁
    · rw [indicator_of_mem hx, ← lintegral_indicator measurableSet_Ioo]
      congr 1
      funext y
      simp [P, hx, indicator_apply]
    · simp [P, hx]
  rw [hleft, lintegral_pair_eq_two_pos_shifts hP hPs]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr : 0 < r := hr
  dsimp only
  rw [← lintegral_indicator measurableSet_Ioo]
  congr 1
  funext x
  have he : (x, x + r) ∈ Ioo a₀ a₁ ×ˢ Ioo a₀ a₁ ↔ x ∈ Ioo a₀ (a₁ - r) := by
    simp only [mem_prod, mem_Ioo]
    constructor
    · intro h; exact ⟨h.1.1, by linarith [h.2.2]⟩
    · intro h; exact ⟨⟨h.1, by linarith [h.2]⟩, ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  simp only [P, indicator_apply, he]

/-- The fractional trace seminorm in displacement form. -/
theorem lintegral_gagliardo_interval_eq {T : ℝ → ℂ} (hT : Measurable T) (a₀ a₁ : ℝ) :
    (∫⁻ a in Ioo a₀ a₁, ∫⁻ a' in Ioo a₀ a₁,
      ENNReal.ofReal (‖T a - T a'‖ ^ 2 / (a - a') ^ 2)) =
      2 * ∫⁻ r in Ioi 0, (ENNReal.ofReal r⁻¹) ^ 2 *
        ∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖T (a + r) - T a‖ ^ 2) := by
  rw [lintegral_interval_pair_eq_two_pos_shifts
    (K := fun p ↦ ENNReal.ofReal (‖T p.1 - T p.2‖ ^ 2 / (p.1 - p.2) ^ 2))
    (by fun_prop) (fun x y ↦ by dsimp only; rw [norm_sub_rev, sub_sq_comm]) a₀ a₁]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro a _
  dsimp only
  rw [norm_sub_rev, show a - (a + r) = -r by ring, neg_sq, div_eq_mul_inv, ← inv_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (inv_nonneg.2 hr.le), mul_comm]

/-- The tangential derivative may be replaced by a measurable representative
on the open domain. -/
theorem HasWeakPartialOn.congr_right_on {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {j : Fin 2} {F A A' : ℝ × ℝ → ℂ} (h : HasWeakPartialOn U j F A)
    (hAA' : A =ᵐ[volume.restrict U] A') : HasWeakPartialOn U j F A' := by
  refine ⟨h.1, h.2.1.congr hAA', fun φ hφ ↦ ?_⟩
  rw [h.2.2 φ hφ]
  congr 1
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU.measurableSet).1 hAA'] with p hp
  by_cases hpU : p ∈ U
  · rw [hp hpU]
  · have hφp : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ hpU (hφ.tsupport_subset ht))
    rw [hφp, mul_zero, mul_zero]

/-- The scalar averaging step in the rectangle trace inequality. The interval
of comparison heights has the same scale as the horizontal displacement. -/
theorem gagliardo_le_of_averaged_increments {a₀ a₁ H c : ℝ}
    {T : ℝ → ℂ} {V E : ℝ → ℝ≥0∞} (hT : Measurable T)
    (hV : Measurable V) (hE : Measurable E) (hc : 0 < c)
    (hscale : 2 * c * (a₁ - a₀) ≤ H)
    (hinc : ∀ r, 0 < r → r < a₁ - a₀ →
      ∀ᵐ t ∂(volume.restrict (Ioo 0 H)),
        (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖T (a + r) - T a‖ ^ 2)) ≤
          6 * V t + 3 * ENNReal.ofReal (r ^ 2) * E t) :
    (∫⁻ a in Ioo a₀ a₁, ∫⁻ a' in Ioo a₀ a₁,
      ENNReal.ofReal (‖T a - T a'‖ ^ 2 / (a - a') ^ 2)) ≤
      ENNReal.ofReal (18 * c) *
        (∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * V t) +
      ENNReal.ofReal (6 * c⁻¹) * ∫⁻ t in Ioi 0, E t := by
  let S := fun r ↦ ∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖T (a + r) - T a‖ ^ 2)
  have hpoint : ∀ r ∈ Ioi (0 : ℝ), (ENNReal.ofReal r⁻¹) ^ 2 * S r ≤
      ∫⁻ s in Ioo (1 : ℝ) 2,
        6 * ((ENNReal.ofReal r⁻¹) ^ 2 * V (r * c * s)) + 3 * E (r * c * s) := by
    intro r hr
    have hr : 0 < r := hr
    by_cases hrL : r < a₁ - a₀
    · have h0 := (ae_restrict_iff' measurableSet_Ioo).1 (hinc r hr hrL)
      have hsc := (Measure.quasiMeasurePreserving_smul volume (mul_pos hr hc).ne').ae h0
      have hgood : ∀ᵐ s ∂(volume.restrict (Ioo (1 : ℝ) 2)),
          S r ≤ 6 * V (r * c * s) + 3 * ENNReal.ofReal (r ^ 2) * E (r * c * s) := by
        filter_upwards [ae_restrict_of_ae hsc, ae_restrict_mem measurableSet_Ioo] with s hs hsI
        apply hs
        change 0 < (r * c) * s ∧ (r * c) * s < H
        constructor
        · exact mul_pos (mul_pos hr hc) (by linarith [hsI.1])
        · have hrc : r * c < (a₁ - a₀) * c := mul_lt_mul_of_pos_right hrL hc
          nlinarith [hsI.2, mul_pos hr hc]
      have hcancel : (ENNReal.ofReal r⁻¹) ^ 2 * ENNReal.ofReal (r ^ 2) = 1 := by
        rw [← ENNReal.ofReal_pow (inv_nonneg.2 hr.le),
          ← ENNReal.ofReal_mul (sq_nonneg r⁻¹)]
        norm_num [inv_pow, hr.ne']
      calc
        _ = ∫⁻ _ in Ioo (1 : ℝ) 2, (ENNReal.ofReal r⁻¹) ^ 2 * S r := by
          norm_num [Real.volume_Ioo]
        _ ≤ ∫⁻ s in Ioo (1 : ℝ) 2, (ENNReal.ofReal r⁻¹) ^ 2 *
            (6 * V (r * c * s) + 3 * ENNReal.ofReal (r ^ 2) * E (r * c * s)) := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with s hs
          gcongr
        _ = _ := by
          congr 1
          funext s
          rw [mul_add]
          have he : (ENNReal.ofReal r⁻¹) ^ 2 *
              (3 * ENNReal.ofReal (r ^ 2) * E (r * c * s)) = 3 * E (r * c * s) := by
            calc
              _ = 3 * ((ENNReal.ofReal r⁻¹) ^ 2 * ENNReal.ofReal (r ^ 2)) * E (r * c * s) := by ring
              _ = _ := by rw [hcancel, mul_one]
          rw [he]
          ring
    · have he : Ioo a₀ (a₁ - r) = ∅ := Ioo_eq_empty_of_le (by linarith)
      simp [S, he]
  rw [lintegral_gagliardo_interval_eq hT]
  calc
    _ ≤ 2 * ∫⁻ r in Ioi 0, ∫⁻ s in Ioo (1 : ℝ) 2,
        6 * ((ENNReal.ofReal r⁻¹) ^ 2 * V (r * c * s)) + 3 * E (r * c * s) := by
      exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hpoint) 2
    _ = 12 * (∫⁻ r in Ioi 0, ∫⁻ s in Ioo (1 : ℝ) 2,
        (ENNReal.ofReal r⁻¹) ^ 2 * V (r * c * s)) +
        6 * ∫⁻ r in Ioi 0, ∫⁻ s in Ioo (1 : ℝ) 2, E (r * c * s) := by
      have hf : Measurable (fun p : ℝ × ℝ ↦
          (ENNReal.ofReal p.1⁻¹) ^ 2 * V (p.1 * c * p.2)) := by fun_prop
      have hg : Measurable (fun p : ℝ × ℝ ↦ E (p.1 * c * p.2)) := by fun_prop
      rw [← lintegral_prod
        (fun p : ℝ × ℝ ↦ 6 * ((ENNReal.ofReal p.1⁻¹) ^ 2 * V (p.1 * c * p.2)) +
          3 * E (p.1 * c * p.2)) (by fun_prop),
        lintegral_add_left (hf.const_mul 6),
        lintegral_const_mul' 6 _ (by norm_num), lintegral_const_mul' 3 _ (by norm_num),
        lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable]
      ring
    _ ≤ 12 * (ENNReal.ofReal (3 / 2 * c) *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * V t) +
        6 * (ENNReal.ofReal c⁻¹ * ∫⁻ t in Ioi 0, E t) := by
      rw [lintegral_band_average_inv_sq hV hc]
      gcongr
      exact lintegral_band_average_le hE hc
    _ = _ := by
      have hnum : (12 : ℝ≥0∞) * (3 / 2) = 18 := by
        have hn : ENNReal.ofReal ((12 : ℝ) * (3 / 2)) = ENNReal.ofReal 18 := by norm_num
        simpa only [ENNReal.ofReal_mul (by norm_num : 0 ≤ (12 : ℝ)),
          ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ)),
          ENNReal.ofReal_ofNat] using hn
      simp only [← mul_assoc]
      congr 2 <;> norm_num [ENNReal.ofReal_mul, ENNReal.ofReal_div_of_pos, ← mul_assoc]
      rw [hnum]

/-- A weighted indicator inside the positive half-line integrates just on its
support. This also applies to nonmeasurable nonnegative functions. -/
theorem lintegral_Ioi_weighted_indicator {J : Set ℝ} (hJ : MeasurableSet J)
    (hJ0 : J ⊆ Ioi 0) (w v : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi 0, w t * J.indicator v t) = ∫⁻ t in J, w t * v t := by
  simp_rw [← indicator_mul_right]
  rw [lintegral_indicator hJ, Measure.restrict_restrict hJ,
    inter_eq_left.2 hJ0]

/-- Shift a one-sided strip back to the original transverse coordinate. -/
theorem lintegral_shifted_strip_le {a₀ a₁ b₁ b₂ b₀ : ℝ} {f : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hb₀ : b₀ ∈ Ioo b₁ b₂) :
    (∫⁻ t in Ioo 0 (b₂ - b₀), ∫⁻ a in Ioo a₀ a₁, f (a, b₀ + t)) ≤
      ∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂, f p := by
  rw [lintegral_lintegral_swap (by fun_prop), Measure.volume_eq_prod,
    setLIntegral_prod _ hf.aemeasurable]
  apply lintegral_mono
  intro a
  have h := (measurePreserving_add_left (volume : Measure ℝ) b₀).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft b₀).measurableEmbedding (fun b ↦ f (a, b)) (Ioo b₀ b₂)
  simp only [preimage_const_add_Ioo, sub_self] at h
  dsimp only
  rw [h]
  exact lintegral_mono_set (Ioo_subset_Ioo hb₀.1.le le_rfl)

/-- The integrated three-side rectangular comparison. -/
theorem rectangle_trace_increment_le {a₀ a₁ b b₀ r : ℝ} {G A : ℝ × ℝ → ℂ}
    (hG : Measurable G) (hr : 0 < r)
    (hhor : (∫⁻ a in Ioo a₀ (a₁ - r),
        ENNReal.ofReal (‖G (a + r, b) - G (a, b)‖ ^ 2)) ≤
      ENNReal.ofReal (r ^ 2) * ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b)‖ ^ 2)) :
    (∫⁻ a in Ioo a₀ (a₁ - r),
        ENNReal.ofReal (‖G (a + r, b₀) - G (a, b₀)‖ ^ 2)) ≤
      6 * (∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖G (a, b) - G (a, b₀)‖ ^ 2)) +
      3 * ENNReal.ofReal (r ^ 2) * ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b)‖ ^ 2) := by
  let V := fun a ↦ ENNReal.ofReal (‖G (a, b) - G (a, b₀)‖ ^ 2)
  let W := fun a ↦ ENNReal.ofReal (‖G (a + r, b) - G (a, b)‖ ^ 2)
  have hVm : Measurable V := by fun_prop
  have hWm : Measurable W := by fun_prop
  calc
    _ ≤ ∫⁻ a in Ioo a₀ (a₁ - r), 3 * (V (a + r) + W a + V a) := by
      apply lintegral_mono
      intro a
      have hn := norm_sub_sq_le_three (G (a + r, b₀)) (G (a, b₀))
        (G (a + r, b)) (G (a, b))
      rw [norm_sub_rev (G (a + r, b₀)) (G (a + r, b))] at hn
      apply (ENNReal.ofReal_le_ofReal hn).trans_eq
      simp only [V, W, ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ))]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    _ = 3 * ((∫⁻ a in Ioo a₀ (a₁ - r), V (a + r)) +
        (∫⁻ a in Ioo a₀ (a₁ - r), W a) + ∫⁻ a in Ioo a₀ (a₁ - r), V a) := by
      rw [lintegral_const_mul' 3 _ (by norm_num),
        lintegral_add_left (f := fun a ↦ V (a + r) + W a) (by fun_prop),
        lintegral_add_left (f := fun a ↦ V (a + r)) (by fun_prop)]
    _ ≤ 3 * ((∫⁻ a in Ioo a₀ a₁, V a) +
        (ENNReal.ofReal (r ^ 2) * ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b)‖ ^ 2)) +
        ∫⁻ a in Ioo a₀ a₁, V a) := by
      apply mul_le_mul_right
      apply add_le_add
      · exact add_le_add (lintegral_translate_interval_le V hr) hhor
      · exact lintegral_mono_set (Ioo_subset_Ioo le_rfl (by linarith))
    _ = _ := by dsimp only [V]; ring

/-- The vertical term of the fractional trace estimate is precisely a Hardy
integral, integrated over the tangential coordinate. -/
theorem HasACLSectionsOn.lintegral_vertical_trace_difference_le {a₀ a₁ b₁ b₂ b₀ : ℝ}
    {G B : ℝ × ℝ → ℂ} (hG : HasACLSectionsOn (Ioo a₀ a₁) (Ioo b₁ b₂) G B)
    (hGm : Measurable G) (hb₀ : b₀ ∈ Ioo b₁ b₂)
    (hGL : MemLp G 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hBL : MemLp B 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂))) :
    (∫⁻ t in Ioo 0 (b₂ - b₀), (ENNReal.ofReal t⁻¹) ^ 2 *
      ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖G (a, b₀ + t) - G (a, b₀)‖ ^ 2)) ≤
      4 * ∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂, ENNReal.ofReal (‖B p‖ ^ 2) := by
  calc
    _ = ∫⁻ t in Ioo 0 (b₂ - b₀), ∫⁻ a in Ioo a₀ a₁,
        ENNReal.ofReal (‖G (a, b₀ + t) - G (a, b₀)‖ ^ 2 / t ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      funext a
      rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht.1),
        ENNReal.ofReal_pow ht.1.le, ENNReal.ofReal_inv_of_pos ht.1,
        div_eq_mul_inv, ENNReal.inv_pow, mul_comm]
    _ = ∫⁻ a in Ioo a₀ a₁, ∫⁻ t in Ioo 0 (b₂ - b₀),
        ENNReal.ofReal (‖G (a, b₀ + t) - G (a, b₀)‖ ^ 2 / t ^ 2) :=
      lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ a in Ioo a₀ a₁, 4 * ∫⁻ b in Ioo b₀ b₂, ENNReal.ofReal (‖B (a, b)‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [hG.ae_hasIntervalH1 hGL hBL] with a ha
      exact ha.lintegral_sq_sub_div_sq_le hb₀
    _ ≤ 4 * ∫⁻ a in Ioo a₀ a₁, ∫⁻ b in Ioo b₁ b₂, ENNReal.ofReal (‖B (a, b)‖ ^ 2) := by
      rw [lintegral_const_mul' 4 _ (by norm_num)]
      apply mul_le_mul_right
      apply lintegral_mono
      intro a
      exact lintegral_mono_set (Ioo_subset_Ioo hb₀.1.le le_rfl)
    _ = _ := by
      congr 1
      rw [Measure.volume_eq_prod, setLIntegral_prod]
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (hBL.aestronglyMeasurable.aemeasurable.norm.pow_const 2)

/-- A fractional trace bound from the two directional ACL estimates. The
constant is explicit and depends only on the rectangle and the chosen line. -/
theorem HasACLSectionsOn.gagliardo_trace_le {a₀ a₁ b₁ b₂ b₀ c : ℝ}
    {G A B : ℝ × ℝ → ℂ} (hG : HasACLSectionsOn (Ioo a₀ a₁) (Ioo b₁ b₂) G B)
    (hGm : Measurable G) (hAm : Measurable A) (hb₀ : b₀ ∈ Ioo b₁ b₂)
    (hc : 0 < c) (hscale : 2 * c * (a₁ - a₀) ≤ b₂ - b₀)
    (hGL : MemLp G 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hBL : MemLp B 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hhor : ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)), ∀ r, 0 < r →
      (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖G (a + r, b) - G (a, b)‖ ^ 2)) ≤
        ENNReal.ofReal (r ^ 2) * ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b)‖ ^ 2)) :
    (∫⁻ a in Ioo a₀ a₁, ∫⁻ a' in Ioo a₀ a₁,
      ENNReal.ofReal (‖G (a, b₀) - G (a', b₀)‖ ^ 2 / (a - a') ^ 2)) ≤
      ENNReal.ofReal (72 * c) * (∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂,
        ENNReal.ofReal (‖B p‖ ^ 2)) +
      ENNReal.ofReal (6 * c⁻¹) * ∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂,
        ENNReal.ofReal (‖A p‖ ^ 2) := by
  let J := Ioo 0 (b₂ - b₀)
  let V := J.indicator (fun t ↦ ∫⁻ a in Ioo a₀ a₁,
    ENNReal.ofReal (‖G (a, b₀ + t) - G (a, b₀)‖ ^ 2))
  let E := J.indicator (fun t ↦ ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b₀ + t)‖ ^ 2))
  have hVm : Measurable V := by
    apply Measurable.indicator _ measurableSet_Ioo
    exact (show Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (‖G (p.2, b₀ + p.1) - G (p.2, b₀)‖ ^ 2)) by
        fun_prop).lintegral_prod_right'
  have hEm : Measurable E := by
    apply Measurable.indicator _ measurableSet_Ioo
    exact (show Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (‖A (p.2, b₀ + p.1)‖ ^ 2)) by fun_prop).lintegral_prod_right'
  have hVbound : (∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * V t) ≤
      4 * ∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂, ENNReal.ofReal (‖B p‖ ^ 2) := by
    change (∫⁻ t in Ioi 0, (ENNReal.ofReal t⁻¹) ^ 2 * J.indicator _ t) ≤ _
    rw [lintegral_Ioi_weighted_indicator measurableSet_Ioo (fun _ ht ↦ ht.1)]
    exact hG.lintegral_vertical_trace_difference_le hGm hb₀ hGL hBL
  have hEbound : (∫⁻ t in Ioi 0, E t) ≤
      ∫⁻ p in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂, ENNReal.ofReal (‖A p‖ ^ 2) := by
    have he := lintegral_Ioi_weighted_indicator
      (measurableSet_Ioo (a := 0) (b := b₂ - b₀)) (fun _ ht ↦ ht.1) (fun _ ↦ 1)
      (fun t ↦ ∫⁻ a in Ioo a₀ a₁, ENNReal.ofReal (‖A (a, b₀ + t)‖ ^ 2))
    simp only [one_mul] at he
    rw [show (∫⁻ t in Ioi 0, E t) = _ from he]
    exact lintegral_shifted_strip_le
      (f := fun p ↦ ENNReal.ofReal (‖A p‖ ^ 2)) (by fun_prop) hb₀
  have hinc : ∀ r, 0 < r → r < a₁ - a₀ →
      ∀ᵐ t ∂(volume.restrict J),
        (∫⁻ a in Ioo a₀ (a₁ - r), ENNReal.ofReal (‖G (a + r, b₀) - G (a, b₀)‖ ^ 2)) ≤
          6 * V t + 3 * ENNReal.ofReal (r ^ 2) * E t := by
    intro r hr _
    have hs := (measurePreserving_add_left volume b₀).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hhor)
    filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Ioo] with t ht htJ
    have hbt : b₀ + t ∈ Ioo b₁ b₂ := ⟨by linarith [hb₀.1, htJ.1], by linarith [htJ.2]⟩
    change _ ≤ 6 * J.indicator _ t + 3 * ENNReal.ofReal (r ^ 2) * J.indicator _ t
    rw [indicator_of_mem htJ, indicator_of_mem htJ]
    exact rectangle_trace_increment_le hGm hr (ht hbt r hr)
  have hbase := gagliardo_le_of_averaged_increments
    (show Measurable (fun a ↦ G (a, b₀)) by fun_prop) hVm hEm hc hscale hinc
  refine hbase.trans ((add_le_add (mul_le_mul_right hVbound _)
    (mul_le_mul_right hEbound _)).trans_eq ?_)
  have hcoeff : ENNReal.ofReal (18 * c) * 4 = ENNReal.ofReal (72 * c) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [← mul_assoc, hcoeff]

/-- The diagonal Jacobian cancels the factor two in the parallelogram identity.
An arbitrary measurable representative of the tangential derivative is allowed. -/
theorem diagonal_gradient_energy_le {a₀ a₁ b₁ b₂ : ℝ}
    {F Fx Fy A : ℝ × ℝ → ℂ} (hAm : Measurable A)
    (hA : A =ᵐ[volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)]
      ((fun p ↦ Fx p + Fy p) ∘ diagInv))
    (hF : MemLp F 2 (volume.restrict (diagRect (Ioo a₀ a₁) (Ioo b₁ b₂))))
    (hFx : MemLp Fx 2 (volume.restrict (diagRect (Ioo a₀ a₁) (Ioo b₁ b₂))))
    (hFy : MemLp Fy 2 (volume.restrict (diagRect (Ioo a₀ a₁) (Ioo b₁ b₂)))) :
    (∫⁻ q in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂, ENNReal.ofReal (‖A q‖ ^ 2)) +
      (∫⁻ q in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂,
        ENNReal.ofReal (‖Fx (diagInv q) - Fy (diagInv q)‖ ^ 2)) ≤
      ENNReal.ofReal (∫ p in diagRect (Ioo a₀ a₁) (Ioo b₁ b₂),
        ‖F p‖ ^ 2 + ‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2) := by
  calc
    _ = ∫⁻ q in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂,
        ENNReal.ofReal (‖A q‖ ^ 2 +
          ‖Fx (diagInv q) - Fy (diagInv q)‖ ^ 2) := by
      simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      rw [lintegral_add_left (by fun_prop)]
    _ = ∫⁻ q in Ioo a₀ a₁ ×ˢ Ioo b₁ b₂,
        ENNReal.ofReal (2 * (‖Fx (diagInv q)‖ ^ 2 + ‖Fy (diagInv q)‖ ^ 2)) := by
      apply lintegral_congr_ae
      filter_upwards [hA] with q hq
      rw [hq]
      congr 1
      dsimp only [Function.comp_apply]
      nlinarith only [parallelogram_law_with_norm ℝ (Fx (diagInv q)) (Fy (diagInv q))]
    _ = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) *
        ∫⁻ p in diagRect (Ioo a₀ a₁) (Ioo b₁ b₂),
          ENNReal.ofReal (‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2)) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        setLIntegral_comp_diagInv measurableSet_Ioo measurableSet_Ioo
          (fun p ↦ ENNReal.ofReal (‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2))]
    _ = ∫⁻ p in diagRect (Ioo a₀ a₁) (Ioo b₁ b₂),
        ENNReal.ofReal (‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    _ ≤ ∫⁻ p in diagRect (Ioo a₀ a₁) (Ioo b₁ b₂),
        ENNReal.ofReal (‖F p‖ ^ 2 + ‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2) := by
      apply lintegral_mono
      intro p
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ‖F p‖])
    _ = _ := by
      exact (ofReal_integral_eq_lintegral_ofReal
        ((hF.norm.integrable_sq.add hFx.norm.integrable_sq).add hFy.norm.integrable_sq)
        (Eventually.of_forall (fun p ↦ by
          dsimp only [Pi.add_apply, Pi.zero_apply]
          positivity))).symm

/-- Absolute continuity on lines, and the trace on a line `b = b₀`. Let `F ∈ H¹` on a
    neighbourhood of the diagonal rectangle `Q = {a₀ < a < a₁, b₁ < b < b₂}` with weak
    derivatives `Fx, Fy`. Then `F` has a representative `G` that is locally absolutely
    continuous on almost every line `a = const` in `Q`, with derivative `∂_b = ∂ₓ - ∂_y`, and
    whose trace on the line `b = b₀` (`b₁ < b₀ < b₂`) has finite Gagliardo seminorm, bounded by
    the `H¹(Q)` norm. The constant depends only on the rectangle and the trace line, not
    on `U`, the function, or its weak derivatives. -/
theorem exists_acl_trace {a₀ a₁ b₁ b₂ b₀ : ℝ} (ha : a₀ < a₁)
    (hb₀ : b₀ ∈ Set.Ioo b₁ b₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (ℝ × ℝ)) (F Fx Fy : ℝ × ℝ → ℂ),
      IsOpen U → diagRect (Set.Ioo a₀ a₁) (Set.Ioo b₁ b₂) ⊆ U →
      MemLp F 2 (volume.restrict U) → MemLp Fx 2 (volume.restrict U) →
      MemLp Fy 2 (volume.restrict U) → HasWeakPartialOn U 0 F Fx → HasWeakPartialOn U 1 F Fy →
    ∃ G : ℝ × ℝ → ℂ, (∀ᵐ p ∂(volume.restrict U), G p = F p) ∧
      (∀ᵐ a ∂(volume.restrict (Set.Ioo a₀ a₁)),
        (∀ c d, b₁ < c → c ≤ d → d < b₂ →
          AbsolutelyContinuousOnInterval (fun b ↦ G (diagInv (a, b))) c d) ∧
        ∀ᵐ b ∂(volume.restrict (Set.Ioo b₁ b₂)),
          HasDerivAt (fun b ↦ G (diagInv (a, b))) (Fx (diagInv (a, b)) - Fy (diagInv (a, b))) b) ∧
      (∫⁻ a in Set.Ioo a₀ a₁, ∫⁻ a' in Set.Ioo a₀ a₁,
          ENNReal.ofReal (‖G (diagInv (a, b₀)) - G (diagInv (a', b₀))‖ ^ 2 / (a - a') ^ 2) ≤
        ENNReal.ofReal (C * ∫ p in diagRect (Set.Ioo a₀ a₁) (Set.Ioo b₁ b₂),
          ‖F p‖ ^ 2 + ‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2)) := by
  let c := (b₂ - b₀) / (2 * (a₁ - a₀))
  have hc : 0 < c := div_pos (sub_pos.2 hb₀.2) (mul_pos (by norm_num) (sub_pos.2 ha))
  have hscale : 2 * c * (a₁ - a₀) ≤ b₂ - b₀ := by
    dsimp only [c]
    exact le_of_eq (by field_simp [(sub_pos.2 ha).ne'])
  let C := 72 * c + 6 * c⁻¹
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro U F Fx Fy hU hQ hFL hFxL hFyL hx hy
  have hb : b₁ < b₂ := hb₀.1.trans hb₀.2
  let R := Ioo a₀ a₁ ×ˢ Ioo b₁ b₂
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRU : R ⊆ diagInv ⁻¹' U := by
    intro q hq
    exact hQ (mem_diagRect_diagInv.2 hq)
  have hFLd := (memLp_comp_diagInv hU.measurableSet hFL).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  have hAL := (memLp_comp_diagInv hU.measurableSet (hFxL.add hFyL)).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  have hBL := (memLp_comp_diagInv hU.measurableSet (hFxL.sub hFyL)).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  let A₀ := (fun p ↦ Fx p + Fy p) ∘ diagInv
  let A := hAL.aestronglyMeasurable.mk A₀
  have hAm : Measurable A := hAL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hAA : A₀ =ᵐ[volume.restrict R] A := hAL.aestronglyMeasurable.ae_eq_mk
  have hAL' : MemLp A 2 (volume.restrict R) := hAL.ae_eq hAA
  have hda := ((hx.comp_diagInv_fst hU hy).mono hRU).congr_right_on hRo hAA
  obtain ⟨G, hGm, hGF, hG⟩ := exists_diagonal_acl_rep hU ha hb hQ hx hy
  have hGFd : (G ∘ diagInv) =ᵐ[volume.restrict R] (F ∘ diagInv) := by
    have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    have hq := (Measure.LinearMap.quasiMeasurePreserving volume
      (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
      (by rw [det_diagInvLinear]; norm_num)).ae
        ((ae_restrict_iff' hU.measurableSet).1 hGF)
    filter_upwards [ae_restrict_of_ae hq, ae_restrict_mem hRo.measurableSet] with q hq hqR
    exact hq (hRU hqR)
  have hGL : MemLp (G ∘ diagInv) 2 (volume.restrict R) := hFLd.ae_eq hGFd.symm
  have hGa : HasACLSectionsOn (Ioo a₀ a₁) (Ioo b₁ b₂) (G ∘ diagInv)
      ((fun p ↦ Fx p - Fy p) ∘ diagInv) := by
    filter_upwards [hG] with a haG
    refine ⟨?_, haG.2⟩
    intro d e hde
    have hd := hde left_mem_uIcc
    have he := hde right_mem_uIcc
    rcases le_total d e with h | h
    · exact haG.1 d e hd.1 h he.2
    · exact (haG.1 e d he.1 h hd.2).symm
  have hhor := hda.ae_horizontal_translate_le ha hb hFLd hAL' hGFd
  have hbound := hGa.gagliardo_trace_le (hGm.comp diagInv.continuous.measurable)
    hAm hb₀ hc hscale hGL hBL hhor
  have henergy := diagonal_gradient_energy_le hAm hAA.symm
    (hFL.mono_measure (Measure.restrict_mono hQ le_rfl))
    (hFxL.mono_measure (Measure.restrict_mono hQ le_rfl))
    (hFyL.mono_measure (Measure.restrict_mono hQ le_rfl))
  refine ⟨G, hGF, hG, hbound.trans ?_⟩
  let IA := ∫⁻ q in R, ENNReal.ofReal (‖A q‖ ^ 2)
  let IB := ∫⁻ q in R, ENNReal.ofReal (‖Fx (diagInv q) - Fy (diagInv q)‖ ^ 2)
  let Z := ∫ p in diagRect (Ioo a₀ a₁) (Ioo b₁ b₂),
    ‖F p‖ ^ 2 + ‖Fx p‖ ^ 2 + ‖Fy p‖ ^ 2
  change ENNReal.ofReal (72 * c) * IB + ENNReal.ofReal (6 * c⁻¹) * IA ≤ ENNReal.ofReal (C * Z)
  calc
    _ ≤ ENNReal.ofReal (72 * c) * (IA + IB) +
        ENNReal.ofReal (6 * c⁻¹) * (IA + IB) := by
      apply add_le_add
      · exact mul_le_mul_right (le_add_of_nonneg_left zero_le) _
      · exact mul_le_mul_right (le_add_of_nonneg_right zero_le) _
    _ = (ENNReal.ofReal (72 * c) + ENNReal.ofReal (6 * c⁻¹)) * (IA + IB) := by ring
    _ ≤ (ENNReal.ofReal (72 * c) + ENNReal.ofReal (6 * c⁻¹)) * ENNReal.ofReal Z :=
      mul_le_mul_right henergy _
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC]


end NoEmbeddedEigenvalues
