module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterNumeratorBounds
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SpecifiedJetLp
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Second fixed-time numerator bulk energy

Blueprint: `def:second-level-bulk`, `lem:second-level-density-bound`,
`lem:second-numerator-bulk-bound`, `lem:second-numerator-bulk`,
`lem:transport-second-bulk-data`.

The formal second level contraction retains every ordered entry of the supplied
weak jet. Its bulk bound is separate from a weak moving-endpoint differentiation
formula: no assertion of numerator H² follows from this estimate alone.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real
open scoped Topology ContDiff

/-- Actual quarter-jet energy and all its sections, for any order and weight. -/
theorem quarterJet_energy_integrable {k : ℕ} {b s : ℝ} (hb : b ≤ 1)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ w, w.length = k → MemLp (fun p ↦ D w p /
      (Real.rpow (saddleDist p) s : ℂ)) 2 (volume.restrict cellSquare)) :
    IntegrableOn (quarterJetEnergy k s D) (Ioo 0 b) ∧
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), QuarterJetIntegrable k s D h ∧
      ∀ w, w.length = k → MemLp (fun t ↦ D w (dipoleOrbit h t) /
        (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)) 2
        (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
  have hL (w) (hw : w.length = k) :=
    memLp_comp_quarterOrbitStrip_of_memLp hb (hD w hw)
  have hi : IntegrableOn (quarterJetDensity k s D) (quarterOrbitStrip b) := by
    exact integrable_finsetSum _ fun w _ ↦
      (hL (List.ofFn w) List.length_ofFn).integrable_norm_pow (by norm_num)
  obtain ⟨hmass, hfib⟩ := integrable_quarterStrip_sections hi
  have hsections (w : List (Fin 2)) : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      w.length = k → MemLp (fun t ↦ D w (dipoleOrbit h t) /
        (Real.rpow (saddleDist (dipoleOrbit h t)) s : ℂ)) 2
        (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
    by_cases hw : w.length = k
    · filter_upwards [memLp_quarterStrip_sections (hL w hw)] with h hh _
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact hh
    · exact Eventually.of_forall fun _ hh ↦ (hw hh).elim
  refine ⟨hmass, ?_⟩
  filter_upwards [hfib, ae_all_iff.2 hsections] with h hi hs
  exact ⟨hi, hs⟩

/-- The first level vector is jointly smooth at every interior level. -/
theorem contDiffAt_orbit_level_derivative {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ deriv (fun x ↦ dipoleOrbit x q.2) q.1) (h, t) := by
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦
      fderiv ℝ (fun p : ℝ × ℝ ↦ dipoleOrbit p.1 p.2) q (1, 0)) (h, t) :=
    ((contDiffAt_orbitMap hh).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  apply hs.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds hh] with q hq
  have hd := ((contDiffAt_orbitMap (t := q.2) hq).differentiableAt (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv

/-- The second level vector is jointly smooth at every interior level. -/
theorem contDiffAt_orbit_level_second_derivative {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦
      deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y q.2) x) q.1) (h, t) := by
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ fderiv ℝ
      (fun p : ℝ × ℝ ↦ deriv (fun x ↦ dipoleOrbit x p.2) p.1) q (1, 0)) (h, t) :=
    ((contDiffAt_orbit_level_derivative hh).fderiv_right (m := ∞)
      (by simp)).clm_apply contDiffAt_const
  apply hs.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds hh] with q hq
  have hd := ((contDiffAt_orbit_level_derivative (t := q.2) hq).differentiableAt
    (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv

/-- Formal second fixed-time level contraction. The order of each second jet
word is retained; this definition asserts no weak differentiation identity. -/
def quarterForcingSecondLevelDerivative (D : List (Fin 2) → ℝ × ℝ → ℂ)
    (q : ℝ × ℝ) : ℂ :=
  let V := deriv (fun x ↦ dipoleOrbit x q.2) q.1
  let W := deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y q.2) x) q.1
  (∑ j : Fin 2, (axisCoord j W : ℂ) * D [j] (dipoleOrbit q.1 q.2)) +
    ∑ w : Fin 2 → Fin 2, ((axisCoord (w 0) V * axisCoord (w 1) V : ℝ) : ℂ) *
      D (List.ofFn w) (dipoleOrbit q.1 q.2)

/-- A finite complex sum has square norm bounded by its number of terms times
its square-norm energy. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖∑ i, z i‖ ^ 2 ≤ Fintype.card ι * ∑ i, ‖z i‖ ^ 2 := by
  have hn := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
    (norm_sum_le Finset.univ z)
  exact hn.trans (by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ ‖z i‖))

/-- Cauchy–Schwarz under a pointwise square-density majorant. Actual
integrability of the complex field is established before its integral is bounded. -/
theorem norm_integral_sq_le_of_sq_le_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → ℂ} {W E : α → ℝ}
    (hF : AEStronglyMeasurable F μ) (hW : Integrable W μ) (hE : Integrable E μ)
    (hWp : ∀ᵐ a ∂μ, 0 ≤ W a) (hEp : ∀ᵐ a ∂μ, 0 ≤ E a)
    (hbound : ∀ᵐ a ∂μ, ‖F a‖ ^ 2 ≤ W a * E a) :
    Integrable F μ ∧ ‖∫ a, F a ∂μ‖ ^ 2 ≤ (∫ a, W a ∂μ) * ∫ a, E a ∂μ := by
  have hsqrt {G : α → ℝ} (hG : Integrable G μ) (hp : ∀ᵐ a ∂μ, 0 ≤ G a) :
      MemLp (fun a ↦ (Real.sqrt (G a) : ℂ)) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (Real.continuous_sqrt.comp_aestronglyMeasurable hG.aestronglyMeasurable))).2
    apply hG.congr
    filter_upwards [hp] with a ha
    simp [Complex.norm_real, Real.sq_sqrt ha]
  have hWL := hsqrt hW hWp
  have hEL := hsqrt hE hEp
  have hP := hWL.integrable_mul hEL
  have hb : ∀ᵐ a ∂μ, ‖F a‖ ≤ ‖(Real.sqrt (W a) : ℂ) * (Real.sqrt (E a) : ℂ)‖ := by
    filter_upwards [hWp, hEp, hbound] with a hw he hb
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg (sqrt_nonneg _)]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    simpa only [mul_pow, sq_sqrt hw, sq_sqrt he] using hb
  have hFI := hP.norm.mono' hF hb
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp (fun a ↦ (Real.sqrt (W a) : ℂ)) (ENNReal.ofReal 2) μ by simpa using hWL)
    (show MemLp (fun a ↦ (Real.sqrt (E a) : ℂ)) (ENNReal.ofReal 2) μ by simpa using hEL)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  have hn := (norm_integral_le_integral_norm (f := F)).trans
    ((integral_mono_ae hFI.norm hP.norm hb).trans (by simpa only [Pi.mul_apply, norm_mul] using hh))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  rw [mul_pow, sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)] at hs
  have hEq {G : α → ℝ} (hp : ∀ᵐ a ∂μ, 0 ≤ G a) :
      (∫ a, ‖(Real.sqrt (G a) : ℂ)‖ ^ 2 ∂μ) = ∫ a, G a ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp] with a ha
    simp [Complex.norm_real, Real.sq_sqrt ha]
  exact ⟨hFI, by simpa only [hEq hWp, hEq hEp] using hs⟩

/-- The formal second contraction costs at most six times the common
coefficient square and the exact sum of the first- and second-jet densities. -/
theorem quarterForcingSecondLevelDerivative_sq_le_density
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hr : 0 < saddleDist (dipoleOrbit q.1 q.2))
    (hV : ‖deriv (fun x ↦ dipoleOrbit x q.2) q.1‖ ≤ C / saddleDist (dipoleOrbit q.1 q.2))
    (hW : ‖deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y q.2) x) q.1‖ ≤
      C / saddleDist (dipoleOrbit q.1 q.2) ^ 2) :
    ‖quarterForcingSecondLevelDerivative D q‖ ^ 2 ≤
      (6 * C ^ 4 / saddleDist (dipoleOrbit q.1 q.2) ^ 4) *
        (quarterJetDensity 1 0 D q + quarterJetDensity 2 0 D q) := by
  let V := deriv (fun x ↦ dipoleOrbit x q.2) q.1
  let W := deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y q.2) x) q.1
  let r := saddleDist (dipoleOrbit q.1 q.2)
  let Z : Fin 2 ⊕ (Fin 2 → Fin 2) → ℂ := Sum.elim
    (fun j ↦ D [j] (dipoleOrbit q.1 q.2))
    (fun w ↦ D (List.ofFn w) (dipoleOrbit q.1 q.2))
  let A : Fin 2 ⊕ (Fin 2 → Fin 2) → ℂ := Sum.elim
    (fun j ↦ (axisCoord j W : ℂ))
    (fun w ↦ ((axisCoord (w 0) V * axisCoord (w 1) V : ℝ) : ℂ))
  have haxis (j : Fin 2) (p : ℝ × ℝ) : ‖axisCoord j p‖ ≤ ‖p‖ := by
    unfold axisCoord
    split_ifs
    · exact norm_fst_le p
    · exact norm_snd_le p
  have ha (i) : ‖A i‖ ≤ C ^ 2 / r ^ 2 := by
    cases i with
    | inl j =>
      change ‖(axisCoord j W : ℂ)‖ ≤ _
      rw [Complex.norm_real]
      exact ((haxis j W).trans hW).trans
        (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg r))
    | inr w =>
      change ‖((axisCoord (w 0) V * axisCoord (w 1) V : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, norm_mul]
      calc _ ≤ (C / r) * (C / r) :=
            mul_le_mul ((haxis _ V).trans hV) ((haxis _ V).trans hV)
              (norm_nonneg _) (by positivity)
           _ = _ := by ring
  have he : quarterJetDensity 1 0 D q + quarterJetDensity 2 0 D q = ∑ i, ‖Z i‖ ^ 2 := by
    rw [quarterJetDensity_one]
    simp only [Fintype.sum_sum_type, Z, Sum.elim_inl, Sum.elim_inr,
      quarterJetDensity, Real.rpow_eq_pow, Real.rpow_zero, Complex.ofReal_one, div_one]
    rw [Fin.sum_univ_two]
  have hs := norm_sum_sq_le_card_mul_sum_norm_sq (fun i ↦ A i * Z i)
  have hz : ∑ i, ‖A i * Z i‖ ^ 2 ≤ (C ^ 4 / r ^ 4) * ∑ i, ‖Z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, mul_pow]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C ^ 2 / r ^ 2)).2 (ha i)
    convert mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖Z i‖) using 1
    ring
  have hsum : (∑ i, A i * Z i) = quarterForcingSecondLevelDerivative D q := by
    simp only [Fintype.sum_sum_type, A, Z, Sum.elim_inl, Sum.elim_inr,
      quarterForcingSecondLevelDerivative, V, W]
  rw [hsum] at hs
  norm_num only [Fintype.card_sum, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] at hs
  rw [he]
  calc _ ≤ 6 * ∑ i, ‖A i * Z i‖ ^ 2 := hs
       _ ≤ 6 * ((C ^ 4 / r ^ 4) * ∑ i, ‖Z i‖ ^ 2) := by gcongr
       _ = _ := by ring

/-- The formal contraction is jointly a.e. measurable for the original raw
jet; smooth geometric coefficients do not require measurable ACL choices. -/
theorem aestronglyMeasurable_quarterSecondLevelDerivative {b : ℝ} (hb : b ≤ 1)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict cellSquare)) :
    AEStronglyMeasurable (quarterForcingSecondLevelDerivative D)
      (volume.restrict (quarterOrbitStrip b)) := by
  have hV : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun x ↦ dipoleOrbit x q.2) q.1)
      (quarterOrbitStrip b) := fun q hq ↦
    (contDiffAt_orbit_level_derivative ⟨hq.1, hq.2.1.trans_le hb⟩).continuousAt.continuousWithinAt
  have hW : ContinuousOn (fun q : ℝ × ℝ ↦
      deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y q.2) x) q.1) (quarterOrbitStrip b) := fun q hq ↦
    (contDiffAt_orbit_level_second_derivative
      ⟨hq.1, hq.2.1.trans_le hb⟩).continuousAt.continuousWithinAt
  have ha (j : Fin 2) {F : ℝ × ℝ → ℝ × ℝ} (hF : ContinuousOn F (quarterOrbitStrip b)) :
      ContinuousOn (fun q ↦ axisCoord j (F q)) (quarterOrbitStrip b) := by
    unfold axisCoord
    split_ifs
    · exact hF.fst
    · exact hF.snd
  have hL (w) (hw : w.length ≤ 2) :=
    (memLp_comp_quarterOrbitStrip_of_memLp hb (hD w hw)).aestronglyMeasurable
  apply AEStronglyMeasurable.add
  · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
      ((Complex.continuous_ofReal.comp_continuousOn (ha j hW)).aestronglyMeasurable
        (measurableSet_quarterOrbitStrip b)).mul (hL [j] (by simp))
  · exact Finset.aestronglyMeasurable_fun_sum _ fun w _ ↦
      ((Complex.continuous_ofReal.comp_continuousOn
        ((ha (w 0) hV).mul (ha (w 1) hV))).aestronglyMeasurable
        (measurableSet_quarterOrbitStrip b)).mul (hL (List.ofFn w) (by simp))

/-- Joint a.e. measurability on a moving strip suffices for a.e. measurable
raw interval integrals and sections, even before integrability is known. -/
theorem aestronglyMeasurable_quarterStrip_integral {b : ℝ} (hb : b ≤ 1)
    {F : ℝ × ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict (quarterOrbitStrip b))) :
    AEStronglyMeasurable (fun h ↦ ∫ t in (-eighthPeriod h)..eighthPeriod h, F (h, t))
      (volume.restrict (Ioo 0 b)) ∧
    ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), AEStronglyMeasurable (fun t ↦ F (h, t))
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))) := by
  have hI := (aestronglyMeasurable_indicator_iff (measurableSet_quarterOrbitStrip b)).2 hF
  have hP : AEStronglyMeasurable ((quarterOrbitStrip b).indicator F)
      ((volume : Measure ℝ).prod volume) := by rwa [← Measure.volume_eq_prod]
  have he (h : ℝ) (hh : h ∈ Ioo 0 b) :
      (fun t ↦ (quarterOrbitStrip b).indicator F (h, t)) =
        (Ioo (-eighthPeriod h) (eighthPeriod h)).indicator (fun t ↦ F (h, t)) := by
    funext t
    simp only [indicator_apply, quarterOrbitStrip, mem_ofPred_eq, hh.1, hh.2, true_and, mem_Ioo]
  constructor
  · apply hP.integral_prod_right'.restrict.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hL := eighthPeriod_pos hh.1 (hh.2.trans_le hb)
    rw [he h hh, integral_indicator measurableSet_Ioo, ← integral_Icc_eq_integral_Ioo,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  · filter_upwards [ae_restrict_of_ae hP.prodMk_left, ae_restrict_mem measurableSet_Ioo]
      with h hh hhI
    rw [he h hhI] at hh
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioo).1 hh

/-- Cauchy–Schwarz for the formal second level bulk. The inverse fourth
moment is explicit, and genuine fiber integrability is part of the conclusion. -/
theorem quarterForcingSecondLevelDerivative_integral_bound
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {h C A : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1)
    (hC : 1 ≤ C)
    (hE : QuarterJetIntegrable 1 0 D h ∧ QuarterJetIntegrable 2 0 D h)
    (hF : AEStronglyMeasurable (fun t ↦ quarterForcingSecondLevelDerivative D (h, t))
      (volume.restrict (Icc (-eighthPeriod h) (eighthPeriod h))))
    (hd : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h), 0 < saddleDist (dipoleOrbit h t))
    (hV : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t))
    (hW : ∀ t ∈ Icc (-eighthPeriod h) (eighthPeriod h),
      ‖deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y t) x) h‖ ≤ C / saddleDist (dipoleOrbit h t) ^ 2)
    (hMoment : (∫ t in (-eighthPeriod h)..eighthPeriod h,
      Real.rpow (saddleDist (dipoleOrbit h t)) (-4)) ≤ A / h ^ 2) (lam : ℝ) :
    IntervalIntegrable (fun t ↦ quarterForcingSecondLevelDerivative D (h, t) *
      Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume (-eighthPeriod h) (eighthPeriod h) ∧
    h ^ 2 * ‖∫ t in (-eighthPeriod h)..eighthPeriod h,
      quarterForcingSecondLevelDerivative D (h, t) *
        Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ ^ 2 ≤
      (6 * C ^ 4 * A) * (quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) := by
  let L := eighthPeriod h
  have hL := eighthPeriod_pos hh.1 hh.2
  have hdc : Continuous (fun t ↦ saddleDist (dipoleOrbit h t)) :=
    (Metric.continuous_infDist_pt saddleSet).comp (continuous_iff_continuousAt.2
      (fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt))
  have hw : IntegrableOn (fun t ↦ Real.rpow (saddleDist (dipoleOrbit h t)) (-4)) (Icc (-L) L) :=
    (hdc.continuousOn.rpow_const (fun t ht ↦ Or.inl (hd t ht).ne')).integrableOn_Icc
  have hE' : IntegrableOn (fun t ↦ quarterJetDensity 1 0 D (h, t) +
      quarterJetDensity 2 0 D (h, t)) (Icc (-L) L) := by
    change Integrable _ (volume.restrict (Icc (-L) L))
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hE.1.add hE.2
  have hphase (t : ℝ) : ‖Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hEq (t : ℝ) : Real.rpow (saddleDist (dipoleOrbit h t)) (-4) =
      1 / saddleDist (dipoleOrbit h t) ^ 4 := by
    simp only [Real.rpow_eq_pow]
    rw [show (-4 : ℝ) = -(4 : ℕ) by norm_num, Real.rpow_neg_natCast]
    simp [zpow_neg, one_div]
  obtain ⟨hi, hbound⟩ := norm_integral_sq_le_of_sq_le_mul
    (hF.mul (by fun_prop : AEStronglyMeasurable
      (fun t ↦ Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) _))
    (hw.const_mul (6 * C ^ 4)) hE'
    (Eventually.of_forall fun t ↦ by rw [hEq]; positivity)
    (Eventually.of_forall fun t ↦ by unfold quarterJetDensity; positivity)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [Pi.mul_apply, norm_mul, hphase, mul_one, hEq]
      convert quarterForcingSecondLevelDerivative_sq_le_density D (h, t) hC (hd t ht)
        (hV t ht) (hW t ht) using 1
      ring)
  have hEnergy : (∫ t in Icc (-L) L,
      quarterJetDensity 1 0 D (h, t) + quarterJetDensity 2 0 D (h, t)) =
      quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h := by
    rw [integral_Icc_eq_integral_Ioo, integral_add hE.1 hE.2]
    rfl
  rw [integral_const_mul, hEnergy] at hbound
  have hMoment' : (∫ t in Icc (-L) L,
      Real.rpow (saddleDist (dipoleOrbit h t)) (-4)) ≤ A / h ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    exact hMoment
  have hEp : 0 ≤ quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h := by
    unfold quarterJetEnergy quarterJetDensity
    positivity
  have hM := mul_le_mul_of_nonneg_left hMoment' (by positivity : 0 ≤ 6 * C ^ 4)
  have hB := hbound.trans (mul_le_mul_of_nonneg_right hM hEp)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -L ≤ L)).2 hi, ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L), ← integral_Icc_eq_integral_Ioc]
  have hs := mul_le_mul_of_nonneg_left hB (sq_nonneg h)
  convert hs using 1
  field_simp [hh.1.ne']

/-- The second fixed-time bulk integral, before adding moving-endpoint terms. -/
def quarterSecondBulk (lam : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ t in (-eighthPeriod h)..eighthPeriod h, quarterForcingSecondLevelDerivative D (h, t) *
    Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))

/-- Finite unweighted first and second jet norms yield one collar and constant
for every real frequency, with actual bulk L² and one common good-level set. -/
theorem second_numerator_bulk_estimates {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict cellSquare)) :
    ∃ b K : ℝ, 0 < b ∧ b < 1 / 2 ∧ 0 < K ∧
      IntegrableOn (fun h ↦ quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) (Ioo 0 b) ∧
      (∀ lam : ℝ, MemLp (fun h : ℝ ↦ (h : ℂ) * quarterSecondBulk lam D h) 2
        (volume.restrict (Ioo 0 b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
        QuarterJetIntegrable 1 0 D h ∧ QuarterJetIntegrable 2 0 D h ∧ ∀ lam : ℝ,
          IntervalIntegrable (fun t ↦ quarterForcingSecondLevelDerivative D (h, t) *
            Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume
              (-eighthPeriod h) (eighthPeriod h) ∧
          h ^ 2 * ‖quarterSecondBulk lam D h‖ ^ 2 ≤
            K * (quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) := by
  obtain ⟨C₀, rV, hrV, _, hVW⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨A₀, rI, hrI, hMoment⟩ := integral_saddleDist_rpow_le
  obtain ⟨c, _, rS, hc, hrS, hDistance⟩ := saddleDist_dipoleOrbit
  let C := max 1 C₀
  let A := max 0 A₀
  let b := min rV (min rI (min rS (1 / 4)))
  let K := 6 * C ^ 4 * A + 1
  have hb : 0 < b := lt_min hrV (lt_min hrI (lt_min hrS (by norm_num)))
  have hbhalf : b < 1 / 2 := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hb1 : b ≤ 1 := by linarith
  have hC : 1 ≤ C := le_max_left _ _
  have hK : 0 < K := by dsimp [K, A]; positivity
  have hL (k : ℕ) (hk : k ≤ 2) : ∀ w, w.length = k →
      MemLp (fun p ↦ D w p / (Real.rpow (saddleDist p) 0 : ℂ)) 2
        (volume.restrict cellSquare) := by
    intro w hw
    simpa only [Real.rpow_eq_pow, Real.rpow_zero, Complex.ofReal_one, div_one]
      using hD w (hw.le.trans hk)
  have hE₁ := quarterJet_energy_integrable hb1 (hL 1 (by norm_num))
  have hE₂ := quarterJet_energy_integrable hb1 (hL 2 (by norm_num))
  have hF := aestronglyMeasurable_quarterSecondLevelDerivative hb1 hD
  have hFsections := (aestronglyMeasurable_quarterStrip_integral hb1 hF).2
  have hAE : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
      QuarterJetIntegrable 1 0 D h ∧ QuarterJetIntegrable 2 0 D h ∧ ∀ lam : ℝ,
        IntervalIntegrable (fun t ↦ quarterForcingSecondLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume
            (-eighthPeriod h) (eighthPeriod h) ∧
        h ^ 2 * ‖quarterSecondBulk lam D h‖ ^ 2 ≤
          K * (quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) := by
    filter_upwards [hE₁.2, hE₂.2, hFsections, ae_restrict_mem measurableSet_Ioo]
      with h hE₁ hE₂ hFh hh
    have hh1 : h ∈ Ioo (0 : ℝ) 1 := ⟨hh.1, hh.2.trans_le hb1⟩
    have hhV : h ∈ Ioo (0 : ℝ) rV := ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩
    have hhI : h ∈ Ioo (0 : ℝ) rI :=
      ⟨hh.1, hh.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hhS : h ∈ Ioo (0 : ℝ) rS :=
      ⟨hh.1, hh.2.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))⟩
    have hd (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
        0 < saddleDist (dipoleOrbit h t) :=
      (mul_pos hc (exp_pos _)).trans_le (hDistance h hhS t ((abs_le).2 ht)).1
    have hV (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
        ‖deriv (fun x ↦ dipoleOrbit x t) h‖ ≤ C / saddleDist (dipoleOrbit h t) :=
      ((hVW h hhV t ((abs_le).2 ht)).1).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (hd t ht).le)
    have hW (t : ℝ) (ht : t ∈ Icc (-eighthPeriod h) (eighthPeriod h)) :
        ‖deriv (fun x ↦ deriv (fun y ↦ dipoleOrbit y t) x) h‖ ≤
          C / saddleDist (dipoleOrbit h t) ^ 2 :=
      ((hVW h hhV t ((abs_le).2 ht)).2).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    have hM : (∫ t in (-eighthPeriod h)..eighthPeriod h,
        Real.rpow (saddleDist (dipoleOrbit h t)) (-4)) ≤ A / h ^ 2 :=
      ((hMoment h hhI).2).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    refine ⟨hE₁.1, hE₂.1, fun lam ↦ ?_⟩
    obtain ⟨hi, he⟩ := quarterForcingSecondLevelDerivative_integral_bound hh1 hC
      ⟨hE₁.1, hE₂.1⟩ hFh hd hV hW hM lam
    refine ⟨hi, he.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
    unfold quarterJetEnergy quarterJetDensity
    positivity
  refine ⟨b, K, hb, hbhalf, hK, hE₁.1.add hE₂.1, ?_, hAE⟩
  intro lam
  have hphase : AEStronglyMeasurable (fun q : ℝ × ℝ ↦
      Complex.exp (-Complex.I * ((lam * q.2 : ℝ) : ℂ)))
      (volume.restrict (quarterOrbitStrip b)) := by fun_prop
  have hm := (aestronglyMeasurable_quarterStrip_integral hb1 (hF.mul hphase)).1
  have hm' : AEStronglyMeasurable (fun h : ℝ ↦ (h : ℂ) * quarterSecondBulk lam D h)
      (volume.restrict (Ioo 0 b)) := (by fun_prop :
    AEStronglyMeasurable (fun h : ℝ ↦ (h : ℂ)) (volume.restrict (Ioo 0 b))).mul hm
  apply (memLp_two_iff_integrable_sq_norm hm').2
  apply ((hE₁.1.add hE₂.1).const_mul K).mono' (hm'.norm.pow 2)
  filter_upwards [hAE] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [Pi.pow_apply, Pi.add_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs] using (hh.2.2 lam).2

/-- Sobolev regularity supplies the norms for every original ordered weak
entry; the supplied full jet is not replaced by a chosen one. -/
theorem MemSobolevOn.second_numerator_bulk_estimates {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevOn 2 U f) (hU : IsOpen U)
    (hcell : cellSquare ⊆ U) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 U f D) :
    ∃ b K : ℝ, 0 < b ∧ b < 1 / 2 ∧ 0 < K ∧
      IntegrableOn (fun h ↦ quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) (Ioo 0 b) ∧
      (∀ lam : ℝ, MemLp (fun h : ℝ ↦ (h : ℂ) * quarterSecondBulk lam D h) 2
        (volume.restrict (Ioo 0 b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
        QuarterJetIntegrable 1 0 D h ∧ QuarterJetIntegrable 2 0 D h ∧ ∀ lam : ℝ,
          IntervalIntegrable (fun t ↦ quarterForcingSecondLevelDerivative D (h, t) *
            Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) volume
              (-eighthPeriod h) (eighthPeriod h) ∧
          h ^ 2 * ‖quarterSecondBulk lam D h‖ ^ 2 ≤
            K * (quarterJetEnergy 1 0 D h + quarterJetEnergy 2 0 D h) := by
  apply NoEmbeddedEigenvalues.second_numerator_bulk_estimates
  intro w hw
  exact (hf.memLp_weakJet hU hD w hw).mono_measure (Measure.restrict_mono_set _ hcell)

/-- The original pair and specified first derivatives construct their own
second bulk jet and its norms. No Hessian, ray or second numerator input is assumed. -/
theorem IsTransportPair.exists_second_numerator_bulk_data
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j)) :
    ∃ J : List (Fin 2) → ℝ × ℝ → ℂ, HasWeakJetOn 2 U f J ∧
      (∀ j, J [j] = D j) ∧ ∃ b K : ℝ, 0 < b ∧ b < 1 / 2 ∧ 0 < K ∧
      IntegrableOn (fun h ↦ quarterJetEnergy 1 0 J h + quarterJetEnergy 2 0 J h) (Ioo 0 b) ∧
      (∀ μ : ℝ, MemLp (fun h : ℝ ↦ (h : ℂ) * quarterSecondBulk μ J h) 2
        (volume.restrict (Ioo 0 b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 b)),
        QuarterJetIntegrable 1 0 J h ∧ QuarterJetIntegrable 2 0 J h ∧ ∀ μ : ℝ,
          IntervalIntegrable (fun t ↦ quarterForcingSecondLevelDerivative J (h, t) *
            Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) volume
              (-eighthPeriod h) (eighthPeriod h) ∧
          h ^ 2 * ‖quarterSecondBulk μ J h‖ ^ 2 ≤
            K * (quarterJetEnergy 1 0 J h + quarterJetEnergy 2 0 J h) := by
  obtain ⟨J, hJ, hfirst⟩ := MemSobolevOn.exists_weakJet_two_with_first
    hp.memSobolevOn hp.isOrbitUnion.1 hD
  exact ⟨J, hJ, hfirst, hp.memSobolevOn.second_numerator_bulk_estimates hp.isOrbitUnion.1
    (subset_closure.trans hcell) hJ⟩

end NoEmbeddedEigenvalues
