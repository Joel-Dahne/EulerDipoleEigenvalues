import NoEmbeddedEigenvalues.Transport.WeightedForcing.LogarithmicRayTransport
import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterRayTraceUniqueness

/-!
# Logarithmic summation of compatible numerator estimates

Blueprint: `lem:log-numerator-summation`, `lem:log-endpoint-change-variables`.

Restriction retains exactly the same derivative and ray-trace representatives.
The weighted estimates are obtained from the existing a.e. quantitative bounds,
without differentiating the logarithm or replacing compatible witnesses.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Restrict the level interval without changing any derivative or trace witness. -/
def WeightedQuarterNumeratorData.restrict {lam h₀ b : ℝ} {U : Set (ℝ × ℝ)}
    {g : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D h₀) (hb : b ≤ h₀) :
    WeightedQuarterNumeratorData lam U g D b := by
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 h₀ := fun _ hx ↦ ⟨hx.1, hx.2.trans_le hb⟩
  have hm := Measure.restrict_mono hsub (le_rfl : (volume : Measure ℝ) ≤ volume)
  refine {
    first := d.first
    second := d.second
    halfFirst := d.halfFirst
    numerator_h2 := fun a c ha hac hc ↦ d.numerator_h2 a c ha hac (hc.trans_le hb)
    half_h1 := fun a c ha hac hc ↦ d.half_h1 a c ha hac (hc.trans_le hb)
    first_lp := d.first_lp.mono_measure hm
    half_lp := d.half_lp.mono_measure hm
    second_lp := d.second_lp.mono_measure hm
    radius := d.radius
    radius_pos := d.radius_pos
    radius_lt := d.radius_lt
    endpoint_radius_lt := (monotone_quarterEndpointRadius hb).trans_lt d.endpoint_radius_lt
    gradientTrace := d.gradientTrace
    ray_trace := d.ray_trace
    endpoint_value_lp := fun side ↦ (d.endpoint_value_lp side).mono_measure hm
    endpoint_gradient_lp := fun side j ↦ (d.endpoint_gradient_lp side j).mono_measure hm
    fibers_integrable := d.fibers_integrable.filter_mono (ae_mono hm)
    mass_integrable := ⟨d.mass_integrable.1.mono_set hsub,
      d.mass_integrable.2.1.mono_set hsub, d.mass_integrable.2.2.mono_set hsub⟩
    forcing_level_weak := d.forcing_level_weak.mono ?_
    bound := d.bound
    bound_pos := d.bound_pos
    subinterval_bound := d.subinterval_bound.filter_mono (ae_mono hm)
    first_bound := d.first_bound.filter_mono (ae_mono hm)
    second_bound := d.second_bound.filter_mono (ae_mono hm)
  }
  intro q hq
  exact ⟨hq.1, hq.2.1.trans_le hb, hq.2.2⟩

/-- A square majorant can be summed against the logarithmic measure provided
actual level-side measurability is already available. -/
theorem memLp_log_of_sq_bound {b : ℝ} (hb : b ≤ 1) {F : ℝ → ℂ} {B : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioo 0 b)))
    (hB : IntegrableOn (fun h ↦ logLevelWeight h * B h) (Ioo 0 b))
    (hbound : ∀ᵐ h ∂(volume.restrict (Ioo 0 b)), ‖F h‖ ^ 2 ≤ B h) :
    MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * F h) 2
      (volume.restrict (Ioo 0 b)) := by
  have hm : Measurable (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ)) := by
    unfold logLevelWeight; fun_prop
  have hfm := hm.aestronglyMeasurable.mul hF.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hfm).mpr
  apply hB.mono' (hfm.norm.pow 2)
  filter_upwards [hbound, ae_restrict_mem measurableSet_Ioo] with h hh hhI
  have hlog := logLevelWeight_nonneg hhI.1 (hhI.2.trans_le hb).le
  change ‖‖(Real.sqrt (logLevelWeight h) : ℂ) * F h‖ ^ 2‖ ≤ logLevelWeight h * B h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hlog]
  exact mul_le_mul_of_nonneg_left hh hlog

/-- Five genuine logarithmic mass bounds sum the already specified numerator
and half-numerator derivative estimates. -/
theorem WeightedQuarterNumeratorData.log_estimates {lam b : ℝ} {U : Set (ℝ × ℝ)}
    {g : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (d : WeightedQuarterNumeratorData lam U g D b) (hb : b ≤ 1)
    (hK : IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 (3 / 2) D h) (Ioo 0 b))
    (hK₁ : IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 1 0 D h) (Ioo 0 b))
    (hK₂ : IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy 2 0 D h) (Ioo 0 b))
    (hval : IntegrableOn (fun h ↦ logLevelWeight h * quarterEndpointValueEnergy g h) (Ioo 0 b))
    (hgrad : IntegrableOn (fun h ↦ logLevelWeight h *
      quarterEndpointGradientEnergy d.gradientTrace h) (Ioo 0 b)) :
    MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.first h) 2
      (volume.restrict (Ioo 0 b)) ∧
    MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * d.halfFirst h) 2
      (volume.restrict (Ioo 0 b)) ∧
    MemLp (fun h ↦ (Real.sqrt (logLevelWeight h) : ℂ) * (h : ℂ) * d.second h) 2
      (volume.restrict (Ioo 0 b)) := by
  have hfirst : IntegrableOn (fun h ↦ logLevelWeight h *
      (d.bound * (quarterJetEnergy 1 (3 / 2) D h + quarterEndpointValueEnergy g h))) (Ioo 0 b) := by
    unfold IntegrableOn
    convert (hK.add hval).const_mul d.bound using 1
    funext h; dsimp; ring
  have hsecond : IntegrableOn (fun h ↦ logLevelWeight h * (d.bound *
      (quarterJetEnergy 2 0 D h + quarterJetEnergy 1 0 D h +
        quarterEndpointGradientEnergy d.gradientTrace h + quarterEndpointValueEnergy g h)))
      (Ioo 0 b) := by
    unfold IntegrableOn
    convert (((hK₂.add hK₁).add hgrad).add hval).const_mul d.bound using 1
    funext h; dsimp; ring
  refine ⟨memLp_log_of_sq_bound hb d.first_lp hfirst ?_,
    memLp_log_of_sq_bound hb d.half_lp hfirst ?_, ?_⟩
  · filter_upwards [d.first_bound] with h hh
    linarith [sq_nonneg (‖d.halfFirst h‖)]
  · filter_upwards [d.first_bound] with h hh
    linarith [sq_nonneg (‖d.first h‖)]
  · have hi := memLp_log_of_sq_bound hb d.second_lp hsecond (by
      filter_upwards [d.second_bound] with h hh
      simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh)
    convert hi using 1
    funext h; ring

/-- Squared complex quotient norm, retaining the totalized real power at zero. -/
theorem norm_div_rpow_sq {r : ℝ} (hr : 0 ≤ r) (s : ℝ) (z : ℂ) :
    ‖z / (Real.rpow r s : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / Real.rpow r (2 * s) := by
  have he : (r ^ s) ^ 2 = (r ^ (2 * s) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    congr 1
    norm_num
    ring
  change ‖z / ((r ^ s : ℝ) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (r ^ (2 * s) : ℝ)
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr _), he]

/-- The existing unweighted endpoint L² bound supplies the measurability needed
by logarithmic ray transport. Radial and level powers are paired exactly. -/
theorem integrable_log_endpoint_of_memLp {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {n : ℕ} (hn : n = 1 ∨ n = 2)
    {F : ℝ → ℂ}
    (hraw : MemLp (fun h ↦ F (quarterEndpointRadius h) /
      (Real.rpow h ((n : ℝ) / 2) : ℂ)) 2 (volume.restrict (Ioo 0 b)))
    (hray : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * F r /
      (Real.rpow r (((2 * n - 1 : ℕ) : ℝ) / 2) : ℂ)) 2 (volume.restrict (Ioo 0 ρ))) :
    IntegrableOn (fun h ↦ logLevelWeight h * ‖F (quarterEndpointRadius h)‖ ^ 2 / h ^ n)
      (Ioo 0 b) := by
  have he {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (z : ℂ) :
      ‖z / (Real.rpow r ((m : ℝ) / 2) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / r ^ m := by
    rw [norm_div_rpow_sq hr]
    have hh : 2 * ((m : ℝ) / 2) = (m : ℝ) := by ring
    rw [hh, Real.rpow_eq_pow, Real.rpow_natCast]
  have hme : AEStronglyMeasurable
      (fun h ↦ ‖F (quarterEndpointRadius h)‖ ^ 2 / h ^ n) (volume.restrict (Ioo 0 b)) := by
    apply (hraw.aestronglyMeasurable.norm.pow 2).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact he hh.1.le n _
  have hlog : Measurable logLevelWeight := by unfold logLevelWeight; fun_prop
  apply integrable_log_endpoint_pullback hb hρ hn (B := fun r ↦ ‖F r‖ ^ 2)
    (fun _ ↦ sq_nonneg _) (by
      apply (hlog.aestronglyMeasurable.mul hme).congr
      exact Eventually.of_forall fun h ↦ by dsimp; ring)
  have hRi : IntegrableOn (fun r ↦ ‖(Real.sqrt (logRadiusWeight r) : ℂ) * F r /
      (Real.rpow r (((2 * n - 1 : ℕ) : ℝ) / 2) : ℂ)‖ ^ 2) (Ioo 0 ρ) :=
    hray.norm.integrable_sq
  apply hRi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hl : 0 ≤ logRadiusWeight r := by unfold logRadiusWeight; positivity
  rw [mul_div_assoc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hl, he hr.1.le, mul_div_assoc]

theorem integrable_log_endpoint_value {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {F : ℝ → ℂ}
    (hraw : MemLp (fun h ↦ F (quarterEndpointRadius h) / (h : ℂ)) 2
      (volume.restrict (Ioo 0 b)))
    (hray : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * F r /
      (Real.rpow r (3 / 2) : ℂ)) 2 (volume.restrict (Ioo 0 ρ))) :
    IntegrableOn (fun h ↦ logLevelWeight h * ‖F (quarterEndpointRadius h)‖ ^ 2 / h ^ 2)
      (Ioo 0 b) := by
  apply integrable_log_endpoint_of_memLp hb hρ (n := 2) (Or.inr rfl)
  · simpa [Real.rpow_eq_pow] using hraw
  · simpa using hray

theorem integrable_log_endpoint_gradient {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {F : ℝ → ℂ}
    (hraw : MemLp (fun h ↦ F (quarterEndpointRadius h) / (Real.sqrt h : ℂ)) 2
      (volume.restrict (Ioo 0 b)))
    (hray : MemLp (fun r ↦ (Real.sqrt (logRadiusWeight r) : ℂ) * F r /
      (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 ρ))) :
    IntegrableOn (fun h ↦ logLevelWeight h * ‖F (quarterEndpointRadius h)‖ ^ 2 / h)
      (Ioo 0 b) := by
  have hi := integrable_log_endpoint_of_memLp hb hρ (n := 1) (Or.inl rfl)
    (F := F) (by simpa [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using hraw)
    (by simpa [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using hray)
  simpa only [pow_one] using hi

end NoEmbeddedEigenvalues
