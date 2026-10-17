import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import NoEmbeddedEigenvalues.SobolevLocal

/-!
# Mollification in one variable

Blueprint: `def:line-mollifier`, `lem:line-mollifier-kernel`,
`lem:line-mollifier-contraction`, `lem:line-mollifier-convergence`;
remaining estimates stated in `lem:line-mollifier`.

Functions `F(h, θ)` on `ℝ²` are mollified in the first variable only,
`M_ε F(h, θ) = ∫ ρ_ε(h - h') F(h', θ) dh'` with `ρ_ε(h) = ε⁻¹ ρ(h/ε)` for a fixed smooth even
bump `ρ` supported in `[-1, 1]` with integral one. `L²` statements are for the measure
`dh ⊗ μ` with an arbitrary s-finite `μ` in `θ`, since `M_ε` acts on each line `θ = const`
separately. The contraction follows by probability averaging and a measure-preserving
translation, including joint a.e. measurability. Strong continuity of translations follows
fiberwise by dominated convergence, and the shrinking kernel support gives convergence of
mollification. This is the one-dimensional input of the transversal mollifier
(`TransversalMollifier.lean`), where `(h, θ)` are action-angle coordinates.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal

/-- The fixed bump `ρ`: smooth, even, nonnegative, positive exactly on `(-1, 1)`, with
    integral one. -/
def stdBump : ℝ → ℝ :=
  (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume

/-- The rescaled bump `ρ_ε(h) = ε⁻¹ ρ(h/ε)`. -/
def mollifierKernel (ε h : ℝ) : ℝ := ε⁻¹ * stdBump (h / ε)

/-- Mollification in the first variable, `M_ε F(h, θ) = ∫ ρ_ε(h - h') F(h', θ) dh'`. -/
def mollifyFst (ε : ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ h', mollifierKernel ε (q.1 - h') • F (h', q.2)

/-- `∂_h M_ε F = ∫ ρ_ε'(h - h') F(h', θ) dh'`. -/
def mollifyFstDeriv (ε : ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ h', deriv (mollifierKernel ε) (q.1 - h') • F (h', q.2)

theorem contDiff_stdBump : ContDiff ℝ ∞ stdBump :=
  ContDiffBump.contDiff_normed _

theorem stdBump_nonneg (h : ℝ) : 0 ≤ stdBump h :=
  ContDiffBump.nonneg_normed _ h

theorem stdBump_neg (h : ℝ) : stdBump (-h) = stdBump h :=
  ContDiffBump.normed_neg _ h

theorem support_stdBump : Function.support stdBump = Ioo (-1) 1 := by
  rw [stdBump, ContDiffBump.support_normed_eq, Real.ball_eq_Ioo]
  norm_num

theorem integral_stdBump : ∫ h, stdBump h = 1 :=
  ContDiffBump.integral_normed _

/-- Rescaling preserves the unit integral of the mollifier kernel. -/
theorem integral_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    ∫ h, mollifierKernel ε h = 1 := by
  rw [show (fun h => mollifierKernel ε h) = (fun h => ε⁻¹ * stdBump (ε⁻¹ * h)) by
    funext h
    simp [mollifierKernel, div_eq_mul_inv, mul_comm]]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left, integral_stdBump]
  simp [abs_of_pos hε, hε.ne']

/-- The rescaled mollifier kernel is smooth. -/
theorem contDiff_mollifierKernel (ε : ℝ) : ContDiff ℝ ∞ (mollifierKernel ε) := by
  by_cases hε : ε = 0
  · convert (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))) using 1
    funext h
    simp [mollifierKernel, hε]
  · rw [show mollifierKernel ε = (fun h => ε⁻¹ * (stdBump ∘ (fun x => x / ε)) h) by
      funext h
      rfl]
    exact (contDiff_const.mul
      (contDiff_stdBump.comp (contDiff_id.div_const ε)))

/-- For positive scales the mollifier kernel has compact support. -/
theorem hasCompactSupport_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierKernel ε) := by
  have hstd : HasCompactSupport stdBump := by
    exact ContDiffBump.hasCompactSupport_normed _
  have hcomp := hstd.comp_smul (G₀ := ℝ) (c := ε⁻¹) (inv_ne_zero hε.ne')
  have hcomp' : HasCompactSupport (fun h => stdBump (h / ε)) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using hcomp
  change HasCompactSupport (fun h => ε⁻¹ * stdBump (h / ε))
  exact hcomp'.mul_left

/-- The derivative kernel has zero integral, the cancellation behind
`ε M'_ε F → 0`. -/
theorem integral_deriv_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    ∫ h, deriv (mollifierKernel ε) h = 0 := by
  have hcont : ContDiff ℝ 1 (mollifierKernel ε) :=
    (contDiff_mollifierKernel ε).of_le (by norm_num)
  have hderiv_int : Integrable (deriv (mollifierKernel ε)) :=
    (hcont.continuous_deriv le_rfl).integrable_of_hasCompactSupport
      (hasCompactSupport_mollifierKernel hε).deriv
  have hleft : IntegrableOn (deriv (mollifierKernel ε)) (Iic 0) := hderiv_int.integrableOn
  have hright : IntegrableOn (deriv (mollifierKernel ε)) (Ioi 0) := hderiv_int.integrableOn
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
  rw [HasCompactSupport.integral_Iic_deriv_eq hcont
      (hasCompactSupport_mollifierKernel hε) 0,
    HasCompactSupport.integral_Ioi_deriv_eq hcont
      (hasCompactSupport_mollifierKernel hε) 0]
  simp

/-- Averaging over a probability factor is an `L²` contraction. -/
private theorem eLpNorm_integral_prob_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [IsProbabilityMeasure ν] {σ : Measure β} [SFinite σ]
    {G : α × β → ℂ} (hG : MemLp G 2 (ν.prod σ)) :
    MemLp (fun q ↦ ∫ t, G (t, q) ∂ν) 2 σ ∧
      eLpNorm (fun q ↦ ∫ t, G (t, q) ∂ν) 2 σ ≤ eLpNorm G 2 (ν.prod σ) := by
  have hmeas : AEStronglyMeasurable (fun q ↦ ∫ t, G (t, q) ∂ν) σ :=
    hG.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hsec : ∀ᵐ q ∂σ, AEStronglyMeasurable (fun t ↦ G (t, q)) ν :=
    hG.aestronglyMeasurable.prodMk_right
  have hbound : ∀ᵐ q ∂σ,
      ‖∫ t, G (t, q) ∂ν‖ₑ ^ (2 : ℝ) ≤
        (eLpNorm (fun t ↦ G (t, q)) 2 ν) ^ (2 : ℝ) := by
    filter_upwards [hsec] with q hq
    calc
      ‖∫ t, G (t, q) ∂ν‖ₑ ^ (2 : ℝ) ≤
          (eLpNorm (fun t ↦ G (t, q)) 1 ν) ^ (2 : ℝ) := by
            gcongr
            exact enorm_integral_le_lintegral_enorm _ |>.trans
              (lintegral_enorm_le_eLpNorm_one)
      _ ≤ (eLpNorm (fun t ↦ G (t, q)) 2 ν) ^ (2 : ℝ) := by
        gcongr
        exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hpow : eLpNorm (fun q ↦ ∫ t, G (t, q) ∂ν) 2 σ ^ (2 : ℝ) ≤
      eLpNorm G 2 (ν.prod σ) ^ (2 : ℝ) := by
    calc
      eLpNorm (fun q ↦ ∫ t, G (t, q) ∂ν) 2 σ ^ (2 : ℝ) =
          ∫⁻ q, ‖∫ t, G (t, q) ∂ν‖ₑ ^ (2 : ℝ) ∂σ :=
        eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hmeas
      _ ≤
          ∫⁻ (q : β), (eLpNorm (fun t ↦ G (t, q)) 2 ν) ^ (2 : ℝ) ∂σ :=
        lintegral_mono_ae hbound
      _ = ∫⁻ q, ∫⁻ t, ‖G (t, q)‖ₑ ^ (2 : ℝ) ∂ν ∂σ := by
        apply lintegral_congr_ae
        filter_upwards [hsec] with q hq
        exact eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hq
      _ = ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(ν.prod σ) := by
        symm
        apply lintegral_prod_symm
        exact (AEMeasurable.pow_const hG.aestronglyMeasurable.enorm 2)
      _ = eLpNorm G 2 (ν.prod σ) ^ (2 : ℝ) := by
        symm
        exact eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
          hG.aestronglyMeasurable
  have hnorm : eLpNorm (fun q ↦ ∫ t, G (t, q) ∂ν) 2 σ ≤ eLpNorm G 2 (ν.prod σ) :=
    (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hpow
  exact ⟨lt_of_le_of_lt hnorm hG.eLpNorm_lt_top, hnorm⟩

/-- The kernel regarded as a measure on translation parameters. -/
private def mollifierMeasure (ε : ℝ) : Measure ℝ :=
  volume.withDensity (fun t ↦ ENNReal.ofReal (mollifierKernel ε t))

private theorem isProbabilityMeasure_mollifierMeasure {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (mollifierMeasure ε) := by
  apply IsProbabilityMeasure.mk
  rw [mollifierMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcont : Continuous (mollifierKernel ε) :=
    (contDiff_mollifierKernel ε).continuous
  have hint : Integrable (mollifierKernel ε) :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_mollifierKernel hε)
  have hnonneg : 0 ≤ᵐ[volume] mollifierKernel ε :=
    Filter.Eventually.of_forall (fun t ↦ by
      exact mul_nonneg (inv_nonneg.mpr hε.le) (stdBump_nonneg (t / ε)))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_mollifierKernel hε]
  simp

/-- The convolution formula is also a probability average of translates. -/
private theorem mollifyFst_eq_average {ε : ℝ} (hε : 0 < ε)
    (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    mollifyFst ε F q = ∫ t, F (q.1 - t, q.2) ∂mollifierMeasure ε := by
  change (∫ h', mollifierKernel ε (q.1 - h') • F (h', q.2)) =
    ∫ t, F (q.1 - t, q.2) ∂volume.withDensity
      (fun t ↦ ENNReal.ofReal (mollifierKernel ε t))
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hnonneg : ∀ t, 0 ≤ mollifierKernel ε t := fun t ↦
      mul_nonneg (inv_nonneg.mpr hε.le) (stdBump_nonneg (t / ε))
    have hkernel : (fun t ↦ (ENNReal.ofReal (mollifierKernel ε t)).toReal •
        F (q.1 - t, q.2)) = (fun t ↦ mollifierKernel ε t • F (q.1 - t, q.2)) := by
      funext t
      rw [ENNReal.toReal_ofReal (hnonneg t)]
    rw [hkernel]
    let g : ℝ → ℂ := fun h' ↦ mollifierKernel ε (q.1 - h') • F (h', q.2)
    have hmp : MeasurePreserving (MeasurableEquiv.subLeft q.1) volume volume :=
      volume.measurePreserving_sub_left q.1
    have hchange := hmp.integral_comp' g
    simpa [g, MeasurableEquiv.subLeft, Equiv.subLeft, sub_sub_cancel] using hchange.symm
  · exact (contDiff_mollifierKernel ε).continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun t ↦ ENNReal.ofReal_lt_top)

/-- Joint translation preserves the `L²` norm when the translation parameter has
probability law `ν`. -/
private theorem memLp_translateFst {μ ν : Measure ℝ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    MemLp (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - p.1, p.2.2)) 2
        (ν.prod ((volume : Measure ℝ).prod μ)) ∧
      eLpNorm (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - p.1, p.2.2)) 2
        (ν.prod ((volume : Measure ℝ).prod μ)) =
        eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  have hfiber : ∀ t : ℝ, MeasurePreserving
      (fun q : ℝ × ℝ ↦ (q.1 - t, q.2)) σ σ := by
    intro t
    have hsub : MeasurePreserving (fun x : ℝ ↦ x - t) volume volume := by
      simpa [Function.comp_def] using
        (Measure.measurePreserving_neg volume).comp (volume.measurePreserving_sub_left t)
    exact hsub.prod (MeasurePreserving.id μ)
  let g : ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun t q ↦ (q.1 - t, q.2)
  have hS' : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.1, g p.1 p.2))
      (ν.prod σ) (ν.prod σ) := by
    refine (MeasurePreserving.id ν).skew_product (μc := σ) (μd := σ) ?_ ?_
    · fun_prop
    · filter_upwards [] with t
      exact (hfiber t).map_eq
  have hS : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.1, (p.2.1 - p.1, p.2.2)))
      (ν.prod σ) (ν.prod σ) := by
    simpa [g] using hS'
  have hT : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.2.1 - p.1, p.2.2)) (ν.prod σ) σ :=
    measurePreserving_snd.comp hS
  have hmem := hF.comp_measurePreserving hT
  have hnorm := eLpNorm_comp_measurePreserving (p := (2 : ENNReal))
    hF.aestronglyMeasurable hT
  constructor
  · simpa [σ, Function.comp_def] using hmem
  · simpa [σ, Function.comp_def] using hnorm

/-- Lebesgue translations are strongly continuous on scalar `L²`. -/
private theorem tendsto_eLpNorm_translate_sub {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦ f (x - t) - f x) 2 volume)
      (𝓝 0) (𝓝 0) := by
  let fL : Lp ℂ 2 volume := hf.toLp f
  let g : ℝ → C(ℝ, ℝ) := fun t =>
    ⟨fun x => x - t, (continuous_id.sub continuous_const)⟩
  have hg : Tendsto g (𝓝 0) (𝓝 (ContinuousMap.id ℝ)) := by
    have hc : Continuous g := by
      apply ContinuousMap.continuous_of_continuous_uncurry g
      change Continuous (fun p : ℝ × ℝ => p.2 - p.1)
      fun_prop
    have hg0 : g 0 = ContinuousMap.id ℝ := by ext x; simp [g]
    rw [← hg0]
    exact hc.tendsto 0
  have hgm : ∀ t : ℝ, MeasurePreserving (g t) volume volume := by
    intro t
    exact measurePreserving_sub_right volume t
  have hcomp := Filter.Tendsto.compMeasurePreservingLp
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => fL) (𝓝 0) (𝓝 fL)) hg hgm
    (MeasurePreserving.id volume) (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hcomp' : Tendsto (fun t => Lp.compMeasurePreserving (g t) (hgm t) (fL))
      (𝓝 0) (𝓝 fL) := by
    simpa [g, fL] using hcomp
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun t => Lp.compMeasurePreserving (g t) (hgm t) fL) f hf).mp hcomp'
  convert hnorm using 1
  · funext t
    apply eLpNorm_congr_ae
    have hfxg := (hgm t).quasiMeasurePreserving.ae hf.coeFn_toLp
    filter_upwards [Lp.coeFn_compMeasurePreserving fL (hgm t), hfxg] with x hx hfx
    simp only [Function.comp_apply, g] at hx
    change f (x - t) - f x =
      (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 volume) x - f x
    have hx' : (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 volume) x = f (x - t) := by
      calc
        (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 volume) x = fL (g t x) := hx
        _ = f (x - t) := by
          simpa [g] using hfx
    rw [hx']

/-- The squared product `L²` norm is the integral of the squared fiber norms. -/
private theorem eLpNorm_two_prod_rpow_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [SFinite ν] {σ : Measure β} [SFinite σ]
    {G : α × β → ℂ} (hG : AEStronglyMeasurable G (ν.prod σ)) :
    eLpNorm G 2 (ν.prod σ) ^ (2 : ℝ) =
      ∫⁻ q, eLpNorm (fun t ↦ G (t, q)) 2 ν ^ (2 : ℝ) ∂σ := by
  have hsec : ∀ᵐ q ∂σ, AEStronglyMeasurable (fun t ↦ G (t, q)) ν :=
    hG.prodMk_right
  calc
    eLpNorm G 2 (ν.prod σ) ^ (2 : ℝ) =
        ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(ν.prod σ) :=
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hG
    _ = ∫⁻ q, ∫⁻ t, ‖G (t, q)‖ₑ ^ (2 : ℝ) ∂ν ∂σ := by
      rw [lintegral_prod_symm]
      exact (AEMeasurable.pow_const hG.enorm 2)
    _ = ∫⁻ q, eLpNorm (fun t ↦ G (t, q)) 2 ν ^ (2 : ℝ) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hsec] with q hq
      exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hq).symm

private theorem ae_memLp_two_section {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [SFinite ν] {σ : Measure β} [SFinite σ]
    {G : α × β → ℂ} (hG : MemLp G 2 (ν.prod σ)) :
    ∀ᵐ q ∂σ, MemLp (fun t ↦ G (t, q)) 2 ν := by
  have hsec : ∀ᵐ q ∂σ, AEStronglyMeasurable (fun t ↦ G (t, q)) ν :=
    hG.aestronglyMeasurable.prodMk_right
  let E : β → ENNReal := fun q ↦ ∫⁻ t, ‖G (t, q)‖ₑ ^ (2 : ℝ) ∂ν
  have hE : AEMeasurable E σ :=
    (AEMeasurable.pow_const hG.aestronglyMeasurable.enorm 2).lintegral_prod_left'
  have hEint : ∫⁻ q, E q ∂σ ≠ ⊤ := by
    have hEq : (∫⁻ q, E q ∂σ) =
        ∫⁻ q, eLpNorm (fun t ↦ G (t, q)) 2 ν ^ (2 : ℝ) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hsec] with q hq
      dsimp [E]
      exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hq).symm
    rw [hEq, ← eLpNorm_two_prod_rpow_eq hG.aestronglyMeasurable]
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      hG.eLpNorm_lt_top.ne)
  have hfinite : ∀ᵐ q ∂σ, E q < ⊤ := ae_lt_top' hE hEint
  filter_upwards [hsec, hfinite] with q hq hqfin
  have hpow : eLpNorm (fun t ↦ G (t, q)) 2 ν ^ (2 : ℝ) = E q := by
    dsimp [E]
    exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hq)
  have hnorm : eLpNorm (fun t ↦ G (t, q)) 2 ν < ⊤ := by
    rw [← hpow] at hqfin
    by_contra h
    have htop : eLpNorm (fun t ↦ G (t, q)) 2 ν = ⊤ := le_antisymm le_top (not_lt.mp h)
    rw [htop] at hqfin
    simp at hqfin
  exact hnorm

/-- Strong continuity of first-variable translations, without a regularity
assumption on the transverse measure. -/
private theorem tendsto_eLpNorm_translateFst_sub {μ : Measure ℝ} [SFinite μ]
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun q ↦ F (q.1 - t, q.2) - F q) 2
      ((volume : Measure ℝ).prod μ)) (𝓝 0) (𝓝 0) := by
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  let D : ℝ → (ℝ × ℝ) → ℂ :=
    fun t q ↦ F (q.1 - t, q.2) - F q
  have hDmem : ∀ t : ℝ, MemLp (D t) 2 σ := by
    intro t
    have htr : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 - t, q.2)) σ σ := by
      exact (measurePreserving_sub_right volume t).prod (MeasurePreserving.id μ)
    have hc := hF.comp_measurePreserving htr
    change MemLp (fun q : ℝ × ℝ ↦ F (q.1 - t, q.2) - F q) 2 σ
    exact hc.sub hF
  have hsec := ae_memLp_two_section hF
  let E : ℝ → ℝ → ENNReal := fun t θ ↦
    ∫⁻ h, ‖D t (h, θ)‖ₑ ^ (2 : ℝ) ∂volume
  have hEmeas : ∀ t, AEMeasurable (E t) μ := by
    intro t
    exact ((hDmem t).aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_left'
  let EF : ℝ → ENNReal := fun θ ↦ ∫⁻ h, ‖F (h, θ)‖ₑ ^ (2 : ℝ) ∂volume
  have hEFint : ∫⁻ θ, EF θ ∂μ ≠ ⊤ := by
    dsimp [EF]
    have hEq : (∫⁻ θ, EF θ ∂μ) =
        eLpNorm F 2 σ ^ (2 : ℝ) := by
      calc
        _ = ∫⁻ θ, eLpNorm (fun h ↦ F (h, θ)) 2 volume ^ (2 : ℝ) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hsec] with θ hθ
          dsimp [EF]
          exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
            hθ.aestronglyMeasurable).symm
        _ = _ := (eLpNorm_two_prod_rpow_eq hF.aestronglyMeasurable).symm
    rw [hEq]
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_lt_top.ne)
  have hbound : ∀ t, ∀ᵐ θ ∂μ, E t θ ≤ 4 * EF θ := by
    intro t
    filter_upwards [hsec] with θ hθ
    have htr : MeasurePreserving (fun h : ℝ ↦ h - t) volume volume :=
      measurePreserving_sub_right volume t
    have hnorm : eLpNorm (fun h ↦ F (h - t, θ) - F (h, θ)) 2 volume ≤
        2 * eLpNorm (fun h ↦ F (h, θ)) 2 volume := by
      calc
        _ ≤ eLpNorm (fun h ↦ F (h - t, θ)) 2 volume +
            eLpNorm (fun h ↦ F (h, θ)) 2 volume := eLpNorm_sub_le (by norm_num)
        _ = 2 * eLpNorm (fun h ↦ F (h, θ)) 2 volume := by
          rw [← eLpNorm_comp_measurePreserving hθ.aestronglyMeasurable htr]
          simp only [Function.comp_def]
          ring
    have hdt : MemLp (fun h ↦ F (h - t, θ) - F (h, θ)) 2 volume := by
      have hc := hθ.comp_measurePreserving htr
      exact hc.sub hθ
    have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hdt.aestronglyMeasurable
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hθ.aestronglyMeasurable
    dsimp [E, EF]
    calc
      (∫⁻ h, ‖D t (h, θ)‖ₑ ^ (2 : ℝ) ∂volume) =
          eLpNorm (fun h ↦ F (h - t, θ) - F (h, θ)) 2 volume ^ (2 : ℝ) := by
            dsimp [D]
            exact hp.symm
      _ ≤
          (2 * eLpNorm (fun h ↦ F (h, θ)) 2 volume) ^ (2 : ℝ) := by
            gcongr
      _ = 4 * eLpNorm (fun h ↦ F (h, θ)) 2 volume ^ (2 : ℝ) := by
        norm_num [ENNReal.rpow_two, mul_pow]
      _ = 4 * (∫⁻ h, ‖F (h, θ)‖ₑ ^ (2 : ℝ) ∂volume) :=
        congrArg (fun x : ENNReal ↦ 4 * x) hpow
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun t ↦ E t θ) (𝓝 0) (𝓝 0) := by
    filter_upwards [hsec] with θ hθ
    have hs := tendsto_eLpNorm_translate_sub hθ
    have heq : (fun t ↦ E t θ) =ᶠ[𝓝 0]
        (fun t ↦ eLpNorm (fun h ↦ F (h - t, θ) - F (h, θ)) 2 volume ^ (2 : ℝ)) := by
      filter_upwards [] with t
      dsimp [E]
      have hdt : MemLp (fun h ↦ F (h - t, θ) - F (h, θ)) 2 volume := by
        have htr : MeasurePreserving (fun h : ℝ ↦ h - t) volume volume :=
          measurePreserving_sub_right volume t
        have hc := hθ.comp_measurePreserving htr
        exact hc.sub hθ
      exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        hdt.aestronglyMeasurable).symm
    apply Filter.Tendsto.congr' heq.symm
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      using (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hs
  have hint : Tendsto (fun t ↦ ∫⁻ θ, E t θ ∂μ) (𝓝 0) (𝓝 0) := by
    have hbfin : (∫⁻ θ, 4 * EF θ ∂μ) ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
      exact (ENNReal.mul_lt_top (by norm_num) hEFint.lt_top).ne
    simpa using tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (F := E) (f := fun _ : ℝ => 0) (l := 𝓝 0) (fun θ ↦ 4 * EF θ)
      (Filter.Eventually.of_forall hEmeas) (Filter.Eventually.of_forall hbound) hbfin hlim
  have hsq : Tendsto (fun t ↦ eLpNorm (D t) 2 σ ^ (2 : ℝ)) (𝓝 0) (𝓝 0) := by
    convert hint using 1
    funext t
    rw [eLpNorm_two_prod_rpow_eq (hDmem t).aestronglyMeasurable]
    apply lintegral_congr_ae
    filter_upwards [ae_memLp_two_section (hDmem t)] with θ hθ
    dsimp [E]
    exact eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hθ.aestronglyMeasurable
  have hsqrt := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, ← ENNReal.rpow_mul] at hsqrt
  norm_num at hsqrt
  exact hsqrt

private theorem ae_abs_lt_mollifierMeasure {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ t ∂mollifierMeasure ε, |t| < ε := by
  rw [mollifierMeasure, ae_withDensity_iff
    ((contDiff_mollifierKernel ε).continuous.measurable.ennreal_ofReal)]
  filter_upwards [] with t ht
  have hk : mollifierKernel ε t ≠ 0 := by
    intro hk
    apply ht
    simp [hk]
  have hs : stdBump (t / ε) ≠ 0 := by
    intro hs
    apply hk
    simp [mollifierKernel, hs]
  have hmem : t / ε ∈ Function.support stdBump := hs
  rw [support_stdBump] at hmem
  rw [abs_lt]
  constructor
  · have h := (lt_div_iff₀ hε).mp (by simpa using hmem.1)
    nlinarith
  · have h := (div_lt_iff₀ hε).mp hmem.2
    nlinarith

/-- A uniform bound on small translations bounds the mollification error. -/
private theorem eLpNorm_mollifyFst_sub_le_of_translate_bound
    {μ : Measure ℝ} [SFinite μ] {ε : ℝ} {F : ℝ × ℝ → ℂ} {C : ENNReal}
    (hε : 0 < ε) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ))
    (hbound : ∀ t : ℝ, |t| < ε →
      eLpNorm (fun q ↦ F (q.1 - t, q.2) - F q) 2 ((volume : Measure ℝ).prod μ) ≤ C) :
    eLpNorm (mollifyFst ε F - F) 2 ((volume : Measure ℝ).prod μ) ≤ C := by
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  let ν := mollifierMeasure ε
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_mollifierMeasure hε
  let G : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ F (p.2.1 - p.1, p.2.2)
  let B : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ F p.2
  let D : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ G p - B p
  have hG : MemLp G 2 (ν.prod σ) := by
    simpa [G, ν, σ] using (memLp_translateFst (μ := μ) (ν := ν) hF).1
  have hB : MemLp B 2 (ν.prod σ) := by
    have h := hF.comp_measurePreserving (measurePreserving_snd :
      MeasurePreserving (fun p : ℝ × (ℝ × ℝ) ↦ p.2) (ν.prod σ) σ)
    simpa [B, σ, Function.comp_def] using h
  have hD : MemLp D 2 (ν.prod σ) := hG.sub hB
  have havg : mollifyFst ε F - F =ᵐ[σ]
      (fun q ↦ ∫ t, D (t, q) ∂ν) := by
    filter_upwards [ae_memLp_two_section hG] with q hq
    have hi : Integrable (fun t ↦ G (t, q)) ν := hq.integrable (by norm_num)
    have hc : Integrable (fun _ : ℝ ↦ F q) ν := integrable_const _
    change mollifyFst ε F q - F q = _
    rw [mollifyFst_eq_average hε F q]
    simp only [D, G, B]
    rw [integral_sub hi hc]
    simp [G, ν]
  have havg' : eLpNorm (mollifyFst ε F - F) 2 σ ≤
      eLpNorm (fun q ↦ ∫ t, D (t, q) ∂ν) 2 σ := by
    rw [eLpNorm_congr_ae havg]
  have havg_bound := (eLpNorm_integral_prob_le hD).2
  have hnormsq : eLpNorm D 2 (ν.prod σ) ^ (2 : ℝ) ≤ C ^ (2 : ℝ) := by
    rw [show eLpNorm D 2 (ν.prod σ) ^ (2 : ℝ) =
      ∫⁻ t, eLpNorm (fun q ↦ D (t, q)) 2 σ ^ (2 : ℝ) ∂ν by
      have hswap := eLpNorm_two_prod_rpow_eq (ν := σ) (σ := ν)
        (G := D ∘ Prod.swap) hD.aestronglyMeasurable.prod_swap
      calc
        eLpNorm D 2 (ν.prod σ) ^ (2 : ℝ) =
            eLpNorm (D ∘ Prod.swap) 2 (σ.prod ν) ^ (2 : ℝ) := by
              rw [eLpNorm_comp_measurePreserving hD.aestronglyMeasurable
                (Measure.measurePreserving_swap (μ := σ) (ν := ν))]
        _ = _ := hswap]
    calc
      _ ≤ ∫⁻ t, C ^ (2 : ℝ) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_abs_lt_mollifierMeasure hε] with t ht
        gcongr
        exact hbound t ht
      _ = C ^ (2 : ℝ) := by simp
  have hnorm : eLpNorm D 2 (ν.prod σ) ≤ C := by
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hnormsq
  exact havg'.trans (havg_bound.trans hnorm)

/-! ### `lem:line-mollifier` -/

section LineMollifier

variable {μ : Measure ℝ} [SFinite μ] {ε : ℝ} {F : ℝ × ℝ → ℂ}

/-- `M_ε` is a contraction of `L²(dh ⊗ μ)`. -/
theorem eLpNorm_mollifyFst_le (hε : 0 < ε) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    MemLp (mollifyFst ε F) 2 ((volume : Measure ℝ).prod μ) ∧
      eLpNorm (mollifyFst ε F) 2 ((volume : Measure ℝ).prod μ) ≤
        eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  let _ : IsProbabilityMeasure (mollifierMeasure ε) :=
    isProbabilityMeasure_mollifierMeasure hε
  have htranslate := memLp_translateFst (μ := μ) (ν := mollifierMeasure ε) hF
  have havg : mollifyFst ε F =
      (fun q : ℝ × ℝ ↦ ∫ t, F (q.1 - t, q.2) ∂mollifierMeasure ε) := by
    funext q
    exact mollifyFst_eq_average hε F q
  rw [havg]
  refine ⟨(eLpNorm_integral_prob_le htranslate.1).1, ?_⟩
  calc
    eLpNorm (fun q : ℝ × ℝ ↦ ∫ t, F (q.1 - t, q.2) ∂mollifierMeasure ε) 2
        ((volume : Measure ℝ).prod μ) ≤
        eLpNorm (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - p.1, p.2.2)) 2
          ((mollifierMeasure ε).prod ((volume : Measure ℝ).prod μ)) :=
      (eLpNorm_integral_prob_le htranslate.1).2
    _ = eLpNorm F 2 ((volume : Measure ℝ).prod μ) := htranslate.2

/-- `M_ε F → F` in `L²(dh ⊗ μ)`. -/
theorem tendsto_mollifyFst (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    Tendsto (fun ε ↦ eLpNorm (mollifyFst ε F - F) 2 ((volume : Measure ℝ).prod μ))
      (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have htr := (ENNReal.tendsto_nhds_zero.mp
    (tendsto_eLpNorm_translateFst_sub hF)) δ hδ
  rcases Metric.mem_nhds_iff.mp htr with ⟨η, hη, hηbound⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with ε hε hεη
  apply eLpNorm_mollifyFst_sub_le_of_translate_bound hε hF
  intro t ht
  apply hηbound
  have htη : |t| < η := lt_trans ht hεη
  exact Metric.mem_ball'.2 (by simpa [Real.dist_eq] using htη)

/-- `ε ∂_h M_ε F → 0` in `L²(dh ⊗ μ)`, because `ε ρ_ε'` is the rescaling of `ρ'`, which has
    integral zero. -/
theorem tendsto_smul_mollifyFstDeriv (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    (∀ ε > 0, MemLp (mollifyFstDeriv ε F) 2 ((volume : Measure ℝ).prod μ)) ∧
      Tendsto (fun ε ↦ eLpNorm (ε • mollifyFstDeriv ε F) 2 ((volume : Measure ℝ).prod μ))
        (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- The commutator with an `L`-Lipschitz function of `h` is `O(εL)`. -/
theorem eLpNorm_mollifyFst_mul_sub_le (hε : 0 < ε) {s : ℝ → ℝ} {L : ℝ≥0}
    (hs : LipschitzWith L s) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    eLpNorm (fun q ↦ mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q - (s q.1 : ℂ) * mollifyFst ε F q)
        2 ((volume : Measure ℝ).prod μ) ≤
      ENNReal.ofReal (ε * L) * eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  sorry

/-- `M_ε' F` is the weak `h`-derivative of `M_ε F`. -/
theorem hasWeakPartialOn_mollifyFst (hε : 0 < ε) (hF : LocallyIntegrable F) :
    HasWeakPartialOn univ 0 (mollifyFst ε F) (mollifyFstDeriv ε F) := by
  sorry

/-- `M_ε` commutes with weak derivatives. -/
theorem HasWeakPartialOn.mollify (hε : 0 < ε) {j : Fin 2} {G : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn univ j F G) :
    HasWeakPartialOn univ j (mollifyFst ε F) (mollifyFst ε G) := by
  sorry

/-- If `∂_h F = G` weakly, then `M_ε' F = M_ε G`. -/
theorem mollifyFstDeriv_ae_eq (hε : 0 < ε) {G : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn univ 0 F G) :
    mollifyFstDeriv ε F =ᵐ[volume] mollifyFst ε G := by
  sorry

end LineMollifier

end NoEmbeddedEigenvalues
