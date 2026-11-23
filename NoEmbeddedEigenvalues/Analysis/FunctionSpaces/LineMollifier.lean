module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal

/-!
# Mollification in one variable

Blueprint: `def:line-mollifier`, `lem:line-mollifier-kernel`,
`lem:line-mollifier-contraction`, `lem:line-mollifier-convergence`,
`lem:line-mollifier-cancellation`, `lem:line-mollifier-commutator` and
`lem:line-mollifier` (all proved).

Functions `F(h, θ)` on `ℝ²` are mollified in the first variable only,
`M_ε F(h, θ) = ∫ ρ_ε(h - h') F(h', θ) dh'` with `ρ_ε(h) = ε⁻¹ ρ(h/ε)` for a fixed smooth even
bump `ρ` supported in `[-1, 1]` with integral one. `L²` statements are for the measure
`dh ⊗ μ` with an arbitrary s-finite `μ` in `θ`, since `M_ε` acts on each line `θ = const`
separately. The contraction follows by probability averaging and a measure-preserving
translation, including joint a.e. measurability. Strong continuity of translations follows
fiberwise by dominated convergence, and the shrinking kernel support gives convergence of
mollification. The derivative kernel has zero mass, so its rescaled convolution is an
average of translation differences and tends to zero in `L²`. The Lipschitz commutator
is bounded by multiplication with `s(h - t) - s(h)` on the kernel support. This is the
one-dimensional input of the transversal mollifier (`TransversalMollifier.lean`), where
`(h, θ)` are action-angle coordinates.

For locally integrable input with planar Lebesgue measure, compact kernel support gives
local integrability of both convolutions by truncating the input on a compact set and
using a measure-preserving shear. Almost every angular line is locally integrable;
Mathlib's classical convolution derivative and one-dimensional integration by parts
therefore give the first weak derivative. Testing against translated test functions
proves commutation with existing weak derivatives. Uniqueness of weak derivatives
identifies the derivative-kernel convolution with mollification of the weak derivative.
-/

@[expose] public section

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

/-- Derivative of the rescaled bump. -/
theorem deriv_mollifierKernel (ε h : ℝ) :
    deriv (mollifierKernel ε) h = ε⁻¹ * ε⁻¹ * deriv stdBump (h / ε) := by
  by_cases hε : ε = 0
  · subst ε
    rw [show mollifierKernel 0 = (fun _ : ℝ => 0) by
      funext x
      simp [mollifierKernel]]
    simp
  · change deriv (fun x : ℝ => ε⁻¹ * stdBump (x / ε)) h = _
    have hdiv : HasDerivAt (fun x : ℝ => x / ε) ε⁻¹ h := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id h).mul_const ε⁻¹
    have hstd : HasDerivAt stdBump (deriv stdBump (h / ε)) (h / ε) := by
      exact (contDiff_stdBump.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hcomp := hstd.comp h hdiv
    have hmul := hcomp.const_mul ε⁻¹
    simpa only [Function.comp_apply, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv

/-- The derivative of the fixed bump has compact support. -/
theorem hasCompactSupport_deriv_stdBump : HasCompactSupport (deriv stdBump) := by
  have hs : HasCompactSupport stdBump := ContDiffBump.hasCompactSupport_normed _
  exact hs.deriv

/-- Rescaling the derivative kernel inside the mollification integral. -/
theorem smul_mollifyFstDeriv_eq_integral {ε : ℝ} (hε : 0 < ε)
    (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    ε • mollifyFstDeriv ε F q =
      ∫ t, deriv stdBump t • F (q.1 - ε * t, q.2) := by
  rw [mollifyFstDeriv]
  simp_rw [deriv_mollifierKernel]
  rw [← MeasureTheory.integral_smul]
  have hsub : (∫ a, (ε • (ε⁻¹ * ε⁻¹ * deriv stdBump ((q.1 - a) / ε))) •
        F (a, q.2)) =
      ∫ s, (ε • (ε⁻¹ * ε⁻¹ * deriv stdBump (s / ε))) •
        F (q.1 - s, q.2) := by
    let k : ℝ → ℂ := fun a ↦
      (ε • (ε⁻¹ * ε⁻¹ * deriv stdBump ((q.1 - a) / ε))) • F (a, q.2)
    have hmp : MeasurePreserving (MeasurableEquiv.subLeft q.1) volume volume :=
      volume.measurePreserving_sub_left q.1
    have hc := hmp.integral_comp' k
    simpa [k, MeasurableEquiv.subLeft, Equiv.subLeft, sub_sub_cancel] using hc.symm
  have hsub' : (∫ a, ε • (ε⁻¹ * ε⁻¹ * deriv stdBump ((q.1 - a) / ε)) •
        F (a, q.2)) =
      ∫ s, ε • (ε⁻¹ * ε⁻¹ * deriv stdBump (s / ε)) •
        F (q.1 - s, q.2) := by
    simpa only [smul_smul, smul_eq_mul] using hsub
  rw [hsub']
  let g : ℝ → ℂ := fun s ↦ deriv stdBump (s / ε) • F (q.1 - s, q.2)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g ε
  rw [abs_of_pos (inv_pos.mpr hε)] at hscale
  rw [MeasureTheory.integral_smul]
  have hpoint2 (x : ℝ) (z : ℂ) :
      (ε⁻¹ * ε⁻¹ * x) • z = ε⁻¹ • (ε⁻¹ • (x • z)) := by
    simp [mul_assoc]
  simp_rw [hpoint2]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  have hdiv (x : ℝ) : ε * x / ε = x := by
    field_simp [hε.ne']
  have hfun : (fun x ↦ g (ε * x)) =
      (fun x ↦ deriv stdBump x • F (q.1 - ε * x, q.2)) := by
    funext x
    simp [g, hdiv]
  rw [hfun] at hscale
  simpa [g, div_eq_mul_inv, smul_smul, mul_assoc, mul_comm, mul_left_comm,
    hε.ne'] using hscale.symm

/-- Averaging over a probability factor is an `L²` contraction. -/
theorem eLpNorm_integral_prob_le {α β : Type*}
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
            exact eNorm_integral_le_lintegral_eNorm _ |>.trans
              (lintegral_eNorm_le_eLpNorm_one)
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
        exact (AEMeasurable.pow_const hG.aestronglyMeasurable.eNorm 2)
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

/-- Translations of a scalar `L²` function are strongly continuous at the identity. -/
theorem tendsto_eLpNorm_translate_sub {G : Type*} [NormedAddCommGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] [μ.IsAddRightInvariant] {f : G → ℂ} (hf : MemLp f 2 μ) :
    Tendsto (fun t : G ↦ eLpNorm (fun x ↦ f (x - t) - f x) 2 μ)
      (𝓝 0) (𝓝 0) := by
  let fL : Lp ℂ 2 μ := hf.toLp f
  let g : G → C(G, G) := fun t =>
    ⟨fun x => x - t, (continuous_id.sub continuous_const)⟩
  have hg : Tendsto g (𝓝 0) (𝓝 (ContinuousMap.id G)) := by
    have hc : Continuous g := by
      apply ContinuousMap.continuous_of_continuous_uncurry g
      change Continuous (fun p : G × G => p.2 - p.1)
      fun_prop
    have hg0 : g 0 = ContinuousMap.id G := by ext x; simp [g]
    rw [← hg0]
    exact hc.tendsto 0
  have hgm : ∀ t : G, MeasurePreserving (g t) μ μ := by
    intro t
    exact measurePreserving_sub_right μ t
  have hcomp := Filter.Tendsto.compMeasurePreservingLp
    (tendsto_const_nhds : Tendsto (fun _ : G => fL) (𝓝 0) (𝓝 fL)) hg hgm
    (MeasurePreserving.id μ) (by norm_num : (2 : ENNReal) ≠ ⊤)
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
      (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 μ) x - f x
    have hx' : (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 μ) x = f (x - t) := by
      calc
        (Lp.compMeasurePreserving (g t) (hgm t) fL : Lp ℂ 2 μ) x = fL (g t x) := hx
        _ = f (x - t) := by
          simpa [g] using hfx
    rw [hx']

/-- The squared product `L²` norm is the integral of the squared fiber norms. -/
theorem eLpNorm_two_prod_rpow_eq {α β : Type*}
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
      exact (AEMeasurable.pow_const hG.eNorm 2)
    _ = ∫⁻ q, eLpNorm (fun t ↦ G (t, q)) 2 ν ^ (2 : ℝ) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hsec] with q hq
      exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hq).symm

/-- A square-integrable function on a product has square-integrable sections a.e. -/
theorem ae_memLp_two_section {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [SFinite ν] {σ : Measure β} [SFinite σ]
    {G : α × β → ℂ} (hG : MemLp G 2 (ν.prod σ)) :
    ∀ᵐ q ∂σ, MemLp (fun t ↦ G (t, q)) 2 ν := by
  have hsec : ∀ᵐ q ∂σ, AEStronglyMeasurable (fun t ↦ G (t, q)) ν :=
    hG.aestronglyMeasurable.prodMk_right
  let E : β → ENNReal := fun q ↦ ∫⁻ t, ‖G (t, q)‖ₑ ^ (2 : ℝ) ∂ν
  have hE : AEMeasurable E σ :=
    (AEMeasurable.pow_const hG.aestronglyMeasurable.eNorm 2).lintegral_prod_left'
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
    exact ((hDmem t).aestronglyMeasurable.eNorm.pow_const 2).lintegral_prod_left'
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

/-- Joint translation by a measurable parameter preserves the `L²` norm. -/
private theorem memLp_translateFst_param {μ ν : Measure ℝ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) (τ : ℝ → ℝ)
    (hτ : Measurable τ) :
    MemLp (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - τ p.1, p.2.2)) 2
        (ν.prod ((volume : Measure ℝ).prod μ)) ∧
      eLpNorm (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - τ p.1, p.2.2)) 2
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
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.1, g (τ p.1) p.2))
      (ν.prod σ) (ν.prod σ) := by
    refine (MeasurePreserving.id ν).skew_product (g := fun t q ↦ g (τ t) q)
      (μc := σ) (μd := σ) ?_ ?_
    · change Measurable (fun p : ℝ × (ℝ × ℝ) ↦
        (p.2.1 - τ p.1, p.2.2))
      exact ((measurable_fst.comp measurable_snd).sub
        (hτ.comp measurable_fst)).prodMk (measurable_snd.comp measurable_snd)
    · filter_upwards [] with t
      exact (hfiber (τ t)).map_eq
  have hS : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.1, (p.2.1 - τ p.1, p.2.2)))
      (ν.prod σ) (ν.prod σ) := by
    simpa [g] using hS'
  have hT : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) ↦ (p.2.1 - τ p.1, p.2.2)) (ν.prod σ) σ :=
    measurePreserving_snd.comp hS
  have hmem := hF.comp_measurePreserving hT
  have hnorm := eLpNorm_comp_measurePreserving (p := (2 : ENNReal))
    hF.aestronglyMeasurable hT
  constructor
  · simpa [σ, Function.comp_def] using hmem
  · simpa [σ, Function.comp_def] using hnorm

/-- `L²` continuity of scaled first-variable translations. -/
private theorem tendsto_eLpNorm_scaled_translateFst_sub
    {μ ν : Measure ℝ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    Tendsto (fun ε : ℝ ↦ eLpNorm
      (fun p : ℝ × (ℝ × ℝ) ↦ F (p.2.1 - ε * p.1, p.2.2) - F p.2) 2
      (ν.prod ((volume : Measure ℝ).prod μ))) (𝓝 0) (𝓝 0) := by
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  let D : ℝ → ℝ × (ℝ × ℝ) → ℂ :=
    fun ε p ↦ F (p.2.1 - ε * p.1, p.2.2) - F p.2
  have hDmem : ∀ ε : ℝ, MemLp (D ε) 2 (ν.prod σ) := by
    intro ε
    have hG := memLp_translateFst_param (μ := μ) (ν := ν) hF (fun t : ℝ ↦ ε * t)
      (measurable_const.mul measurable_id)
    have hB := hF.comp_measurePreserving (measurePreserving_snd :
      MeasurePreserving (fun p : ℝ × (ℝ × ℝ) ↦ p.2) (ν.prod σ) σ)
    have hsub := hG.1.sub hB
    convert hsub using 1
    funext p
    rfl
  have hEmeas : ∀ ε : ℝ, AEMeasurable
      (fun t : ℝ ↦ ∫⁻ q, ‖D ε (t, q)‖ₑ ^ (2 : ℝ) ∂σ) ν := by
    intro ε
    exact ((hDmem ε).aestronglyMeasurable.eNorm.pow_const 2).lintegral_prod_right'
  let E : ℝ → ℝ → ENNReal := fun ε t ↦
    ∫⁻ q, ‖D ε (t, q)‖ₑ ^ (2 : ℝ) ∂σ
  have hEmeas' : ∀ ε : ℝ, AEMeasurable (E ε) ν := by
    simpa [E] using hEmeas
  have hdt : ∀ ε t : ℝ, MemLp (fun q : ℝ × ℝ ↦
      F (q.1 - ε * t, q.2) - F q) 2 σ := by
    intro ε t
    have htr : MeasurePreserving (fun q : ℝ × ℝ ↦
        (q.1 - ε * t, q.2)) σ σ := by
      exact (measurePreserving_sub_right volume (ε * t)).prod
        (MeasurePreserving.id μ)
    exact (hF.comp_measurePreserving htr).sub hF
  have hEeq : ∀ ε t : ℝ, E ε t =
      eLpNorm (fun q : ℝ × ℝ ↦ F (q.1 - ε * t, q.2) - F q) 2 σ ^ (2 : ℝ) := by
    intro ε t
    dsimp [E, D]
    exact (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hdt ε t).aestronglyMeasurable).symm
  let C : ENNReal := 4 * eLpNorm F 2 σ ^ (2 : ℝ)
  have hbound : ∀ ε : ℝ, ∀ᵐ t ∂ν, E ε t ≤ C := by
    intro ε
    filter_upwards [] with t
    rw [hEeq]
    have htr : MeasurePreserving (fun q : ℝ × ℝ ↦
        (q.1 - ε * t, q.2)) σ σ := by
      exact (measurePreserving_sub_right volume (ε * t)).prod
        (MeasurePreserving.id μ)
    have hnorm : eLpNorm (fun q : ℝ × ℝ ↦
        F (q.1 - ε * t, q.2) - F q) 2 σ ≤ 2 * eLpNorm F 2 σ := by
      calc
        _ ≤ eLpNorm (fun q : ℝ × ℝ ↦ F (q.1 - ε * t, q.2)) 2 σ +
            eLpNorm F 2 σ := eLpNorm_sub_le (by norm_num)
        _ = 2 * eLpNorm F 2 σ := by
          rw [← eLpNorm_comp_measurePreserving hF.aestronglyMeasurable htr]
          simp only [Function.comp_def]
          ring
    dsimp [C]
    calc
      _ ≤ (2 * eLpNorm F 2 σ) ^ (2 : ℝ) := by gcongr
      _ = 4 * eLpNorm F 2 σ ^ (2 : ℝ) := by
        norm_num [ENNReal.rpow_two, mul_pow]
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun ε : ℝ ↦ E ε t) (𝓝 0) (𝓝 0) := by
    filter_upwards [] with t
    have hscale : Tendsto (fun ε : ℝ ↦ ε * t) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id.mul_const t : Tendsto (fun ε : ℝ ↦ ε * t)
        (𝓝 0) (𝓝 (0 * t)))
    have hs := (tendsto_eLpNorm_translateFst_sub hF).comp hscale
    have heq : (fun ε : ℝ ↦ E ε t) =
        (fun ε : ℝ ↦ eLpNorm (fun q : ℝ × ℝ ↦
          F (q.1 - ε * t, q.2) - F q) 2 σ ^ (2 : ℝ)) := by
      funext ε
      exact hEeq ε t
    rw [heq]
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      using (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hs
  have hbfin : (∫⁻ t, C ∂ν) ≠ ⊤ := by
    have hC : C < ⊤ := by
      dsimp [C]
      exact ENNReal.mul_lt_top (by norm_num)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_lt_top.ne)
    rw [lintegral_const, measure_univ]
    simpa only [mul_one] using hC.ne
  have hint : Tendsto (fun ε : ℝ ↦ ∫⁻ t, E ε t ∂ν) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_lintegral_filter_of_dominated_convergence'
      (μ := ν) (F := E) (f := fun _ : ℝ ↦ 0) (l := 𝓝 0) (fun _ : ℝ ↦ C)
      (Filter.Eventually.of_forall hEmeas') (Filter.Eventually.of_forall hbound) hbfin hlim
  have hsq : Tendsto (fun ε : ℝ ↦ eLpNorm (D ε) 2 (ν.prod σ) ^ (2 : ℝ))
      (𝓝 0) (𝓝 0) := by
    convert hint using 1
    funext ε
    have hswap := eLpNorm_two_prod_rpow_eq (ν := σ) (σ := ν)
      (G := (D ε) ∘ Prod.swap)
      (hDmem ε).aestronglyMeasurable.prod_swap
    calc
      eLpNorm (D ε) 2 (ν.prod σ) ^ (2 : ℝ) =
          eLpNorm ((D ε) ∘ Prod.swap) 2 (σ.prod ν) ^ (2 : ℝ) := by
            rw [eLpNorm_comp_measurePreserving (hDmem ε).aestronglyMeasurable
              (Measure.measurePreserving_swap (μ := σ) (ν := ν))]
      _ = ∫⁻ t, eLpNorm (fun q : ℝ × ℝ ↦ D ε (t, q)) 2 σ ^ (2 : ℝ) ∂ν := hswap
      _ = ∫⁻ t, E ε t ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [] with t
        rw [hEeq]
  have hsqrt := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, ← ENNReal.rpow_mul] at hsqrt
  norm_num at hsqrt
  simpa [D, σ] using hsqrt

/-! ### `lem:line-mollifier` -/

private def derivativeParamMeasure : Measure ℝ :=
  (2 : ENNReal)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)

private instance derivativeParamMeasure_isProbability :
    IsProbabilityMeasure derivativeParamMeasure := by
  refine ⟨?_⟩
  norm_num [derivativeParamMeasure, smul_apply, Real.volume_Icc,
    ENNReal.ofReal_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private theorem integral_two_deriv_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : ℝ → E) :
    (∫ t, ((2 : ℝ) • deriv stdBump t) • H t ∂derivativeParamMeasure) =
      ∫ t, deriv stdBump t • H t := by
  have hderiv : ∀ x ∉ Icc (-1 : ℝ) 1, deriv stdBump x • H x = 0 := by
    intro x hx
    have h' : x ∉ Function.support (deriv stdBump) := by
      intro h
      apply hx
      have h'' : x ∈ tsupport stdBump := support_deriv_subset h
      rw [show tsupport stdBump = closure (Ioo (-1 : ℝ) 1) by
        simp [tsupport, support_stdBump], closure_Ioo (by norm_num)] at h''
      exact h''
    simp [Function.mem_support] at h'
    simp [h']
  rw [derivativeParamMeasure, MeasureTheory.integral_smul_measure]
  norm_num
  calc
    (1 / 2 : ℝ) • (∫ x in Icc (-1 : ℝ) 1,
        ((2 : ℝ) • deriv stdBump x) • H x) =
        (1 / 2 : ℝ) • (∫ x in Icc (-1 : ℝ) 1,
          (2 : ℝ) • (deriv stdBump x • H x)) := by
            congr 2
            funext x
            simp [smul_smul]
    _ = ∫ x in Icc (-1 : ℝ) 1, deriv stdBump x • H x := by
      rw [integral_smul]
      simp
    _ = ∫ x, deriv stdBump x • H x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hderiv

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
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  let a : ℝ → ℝ := fun t ↦ (2 : ℝ) • deriv stdBump t
  have hda : Continuous (deriv stdBump) :=
    contDiff_stdBump.continuous_deriv (by norm_num)
  have ha : Continuous a := by
    dsimp [a]
    fun_prop
  have hsa : HasCompactSupport a := by
    dsimp [a]
    convert (hasCompactSupport_deriv_stdBump.smul_left :
      HasCompactSupport ((fun _ : ℝ ↦ (2 : ℝ)) • deriv stdBump)) using 1
  obtain ⟨C, hC⟩ := hda.bounded_above_of_compact_support
    hasCompactSupport_deriv_stdBump
  have ha_bound : ∀ t, ‖a t‖ ≤ 2 * C := by
    intro t
    dsimp [a]
    calc
      |2 * deriv stdBump t| = 2 * |deriv stdBump t| := by
        rw [abs_mul]
        norm_num
      _ ≤ 2 * C := by
        gcongr
        simpa [Real.norm_eq_abs] using hC t
  have hAmeas : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) ↦ a p.1)
      (derivativeParamMeasure.prod σ) := by
    exact (ha.measurable.comp measurable_fst).aestronglyMeasurable
  have hAtop : MemLp (fun p : ℝ × (ℝ × ℝ) ↦ a p.1) ⊤
      (derivativeParamMeasure.prod σ) := by
    apply memLp_top_of_bound hAmeas (2 * C)
    filter_upwards [] with p
    exact ha_bound p.1
  have ha_int : Integrable a derivativeParamMeasure :=
    ha.integrable_of_hasCompactSupport hsa
  have hderiv_zero : (∫ t, deriv stdBump t) = 0 := by
    simpa [deriv_mollifierKernel] using
      (integral_deriv_mollifierKernel (ε := (1 : ℝ)) (by norm_num))
  have ha_zero : (∫ t, a t ∂derivativeParamMeasure) = 0 := by
    have h := integral_two_deriv_smul (E := ℝ) (fun _ ↦ (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at h
    exact h.trans hderiv_zero
  have hbase : MemLp (fun p : ℝ × (ℝ × ℝ) ↦ F p.2) 2
      (derivativeParamMeasure.prod σ) := by
    have h := hF.comp_measurePreserving (measurePreserving_snd :
      MeasurePreserving (fun p : ℝ × (ℝ × ℝ) ↦ p.2)
        (derivativeParamMeasure.prod σ) σ)
    simpa [σ, Function.comp_def] using h
  have hmem : ∀ ε > 0, MemLp (mollifyFstDeriv ε F) 2 σ := by
    intro ε hε
    let G : ℝ × (ℝ × ℝ) → ℂ :=
      fun p ↦ F (p.2.1 - ε * p.1, p.2.2)
    let W : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ a p.1 • G p
    have hG := memLp_translateFst_param (μ := μ) (ν := derivativeParamMeasure)
      hF (fun t : ℝ ↦ ε * t) (measurable_const.mul measurable_id)
    have hW : MemLp W 2 (derivativeParamMeasure.prod σ) := by
      have h := MeasureTheory.MemLp.smul (p := (⊤ : ENNReal))
        (q := (2 : ENNReal)) (r := (2 : ENNReal)) hAtop hG.1
      convert h using 1
    have hWA := (eLpNorm_integral_prob_le hW).1
    have hWAeq : (fun q ↦ ∫ t, W (t, q) ∂derivativeParamMeasure) =
        (ε • mollifyFstDeriv ε F) := by
      funext q
      calc
        (∫ t, W (t, q) ∂derivativeParamMeasure) =
            ∫ t, deriv stdBump t • F (q.1 - ε * t, q.2) := by
              dsimp [W, G]
              simpa [a] using (integral_two_deriv_smul
                (E := ℂ) (fun t ↦ F (q.1 - ε * t, q.2)))
        _ = ε • mollifyFstDeriv ε F q :=
          (smul_mollifyFstDeriv_eq_integral hε F q).symm
    have hsmul : MemLp (ε • mollifyFstDeriv ε F) 2 σ := by
      rw [← hWAeq]
      exact hWA
    simpa [smul_smul, hε.ne'] using hsmul.const_smul (ε⁻¹ : ℝ)
  let D : ℝ → ℝ × (ℝ × ℝ) → ℂ := fun ε p ↦
    F (p.2.1 - ε * p.1, p.2.2) - F p.2
  let WD : ℝ → ℝ × (ℝ × ℝ) → ℂ := fun ε p ↦
    a p.1 • D ε p
  have hDmem : ∀ ε, MemLp (D ε) 2 (derivativeParamMeasure.prod σ) := by
    intro ε
    have hG := memLp_translateFst_param (μ := μ) (ν := derivativeParamMeasure)
      hF (fun t : ℝ ↦ ε * t) (measurable_const.mul measurable_id)
    have h := hG.1.sub hbase
    convert h using 1
  have hWDmem : ∀ ε, MemLp (WD ε) 2
      (derivativeParamMeasure.prod σ) := by
    intro ε
    have h := MeasureTheory.MemLp.smul (p := (⊤ : ENNReal))
      (q := (2 : ENNReal)) (r := (2 : ENNReal)) hAtop (hDmem ε)
    convert h using 1
  let K : ENNReal := eLpNorm (fun p : ℝ × (ℝ × ℝ) ↦ a p.1) ⊤
      (derivativeParamMeasure.prod σ)
  have hK : K ≠ ⊤ := by
    dsimp [K]
    exact (hAtop.eLpNorm_lt_top).ne
  have hDlim : Tendsto (fun ε : ℝ ↦ eLpNorm (D ε) 2
      (derivativeParamMeasure.prod σ)) (𝓝 0) (𝓝 0) := by
    simpa [D] using (tendsto_eLpNorm_scaled_translateFst_sub
      (μ := μ) (ν := derivativeParamMeasure) hF)
  have hWDlim : Tendsto (fun ε : ℝ ↦ eLpNorm (WD ε) 2
      (derivativeParamMeasure.prod σ)) (𝓝 0) (𝓝 0) := by
    have hprod : Tendsto (fun ε : ℝ ↦ K * eLpNorm (D ε) 2
        (derivativeParamMeasure.prod σ)) (𝓝 0) (𝓝 0) := by
      simpa [K] using ENNReal.Tendsto.const_mul hDlim (Or.inr hK)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ENNReal))
        (𝓝 0) (𝓝 0)) hprod
    · intro ε
      exact bot_le
    · intro ε
      exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hAmeas
  have hAvgDlim : Tendsto (fun ε : ℝ ↦ eLpNorm
      (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) 2 σ)
      (𝓝 0) (𝓝 0) := by
    have hprod : ∀ ε, eLpNorm
        (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) 2 σ ≤
        eLpNorm (WD ε) 2 (derivativeParamMeasure.prod σ) := by
      intro ε
      exact (eLpNorm_integral_prob_le (hWDmem ε)).2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ENNReal))
        (𝓝 0) (𝓝 0)) hWDlim
    · intro ε
      exact bot_le
    · intro ε
      exact hprod ε
  have hcancel : ∀ ε > 0, (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) =ᵐ[σ]
      (ε • mollifyFstDeriv ε F) := by
    intro ε hε
    let G : ℝ × (ℝ × ℝ) → ℂ :=
      fun p ↦ F (p.2.1 - ε * p.1, p.2.2)
    let W : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ a p.1 • G p
    have hG := memLp_translateFst_param (μ := μ) (ν := derivativeParamMeasure)
      hF (fun t : ℝ ↦ ε * t) (measurable_const.mul measurable_id)
    have hW : MemLp W 2 (derivativeParamMeasure.prod σ) := by
      have h := MeasureTheory.MemLp.smul (p := (⊤ : ENNReal))
        (q := (2 : ENNReal)) (r := (2 : ENNReal)) hAtop hG.1
      convert h using 1
    have hsec := ae_memLp_two_section hW
    filter_upwards [hsec] with q hq
    have hi : Integrable (fun t ↦ W (t, q)) derivativeParamMeasure :=
      hq.integrable (by norm_num)
    have hi0 : Integrable (fun t : ℝ ↦ a t • F q) derivativeParamMeasure :=
      ha_int.smul_const (F q)
    calc
      (∫ t, WD ε (t, q) ∂derivativeParamMeasure) =
          ∫ t, W (t, q) - a t • F q ∂derivativeParamMeasure := by
            apply integral_congr_ae
            filter_upwards [] with t
            simp [WD, D, W, G]
            ring
      _ = (∫ t, W (t, q) ∂derivativeParamMeasure) -
          ∫ t, a t • F q ∂derivativeParamMeasure := integral_sub hi hi0
      _ = (∫ t, W (t, q) ∂derivativeParamMeasure) := by
        rw [integral_smul_const, ha_zero]
        simp
      _ = ε • mollifyFstDeriv ε F q := by
        dsimp [W, G]
        calc
          (∫ t, a t • F (q.1 - ε * t, q.2) ∂derivativeParamMeasure) =
              ∫ t, deriv stdBump t • F (q.1 - ε * t, q.2) := by
                simpa [a] using (integral_two_deriv_smul
                  (E := ℂ) (fun t ↦ F (q.1 - ε * t, q.2)))
          _ = ε • mollifyFstDeriv ε F q :=
            (smul_mollifyFstDeriv_eq_integral hε F q).symm
  have hnorm : Tendsto (fun ε : ℝ ↦ eLpNorm
      (ε • mollifyFstDeriv ε F) 2 σ) (𝓝[>] 0) (𝓝 0) := by
    have heq : (fun ε : ℝ ↦ eLpNorm (ε • mollifyFstDeriv ε F) 2 σ) =ᶠ[(𝓝[>] 0)]
        (fun ε ↦ eLpNorm (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) 2 σ) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [eLpNorm_congr_ae (hcancel ε hε)]
    have hAvgDlim' : Tendsto
        (fun ε : ℝ ↦ eLpNorm (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) 2 σ)
        (𝓝[>] 0) (𝓝 0) := hAvgDlim.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    exact Filter.Tendsto.congr' (f₁ := fun ε : ℝ ↦
        eLpNorm (fun q ↦ ∫ t, WD ε (t, q) ∂derivativeParamMeasure) 2 σ)
      (f₂ := fun ε : ℝ ↦ eLpNorm (ε • mollifyFstDeriv ε F) 2 σ)
      (l₁ := 𝓝[>] (0 : ℝ)) (l₂ := 𝓝 0) heq.symm hAvgDlim'
  refine ⟨hmem, ?_⟩
  exact hnorm

/-- The commutator with an `L`-Lipschitz function of `h` is `O(εL)`. -/
theorem eLpNorm_mollifyFst_mul_sub_le (hε : 0 < ε) {s : ℝ → ℝ} {L : ℝ≥0}
    (hs : LipschitzWith L s) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    eLpNorm (fun q ↦ mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q - (s q.1 : ℂ) * mollifyFst ε F q)
        2 ((volume : Measure ℝ).prod μ) ≤
      ENNReal.ofReal (ε * L) * eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  let σ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod μ
  let ν := mollifierMeasure ε
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_mollifierMeasure hε
  let G : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ F (p.2.1 - p.1, p.2.2)
  let A : ℝ × (ℝ × ℝ) → ℝ :=
    fun p ↦ s (p.2.1 - p.1) - s p.2.1
  let H : ℝ × (ℝ × ℝ) → ℂ := fun p ↦ A p • G p
  have hG := memLp_translateFst (μ := μ) (ν := ν) hF
  have hGmem : MemLp G 2 (ν.prod σ) := by
    simpa [G, ν, σ] using hG.1
  have hGnorm : eLpNorm G 2 (ν.prod σ) = eLpNorm F 2 σ := by
    simpa [G, ν, σ] using hG.2
  have hAmeas : Measurable A := by
    have hsc : Continuous s := hs.continuous
    dsimp [A]
    fun_prop
  have hAbound : ∀ᵐ p ∂(ν.prod σ), ‖A p‖ ≤ ε * (L : ℝ) := by
    have ht := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := σ)).ae
      (ae_abs_lt_mollifierMeasure hε)
    filter_upwards [ht] with p hp
    have hdist := hs.dist_le_mul (p.2.1 - p.1) p.2.1
    calc
      ‖A p‖ = |s (p.2.1 - p.1) - s p.2.1| := by simp [A, Real.norm_eq_abs]
      _ = dist (s (p.2.1 - p.1)) (s p.2.1) := by rw [Real.dist_eq]
      _ ≤ (L : ℝ) * dist (p.2.1 - p.1) p.2.1 := hdist
      _ = (L : ℝ) * |p.1| := by
        rw [Real.dist_eq]
        congr 1
        simp
      _ ≤ ε * (L : ℝ) := by
        have hple : |p.1| ≤ ε := le_of_lt hp
        calc
          (L : ℝ) * |p.1| ≤ (L : ℝ) * ε :=
            mul_le_mul_of_nonneg_left hple L.2
          _ = ε * (L : ℝ) := by ring
  have hAtop : MemLp A ⊤ (ν.prod σ) :=
    memLp_top_of_bound hAmeas.aestronglyMeasurable (ε * (L : ℝ)) hAbound
  have hAnorm : eLpNorm A ⊤ (ν.prod σ) ≤ ENNReal.ofReal (ε * (L : ℝ)) := by
    rw [eLpNorm_exponent_top hAmeas.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hAbound
  have hHmem : MemLp H 2 (ν.prod σ) := by
    have h := MeasureTheory.MemLp.smul (p := (⊤ : ENNReal))
      (q := (2 : ENNReal)) (r := (2 : ENNReal)) hAtop hGmem
    convert h using 1
  have hcomm : (fun q ↦ mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q -
      (s q.1 : ℂ) * mollifyFst ε F q) =ᵐ[σ]
      (fun q ↦ ∫ t, H (t, q) ∂ν) := by
    filter_upwards [ae_memLp_two_section hGmem, ae_memLp_two_section hHmem] with q hGq hHq
    have hiG : Integrable (fun t ↦ G (t, q)) ν := hGq.integrable (by norm_num)
    have hiH : Integrable (fun t ↦ H (t, q)) ν := hHq.integrable (by norm_num)
    have hiCG : Integrable (fun t ↦ (s q.1 : ℂ) • G (t, q)) ν := by
      simpa [smul_eq_mul, mul_comm] using hiG.smul_const (s q.1 : ℂ)
    have hiK : Integrable (fun t ↦ (s (q.1 - t) : ℂ) • G (t, q)) ν := by
      have hi := hiH.add hiCG
      convert hi using 1
      funext t
      dsimp [H, A]
      rw [Complex.ofReal_sub]
      ring
    calc
      mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q -
          (s q.1 : ℂ) * mollifyFst ε F q =
          (∫ t, (s (q.1 - t) : ℂ) • G (t, q) ∂ν) -
            (s q.1 : ℂ) * (∫ t, G (t, q) ∂ν) := by
              rw [mollifyFst_eq_average hε, mollifyFst_eq_average hε]
              rfl
      _ = (∫ t, (s (q.1 - t) : ℂ) • G (t, q) ∂ν) -
          (∫ t, (s q.1 : ℂ) • G (t, q) ∂ν) := by
            change _ - (s q.1 : ℂ) • (∫ t, G (t, q) ∂ν) = _
            rw [hiG.integral_smul]
      _ = ∫ t, (s (q.1 - t) : ℂ) • G (t, q) -
          (s q.1 : ℂ) • G (t, q) ∂ν := (integral_sub hiK hiCG).symm
      _ = (∫ t, H (t, q) ∂ν) := by
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [H, A, G]
        rw [Complex.ofReal_sub]
        ring
  calc
    eLpNorm (fun q ↦ mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q -
        (s q.1 : ℂ) * mollifyFst ε F q) 2 σ =
        eLpNorm (fun q ↦ ∫ t, H (t, q) ∂ν) 2 σ := eLpNorm_congr_ae hcomm
    _ ≤ eLpNorm H 2 (ν.prod σ) := (eLpNorm_integral_prob_le hHmem).2
    _ ≤ eLpNorm A ⊤ (ν.prod σ) * eLpNorm G 2 (ν.prod σ) :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hAmeas.aestronglyMeasurable
    _ ≤ ENNReal.ofReal (ε * (L : ℝ)) * eLpNorm F 2 σ := by
      calc
        eLpNorm A ⊤ (ν.prod σ) * eLpNorm G 2 (ν.prod σ) ≤
            ENNReal.ofReal (ε * (L : ℝ)) * eLpNorm G 2 (ν.prod σ) :=
          mul_le_mul_of_nonneg_right hAnorm bot_le
        _ = ENNReal.ofReal (ε * (L : ℝ)) * eLpNorm F 2 σ := by rw [hGnorm]

/-! ### Local integrability and weak derivatives -/

private def convolveLine (k : ℝ → ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ t, k t • F (q.1 - t, q.2)

private theorem convolveLine_eq (k : ℝ → ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    convolveLine k F q = ∫ t, k (q.1 - t) • F (t, q.2) := by
  have hmp : MeasurePreserving (MeasurableEquiv.subLeft q.1) volume volume :=
    volume.measurePreserving_sub_left q.1
  simpa [convolveLine, MeasurableEquiv.subLeft, Equiv.subLeft, sub_sub_cancel] using
    hmp.integral_comp' (fun t ↦ k (q.1 - t) • F (t, q.2))

private theorem measurePreserving_lineShift :
    MeasurePreserving (fun z : ℝ × (ℝ × ℝ) ↦ (z.1, (z.2.1 - z.1, z.2.2)))
      ((volume : Measure ℝ).prod volume) (volume.prod volume) := by
  refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
    (g := fun t q ↦ (q.1 - t, q.2)) ?_ ?_
  · fun_prop
  · filter_upwards [] with t
    exact ((measurePreserving_sub_right volume t).prod (MeasurePreserving.id volume)).map_eq

private theorem integrable_lineIntegrand {k : ℝ → ℝ} (hk : Integrable k)
    (hF : Integrable F) :
    Integrable (fun z : ℝ × (ℝ × ℝ) ↦ k z.1 • F (z.2.1 - z.1, z.2.2))
      ((volume : Measure ℝ).prod volume) := by
  have hi := hk.smul_prod hF
  exact (measurePreserving_lineShift.integrable_comp hi.aestronglyMeasurable).mpr hi

/-- On compact output sets, only a compact part of the locally integrable input is sampled. -/
private theorem integrable_lineIntegrand_restrict {k : ℝ → ℝ} (hk : Integrable k)
    (hks : HasCompactSupport k) (hF : LocallyIntegrable F) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) :
    Integrable (fun z : ℝ × (ℝ × ℝ) ↦ k z.1 • F (z.2.1 - z.1, z.2.2))
      ((volume : Measure ℝ).prod (volume.restrict K)) := by
  classical
  let L := (fun z : ℝ × (ℝ × ℝ) ↦ (z.2.1 - z.1, z.2.2)) '' (tsupport k ×ˢ K)
  have hL : IsCompact L := (hks.prod hK).image (by fun_prop)
  have hFL : Integrable (L.indicator F) :=
    (integrable_indicator_iff hL.measurableSet).mpr (hF.integrableOn_isCompact hL)
  have hi := (integrable_lineIntegrand hk hFL).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := K)))
  apply hi.congr
  have hq : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume.restrict K)), z.2 ∈ K :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hK.measurableSet)
  filter_upwards [hq] with z hz
  by_cases ht : k z.1 = 0
  · simp [ht]
  · have hm : (z.2.1 - z.1, z.2.2) ∈ L :=
      ⟨z, ⟨subset_closure ht, hz⟩, rfl⟩
    simp [Set.indicator_of_mem hm]

private theorem locallyIntegrable_convolveLine {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) (hF : LocallyIntegrable F) :
    LocallyIntegrable (convolveLine k F) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (integrable_lineIntegrand_restrict (hk.integrable_of_hasCompactSupport hks)
    hks hF hK).integral_prod_right

/-- Almost every line of a locally integrable planar function is locally integrable. -/
private theorem ae_locallyIntegrable_line (hF : LocallyIntegrable F) :
    ∀ᵐ θ ∂(volume : Measure ℝ), LocallyIntegrable (fun h ↦ F (h, θ)) := by
  have hboxes : ∀ n : ℕ, ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Icc (-(n : ℝ)) n → IntegrableOn (fun h ↦ F (h, θ)) (Icc (-(n : ℝ)) n) := by
    intro n
    have hi := hF.integrableOn_isCompact
      ((isCompact_Icc : IsCompact (Icc (-(n : ℝ)) n)).prod
        (isCompact_Icc : IsCompact (Icc (-(n : ℝ)) n)))
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
    exact (ae_restrict_iff' measurableSet_Icc).mp hi.prod_left_ae
  filter_upwards [ae_all_iff.mpr hboxes] with θ hθ
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (max |θ| |x|)
  have ht : |θ| < n := (le_max_left _ _).trans_lt hn
  have hx : |x| < n := (le_max_right _ _).trans_lt hn
  refine ⟨Icc (-(n : ℝ)) n, Icc_mem_nhds (abs_lt.mp hx).1 (abs_lt.mp hx).2, ?_⟩
  exact hθ n ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩

private theorem hasDerivAt_convolveLine {k : ℝ → ℝ} (hk : ContDiff ℝ 1 k)
    (hks : HasCompactSupport k) {θ : ℝ} (hF : LocallyIntegrable (fun h ↦ F (h, θ)))
    (x : ℝ) : HasDerivAt (fun h ↦ convolveLine k F (h, θ))
      (convolveLine (deriv k) F (x, θ)) x := by
  have hd := HasCompactSupport.hasDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip hF hks hk x
  convert hd using 1
  · funext h
    exact convolveLine_eq k F (h, θ)
  · exact convolveLine_eq (deriv k) F (x, θ)

private theorem hasWeakPartialOn_convolveLine {k : ℝ → ℝ} (hk : ContDiff ℝ 1 k)
    (hks : HasCompactSupport k) (hF : LocallyIntegrable F) :
    HasWeakPartialOn univ 0 (convolveLine k F) (convolveLine (deriv k) F) := by
  have hM := locallyIntegrable_convolveLine hk.continuous hks hF
  have hD := locallyIntegrable_convolveLine (hk.continuous_deriv le_rfl) hks.deriv hF
  refine ⟨hM.locallyIntegrableOn univ, hD.locallyIntegrableOn univ, fun φ hφ ↦ ?_⟩
  have i1 : Integrable (fun p ↦ convolveLine k F p * coordPartial 0 φ p)
      ((volume : Measure ℝ).prod volume) :=
    integrable_mul_of_tsupport_subset (hM.locallyIntegrableOn univ)
      (hφ.continuous_coordPartial 0) (hφ.hasCompactSupport_coordPartial 0) (subset_univ _)
  have i2 : Integrable (fun p ↦ convolveLine (deriv k) F p * φ p)
      ((volume : Measure ℝ).prod volume) :=
    integrable_mul_of_tsupport_subset (hD.locallyIntegrableOn univ)
      hφ.contDiff.continuous hφ.hasCompactSupport (subset_univ _)
  have i3 : Integrable (fun p ↦ convolveLine k F p * φ p)
      ((volume : Measure ℝ).prod volume) :=
    integrable_mul_of_tsupport_subset (hM.locallyIntegrableOn univ)
      hφ.contDiff.continuous hφ.hasCompactSupport (subset_univ _)
  calc
    _ = ∫ θ, ∫ h, convolveLine k F (h, θ) * coordPartial 0 φ (h, θ) :=
      integral_prod_symm _ i1
    _ = ∫ θ, -(∫ h, convolveLine (deriv k) F (h, θ) * φ (h, θ)) := by
      apply integral_congr_ae
      filter_upwards [ae_locallyIntegrable_line hF, i1.prod_left_ae,
        i2.prod_left_ae, i3.prod_left_ae] with θ hθ h1 h2 h3
      apply integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := fun h ↦ convolveLine k F (h, θ)) (v := fun h ↦ φ (h, θ))
      · intro x _
        exact hasDerivAt_convolveLine hk hks hθ x
      · intro x _
        simpa [coordPartial] using
          hasDerivAt_partialX (p := (x, θ))
            ((hφ.contDiff.of_le (by simp) : ContDiff ℝ 1 φ).differentiable one_ne_zero _)
      · exact h1
      · exact h2
      · exact h3
    _ = _ := by rw [integral_neg, ← integral_prod_symm _ i2, Measure.volume_eq_prod]

private theorem mollifyFst_eq_convolveLine :
    mollifyFst ε F = convolveLine (mollifierKernel ε) F :=
  funext fun q ↦ (convolveLine_eq _ _ q).symm

private theorem mollifyFstDeriv_eq_convolveLine :
    mollifyFstDeriv ε F = convolveLine (deriv (mollifierKernel ε)) F :=
  funext fun q ↦ (convolveLine_eq _ _ q).symm

/-- `M_ε' F` is the weak `h`-derivative of `M_ε F`. -/
theorem hasWeakPartialOn_mollifyFst (hε : 0 < ε) (hF : LocallyIntegrable F) :
    HasWeakPartialOn univ 0 (mollifyFst ε F) (mollifyFstDeriv ε F) := by
  rw [mollifyFst_eq_convolveLine, mollifyFstDeriv_eq_convolveLine]
  exact hasWeakPartialOn_convolveLine ((contDiff_mollifierKernel ε).of_le (by simp))
    (hasCompactSupport_mollifierKernel hε) hF

/-- The test factor makes the double integral globally integrable. -/
private theorem integrable_lineIntegrand_mul_test {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) (hF : LocallyIntegrable F) {ψ : ℝ × ℝ → ℂ}
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × (ℝ × ℝ) ↦ (k z.1 • F (z.2.1 - z.1, z.2.2)) * ψ z.2)
      ((volume : Measure ℝ).prod volume) := by
  have hi := integrable_lineIntegrand_restrict (hk.integrable_of_hasCompactSupport hks)
    hks hF hψs
  obtain ⟨C, hC⟩ := hψs.exists_bound_of_continuous hψ
  have hm := hi.mul_bdd (hψ.measurable.comp measurable_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z ↦ hC z.2))
  have hlocal : IntegrableOn
      (fun z : ℝ × (ℝ × ℝ) ↦ (k z.1 • F (z.2.1 - z.1, z.2.2)) * ψ z.2)
      (univ ×ˢ tsupport ψ) ((volume : Measure ℝ).prod volume) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
      Function.comp_apply] using hm
  apply hlocal.integrable_of_forall_notMem_eq_zero
  intro z hz
  have hq : z.2 ∉ tsupport ψ := fun h ↦ hz ⟨mem_univ _, h⟩
  rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]

private theorem integral_convolveLine_mul_test {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) (hF : LocallyIntegrable F) {ψ : ℝ × ℝ → ℂ}
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    (∫ q, convolveLine k F q * ψ q) =
      ∫ t, k t • ∫ q, F (q.1 - t, q.2) * ψ q := by
  have hi := integrable_lineIntegrand_mul_test hk hks hF hψ hψs
  calc
    _ = ∫ q, ∫ t, (k t • F (q.1 - t, q.2)) * ψ q := by
      simp only [convolveLine, integral_mul_const]
    _ = ∫ t, ∫ q, (k t • F (q.1 - t, q.2)) * ψ q := integral_integral_swap hi.swap
    _ = _ := by simp only [smul_mul_assoc, integral_smul]

/-- Coordinate partial derivatives commute with translations. -/
theorem coordPartial_translate (j : Fin 2) (φ : ℝ × ℝ → ℂ)
    (v q : ℝ × ℝ) :
    coordPartial j (fun p ↦ φ (p + v)) q = coordPartial j φ (q + v) := by
  fin_cases j
  · change deriv (fun h ↦ φ (h + v.1, q.2 + v.2)) q.1 =
      deriv (fun h ↦ φ (h, q.2 + v.2)) (q.1 + v.1)
    exact deriv_comp_add_const (fun h ↦ φ (h, q.2 + v.2)) v.1 q.1
  · change deriv (fun h ↦ φ (q.1 + v.1, h + v.2)) q.2 =
      deriv (fun h ↦ φ (q.1 + v.1, h)) (q.2 + v.2)
    exact deriv_comp_add_const (fun h ↦ φ (q.1 + v.1, h)) v.2 q.2

private theorem integral_translate_mul_coordPartial {j : Fin 2} {G : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn univ j F G) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn univ φ) (t : ℝ) :
    (∫ q, F (q.1 - t, q.2) * coordPartial j φ q) =
      -(∫ q, G (q.1 - t, q.2) * φ q) := by
  let ψ : ℝ × ℝ → ℂ := fun p ↦ φ (p + (t, 0))
  have hψ : IsTestFunctionOn univ ψ :=
    ⟨hφ.contDiff.comp (contDiff_id.add contDiff_const),
      hφ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (t, 0)), subset_univ _⟩
  have hmp : MeasurePreserving (MeasurableEquiv.addRight (t, (0 : ℝ))) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume t).prod
      (measurePreserving_add_right volume (0 : ℝ))
  calc
    _ = ∫ p, F p * coordPartial j ψ p := by
      simpa [ψ, coordPartial_translate] using
        (hmp.integral_comp' (fun q ↦ F (q.1 - t, q.2) * coordPartial j φ q)).symm
    _ = -(∫ p, G p * ψ p) := hd.2.2 ψ hψ
    _ = _ := by
      congr 1
      simpa [ψ] using hmp.integral_comp' (fun q ↦ G (q.1 - t, q.2) * φ q)

private theorem weakPartial_convolveLine {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {j : Fin 2} {G : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn univ j F G) :
    HasWeakPartialOn univ j (convolveLine k F) (convolveLine k G) := by
  have hF := locallyIntegrableOn_univ.mp hd.1
  have hG := locallyIntegrableOn_univ.mp hd.2.1
  refine ⟨(locallyIntegrable_convolveLine hk hks hF).locallyIntegrableOn univ,
    (locallyIntegrable_convolveLine hk hks hG).locallyIntegrableOn univ, fun φ hφ ↦ ?_⟩
  rw [integral_convolveLine_mul_test hk hks hF
    (hφ.continuous_coordPartial j) (hφ.hasCompactSupport_coordPartial j),
    integral_convolveLine_mul_test hk hks hG hφ.contDiff.continuous hφ.hasCompactSupport]
  simp_rw [integral_translate_mul_coordPartial hd hφ, smul_neg, integral_neg]

/-- `M_ε` commutes with weak derivatives. -/
theorem HasWeakPartialOn.mollify (hε : 0 < ε) {j : Fin 2} {G : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn univ j F G) :
    HasWeakPartialOn univ j (mollifyFst ε F) (mollifyFst ε G) := by
  rw [mollifyFst_eq_convolveLine, mollifyFst_eq_convolveLine]
  exact weakPartial_convolveLine (contDiff_mollifierKernel ε).continuous
    (hasCompactSupport_mollifierKernel hε) hd

/-- If `∂_h F = G` weakly, then `M_ε' F = M_ε G`. -/
theorem mollifyFstDeriv_ae_eq (hε : 0 < ε) {G : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn univ 0 F G) :
    mollifyFstDeriv ε F =ᵐ[volume] mollifyFst ε G := by
  have h1 := hasWeakPartialOn_mollifyFst hε (locallyIntegrableOn_univ.mp hd.1)
  have h2 := hd.mollify hε
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrableOn_univ.mp h1.2.1) (locallyIntegrableOn_univ.mp h2.2.1)
  intro ψ hψ hψs
  let φ : ℝ × ℝ → ℂ := fun p ↦ (ψ p : ℂ)
  have hφ : IsTestFunctionOn univ φ :=
    ⟨Complex.ofRealCLM.contDiff.comp hψ,
      hψs.comp_left (g := Complex.ofReal) (by simp), subset_univ _⟩
  have he : (∫ p, mollifyFstDeriv ε F p * φ p) = ∫ p, mollifyFst ε G p * φ p :=
    neg_injective ((h1.2.2 φ hφ).symm.trans (h2.2.2 φ hφ))
  simpa only [φ, Complex.real_smul, mul_comm] using he

end LineMollifier

end NoEmbeddedEigenvalues
