import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1

/-!
# The canonical transport profile

Blueprint: `def:canonical-profile`, `lem:canonical-profile-ode`,
`lem:canonical-profile-ac`, `lem:canonical-profile-unique`,
`lem:canonical-profile-decay`, `lem:canonical-profile-weighted`.

Local absolute continuity follows by writing the tail as a constant minus a
primitive, applying Mathlib's real-valued primitive theorem to the real and imaginary
parts, and multiplying by the smooth exponential factor. An integrating factor
proves uniqueness among locally absolutely continuous solutions decaying at `+∞`.
Integration by parts on finite intervals, followed by the improper-integral limit,
transfers exponential endpoint decay of `g` to the profile. The weighted `L²` estimate
uses a positive kernel with row integrals one and column integrals at most one;
Cauchy–Schwarz and Tonelli in `ℝ≥0∞` also cover infinite right-hand norms.

For a trace `g` on a separatrix arc with `g' ∈ L¹(ℝ)`, the canonical profile is
`Ω(s) = e^{iλs} ∫_s^∞ g'(t) e^{-iλt} dt` and the canonical transport unknown is
`z = -(Ω + g)/λ`. Lebesgue differentiation gives `Ω' = iλΩ - g'` almost everywhere, hence
`Pz = -Ω` and `(P - λ)z = g` for `P = -i∂ₛ` wherever `g` is differentiable. The profile
tends to `0` at `+∞`; it tends to `0` at `-∞` exactly when the Melnikov condition
`∫ g'(t) e^{-iλt} dt = 0` holds, and then it equals `-e^{iλs} ∫_{-∞}^s g'(t) e^{-iλt} dt`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The integrand `g'(t) e^{-iλt}` of the canonical profile. -/
def profileIntegrand (lam : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ := deriv g t * exp (-(I * lam * t))

/-- The canonical profile `Ω(s) = e^{iλs} ∫_s^∞ g'(t) e^{-iλt} dt`. -/
def canonicalProfile (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  exp (I * lam * s) * ∫ t in Ioi s, profileIntegrand lam g t

/-- The canonical transport unknown `z = -(Ω + g)/λ`. -/
def canonicalUnknown (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  -(canonicalProfile lam g s + g s) / lam

theorem norm_exp_I_mul (lam s : ℝ) : ‖exp (I * lam * s)‖ = 1 := by
  rw [show I * lam * s = ((lam * s : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

theorem norm_exp_neg_I_mul (lam s : ℝ) : ‖exp (-(I * lam * s))‖ = 1 := by
  rw [show -(I * lam * s) = ((-(lam * s) : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

section Profile

variable {lam : ℝ} {g : ℝ → ℂ}

theorem integrable_profileIntegrand (hg : Integrable (deriv g)) :
    Integrable (profileIntegrand lam g) := by
  refine hg.mono (hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
    exp (-(I * lam * t))).aestronglyMeasurable) (Eventually.of_forall fun t ↦ ?_)
  rw [profileIntegrand, norm_mul, norm_exp_neg_I_mul, mul_one]

/-- The tail integral `∫_s^∞` as a constant minus an indefinite integral. -/
theorem integral_Ioi_profileIntegrand (hg : Integrable (deriv g)) (s : ℝ) :
    ∫ t in Ioi s, profileIntegrand lam g t =
      (∫ t in Ioi 0, profileIntegrand lam g t) - ∫ t in (0 : ℝ)..s, profileIntegrand lam g t := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  rw [← intervalIntegral.integral_interval_add_Ioi hq.integrableOn hq.integrableOn,
    intervalIntegral.integral_symm 0 s]
  ring

theorem norm_canonicalProfile (lam : ℝ) (g : ℝ → ℂ) (s : ℝ) :
    ‖canonicalProfile lam g s‖ = ‖∫ t in Ioi s, profileIntegrand lam g t‖ := by
  rw [canonicalProfile, norm_mul, norm_exp_I_mul, one_mul]

/-- `Ω' = iλΩ - g'` almost everywhere. -/
theorem ae_hasDerivAt_canonicalProfile (hg : Integrable (deriv g)) :
    ∀ᵐ s, HasDerivAt (canonicalProfile lam g)
      (I * lam * canonicalProfile lam g s - deriv g s) s := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hq.locallyIntegrable] with s hs
  have hJ : HasDerivAt (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t)
      (-profileIntegrand lam g s) s := by
    have := (hs 0).const_sub (∫ t in Ioi 0, profileIntegrand lam g t)
    convert this using 1
    · funext s
      exact integral_Ioi_profileIntegrand hg s
  have hE : HasDerivAt (fun s : ℝ ↦ exp (I * lam * s)) (exp (I * lam * s) * (I * lam)) s := by
    have := ((hasDerivAt_id (s : ℂ)).const_mul (I * lam)).cexp.comp_ofReal
    simpa [mul_comm] using this
  convert hE.mul hJ using 1
  · rfl
  rw [canonicalProfile, profileIntegrand]
  have : exp (I * lam * s) * exp (-(I * lam * s)) = 1 := by rw [← exp_add]; simp
  linear_combination (deriv g s) * this

/-- `Pz = -Ω` for `P = -i∂ₛ`: `z' = -iΩ` wherever `g` is differentiable and the profile
    equation holds. -/
theorem ae_hasDerivAt_canonicalUnknown (hlam : lam ≠ 0) (hg : Integrable (deriv g))
    (hgd : ∀ᵐ s, DifferentiableAt ℝ g s) :
    ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (I * -canonicalProfile lam g s) s := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam
  filter_upwards [ae_hasDerivAt_canonicalProfile (lam := lam) hg, hgd] with s hΩ hgs
  have := (hΩ.add hgs.hasDerivAt).neg.div_const (lam : ℂ)
  convert this using 1
  · rfl
  field_simp
  ring

/-- `(P - λ)z = g`: `z' = i(λz + g)` wherever `g` is differentiable and the profile equation
    holds. -/
theorem ae_hasDerivAt_canonicalUnknown_sub (hlam : lam ≠ 0) (hg : Integrable (deriv g))
    (hgd : ∀ᵐ s, DifferentiableAt ℝ g s) :
    ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (I * (lam * canonicalUnknown lam g s + g s)) s := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam
  filter_upwards [ae_hasDerivAt_canonicalUnknown hlam hg hgd] with s hs
  convert hs using 1
  rw [canonicalUnknown]
  field_simp
  ring

/-- The profile tends to `0` at `+∞`. -/
theorem tendsto_canonicalProfile_atTop (hg : Integrable (deriv g)) :
    Tendsto (canonicalProfile lam g) atTop (𝓝 0) := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have hJ : Tendsto (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) atTop (𝓝 0) := by
    have := (intervalIntegral_tendsto_integral_Ioi 0 hq.integrableOn tendsto_id).const_sub
      (∫ t in Ioi 0, profileIntegrand lam g t)
    rw [sub_self] at this
    refine this.congr fun s ↦ ?_
    exact (integral_Ioi_profileIntegrand hg s).symm
  rw [tendsto_zero_iff_norm_tendsto_zero] at hJ ⊢
  simpa only [norm_canonicalProfile] using hJ

/-- The profile tends to `0` at `-∞` exactly under the Melnikov condition
    `∫ g'(t) e^{-iλt} dt = 0`. -/
theorem tendsto_canonicalProfile_atBot_iff (hg : Integrable (deriv g)) :
    Tendsto (canonicalProfile lam g) atBot (𝓝 0) ↔ ∫ t, profileIntegrand lam g t = 0 := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have hJ : Tendsto (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) atBot
      (𝓝 (∫ t, profileIntegrand lam g t)) := by
    have := (intervalIntegral_tendsto_integral_Iic 0 hq.integrableOn tendsto_id).add_const
      (∫ t in Ioi 0, profileIntegrand lam g t)
    rw [intervalIntegral.integral_Iic_add_Ioi hq.integrableOn hq.integrableOn] at this
    refine this.congr fun s ↦ ?_
    rw [integral_Ioi_profileIntegrand hg s, intervalIntegral.integral_symm]
    simp only [id]
    ring
  have hN := hJ.norm
  simp only [← norm_canonicalProfile] at hN
  rw [tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    exact norm_eq_zero.1 (tendsto_nhds_unique hN h)
  · intro h
    rwa [h, norm_zero] at hN

/-- Under the Melnikov condition the profile is also `-e^{iλs} ∫_{-∞}^s g'(t) e^{-iλt} dt`. -/
theorem canonicalProfile_eq_Iic (hg : Integrable (deriv g))
    (hM : ∫ t, profileIntegrand lam g t = 0) (s : ℝ) :
    canonicalProfile lam g s = -(exp (I * lam * s) * ∫ t in Iic s, profileIntegrand lam g t) := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  have := intervalIntegral.integral_Iic_add_Ioi (b := s) hq.integrableOn hq.integrableOn
  rw [hM] at this
  rw [canonicalProfile, eq_neg_of_add_eq_zero_right this]
  ring

end Profile

/-! ### Local absolute continuity, uniqueness and bounds -/

section Decay

variable {lam : ℝ} {g : ℝ → ℂ}

/-- The canonical profile is absolutely continuous on every compact interval. -/
theorem absolutelyContinuousOnInterval_canonicalProfile (hg : Integrable (deriv g))
    (c d : ℝ) : AbsolutelyContinuousOnInterval (canonicalProfile lam g) c d := by
  have hq := integrable_profileIntegrand (lam := lam) hg
  -- Mathlib's absolute continuity of primitives is stated for real-valued functions.
  have hr := (reCLM.integrable_comp hq).intervalIntegrable
    |>.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : c ∈ uIcc c d)
  have hi := (imCLM.integrable_comp hq).intervalIntegrable
    |>.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : c ∈ uIcc c d)
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun s ↦ ∫ t in c..s, profileIntegrand lam g t) c d := by
    have h := (ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hr).add
      ((ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hi).const_smul I)
    refine h.congr fun s _ ↦ ?_
    simp only [Pi.add_apply, Function.comp_apply, ofRealCLM_apply, smul_eq_mul]
    rw [reCLM.intervalIntegral_comp_comm hq.intervalIntegrable,
      imCLM.intervalIntegral_comp_comm hq.intervalIntegrable]
    simpa [mul_comm] using re_add_im (∫ t in c..s, profileIntegrand lam g t)
  have htail : AbsolutelyContinuousOnInterval
      (fun s ↦ ∫ t in Ioi s, profileIntegrand lam g t) c d := by
    have hc : AbsolutelyContinuousOnInterval
        (fun _ : ℝ ↦ ∫ t in Ioi c, profileIntegrand lam g t) c d :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    refine (hc.sub hprimitive).congr fun s _ ↦ ?_
    exact (eq_sub_of_add_eq'
      (intervalIntegral.integral_interval_add_Ioi hq.integrableOn hq.integrableOn)).symm
  have hexp : ContDiff ℝ 1 (fun s : ℝ ↦ exp (I * lam * s)) :=
    (contDiff_const.mul ofRealCLM.contDiff).cexp
  exact hexp.contDiffOn.absolutelyContinuousOnInterval.smul htail

/-- The canonical profile is the only locally absolutely continuous solution of
    `Ω' = iλΩ - g'` that tends to `0` at `+∞`. Neither Melnikov nor decay at `-∞` is
    needed for uniqueness. -/
theorem canonicalProfile_unique (hg : Integrable (deriv g)) {Ω : ℝ → ℂ}
    (hac : ∀ c d, AbsolutelyContinuousOnInterval Ω c d)
    (hode : ∀ᵐ s, HasDerivAt Ω (I * lam * Ω s - deriv g s) s)
    (htop : Tendsto Ω atTop (𝓝 0)) :
    Ω = canonicalProfile lam g := by
  let F : ℝ → ℂ := fun s ↦ exp (-(I * lam * s)) * (Ω s - canonicalProfile lam g s)
  have hE : ContDiff ℝ 1 (fun s : ℝ ↦ exp (-(I * lam * s))) :=
    (contDiff_const.mul ofRealCLM.contDiff).neg.cexp
  have hFac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b :=
    hE.contDiffOn.absolutelyContinuousOnInterval.smul
      ((hac a b).sub (absolutelyContinuousOnInterval_canonicalProfile hg a b))
  have hFd : ∀ᵐ s, HasDerivAt F 0 s := by
    filter_upwards [hode, ae_hasDerivAt_canonicalProfile (lam := lam) hg] with s hs hΩ
    have hEd : HasDerivAt (fun s : ℝ ↦ exp (-(I * lam * s)))
        (exp (-(I * lam * s)) * -(I * lam)) s := by
      simpa using (((hasDerivAt_id (s : ℂ)).const_mul (I * lam)).neg.cexp).comp_ofReal
    convert hEd.mul (hs.sub hΩ) using 1
    dsimp [F]
    ring
  have hconst (s : ℝ) : F s = F 0 := by
    obtain ⟨C, hC⟩ := (hFac 0 s).const_of_ae_hasDerivAt_zero
      (hFd.mono fun _ hs _ ↦ hs)
    exact (hC s right_mem_uIcc).trans (hC 0 left_mem_uIcc).symm
  have hnorm (s : ℝ) : ‖Ω s - canonicalProfile lam g s‖ =
      ‖Ω 0 - canonicalProfile lam g 0‖ := by
    simpa only [F, norm_mul, norm_exp_neg_I_mul, one_mul] using congrArg norm (hconst s)
  have hlim : Tendsto (fun s ↦ ‖Ω s - canonicalProfile lam g s‖) atTop (𝓝 0) := by
    simpa using (htop.sub (tendsto_canonicalProfile_atTop hg)).norm
  have hz : ‖Ω 0 - canonicalProfile lam g 0‖ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr fun s ↦ hnorm s)
  funext s
  exact sub_eq_zero.mp (norm_eq_zero.mp ((hnorm s).trans hz))

private theorem integral_profileIntegrand_by_parts
    (hgac : ∀ a b, AbsolutelyContinuousOnInterval g a b)
    (hg : Integrable (deriv g)) (c : ℂ) (a b : ℝ) :
    (∫ t in a..b, profileIntegrand lam g t) =
      (g b - c) * exp (-(I * lam * b)) - (g a - c) * exp (-(I * lam * a)) +
        (I * lam) * ∫ t in a..b, (g t - c) * exp (-(I * lam * t)) := by
  let u : ℝ → ℂ := fun t ↦ (g t - c) * exp (-(I * lam * t))
  have hE : ContDiff ℝ 1 (fun t : ℝ ↦ exp (-(I * lam * t))) :=
    (contDiff_const.mul ofRealCLM.contDiff).neg.cexp
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hu : AbsolutelyContinuousOnInterval u a b :=
    ((hgac a b).sub hc).smul hE.contDiffOn.absolutelyContinuousOnInterval
  have hui : IntervalIntegrable u volume a b := hu.continuousOn.intervalIntegrable
  have hqi := (integrable_profileIntegrand (lam := lam) hg).intervalIntegrable (a := a) (b := b)
  have hdu : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt u (profileIntegrand lam g t - (I * lam) * u t) t := by
    filter_upwards [(hgac a b).boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htab
    have hEd := (((hasDerivAt_id (t : ℂ)).const_mul (I * lam)).neg.cexp).comp_ofReal
    convert ((ht htab).hasDerivAt.sub_const c).mul hEd using 1
    · rfl
    dsimp [u, profileIntegrand]
    ring
  have h := complex_integral_eq_sub_of_ac hu (hqi.sub (hui.const_mul (I * lam))) hdu
  rw [intervalIntegral.integral_sub hqi (hui.const_mul (I * lam)),
    intervalIntegral.integral_const_mul] at h
  dsimp [u] at h
  linear_combination h

/-- Under Melnikov, if `g` approaches its end values `c±` at rate `e^{-α|s|}`, then
    the canonical profile approaches `0` at the same rate. -/
theorem norm_canonicalProfile_le_exp (hgac : ∀ c d, AbsolutelyContinuousOnInterval g c d)
    (hg : Integrable (deriv g)) (hM : ∫ t, profileIntegrand lam g t = 0) {α C : ℝ} {cp cm : ℂ}
    (hα : 0 < α) (hp : ∀ s, 0 ≤ s → ‖g s - cp‖ ≤ C * Real.exp (-α * s))
    (hn : ∀ s, s ≤ 0 → ‖g s - cm‖ ≤ C * Real.exp (α * s)) :
    ∃ C', ∀ s, ‖canonicalProfile lam g s‖ ≤ C' * Real.exp (-α * |s|) := by
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have h := (hgac (t - 1) (t + 1)).continuousOn
    rw [uIcc_of_le (by linarith)] at h
    exact h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  let u : ℂ → ℝ → ℂ := fun c t ↦ (g t - c) * exp (-(I * lam * t))
  have huc (c : ℂ) : Continuous (u c) := by dsimp [u]; fun_prop
  have hun (c : ℂ) (t : ℝ) : ‖u c t‖ = ‖g t - c‖ := by
    simp [u, norm_exp_neg_I_mul]
  have hqp := integrable_profileIntegrand (lam := lam) hg
  have hep : Tendsto (fun t : ℝ ↦ C * Real.exp (-α * t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hα) tendsto_id)).const_mul C
  have hen : Tendsto (fun t : ℝ ↦ C * Real.exp (α * t)) atBot (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.pos_mul_atBot hα tendsto_id)).const_mul C
  have hup : Tendsto (u cp) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hep
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [hun] using hp t ht
  have hun' : Tendsto (u cm) atBot (𝓝 0) := by
    apply squeeze_zero_norm' _ hen
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    simpa only [hun] using hn t ht
  refine ⟨C * (1 + |lam| / α), fun s ↦ ?_⟩
  rcases le_total 0 s with hs | hs
  · have he := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hα) s).const_mul C
    have hb : ∀ᵐ t ∂volume.restrict (Ioi s), ‖u cp t‖ ≤ C * Real.exp (-α * t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hun]
      exact hp t (hs.trans ht.le)
    have hui : IntegrableOn (u cp) (Ioi s) := he.mono' (huc cp).aestronglyMeasurable hb
    have heq : (∫ t in Ioi s, profileIntegrand lam g t) =
        -u cp s + (I * lam) * ∫ t in Ioi s, u cp t := by
      apply tendsto_nhds_unique
        (intervalIntegral_tendsto_integral_Ioi s hqp.integrableOn tendsto_id)
      have h := (hup.sub_const (u cp s)).add
        ((intervalIntegral_tendsto_integral_Ioi s hui tendsto_id).const_mul (I * lam))
      simp only [zero_sub] at h
      exact h.congr fun b ↦ (integral_profileIntegrand_by_parts hgac hg cp s b).symm
    have hni : ‖∫ t in Ioi s, u cp t‖ ≤ C * Real.exp (-α * s) / α := by
      calc
        _ ≤ ∫ t in Ioi s, ‖u cp t‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi s, C * Real.exp (-α * t) := integral_mono_ae hui.norm he hb
        _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hα)]; ring
    rw [abs_of_nonneg hs, norm_canonicalProfile, heq]
    calc
      _ ≤ ‖u cp s‖ + |lam| * ‖∫ t in Ioi s, u cp t‖ := by
        simpa [norm_mul] using norm_add_le (-u cp s) ((I * lam) * ∫ t in Ioi s, u cp t)
      _ ≤ C * Real.exp (-α * s) + |lam| * (C * Real.exp (-α * s) / α) :=
        add_le_add (by rw [hun]; exact hp s hs) (mul_le_mul_of_nonneg_left hni (abs_nonneg _))
      _ = _ := by ring
  · have he := (integrableOn_exp_mul_Iic hα s).const_mul C
    have hb : ∀ᵐ t ∂volume.restrict (Iic s), ‖u cm t‖ ≤ C * Real.exp (α * t) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      rw [hun]
      exact hn t (ht.trans hs)
    have hui : IntegrableOn (u cm) (Iic s) := he.mono' (huc cm).aestronglyMeasurable hb
    have heq : (∫ t in Iic s, profileIntegrand lam g t) =
        u cm s + (I * lam) * ∫ t in Iic s, u cm t := by
      apply tendsto_nhds_unique
        (intervalIntegral_tendsto_integral_Iic s hqp.integrableOn tendsto_id)
      have h := (hun'.const_sub (u cm s)).add
        ((intervalIntegral_tendsto_integral_Iic s hui tendsto_id).const_mul (I * lam))
      simp only [sub_zero] at h
      exact h.congr fun a ↦ (integral_profileIntegrand_by_parts hgac hg cm a s).symm
    have hni : ‖∫ t in Iic s, u cm t‖ ≤ C * Real.exp (α * s) / α := by
      calc
        _ ≤ ∫ t in Iic s, ‖u cm t‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Iic s, C * Real.exp (α * t) := integral_mono_ae hui.norm he hb
        _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hα]; ring
    rw [canonicalProfile_eq_Iic hg hM, norm_neg, norm_mul, norm_exp_I_mul, one_mul, heq,
      abs_of_nonpos hs]
    calc
      _ ≤ ‖u cm s‖ + |lam| * ‖∫ t in Iic s, u cm t‖ := by
        simpa [norm_mul] using norm_add_le (u cm s) ((I * lam) * ∫ t in Iic s, u cm t)
      _ ≤ C * Real.exp (α * s) + |lam| * (C * Real.exp (α * s) / α) :=
        add_le_add (by rw [hun]; exact hn s hs) (mul_le_mul_of_nonneg_left hni (abs_nonneg _))
      _ = _ := by rw [show -α * -s = α * s by ring]; ring

/-- The positive tail kernel on each half line, with no coupling across zero. -/
private def profileKernel (s t : ℝ) : ℝ≥0∞ :=
  if 0 ≤ s then if s < t then ENNReal.ofReal (Real.exp (s - t)) else 0
  else if t ≤ s then ENNReal.ofReal (Real.exp (t - s)) else 0

private theorem measurable_profileKernel :
    Measurable (fun p : ℝ × ℝ ↦ profileKernel p.1 p.2) := by
  unfold profileKernel
  refine Measurable.ite (measurableSet_le measurable_const measurable_fst) ?_ ?_
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (by fun_prop) measurable_const
  · exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (by fun_prop) measurable_const

private theorem lintegral_exp_sub_Ioi (s : ℝ) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (s - t))) = 1 := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (s - t)) (Ioi s) := by
    simpa [IntegrableOn, Real.exp_sub, div_eq_mul_inv, Real.exp_neg] using
      (integrableOn_exp_neg_Ioi s).const_mul (Real.exp s)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ ↦ by positivity)]
  simp_rw [sub_eq_add_neg, Real.exp_add]
  rw [integral_const_mul, integral_exp_neg_Ioi, ← Real.exp_add]
  simp

private theorem lintegral_exp_sub_Iic (s : ℝ) :
    (∫⁻ t in Iic s, ENNReal.ofReal (Real.exp (t - s))) = 1 := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (t - s)) (Iic s) := by
    simpa [IntegrableOn, Real.exp_sub, div_eq_mul_inv] using
      (integrableOn_exp_Iic s).mul_const (Real.exp s)⁻¹
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ ↦ by positivity)]
  simp_rw [sub_eq_add_neg, Real.exp_add]
  rw [integral_mul_const, integral_exp_Iic, ← Real.exp_add]
  simp

private theorem lintegral_profileKernel_row (s : ℝ) : (∫⁻ t, profileKernel s t) = 1 := by
  by_cases hs : 0 ≤ s
  · have heq : profileKernel s = (Ioi s).indicator
        (fun t ↦ ENNReal.ofReal (Real.exp (s - t))) := by
      funext t; simp [profileKernel, hs, Set.indicator_apply]
    rw [heq, lintegral_indicator measurableSet_Ioi]
    exact lintegral_exp_sub_Ioi s
  · have heq : profileKernel s = (Iic s).indicator
        (fun t ↦ ENNReal.ofReal (Real.exp (t - s))) := by
      funext t; simp [profileKernel, hs, Set.indicator_apply]
    rw [heq, lintegral_indicator measurableSet_Iic]
    exact lintegral_exp_sub_Iic s

private theorem lintegral_profileKernel_column (t : ℝ) : (∫⁻ s, profileKernel s t) ≤ 1 := by
  by_cases ht : 0 ≤ t
  · calc
      _ ≤ ∫⁻ s, (Iic t).indicator (fun s ↦ ENNReal.ofReal (Real.exp (s - t))) s := by
        apply lintegral_mono; intro s
        by_cases hs : 0 ≤ s
        · by_cases hst : s < t
          · simp [profileKernel, hs, hst, hst.le]
          · simp [profileKernel, hs, hst]
        · have hts : ¬t ≤ s := by linarith
          simp [profileKernel, hs, hts]
      _ = 1 := by rw [lintegral_indicator measurableSet_Iic]; exact lintegral_exp_sub_Iic t
  · calc
      _ ≤ ∫⁻ s, (Ici t).indicator (fun s ↦ ENNReal.ofReal (Real.exp (t - s))) s := by
        apply lintegral_mono; intro s
        by_cases hs : 0 ≤ s
        · have hst : ¬s < t := by linarith
          simp [profileKernel, hs, hst]
        · by_cases hts : t ≤ s <;> simp [profileKernel, hs, hts]
      _ = 1 := by
        rw [lintegral_indicator measurableSet_Ici, ← restrict_Ioi_eq_restrict_Ici]
        exact lintegral_exp_sub_Ioi t

private theorem lintegral_profileKernel_sq_le {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    (∫⁻ s, (∫⁻ t, profileKernel s t * F t) ^ 2) ≤ ∫⁻ t, F t ^ 2 := by
  have hrow (s : ℝ) : (∫⁻ t, profileKernel s t * F t) ^ 2 ≤
      ∫⁻ t, profileKernel s t * F t ^ 2 := by
    have hk : Measurable (profileKernel s) :=
      measurable_profileKernel.comp (measurable_const.prodMk measurable_id)
    let ν := volume.withDensity (profileKernel s)
    have hν : ν univ = 1 := by
      simp [ν, withDensity_apply _ MeasurableSet.univ, lintegral_profileKernel_row]
    have hFν : AEMeasurable F ν :=
      hF.mono_ac (withDensity_absolutelyContinuous volume (profileKernel s))
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
      (by norm_num [Real.holderConjugate_iff] : Real.HolderConjugate 2 2) hFν
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [mul_one, ENNReal.one_rpow, lintegral_const, hν] at hcs
    have hsq := pow_le_pow_left' hcs 2
    simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hsq
    norm_num at hsq
    simpa only [ν, lintegral_withDensity_eq_lintegral_mul₀ hk.aemeasurable hF,
      lintegral_withDensity_eq_lintegral_mul₀ hk.aemeasurable (hF.pow_const 2),
      Pi.mul_apply] using hsq
  calc
    _ ≤ ∫⁻ s, ∫⁻ t, profileKernel s t * F t ^ 2 := lintegral_mono hrow
    _ = ∫⁻ t, ∫⁻ s, profileKernel s t * F t ^ 2 :=
      lintegral_lintegral_swap (measurable_profileKernel.aemeasurable.mul (hF.comp_snd.pow_const 2))
    _ ≤ ∫⁻ t, F t ^ 2 := by
      apply lintegral_mono; intro t
      have hk : Measurable (fun s ↦ profileKernel s t) :=
        measurable_profileKernel.comp (measurable_id.prodMk measurable_const)
      change (∫⁻ s, profileKernel s t * F t ^ 2) ≤ F t ^ 2
      rw [lintegral_mul_const _ hk]
      calc
        _ ≤ 1 * F t ^ 2 := by gcongr; exact lintegral_profileKernel_column t
        _ = _ := one_mul _

/-- The weighted bound `‖e^{|s|} Ω‖_{L²} ≤ ‖e^{|s|} g'‖_{L²}`: on each half line `e^{|s|}Ω` is
    bounded by a one-sided convolution of `e^{|s|}|g'|` with `e^{-t} 1_{t>0}`. -/
theorem eLpNorm_exp_mul_canonicalProfile_le (hg : Integrable (deriv g))
    (hM : ∫ t, profileIntegrand lam g t = 0) :
    eLpNorm (fun s ↦ (Real.exp |s| : ℂ) * canonicalProfile lam g s) 2 volume ≤
      eLpNorm (fun s ↦ (Real.exp |s| : ℂ) * deriv g s) 2 volume := by
  let f : ℝ → ℂ := fun t ↦ (Real.exp |t| : ℂ) * deriv g t
  let w : ℝ → ℂ := fun s ↦ (Real.exp |s| : ℂ) * canonicalProfile lam g s
  have hw (s : ℝ) : ‖(Real.exp |s| : ℂ)‖ₑ = ENNReal.ofReal (Real.exp |s|) := by
    simp [← ofReal_norm]
  have hqn (t : ℝ) : ‖profileIntegrand lam g t‖ₑ = ‖deriv g t‖ₑ := by
    simp [← ofReal_norm, profileIntegrand, norm_exp_neg_I_mul]
  have hfm : AEStronglyMeasurable f volume :=
    (by fun_prop : Continuous fun t : ℝ ↦ (Real.exp |t| : ℂ)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  have hΩc : Continuous (canonicalProfile lam g) := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have h := (absolutelyContinuousOnInterval_canonicalProfile (lam := lam) hg
      (t - 1) (t + 1)).continuousOn
    rw [uIcc_of_le (by linarith)] at h
    exact h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hwm : AEStronglyMeasurable w volume :=
    ((by fun_prop : Continuous fun t : ℝ ↦ (Real.exp |t| : ℂ)).mul hΩc).aestronglyMeasurable
  have hq := integrable_profileIntegrand (lam := lam) hg
  have hb (s : ℝ) : ‖w s‖ₑ ≤ ∫⁻ t, profileKernel s t * ‖f t‖ₑ := by
    by_cases hs : 0 ≤ s
    · have heq : (fun t ↦ profileKernel s t * ‖f t‖ₑ) =
          (Ioi s).indicator (fun t ↦ ENNReal.ofReal (Real.exp |s|) *
            ‖profileIntegrand lam g t‖ₑ) := by
        funext t
        by_cases hst : s < t
        · rw [Set.indicator_of_mem (s := Ioi s) hst]
          simp only [profileKernel, ite_eq_left hs, ite_eq_left hst, f, enorm_mul, hw, hqn]
          rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst.le)]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            sub_add_cancel]
        · simp [profileKernel, hs, hst]
      rw [heq, lintegral_indicator measurableSet_Ioi,
        lintegral_const_mul'' _ hq.aestronglyMeasurable.enorm.restrict]
      dsimp only [w]
      rw [enorm_mul, hw, ← ofReal_norm, norm_canonicalProfile, ofReal_norm]
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    · have heq : (fun t ↦ profileKernel s t * ‖f t‖ₑ) =
          (Iic s).indicator (fun t ↦ ENNReal.ofReal (Real.exp |s|) *
            ‖profileIntegrand lam g t‖ₑ) := by
        funext t
        by_cases hts : t ≤ s
        · rw [Set.indicator_of_mem (s := Iic s) hts]
          simp only [profileKernel, ite_eq_right hs, ite_eq_left hts, f, enorm_mul, hw, hqn]
          rw [abs_of_nonpos (le_of_not_ge hs), abs_of_nonpos (hts.trans (le_of_not_ge hs))]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show t - s + -t = -s by ring]
        · simp [profileKernel, hs, hts]
      rw [heq, lintegral_indicator measurableSet_Iic,
        lintegral_const_mul'' _ hq.aestronglyMeasurable.enorm.restrict]
      dsimp only [w]
      rw [canonicalProfile_eq_Iic hg hM, enorm_mul, hw, enorm_neg, enorm_mul]
      have hphase : ‖exp (I * lam * s)‖ₑ = 1 := by simp [← ofReal_norm, norm_exp_I_mul]
      rw [hphase, one_mul]
      gcongr
      exact enorm_integral_le_lintegral_enorm _
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two]
  calc
    eLpNorm w 2 volume ^ 2 = ∫⁻ s, ‖w s‖ₑ ^ 2 := by
      simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hwm
    _ ≤ ∫⁻ s, (∫⁻ t, profileKernel s t * ‖f t‖ₑ) ^ 2 :=
      lintegral_mono fun s ↦ pow_le_pow_left' (hb s) 2
    _ ≤ ∫⁻ t, ‖f t‖ₑ ^ 2 := lintegral_profileKernel_sq_le hfm.enorm
    _ = eLpNorm f 2 volume ^ 2 := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hfm).symm

end Decay

end NoEmbeddedEigenvalues
