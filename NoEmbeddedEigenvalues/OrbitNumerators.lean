import NoEmbeddedEigenvalues.QuarterCoordinates
import NoEmbeddedEigenvalues.ScalarDivision
import NoEmbeddedEigenvalues.OrbitNumeratorRegularity
import NoEmbeddedEigenvalues.ResonantCancellation
import NoEmbeddedEigenvalues.QuarterDivisorGeometry

/-!
# Quarter-orbit endpoints and resonant zeros

Both unknown and forcing have the same quarter character. All four fourth roots
of unity are allowed. Endpoint functions are separate locally L² functions of the
level; they are values of orbitwise ACL representatives, not raw spatial traces.
The numerator uses continuous forcing, so its values at resonances are canonical.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A.e. quarter-rotation character on a specified region. -/
def HasQuarterCharacterOn (κ : ℂ) (A : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℂ) : Prop :=
  ∀ᵐ p ∂(volume.restrict A), F (rotLift p) = κ * F p

/-- Midpoint half numerator, with the same phase convention as the full numerator. -/
def quarterHalfNumerator (lam : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ t in (-eighthPeriod h)..0,
    g (dipoleOrbit h t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))

/-- Endpoint formula with locally L² endpoint functions and orbitwise ACL witnesses
(`lem:quarter-endpoint-formula`). No joint choice of raw orbit values is required. -/
theorem quarter_endpoint_formula {lam : ℝ} {κ : ℂ} (_hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) f) :
    ∃ Eminus Eplus : ℝ → ℂ,
      (∀ a b, 0 < a → a < b → b < h₀ →
        MemLp Eminus 2 (volume.restrict (Ioo a b)) ∧
        MemLp Eplus 2 (volume.restrict (Ioo a b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∃ Z : ℝ → ℂ,
        (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
        Function.Periodic Z (orbitPeriod h) ∧
        (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
        (∀ᵐ t, HasDerivAt Z
          (Complex.I * ((lam : ℂ) * Z t + g (dipoleOrbit h t))) t) ∧
        Z (-eighthPeriod h) = Eminus h ∧ Z (eighthPeriod h) = Eplus h ∧
        Eplus h = κ * Eminus h ∧
        quarterDivisor lam κ h * Eminus h =
          Complex.I * Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) *
            quarterNumerator lam g h ∧
        (quarterDivisor lam κ h ≠ 0 → ‖Eminus h‖ = ‖quarterQuotient lam κ g h‖) := by
  have hu : MemLp (transportUnknown lam v f) 2 (volume.restrict U) := by
    convert ((hp.memLp.add hp.memSobolevOn.memLp).neg.const_mul (lam : ℂ)⁻¹) using 1
    funext p
    simp only [transportUnknown, div_eq_mul_inv, mul_comm, Pi.neg_apply, Pi.add_apply]
  have hk : MemLp (fun p ↦ Complex.I * -v p) 2 (volume.restrict U) :=
    hp.memLp.neg.const_mul Complex.I
  obtain ⟨Em, Ep, hElp, hprof⟩ := orbit_endpoint_functions hp.isOrbitUnion.1 hu hk
    hp.hasWeakL0On_transportUnknown hh₀1 hA
  have hfg' := ae_orbit_congr hh₀1.le
    (ae_restrict_of_ae_restrict_of_subset hA hfg)
  have hchar : (fun p ↦ transportUnknown lam v f (rotLift p))
      =ᵐ[volume.restrict (orbitAnnulus 0 h₀)] (fun p ↦ κ * transportUnknown lam v f p) := by
    filter_upwards [hvκ, hfκ] with p hv hf
    simp only [transportUnknown, hv, hf]
    ring
  have hchar' := ae_orbit_congr hh₀1.le hchar
  refine ⟨Em, Ep, hElp, ?_⟩
  filter_upwards [hprof, hfg', hchar', ae_restrict_mem measurableSet_Ioo] with h hZ hfg_h hchar_h hh
  obtain ⟨Z, hzeq, hper, hac, hd, hEm, hEp⟩ := hZ
  have h1 := hh.2.trans hh₀1
  have hcZ : Continuous Z := continuous_iff_continuousAt.2 fun t ↦
    (hac (t - 1) (t + 1)).continuousOn.continuousAt (by
      rw [uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith))
  have hode : ∀ᵐ t, HasDerivAt Z
      (Complex.I * ((lam : ℂ) * Z t + g (dipoleOrbit h t))) t := by
    filter_upwards [hd, hzeq, hfg_h] with t ht hz hf
    convert ht using 1
    rw [hz]
    dsimp only [transportUnknown]
    rw [← hf]
    field_simp [Complex.ofReal_ne_zero.mpr hp.ne_zero]
    ring
  have hquarter : ∀ t, Z (t + 2 * eighthPeriod h) = κ * Z t := by
    have hshift := (measurePreserving_add_right volume
      (2 * eighthPeriod h)).quasiMeasurePreserving.ae hzeq
    have heq : (fun t ↦ Z (t + 2 * eighthPeriod h)) =ᵐ[volume] (fun t ↦ κ * Z t) := by
      filter_upwards [hshift, hchar_h, hzeq] with t ht hc hz
      rw [ht, dipoleOrbit_add_quarter hh.1 h1]
      change transportUnknown lam v f (rotLift (dipoleOrbit h t)) = κ * Z t
      rw [hc, hz]
    exact fun t ↦ congrFun (((hcZ.comp (continuous_id.add continuous_const)).ae_eq_iff_eq volume
      (continuous_const.mul hcZ)).1 heq) t
  have hbound : Ep h = κ * Em h := by
    simpa only [show -eighthPeriod h + 2 * eighthPeriod h = eighthPeriod h by ring,
      hEm, hEp] using hquarter (-eighthPeriod h)
  have hgc : Continuous (fun t ↦ g (dipoleOrbit h t)) := by
    apply hg.comp_continuous
      (continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_dipoleFlow _ t).continuousAt)
    intro t
    have hm : dipoleOrbit h t ∈ puncturedCell := by
      simpa only [actionAngleInv,
        div_mul_cancel₀ t (orbitPeriod_pos hh.1 h1).ne'] using
        actionAngleInv_mem_puncturedCell hh.1 h1 (t / orbitPeriod h)
    exact hA ⟨hm, (levelCoord_dipoleOrbit hh.1 h1 t).symm ▸ hh⟩
  have hint := transport_integratingFactor (hac (-eighthPeriod h) (eighthPeriod h))
    (hgc.intervalIntegrable _ _) (hode.mono fun _ ht _ ↦ ht)
  have hN : (∫ t in (-eighthPeriod h)..(eighthPeriod h),
      Complex.exp (-(Complex.I * (lam : ℂ) * (t : ℂ))) * g (dipoleOrbit h t)) =
        quarterNumerator lam g h := by
    apply intervalIntegral.integral_congr
    intro t _
    push_cast
    rw [show -(Complex.I * (lam : ℂ) * (t : ℂ)) =
      -Complex.I * ((lam : ℂ) * (t : ℂ)) by ring, mul_comm]
  rw [hEm, hEp, hbound, hN] at hint
  let e := Complex.exp (Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ))
  have he : e * Complex.exp (-(Complex.I * (lam : ℂ) * (eighthPeriod h : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    push_cast
    congr 1
    ring
  have he2 : e * Complex.exp (-(Complex.I * (lam : ℂ) * ((-eighthPeriod h : ℝ) : ℂ))) =
      Complex.exp (Complex.I * (quarterPhase lam h : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [quarterPhase]
    push_cast
    ring
  have hdiv : quarterDivisor lam κ h * Em h = Complex.I * e * quarterNumerator lam g h := by
    dsimp only [quarterDivisor]
    linear_combination e * hint - κ * Em h * he + Em h * he2
  refine ⟨Z, hzeq, hper, hac, hode, hEm, hEp, hbound, hdiv, ?_⟩
  intro hn
  have henorm : ‖Complex.I * e‖ = 1 := by
    simp only [norm_mul, Complex.norm_I, one_mul, e, Complex.norm_exp]
    simp
  have hnrm := congrArg norm hdiv
  rw [norm_mul, norm_mul, henorm, one_mul] at hnrm
  rw [quarterQuotient, norm_div]
  apply (eq_div_iff (norm_ne_zero_iff.mpr hn)).2
  simpa only [mul_comm] using hnrm

/-- Canonical local H¹ numerator and resonant cancellation (`lem:numerator-zeros`). -/
theorem numerator_zeros {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hvκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) v)
    (hfκ : HasQuarterCharacterOn κ (orbitAnnulus 0 h₀) f) :
    (∃ N₁ : ℝ → ℂ, HasIntervalH1Loc 0 h₀ (quarterNumerator lam g) N₁) ∧
      ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → quarterNumerator lam g h = 0 := by
  have hU := hp.isOrbitUnion.1
  have hgs : MemSobolevOn 1 U g :=
    MemSobolevOn.congr_ae_on (MemSobolevOnWith.of_succ hp.memSobolevOn) hU.measurableSet
      ((ae_restrict_iff' hU.measurableSet).1 hfg)
  have hNl := quarterNumerator_h1Loc hU hg hgs hh₀1 hA (lam := lam)
  refine ⟨⟨_, hNl⟩, ?_⟩
  obtain ⟨Em, Ep, hEL, hprof⟩ := quarter_endpoint_formula hκ hp hh₀ hh₀1 hA hg hfg hvκ hfκ
  intro h hh hzero
  let a := h / 2
  let b := (h + h₀) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hh.1]
  have hab : a < b := by dsimp [a, b]; linarith [hh.1, hh.2]
  have hb : b < h₀ := by dsimp [b]; linarith [hh.2]
  have hI : h ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith [hh.1, hh.2]
  have hN := hNl a b ha hab hb
  have hNc : ContinuousAt (quarterNumerator lam g) h := by
    apply ((hN.continuousOn_extension hab).continuousAt
      (Icc_mem_nhds hI.1 hI.2)).congr
    filter_upwards [isOpen_Ioo.mem_nhds hI] with x hx
    exact hN.extension_eq hab hx
  have hDd : DifferentiableAt ℝ (quarterDivisor lam κ) h := by
    have hL := (deriv_eighthPeriod_neg hh.1 (hh.2.trans hh₀1)).1
    exact (differentiableAt_const κ).sub
      (((differentiableAt_const Complex.I).mul
        (Complex.ofRealCLM.differentiableAt.comp h (hL.const_mul (2 * lam)))).cexp)
  apply eq_zero_of_integrable_divisor hI hNc hDd hzero
    ((hEL a b ha hab hb).1.integrable (by norm_num))
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha.le hb.le) hprof]
    with x hx
  obtain ⟨Z, -, -, -, -, -, -, -, hd, -⟩ := hx
  have he : ‖Complex.I *
      Complex.exp (Complex.I * ((lam * eighthPeriod x : ℝ) : ℂ))‖ = 1 := by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    simp
  have hn := congrArg norm hd
  rwa [norm_mul, norm_mul, he, one_mul] at hn

end NoEmbeddedEigenvalues
