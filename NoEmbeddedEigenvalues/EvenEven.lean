import NoEmbeddedEigenvalues.Sectors
import NoEmbeddedEigenvalues.NormalField
import NoEmbeddedEigenvalues.CanonicalBoundaryForm
import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.VirialL2
import NoEmbeddedEigenvalues.DuBoisReymond

/-!
# Even–even exclusion

The exclusion theorem and its fixed-rotation-character version are proved from named
analytic inputs, which remain admitted. The endgame uses `f > 0` almost everywhere to
force the vorticity itself to vanish, rather than a weak-gradient constant-function theorem.

Proved here: `lem:ee-neumann`, `lem:ee-bulk-integrable`, `lem:ee-cutoff-identity` (from
`lem:virial-l2`, which is still admitted, and `lem:stream-ibp`), `lem:ee-annular-virial` (from
the cutoff identity by coarea and du Bois-Reymond), `lem:ee-truncated-virial` (from the annular
identity and the center limit), `lem:ee-cell-vanishing`, `lem:cos-diagonal-null`,
`lem:ee-vorticity-from-density`, `lem:nonnegative-exhaustion`,
`lem:ee-canonical-arc-nonneg`, `lem:ee-character-exclusion`, `thm:ee-exclusion`,
`lem:ee-center-limit` and `lem:ee-boundary-integrable` (from the coarea formula of
`lem:orbit-coordinates`), `lem:arc-trace-ac` (from `lem:traces`) and
`lem:ee-boundary-regularity` (from the arc traces, Melnikov and the weighted profile bound).
Input: `lem:ee-gradient-traces`. The interfaces
`lem:canonical-arc-form` and `lem:ee-transport-traces` are proved in
`CanonicalBoundaryForm.lean` and `EigenfunctionTransport.lean`. Levels are handled in orbit
coordinates, and one sequence avoids the null sets of both the virial and trace statements.
The center is cut out of the virial identity, so it is only needed for fields supported in
an annulus.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The normal derivative `ψₙ` of the stream function of `ω` (outward from `{Ψ > 2h}`). -/
abbrev streamNormal (ω : L2) : ℝ × ℝ → ℂ := normalDeriv (streamLiftX ω) (streamLiftY ω)

/-- The tangential derivative `ψₜ` of the stream function of `ω`. -/
abbrev streamTangent (ω : L2) : ℝ × ℝ → ℂ := tangentDeriv (streamLiftX ω) (streamLiftY ω)

/-- Neumann condition (`lem:ee-neumann`): in the even–even sector `ψₙ` is odd and `ψₜ` is even
    under the reflections `S₂(x, y) = (y + π, x + π)` and `S₁(x, y) = (π - y, π - x)` across
    the lines carrying the separatrix arcs. -/
theorem ee_neumann {ω : L2} (hω : InSector true true ω) :
    (∀ᵐ p, streamNormal ω (p.2 + Real.pi, p.1 + Real.pi) = -streamNormal ω p ∧
      streamTangent ω (p.2 + Real.pi, p.1 + Real.pi) = streamTangent ω p) ∧
    (∀ᵐ p, streamNormal ω (Real.pi - p.2, Real.pi - p.1) = -streamNormal ω p ∧
      streamTangent ω (Real.pi - p.2, Real.pi - p.1) = streamTangent ω p) := by
  obtain ⟨h₁x, h₁y⟩ := hω.reflect₁_streamPartial
  obtain ⟨h₂x, h₂y⟩ := hω.reflect₂_streamPartial
  simp only [paritySign, ite_true, neg_smul, one_smul] at h₁x h₁y h₂x h₂y
  have hS₁ (p : ℝ × ℝ) : torusProj (Real.pi - p.2, Real.pi - p.1) = S₁ (torusProj p) := by
    simp [torusProj, S₁]
  have hS₂ (p : ℝ × ℝ) : torusProj (p.2 + Real.pi, p.1 + Real.pi) = S₂ (torusProj p) := by
    simp [torusProj, S₂, add_comm]
  have lift {T : Torus → Torus} {hT : MeasurePreserving T} {g h : L2}
      (heq : pullback T hT g = h) {M : ℝ × ℝ → ℝ × ℝ}
      (hM : ∀ p, torusProj (M p) = T (torusProj p)) :
      ∀ᵐ p, liftL2 g (M p) = liftL2 h p := by
    filter_upwards [ae_torusProj (ae_comp_of_pullback_eq heq)] with p hp
    simpa only [liftL2, hM] using hp
  have hneg (g : L2) : ∀ᵐ p, liftL2 (-g) p = -liftL2 g p :=
    ae_torusProj (Lp.coeFn_neg g)
  have hρ₁ (p : ℝ × ℝ) : gradNorm (Real.pi - p.2, Real.pi - p.1) = gradNorm p := by
    simp only [gradNorm, Real.sin_pi_sub, add_comm]
  have hρ₂ (p : ℝ × ℝ) : gradNorm (p.2 + Real.pi, p.1 + Real.pi) = gradNorm p := by
    simp only [gradNorm, Real.sin_add_pi, neg_sq]
    rw [add_comm]
  constructor
  · filter_upwards [lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂x hS₂,
      lift (M := fun p ↦ (p.2 + Real.pi, p.1 + Real.pi)) h₂y hS₂] with p hx hy
    simp only [streamNormal, streamTangent, normalDeriv, tangentDeriv, streamLiftX,
      streamLiftY, hx, hy, hρ₂, Real.sin_add_pi]
    constructor <;> push_cast <;> ring
  · filter_upwards [lift (M := fun p ↦ (Real.pi - p.2, Real.pi - p.1)) h₁x hS₁,
      lift (M := fun p ↦ (Real.pi - p.2, Real.pi - p.1)) h₁y hS₁,
      hneg (streamPartial 0 ω), hneg (streamPartial 1 ω)] with p hx hy hnx hny
    simp only [streamNormal, streamTangent, normalDeriv, tangentDeriv, streamLiftX,
      streamLiftY, hx, hy, hnx, hny, hρ₁, Real.sin_pi_sub]
    constructor <;> ring

/-- The bulk density evaluated on an `L²` vorticity and its stream derivatives. -/
abbrev eeBulkDensity (ω : L2) (p : ℝ × ℝ) : ℝ :=
  eeDensity p (liftL2 ω p) (streamNormal ω p) (streamTangent ω p)

/-- The exceptional set `cos x = cos y` is null, independently of any vorticity. -/
theorem ae_cos_fst_ne_cos_snd : ∀ᵐ p : ℝ × ℝ, Real.cos p.1 ≠ Real.cos p.2 := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact Eventually.of_forall fun x ↦ by
    rw [ae_iff]
    have hc : {y : ℝ | Real.cos x = Real.cos y}.Countable := by
      apply ((Set.countable_range (fun k : ℤ ↦ 2 * k * Real.pi + x)).union
        (Set.countable_range (fun k : ℤ ↦ 2 * k * Real.pi - x))).mono
      intro y hy
      obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hy
      · exact Or.inl ⟨k, hk.symm⟩
      · exact Or.inr ⟨k, hk.symm⟩
    simpa using hc.measure_zero volume

/-- The level terms of the truncated virial identity on `{Ψ = 2h}`:
    `∮ Re(ψψ̄ₙ) dℓ + (2 - 2h)(∮|ψₙ|² dt - ∮|ψₜ|² dt - ∮ Re(ωψ̄) dt)`. -/
def eeLevelTerm (ω : L2) (h : ℝ) : ℝ :=
  levelIntegral h (fun p ↦ gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) +
    (2 - 2 * h) * (levelIntegral h (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
      levelIntegral h (fun p ↦ ‖streamTangent ω p‖ ^ 2) -
      levelIntegral h (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re))

/-- `|ψₙ| ≤ |ψₓ| + |ψ_y|`, since `|sin x|, |sin y| ≤ ρ` (and `ψₙ = 0` where `ρ = 0`). -/
theorem norm_normalDeriv_le (ψx ψy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    ‖normalDeriv ψx ψy p‖ ≤ ‖ψx p‖ + ‖ψy p‖ := by
  unfold normalDeriv
  rcases (Real.sqrt_nonneg (Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2)).eq_or_lt with hρ | hρ
  · rw [gradNorm, ← hρ]; simp only [Complex.ofReal_zero, div_zero, norm_zero]; positivity
  · have h1 : |Real.sin p.1| ≤ gradNorm p :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (Real.sin p.2)])
    have h2 : |Real.sin p.2| ≤ gradNorm p :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (Real.sin p.1)])
    have hg : 0 < gradNorm p := hρ
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hg.le, div_le_iff₀ hg]
    calc ‖(Real.sin p.1 : ℂ) * ψx p + (Real.sin p.2 : ℂ) * ψy p‖
        ≤ |Real.sin p.1| * ‖ψx p‖ + |Real.sin p.2| * ‖ψy p‖ := by
          refine (norm_add_le _ _).trans ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
      _ ≤ gradNorm p * ‖ψx p‖ + gradNorm p * ‖ψy p‖ := by gcongr
      _ = (‖ψx p‖ + ‖ψy p‖) * gradNorm p := by ring

/-- `|ψₜ| ≤ |ψₓ| + |ψ_y|`. -/
theorem norm_tangentDeriv_le (ψx ψy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    ‖tangentDeriv ψx ψy p‖ ≤ ‖ψx p‖ + ‖ψy p‖ := by
  unfold tangentDeriv
  rcases (Real.sqrt_nonneg (Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2)).eq_or_lt with hρ | hρ
  · rw [gradNorm, ← hρ]; simp only [Complex.ofReal_zero, div_zero, norm_zero]; positivity
  · have h1 : |Real.sin p.1| ≤ gradNorm p :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (Real.sin p.2)])
    have h2 : |Real.sin p.2| ≤ gradNorm p :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (Real.sin p.1)])
    have hg : 0 < gradNorm p := hρ
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hg.le, div_le_iff₀ hg]
    calc ‖(Real.sin p.2 : ℂ) * ψx p - (Real.sin p.1 : ℂ) * ψy p‖
        ≤ |Real.sin p.2| * ‖ψx p‖ + |Real.sin p.1| * ‖ψy p‖ := by
          refine (norm_sub_le _ _).trans ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
      _ ≤ gradNorm p * ‖ψx p‖ + gradNorm p * ‖ψy p‖ := by gcongr
      _ = (‖ψx p‖ + ‖ψy p‖) * gradNorm p := by ring

/-- The bulk is nonnegative even at the center (where the total definitions set `c = f = 0`). -/
theorem eeBulkDensity_nonneg {ω : L2} {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    0 ≤ eeBulkDensity ω p := by
  have h0 : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have h2 : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
  rcases lt_or_eq_of_le h2 with h2 | h2
  · exact eeDensity_nonneg h0 h2 _ _ _
  · simp only [eeBulkDensity, eeDensity, normalCoeff, normalC, h2]
    norm_num

/-- The bulk density is integrable on every truncated cell `{Ψ > 2h}`, `h > 0`
    (`lem:ee-bulk-integrable`): there `0 ≤ f ≤ (2 - Ψ)/Ψ ≤ 1/h` and `0 < c ≤ 1`, so
    `𝒥 ≤ |ω|²/h + 6(|ψₓ|² + |ψ_y|²)`. No eigenvalue equation is needed. -/
theorem integrableOn_eeBulkDensity (ω : L2) {h : ℝ} (h0 : 0 < h) :
    IntegrableOn (eeBulkDensity ω) {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p} := by
  set A : Set (ℝ × ℝ) := {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p}
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have hA : MeasurableSet A := by
    change MeasurableSet ({p : ℝ × ℝ | |(diagCoord p).1| < Real.pi / 2} ∩
      {p | |(diagCoord p).2| < Real.pi / 2} ∩ {p | 2 * h < dipoleLift p})
    unfold diagCoord dipoleLift
    exact ((measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_lt (by fun_prop) measurable_const)).inter
      (measurableSet_lt measurable_const (by fun_prop))
  have hAs : A ⊆ Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨⟨ha, hb⟩, -⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) A :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  have hg : IntegrableOn (fun p ↦ 1 / h * ‖liftL2 ω p‖ ^ 2 +
      6 * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2)) A :=
    ((hsq ω).const_mul _).add (((hsq _).add (hsq _)).const_mul 6)
  refine hg.mono' ?_ ?_
  · have h1 := hmeas ω
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    have hm : Measurable (eeBulkDensity ω) := by
      change Measurable fun p ↦ eeDensity p (liftL2 ω p) (streamNormal ω p) (streamTangent ω p)
      simp only [eeDensity, normalCoeff, normalC, gradSq_dipoleLift, dipoleLift,
        streamNormal, streamTangent, normalDeriv, tangentDeriv, gradNorm, streamLiftX,
        streamLiftY]
      fun_prop
    exact hm.aestronglyMeasurable
  · refine (ae_restrict_iff' hA).2 (Eventually.of_forall fun p hp ↦ ?_)
    have hJ0 := eeBulkDensity_nonneg (ω := ω) hp.1
    rw [Real.norm_of_nonneg hJ0]
    have hΨ0 : 0 < dipoleLift p := by linarith [hp.2]
    have hΨ2 : dipoleLift p ≤ 2 := by
      unfold dipoleLift; linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
    have hXY (u : ℂ) (hu : ‖u‖ ≤ ‖streamLiftX ω p‖ + ‖streamLiftY ω p‖) :
        ‖u‖ ^ 2 ≤ 2 * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2) := by
      nlinarith [norm_nonneg u, sq_nonneg (‖streamLiftX ω p‖ - ‖streamLiftY ω p‖)]
    have hn := hXY _ (norm_normalDeriv_le _ _ p)
    have ht := hXY _ (norm_tangentDeriv_le _ _ p)
    have hω2 := sq_nonneg ‖liftL2 ω p‖
    rcases lt_or_eq_of_le hΨ2 with hlt | heq
    · obtain ⟨hc0, hc1⟩ := normalC_pos_le_one hΨ0 hlt
      have hf0 := normalCoeff_nonneg hΨ0 hlt
      have hf : normalCoeff p ≤ 1 / h := by
        refine (normalCoeff_le hΨ0 hlt).trans ?_
        rw [div_le_div_iff₀ hΨ0 h0]
        nlinarith [hp.2]
      have e1 : normalCoeff p * ‖liftL2 ω p‖ ^ 2 ≤ 1 / h * ‖liftL2 ω p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hf hω2
      have e2 : (2 - normalC p) * ‖streamNormal ω p‖ ^ 2 ≤ 2 * ‖streamNormal ω p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have e3 : normalC p * ‖streamTangent ω p‖ ^ 2 ≤ ‖streamTangent ω p‖ ^ 2 := by
        nlinarith [sq_nonneg ‖streamTangent ω p‖]
      simp only [eeBulkDensity, eeDensity]
      linarith
    · have hf : normalCoeff p = 0 := by simp [normalCoeff, heq]
      have hc : normalC p = 0 := by simp [normalC, heq]
      simp only [eeBulkDensity, eeDensity, hf, hc]
      have : 0 ≤ 1 / h * ‖liftL2 ω p‖ ^ 2 := by positivity
      linarith [sq_nonneg ‖streamTangent ω p‖]

/-- The boundary density `E = ρ Re(ψψ̄ₙ) + (2 - Ψ)(|ψₙ|² - |ψₜ|² - Re(ωψ̄))`; on the level
    `{Ψ = 2h}` its flow-time integral is the level term `G(h)`. -/
def eeBoundaryDensity (ω : L2) (p : ℝ × ℝ) : ℝ :=
  gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re +
    (2 - dipoleLift p) * (‖streamNormal ω p‖ ^ 2 - ‖streamTangent ω p‖ ^ 2 -
      (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)

/-- The boundary density is integrable on the cell (`lem:ee-boundary-integrable`): it is a sum
    of products of `L²` functions with bounded coefficients. -/
theorem integrableOn_eeBoundaryDensity (ω : L2) :
    IntegrableOn (eeBoundaryDensity ω) cellSquare := by
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have hC : MeasurableSet cellSquare := by
    change MeasurableSet ({p : ℝ × ℝ | |(diagCoord p).1| < Real.pi / 2} ∩
      {p | |(diagCoord p).2| < Real.pi / 2})
    unfold diagCoord
    exact (measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hAs : cellSquare ⊆ Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  have hg : IntegrableOn (fun p ↦ 10 * (‖streamLift ω p‖ ^ 2 + ‖streamLiftX ω p‖ ^ 2 +
      ‖streamLiftY ω p‖ ^ 2 + ‖liftL2 ω p‖ ^ 2)) cellSquare :=
    ((((hsq _).add (hsq _)).add (hsq _)).add (hsq _)).const_mul 10
  refine hg.mono' ?_ ?_
  · have h0 := hmeas (invLap ω)
    have h1 := hmeas ω
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    have hm : Measurable (eeBoundaryDensity ω) := by
      change Measurable fun p ↦ gradNorm p *
        (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re +
        (2 - dipoleLift p) * (‖streamNormal ω p‖ ^ 2 - ‖streamTangent ω p‖ ^ 2 -
          (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)
      simp only [dipoleLift, streamNormal, streamTangent, normalDeriv, tangentDeriv, gradNorm,
        streamLiftX, streamLiftY, streamLift]
      fun_prop
    exact hm.aestronglyMeasurable
  · refine (ae_restrict_iff' hC).2 (Eventually.of_forall fun p hp ↦ ?_)
    have hΨ0 : 0 < dipoleLift p := by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
    have hΨ2 : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
    have hρ0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have hρ2 : gradNorm p ≤ 2 := by
      have hsq2 : gradNorm p ^ 2 ≤ 2 := by
        rw [gradNorm, Real.sq_sqrt (by positivity)]
        nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
      nlinarith
    have hn := norm_normalDeriv_le (streamLiftX ω) (streamLiftY ω) p
    have ht := norm_tangentDeriv_le (streamLiftX ω) (streamLiftY ω) p
    set a := ‖streamLift ω p‖
    set X := ‖streamLiftX ω p‖
    set Y := ‖streamLiftY ω p‖
    set w := ‖liftL2 ω p‖
    set n := ‖streamNormal ω p‖
    set t := ‖streamTangent ω p‖
    have hn0 : 0 ≤ n := norm_nonneg _
    have ht0 : 0 ≤ t := norm_nonneg _
    have ha0 : 0 ≤ a := norm_nonneg _
    have hw0 : 0 ≤ w := norm_nonneg _
    have hX0 : 0 ≤ X := norm_nonneg _
    have hY0 : 0 ≤ Y := norm_nonneg _
    have e1 : |(streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re| ≤ a * n := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    have e2 : |(liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re| ≤ w * a := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    have hbd : |eeBoundaryDensity ω p| ≤ 2 * (a * n) + 2 * (n ^ 2 + t ^ 2 + w * a) := by
      unfold eeBoundaryDensity
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hρ0]
        exact mul_le_mul hρ2 e1 (abs_nonneg _) (by norm_num)
      · rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - dipoleLift p)]
        refine mul_le_mul (by linarith) ?_ (abs_nonneg _) (by norm_num)
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans ?_) e2)
        rw [abs_of_nonneg (sq_nonneg n), abs_of_nonneg (sq_nonneg t)]
    rw [Real.norm_eq_abs]
    refine hbd.trans ?_
    have hn2 : n ^ 2 ≤ (X + Y) ^ 2 := pow_le_pow_left₀ hn0 hn 2
    have ht2 : t ^ 2 ≤ (X + Y) ^ 2 := pow_le_pow_left₀ ht0 ht 2
    have han : a * n ≤ a * (X + Y) := mul_le_mul_of_nonneg_left hn ha0
    nlinarith [sq_nonneg (a - X), sq_nonneg (a - Y), sq_nonneg (X - Y), sq_nonneg (w - a)]

/-- On almost every level the flow-time integral of the boundary density is the level term
    (`lem:ee-boundary-integrable`): `Ψ = 2h` there, and the three level integrals exist. -/
theorem ae_levelIntegral_eeBoundaryDensity (ω : L2) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 1)),
      levelIntegral h (eeBoundaryDensity ω) = eeLevelTerm ω h := by
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have m0 := hmeas (invLap ω)
  have m1 := hmeas ω
  have m2 := hmeas (streamPartial 0 ω)
  have m3 := hmeas (streamPartial 1 ω)
  have hAs : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  -- All four pieces of `E` are dominated by `F = |ψ|² + |ψₓ|² + |ψ_y|² + |ω|²`.
  set F : ℝ × ℝ → ℝ := fun p ↦ ‖streamLift ω p‖ ^ 2 + ‖streamLiftX ω p‖ ^ 2 +
    ‖streamLiftY ω p‖ ^ 2 + ‖liftL2 ω p‖ ^ 2 with hFdef
  have hF : IntegrableOn F cellSquare := (((hsq _).add (hsq _)).add (hsq _)).add (hsq _)
  have hρm : Measurable gradNorm := by
    unfold gradNorm
    fun_prop
  have hnm : Measurable (streamNormal ω) := by
    change Measurable fun p ↦ normalDeriv (streamLiftX ω) (streamLiftY ω) p
    simp only [normalDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have htm : Measurable (streamTangent ω) := by
    change Measurable fun p ↦ tangentDeriv (streamLiftX ω) (streamLiftY ω) p
    simp only [tangentDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have hsm : Measurable (streamLift ω) := m0
  have hre (u v : ℂ) : |(u * (starRingEnd ℂ) v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hρ2 (p : ℝ × ℝ) : gradNorm p ≤ 2 := by
    have h0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have h2 : gradNorm p ^ 2 ≤ 2 := by
      rw [gradNorm, Real.sq_sqrt (by positivity)]
      nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
    nlinarith
  have hn (p : ℝ × ℝ) : ‖streamNormal ω p‖ ^ 2 ≤ 2 * F p := by
    have := norm_normalDeriv_le (streamLiftX ω) (streamLiftY ω) p
    have h0' := norm_nonneg (streamNormal ω p)
    simp only [hFdef]
    nlinarith [sq_nonneg (‖streamLiftX ω p‖ - ‖streamLiftY ω p‖),
      norm_nonneg (streamLiftX ω p), norm_nonneg (streamLiftY ω p),
      sq_nonneg ‖streamLift ω p‖, sq_nonneg ‖liftL2 ω p‖]
  have ht (p : ℝ × ℝ) : ‖streamTangent ω p‖ ^ 2 ≤ 2 * F p := by
    have := norm_tangentDeriv_le (streamLiftX ω) (streamLiftY ω) p
    have h0' := norm_nonneg (streamTangent ω p)
    simp only [hFdef]
    nlinarith [sq_nonneg (‖streamLiftX ω p‖ - ‖streamLiftY ω p‖),
      norm_nonneg (streamLiftX ω p), norm_nonneg (streamLiftY ω p),
      sq_nonneg ‖streamLift ω p‖, sq_nonneg ‖liftL2 ω p‖]
  have hw (p : ℝ × ℝ) : |(liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re| ≤ F p := by
    refine (hre _ _).trans ?_
    simp only [hFdef]
    nlinarith [sq_nonneg (‖liftL2 ω p‖ - ‖streamLift ω p‖),
      sq_nonneg ‖streamLiftX ω p‖, sq_nonneg ‖streamLiftY ω p‖]
  have ha (p : ℝ × ℝ) :
      |gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re| ≤ 3 * F p := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ gradNorm p from Real.sqrt_nonneg _)]
    have h3' : ‖streamLift ω p‖ ^ 2 ≤ F p := by
      simp only [hFdef]
      nlinarith [sq_nonneg ‖streamLiftX ω p‖, sq_nonneg ‖streamLiftY ω p‖,
        sq_nonneg ‖liftL2 ω p‖]
    nlinarith [mul_le_mul (hρ2 p) (hre (streamLift ω p) (streamNormal ω p)) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2), hn p,
      sq_nonneg (‖streamLift ω p‖ - ‖streamNormal ω p‖)]
  have i1 : IntegrableOn (fun p ↦ gradNorm p *
      (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) cellSquare :=
    (hF.const_mul 3).mono' (hρm.mul (Complex.measurable_re.comp
      (hsm.mul (Complex.continuous_conj.measurable.comp hnm)))).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ha p)
  have i2 : IntegrableOn (fun p ↦ ‖streamNormal ω p‖ ^ 2) cellSquare :=
    (hF.const_mul 2).mono' (hnm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hn p)
  have i3 : IntegrableOn (fun p ↦ ‖streamTangent ω p‖ ^ 2) cellSquare :=
    (hF.const_mul 2).mono' (htm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact ht p)
  have i4 : IntegrableOn (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)
      cellSquare :=
    hF.mono' (Complex.measurable_re.comp
      (m1.mul (Complex.continuous_conj.measurable.comp hsm))).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hw p)
  -- On almost every level the pieces are integrable in flow time, and `Ψ = 2h` there.
  filter_upwards [(integral_cellSquare_eq i1).1, (integral_cellSquare_eq i2).1,
    (integral_cellSquare_eq i3).1, (integral_cellSquare_eq i4).1,
    ae_restrict_mem measurableSet_Ioo] with h j1 j2 j3 j4 hh
  have hE : (fun t ↦ eeBoundaryDensity ω (dipoleOrbit h t)) = fun t ↦
      gradNorm (dipoleOrbit h t) * (streamLift ω (dipoleOrbit h t) *
        (starRingEnd ℂ) (streamNormal ω (dipoleOrbit h t))).re +
      (2 - 2 * h) * (‖streamNormal ω (dipoleOrbit h t)‖ ^ 2 -
        ‖streamTangent ω (dipoleOrbit h t)‖ ^ 2 -
        (liftL2 ω (dipoleOrbit h t) * (starRingEnd ℂ) (streamLift ω (dipoleOrbit h t))).re) := by
    funext t
    rw [eeBoundaryDensity, dipoleLift_dipoleOrbit hh.1 hh.2]
  simp only [eeLevelTerm, levelIntegral_eq_setIntegral hh.1 hh.2]
  have j23 : IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2 -
      ‖streamTangent ω (dipoleOrbit h t)‖ ^ 2) (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)) :=
    j2.sub j3
  have j234 : IntegrableOn (fun t ↦ (2 - 2 * h) * (‖streamNormal ω (dipoleOrbit h t)‖ ^ 2 -
      ‖streamTangent ω (dipoleOrbit h t)‖ ^ 2 -
      (liftL2 ω (dipoleOrbit h t) * (starRingEnd ℂ) (streamLift ω (dipoleOrbit h t))).re))
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)) :=
    (j23.sub j4).const_mul _
  rw [hE, integral_add j1 j234, integral_const_mul, integral_sub j23 j4, integral_sub j2 j3]

/-! ### Integrals over the period square of weighted products of lifts

Bookkeeping for `ee_cutoff_identity`: the terms of the virial identity are integrals of
`c Re(u v̄)` with continuous `c` and lifts `u, v` of `L²` functions. -/

/-- `c Re(u v̄)` for the lifts `u, v` of `g, h ∈ L²`. -/
def rePair (c : ℝ × ℝ → ℝ) (g h : L2) (p : ℝ × ℝ) : ℝ :=
  c p * (liftL2 g p * (starRingEnd ℂ) (liftL2 h p)).re

theorem integrableOn_rePair {c : ℝ × ℝ → ℝ} (hc : Continuous c) (g h : L2) :
    IntegrableOn (rePair c g h) periodSquare :=
  (integrableOn_liftL2_mul_conj g h).re.continuousOn_mul hc.continuousOn isCompact_periodSquare

/-- `Re ∫ c u v̄ = ∫ c Re(u v̄)` over the period square for real continuous `c`. -/
theorem re_squarePairing_smul {c : ℝ × ℝ → ℝ} (hc : Continuous c) (g h : L2) :
    (squarePairing (fun p ↦ c p • liftL2 g p) (liftL2 h)).re = squareIntegral (rePair c g h) := by
  have hi : IntegrableOn (fun p ↦ ((c p : ℝ) : ℂ) *
      (liftL2 g p * (starRingEnd ℂ) (liftL2 h p))) periodSquare :=
    (integrableOn_liftL2_mul_conj g h).continuousOn_mul
      (Complex.continuous_ofReal.comp hc).continuousOn isCompact_periodSquare
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  unfold squarePairing squareIntegral
  simp only [Complex.real_smul, mul_assoc]
  rw [← hre]
  congr 1
  funext p
  rw [rePair, Complex.re_ofReal_mul]

/-- Splitting a weighted finite sum of integrable functions on the period square. -/
theorem squareIntegral_weighted_sum {n : ℕ} (w : Fin n → ℝ) (F : Fin n → ℝ × ℝ → ℝ)
    (hF : ∀ i, IntegrableOn (F i) periodSquare) :
    squareIntegral (fun p ↦ ∑ i, w i * F i p) = ∑ i, w i * squareIntegral (F i) := by
  unfold squareIntegral
  rw [integral_finsetSum _ (fun i _ ↦ (hF i).const_mul (w i))]
  exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul (w i) _

theorem re_mul_conj_self (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem re_mul_conj_smul_add (s X Y : ℂ) (a b : ℝ) :
    (s * (starRingEnd ℂ) (a • X + b • Y)).re =
      a * (s * (starRingEnd ℂ) X).re + b * (s * (starRingEnd ℂ) Y).re := by
  rw [Complex.real_smul, Complex.real_smul, map_add, map_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal, mul_add, Complex.add_re,
    show s * ((a : ℂ) * (starRingEnd ℂ) X) = (a : ℂ) * (s * (starRingEnd ℂ) X) by ring,
    show s * ((b : ℂ) * (starRingEnd ℂ) Y) = (b : ℂ) * (s * (starRingEnd ℂ) Y) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- With `N = sₓX + s_yY`, `T = s_yX - sₓY` and `r = (sₓ² + s_y²)^{1/2} ≠ 0`:
    `r Re(s (N/r)‾) = sₓ Re(sX̄) + s_y Re(sȲ)` and `|N/r|² + |T/r|² = |X|² + |Y|²`. -/
theorem normal_tangent_frame {sx sy : ℝ} (hρ : sx ^ 2 + sy ^ 2 ≠ 0) (X Y s : ℂ) :
    √(sx ^ 2 + sy ^ 2) * (s * (starRingEnd ℂ) (((sx : ℂ) * X + (sy : ℂ) * Y) /
        (√(sx ^ 2 + sy ^ 2) : ℂ))).re =
      sx * (s * (starRingEnd ℂ) X).re + sy * (s * (starRingEnd ℂ) Y).re ∧
    ‖((sx : ℂ) * X + (sy : ℂ) * Y) / (√(sx ^ 2 + sy ^ 2) : ℂ)‖ ^ 2 +
      ‖((sy : ℂ) * X - (sx : ℂ) * Y) / (√(sx ^ 2 + sy ^ 2) : ℂ)‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have hpos : 0 < sx ^ 2 + sy ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hρ)
  have hr : 0 < √(sx ^ 2 + sy ^ 2) := Real.sqrt_pos.2 hpos
  have hR : √(sx ^ 2 + sy ^ 2) ^ 2 = sx ^ 2 + sy ^ 2 := Real.sq_sqrt hpos.le
  constructor
  · rw [map_div₀, Complex.conj_ofReal, mul_div_assoc', Complex.div_ofReal_re,
      mul_div_cancel₀ _ hr.ne', map_add, map_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, mul_add, Complex.add_re,
      show s * ((sx : ℂ) * (starRingEnd ℂ) X) = (sx : ℂ) * (s * (starRingEnd ℂ) X) by ring,
      show s * ((sy : ℂ) * (starRingEnd ℂ) Y) = (sy : ℂ) * (s * (starRingEnd ℂ) Y) by ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  · rw [norm_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_pow, div_pow, hR,
      ← add_div, div_eq_iff hρ]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
    ring

/-- The cutoff identity (`lem:ee-cutoff-identity`): for smooth `φ` vanishing outside
    `[a, b] ⊂ (0, 1)` and `χ(s) = φ(s/2)`, `∫_cell χ(Ψ) 𝒥 = ∫_cell χ'(Ψ) E`. From
    `lem:virial-l2` for `χ(Ψ)W`, the cutoff algebra, integration by parts for `ψ ∈ H²`, and the
    passage from the period square to the cell. Pointwise, `χ(Ψ)𝒥 - χ'(Ψ)E` is a weighted sum
    of ten integrands that are integrable on the period square; the virial identity and the two
    integrations by parts make the weighted sum of their integrals vanish. -/
theorem ee_cutoff_identity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {a b : ℝ} (ha : 0 < a)
    (hb : b < 1) (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    ∫ p in cellSquare, φ (dipoleLift p / 2) * eeBulkDensity ω p =
      ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * eeBoundaryDensity ω p := by
  -- The cutoff `χ(s) = φ(s/2)`, supported in `[2a, 2b] ⊂ (0, 2)`.
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ → ℝ, χ = fun s ↦ φ (s / 2) := ⟨_, rfl⟩
  have hχv (r : ℝ) : φ (r / 2) = χ r := by rw [hχdef]
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hχdef ▸ hφ.comp (contDiff_id.div_const 2)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hdχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv χ) := (contDiff_infty_iff_deriv.1 hχ).2
  have hχ' (r : ℝ) : deriv φ (r / 2) / 2 = deriv χ r := by
    have h := (hφd (r / 2)).hasDerivAt.comp r ((hasDerivAt_id r).div_const 2)
    rw [hχdef]
    refine (h.deriv.trans ?_).symm
    ring
  have hχ0 : ∀ s, χ s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b := fun s hs ↦ by
    obtain ⟨h1, h2⟩ := hsupp _ (by rwa [hχdef] at hs)
    constructor <;> linarith
  have hdχ0 : ∀ s, deriv χ s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b := by
    intro s hs
    by_contra hout
    have hev : ∀ᶠ r in 𝓝 s, χ r = 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds
        (show s ∈ (Icc (2 * a) (2 * b))ᶜ from fun h ↦ hout h)] with r hr
      by_contra hne
      exact hr (hχ0 r hne)
    have hev' : χ =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := hev
    exact hs (by rw [hev'.deriv_eq, deriv_const])
  have hε₁ : 0 < 2 * a := by linarith
  have hε₂ : 2 * b < 2 := by linarith
  have hΨs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift := by unfold dipoleLift; fun_prop
  have hΨc : Continuous dipoleLift := hΨs.continuous
  have hpΨ : IsPeriodicLift dipoleLift := fun p ↦ by
    simp only [dipoleLift, Real.cos_add_two_pi, and_self]
  -- The virial identity for `χ(Ψ)W`.
  obtain ⟨hW₁, hW₂, hf, hpW₁, hpW₂, hpf, had⟩ := annularCutoff_normalField hχ hε₁ hε₂ hχ0
  have hle (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 le_top
  have hsuppV : ∀ p, ((χ (dipoleLift p) * normalField₁ p ≠ 0 ∨
      χ (dipoleLift p) * normalField₂ p ≠ 0 ∨ χ (dipoleLift p) * normalCoeff p ≠ 0) →
      2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b) := by
    intro p hp
    apply hχ0
    rcases hp with h | h | h <;> exact left_ne_zero_of_mul h
  have V := (virial_l2 had (hW₁.of_le (hle 3)) (hW₂.of_le (hle 3)) (hf.of_le (hle 2)) hpW₁ hpW₂
    hpf ha hb hsuppV hlam hω).2
  -- `f_χ - div W_χ = φ₁` with `φ₁ = -χ(Ψ) - (Ψ - 2)χ'(Ψ)`.
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℝ × ℝ → ℝ, φ₁ = fun p ↦
      -χ (dipoleLift p) - (dipoleLift p - 2) * deriv χ (dipoleLift p) := ⟨_, rfl⟩
  have hφ₁eq : (fun q ↦ χ (dipoleLift q) * normalCoeff q -
      divergence (fun q ↦ χ (dipoleLift q) * normalField₁ q)
        (fun q ↦ χ (dipoleLift q) * normalField₂ q) q) = φ₁ := by
    rw [hφ₁]
    exact funext fun q ↦ (cutoff_normalField_algebra hχ hε₁ hε₂ hχ0 q).1
  rw [hφ₁eq] at V
  have hφ₁s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₁ := by
    rw [hφ₁]
    exact (hχ.comp hΨs).neg.sub ((hΨs.sub contDiff_const).mul (hdχ.comp hΨs))
  have hφ₁p : IsPeriodicLift φ₁ := fun p ↦ by
    simp only [hφ₁, (hpΨ p).1, (hpΨ p).2, and_self]
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p ↦ χ (dipoleLift p)) := hχ.comp hΨs
  have hcp : IsPeriodicLift (fun p ↦ χ (dipoleLift p)) := fun p ↦ by
    simp only [(hpΨ p).1, (hpΨ p).2, and_self]
  -- Integration by parts for `ψ` with `φ₁` and with `χ(Ψ)`.
  have S1 := (stream_ibp hω.1 hφ₁s hφ₁p).1
  have S2 := (stream_ibp hω.1 hcs hcp).2
  rw [S1] at V
  simp only [streamLift, streamLiftX, streamLiftY] at V S2
  -- Continuity of the coefficients.
  have hc1 {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) : Continuous (partialX u) :=
    (contDiff_partialX (n := 0) (by simpa using hu.of_le (hle 1))).continuous
  have hc2 {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) : Continuous (partialY u) :=
    (contDiff_partialY (n := 0) (by simpa using hu.of_le (hle 1))).continuous
  rw [re_squarePairing_smul hf.continuous ω ω,
    re_squarePairing_smul (hc1 hW₁) (streamPartial 0 ω) (streamPartial 0 ω),
    re_squarePairing_smul (hc1 hW₂) (streamPartial 1 ω) (streamPartial 0 ω),
    re_squarePairing_smul (hc2 hW₁) (streamPartial 0 ω) (streamPartial 1 ω),
    re_squarePairing_smul (hc2 hW₂) (streamPartial 1 ω) (streamPartial 1 ω),
    re_squarePairing_smul hf.continuous (streamPartial 0 ω) (streamPartial 0 ω),
    re_squarePairing_smul hf.continuous (streamPartial 1 ω) (streamPartial 1 ω)] at V
  -- Abbreviations `K = |∇ψ|² + Re(ωψ̄)` and `R = Re(ψ (∇χ(Ψ)·∇ψ)‾)`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ × ℝ → ℝ, K = fun p ↦ ‖liftL2 (streamPartial 0 ω) p‖ ^ 2 +
      ‖liftL2 (streamPartial 1 ω) p‖ ^ 2 +
      (liftL2 ω p * (starRingEnd ℂ) (liftL2 (invLap ω) p)).re := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ × ℝ → ℝ, R = fun p ↦ (liftL2 (invLap ω) p * (starRingEnd ℂ)
      (partialX (fun p ↦ χ (dipoleLift p)) p • liftL2 (streamPartial 0 ω) p +
        partialY (fun p ↦ χ (dipoleLift p)) p • liftL2 (streamPartial 1 ω) p)).re := ⟨_, rfl⟩
  have hKp (p : ℝ × ℝ) : ‖liftL2 (streamPartial 0 ω) p‖ ^ 2 +
      ‖liftL2 (streamPartial 1 ω) p‖ ^ 2 +
      (liftL2 ω p * (starRingEnd ℂ) (liftL2 (invLap ω) p)).re = K p := by rw [hK]
  have hRp (p : ℝ × ℝ) : (liftL2 (invLap ω) p * (starRingEnd ℂ)
      (partialX (fun p ↦ χ (dipoleLift p)) p • liftL2 (streamPartial 0 ω) p +
        partialY (fun p ↦ χ (dipoleLift p)) p • liftL2 (streamPartial 1 ω) p)).re = R p := by
    rw [hR]
  simp only [hKp, hRp] at V S2
  -- Integrability on the period square.
  have hsub : periodSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro q ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith [Real.pi_pos], h2⟩, by linarith [Real.pi_pos], h4⟩
  have hn2 (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) periodSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hsub
  have hKi : IntegrableOn K periodSquare := by
    rw [hK]
    exact ((hn2 _).add (hn2 _)).add (integrableOn_liftL2_mul_conj ω (invLap ω)).re
  have hRi : IntegrableOn R periodSquare := by
    refine ((integrableOn_rePair (hc1 hcs) (invLap ω) (streamPartial 0 ω)).add
      (integrableOn_rePair (hc2 hcs) (invLap ω) (streamPartial 1 ω))).congr_fun
      (fun p _ ↦ ?_) isCompact_periodSquare.isClosed.measurableSet
    rw [hR]
    exact (re_mul_conj_smul_add _ _ _ _ _).symm
  have hFs : ∀ i, IntegrableOn (![rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) ω ω,
      rePair (partialX fun p ↦ χ (dipoleLift p) * normalField₁ p) (streamPartial 0 ω)
        (streamPartial 0 ω),
      rePair (partialX fun p ↦ χ (dipoleLift p) * normalField₂ p) (streamPartial 1 ω)
        (streamPartial 0 ω),
      rePair (partialY fun p ↦ χ (dipoleLift p) * normalField₁ p) (streamPartial 0 ω)
        (streamPartial 1 ω),
      rePair (partialY fun p ↦ χ (dipoleLift p) * normalField₂ p) (streamPartial 1 ω)
        (streamPartial 1 ω),
      rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) (streamPartial 0 ω) (streamPartial 0 ω),
      rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) (streamPartial 1 ω) (streamPartial 1 ω),
      fun p ↦ φ₁ p * K p, fun p ↦ χ (dipoleLift p) * K p, R] i) periodSquare := by
    intro i
    fin_cases i
    · exact integrableOn_rePair hf.continuous _ _
    · exact integrableOn_rePair (hc1 hW₁) _ _
    · exact integrableOn_rePair (hc1 hW₂) _ _
    · exact integrableOn_rePair (hc2 hW₁) _ _
    · exact integrableOn_rePair (hc2 hW₂) _ _
    · exact integrableOn_rePair hf.continuous _ _
    · exact integrableOn_rePair hf.continuous _ _
    · exact hKi.continuousOn_mul hφ₁s.continuous.continuousOn isCompact_periodSquare
    · exact hKi.continuousOn_mul hcs.continuous.continuousOn isCompact_periodSquare
    · exact hRi
  -- The difference of the two sides is pointwise the weighted sum.
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ × ℝ → ℝ, D = fun p ↦ χ (dipoleLift p) * eeBulkDensity ω p -
      deriv χ (dipoleLift p) * eeBoundaryDensity ω p := ⟨_, rfl⟩
  have hD : D = fun p ↦ ∑ i, (![1, 2, 2, 2, 2, -1, -1, 1, 1, 1] : Fin 10 → ℝ) i *
      (![rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) ω ω,
      rePair (partialX fun p ↦ χ (dipoleLift p) * normalField₁ p) (streamPartial 0 ω)
        (streamPartial 0 ω),
      rePair (partialX fun p ↦ χ (dipoleLift p) * normalField₂ p) (streamPartial 1 ω)
        (streamPartial 0 ω),
      rePair (partialY fun p ↦ χ (dipoleLift p) * normalField₁ p) (streamPartial 0 ω)
        (streamPartial 1 ω),
      rePair (partialY fun p ↦ χ (dipoleLift p) * normalField₂ p) (streamPartial 1 ω)
        (streamPartial 1 ω),
      rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) (streamPartial 0 ω) (streamPartial 0 ω),
      rePair (fun p ↦ χ (dipoleLift p) * normalCoeff p) (streamPartial 1 ω) (streamPartial 1 ω),
      fun p ↦ φ₁ p * K p, fun p ↦ χ (dipoleLift p) * K p, R] i) p := by
    funext p
    have hcx : partialX (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -Real.sin p.1 :=
      ((hχd (dipoleLift p)).hasDerivAt.comp p.1
        ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))).deriv
    have hcy : partialY (fun q ↦ χ (dipoleLift q)) p = deriv χ (dipoleLift p) * -Real.sin p.2 :=
      ((hχd (dipoleLift p)).hasDerivAt.comp p.2
        ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))).deriv
    have alg2 := (cutoff_normalField_algebra hχ hε₁ hε₂ hχ0 p).2
      (liftL2 (streamPartial 0 ω) p) (liftL2 (streamPartial 1 ω) p)
    have key : deriv χ (dipoleLift p) *
        (√(Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2) * (liftL2 (invLap ω) p * (starRingEnd ℂ)
          (((Real.sin p.1 : ℂ) * liftL2 (streamPartial 0 ω) p +
            (Real.sin p.2 : ℂ) * liftL2 (streamPartial 1 ω) p) /
            (√(Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2) : ℂ))).re -
        (Real.sin p.1 * (liftL2 (invLap ω) p * (starRingEnd ℂ) (liftL2 (streamPartial 0 ω) p)).re +
          Real.sin p.2 * (liftL2 (invLap ω) p * (starRingEnd ℂ)
            (liftL2 (streamPartial 1 ω) p)).re) +
        (2 - dipoleLift p) * (‖liftL2 (streamPartial 0 ω) p‖ ^ 2 +
          ‖liftL2 (streamPartial 1 ω) p‖ ^ 2 -
          ‖((Real.sin p.1 : ℂ) * liftL2 (streamPartial 0 ω) p +
            (Real.sin p.2 : ℂ) * liftL2 (streamPartial 1 ω) p) /
            (√(Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2) : ℂ)‖ ^ 2 -
          ‖((Real.sin p.2 : ℂ) * liftL2 (streamPartial 0 ω) p -
            (Real.sin p.1 : ℂ) * liftL2 (streamPartial 1 ω) p) /
            (√(Real.sin p.1 ^ 2 + Real.sin p.2 ^ 2) : ℂ)‖ ^ 2)) = 0 := by
      by_cases hk : deriv χ (dipoleLift p) = 0
      · rw [hk, zero_mul]
      · obtain ⟨h1, h2⟩ := hdχ0 _ hk
        have hg := gradSq_dipoleLift_pos (p := p) (by linarith) (by linarith)
        rw [gradSq_dipoleLift] at hg
        have fr := normal_tangent_frame hg.ne' (liftL2 (streamPartial 0 ω) p)
          (liftL2 (streamPartial 1 ω) p) (liftL2 (invLap ω) p)
        linear_combination deriv χ (dipoleLift p) * fr.1 -
          deriv χ (dipoleLift p) * (2 - dipoleLift p) * fr.2
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      hDdef, rePair, hK, hR, hφ₁, eeBulkDensity, eeDensity, eeBoundaryDensity, streamNormal,
      streamTangent, streamLift, streamLiftX, streamLiftY, normalDeriv, tangentDeriv, gradNorm,
      re_mul_conj_self, re_mul_conj_smul_add, hcx, hcy]
    linear_combination -alg2 - key
  have hsum : squareIntegral D = 0 := by
    rw [hD, squareIntegral_weighted_sum _ _ hFs]
    simp [Fin.sum_univ_succ]
    linarith
  -- From the period square to the cell.
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have hDm : Measurable D := by
    have h0 := hmeas (invLap ω)
    have h1 := hmeas ω
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    have hχm : Measurable χ := hχ.continuous.measurable
    have hdχm : Measurable (deriv χ) := hdχ.continuous.measurable
    rw [hDdef]
    simp only [eeBulkDensity, eeDensity, eeBoundaryDensity, normalCoeff, normalC,
      gradSq_dipoleLift, dipoleLift, streamNormal, streamTangent, normalDeriv, tangentDeriv,
      gradNorm, streamLiftX, streamLiftY, streamLift]
    fun_prop
  have hDp : IsPeriodicLift D := by
    intro p
    have hl (g : L2) := isPeriodicLift_liftL2 g p
    rw [hDdef]
    constructor <;>
    simp only [eeBulkDensity, eeDensity, eeBoundaryDensity, normalCoeff, normalC,
      gradSq_dipoleLift, streamNormal, streamTangent, normalDeriv, tangentDeriv, gradNorm,
      streamLiftX, streamLiftY, streamLift, (hl _).1, (hl _).2, (hpΨ p).1, (hpΨ p).2,
      Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hD0 : ∀ p, dipoleLift p ≤ 0 → D p = 0 := by
    intro p hp
    have h1 : χ (dipoleLift p) = 0 := by
      by_contra h
      linarith [(hχ0 _ h).1]
    have h2 : deriv χ (dipoleLift p) = 0 := by
      by_contra h
      linarith [(hdχ0 _ h).1]
    rw [hDdef]
    simp only [h1, h2, zero_mul, sub_zero]
  -- Integrability on the cell.
  have hC : MeasurableSet cellSquare := by
    change MeasurableSet ({p : ℝ × ℝ | |(diagCoord p).1| < Real.pi / 2} ∩
      {p | |(diagCoord p).2| < Real.pi / 2})
    unfold diagCoord
    exact (measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hcpt {g : ℝ → ℝ} (hg : ∀ s, g s ≠ 0 → 2 * a ≤ s ∧ s ≤ 2 * b) : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun s hs ↦ by
      by_contra h
      exact hs (hg s h)
  obtain ⟨C₀, hC₀⟩ := hχ.continuous.bounded_above_of_compact_support (hcpt hχ0)
  obtain ⟨C₁, hC₁⟩ := hdχ.continuous.bounded_above_of_compact_support (hcpt hdχ0)
  have hA : IntegrableOn (fun p ↦ χ (dipoleLift p) * eeBulkDensity ω p) cellSquare := by
    have hJ : IntegrableOn (fun p ↦ χ (dipoleLift p) * eeBulkDensity ω p)
        {p | p ∈ cellSquare ∧ 2 * (a / 2) < dipoleLift p} :=
      (integrableOn_eeBulkDensity ω (show 0 < a / 2 by linarith)).bdd_mul
      (hχ.continuous.comp hΨc).aestronglyMeasurable (Eventually.of_forall fun p ↦ hC₀ _)
    refine hJ.of_forall_sdiff_eq_zero hC fun p hp ↦ ?_
    have hle : dipoleLift p ≤ 2 * (a / 2) := by
      by_contra h
      exact hp.2 ⟨hp.1, by linarith⟩
    have h1 : χ (dipoleLift p) = 0 := by
      by_contra h
      linarith [(hχ0 _ h).1]
    simp [h1]
  have hB : IntegrableOn (fun p ↦ deriv χ (dipoleLift p) * eeBoundaryDensity ω p) cellSquare :=
    (integrableOn_eeBoundaryDensity ω).bdd_mul (hdχ.continuous.comp hΨc).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hC₁ _)
  have hcell := squareIntegral_eq_setIntegral_cellSquare hDp hDm hD0
  rw [hsum, hDdef, integral_sub hA hB] at hcell
  simp only [hχv, hχ']
  linarith

/-- The virial identity on an annulus (`lem:ee-annular-virial`): outside one null set of
    levels, for all `0 < h < h' < 1`, `∫_{2h < Ψ < 2h'} 𝒥 = G(h) - G(h')` with `G` the level
    terms `eeLevelTerm`. By coarea the cutoff identity says that `G` has distributional
    derivative `-2∮𝒥`, and the du Bois-Reymond lemma integrates this. -/
theorem ee_annular_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
      ∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'},
        eeBulkDensity ω p = eeLevelTerm ω h - eeLevelTerm ω h' := by
  have hΨ : Measurable dipoleLift := by unfold dipoleLift; fun_prop
  have hJ (a b : ℝ) (ha : 0 < a) : IntegrableOn (eeBulkDensity ω)
      {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} :=
    (integrableOn_eeBulkDensity ω (half_pos ha)).mono_set
      fun p hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩
  have hE (a b : ℝ) : IntegrableOn (eeBoundaryDensity ω)
      {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b} :=
    (integrableOn_eeBoundaryDensity ω).mono_set fun p hp ↦ hp.1
  -- Test functions: support of the derivative, bounds, and integrals over `[a, b]`.
  have hderiv_supp {φ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∀ s, deriv φ s ≠ 0 → a ≤ s ∧ s ≤ b := by
    intro s hs
    by_contra hns
    apply hs
    have hev : φ =ᶠ[nhds s] fun _ ↦ 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds (show s ∉ Icc a b from hns)] with t ht
      by_contra hne
      exact ht (hsupp t hne)
    rw [hev.deriv_eq, deriv_const]
  have hbound {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∃ C, ∀ s, |g s| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc a b))
    refine ⟨max C 0, fun s ↦ ?_⟩
    by_cases hs : g s = 0
    · simp [hs]
    · have h1 : |g s| ≤ C := by simpa using hC s (hsupp s hs)
      exact h1.trans (le_max_left _ _)
  have hcompl {g F : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∫ s, g s * F s = ∫ s in Icc a b, g s * F s := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_).symm
    have : g s = 0 := by
      by_contra hne
      exact hs (hsupp s hne)
    simp [this]
  -- The cutoff identity in level form: `∫ φ m = ∫ φ' G` with `m = 2∮𝒥` and `G = ∮E`.
  have hid : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ a b, 0 < a → b < 1 →
      (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
      ∫ s, φ s * (2 * levelIntegral s (eeBulkDensity ω)) =
        ∫ s, deriv φ s * levelIntegral s (eeBoundaryDensity ω) := by
    intro φ hφ a b ha hb hsupp
    have hφc : Continuous φ := hφ.continuous
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    obtain ⟨C, hC⟩ := hbound hφc hsupp
    obtain ⟨C', hC'⟩ := hbound hdc (hderiv_supp hsupp)
    have hsupp' : ∀ s, deriv φ s / 2 ≠ 0 → a ≤ s ∧ s ≤ b := fun s hs ↦
      hderiv_supp hsupp s fun h ↦ hs (by simp [h])
    have hC'' : ∀ s, |deriv φ s / 2| ≤ C' / 2 := fun s ↦ by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right (hC' s) (by norm_num)
    have c1 := integral_cellSquare_level_mul hφc.measurable hC ha hb hsupp (hJ a b ha)
    have c2 := integral_cellSquare_level_mul (hdc.measurable.div_const 2) hC'' ha hb hsupp'
      (hE a b)
    have cut := ee_cutoff_identity hlam hω hφ ha hb hsupp
    rw [hcompl hsupp, hcompl (hderiv_supp hsupp)]
    calc ∫ s in Icc a b, φ s * (2 * levelIntegral s (eeBulkDensity ω))
        = 2 * ∫ s in Icc a b, φ s * levelIntegral s (eeBulkDensity ω) := by
          rw [← integral_const_mul]
          congr 1
          funext s
          ring
      _ = ∫ p in cellSquare, φ (dipoleLift p / 2) * eeBulkDensity ω p := c1.symm
      _ = ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * eeBoundaryDensity ω p := cut
      _ = 2 * ∫ s in Icc a b, deriv φ s / 2 * levelIntegral s (eeBoundaryDensity ω) := c2
      _ = ∫ s in Icc a b, deriv φ s * levelIntegral s (eeBoundaryDensity ω) := by
          rw [← integral_const_mul]
          congr 1
          funext s
          ring
  obtain ⟨N₁, hN₁, hdbr⟩ := exists_null_sub_eq_intervalIntegral (α := 0) (β := 1)
    (m := fun h ↦ 2 * levelIntegral h (eeBulkDensity ω))
    (G := fun h ↦ levelIntegral h (eeBoundaryDensity ω))
    (fun a b ha hb ↦ (integrableOn_levelIntegral ha hb (hJ a b ha)).const_mul 2)
    (fun a b ha hb ↦ integrableOn_levelIntegral ha hb (hE a b)) hid
  -- Levels where the boundary integral is not the level term.
  set N₂ : Set ℝ := {h | h ∈ Ioo 0 1 ∧
    levelIntegral h (eeBoundaryDensity ω) ≠ eeLevelTerm ω h}
  have hN₂ : volume N₂ = 0 := by
    have hh := (ae_restrict_iff' measurableSet_Ioo).1 (ae_levelIntegral_eeBoundaryDensity ω)
    simpa only [ae_iff, not_imp] using hh
  refine ⟨N₁ ∪ N₂, measure_union_null hN₁ hN₂, fun h h' h0 hh' h'1 hN hN' ↦ ?_⟩
  have hG (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (htN : t ∉ N₁ ∪ N₂) :
      levelIntegral t (eeBoundaryDensity ω) = eeLevelTerm ω t := by
    by_contra hne
    exact htN (Or.inr ⟨⟨ht0, ht1⟩, hne⟩)
  rw [← hG h h0 (hh'.trans h'1) hN, ← hG h' (h0.trans hh') h'1 hN',
    ← hdbr h h' h0 hh' h'1 (fun H ↦ hN (Or.inl H)) (fun H ↦ hN' (Or.inl H))]
  -- The annulus integral is the coarea formula with `φ = 𝟙_{(h, h')}`.
  set S : Set (ℝ × ℝ) := {p | 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hΨ).inter (measurableSet_lt hΨ measurable_const)
  have hind := integral_cellSquare_level_mul
    (φ := (Ioo h h').indicator fun _ ↦ (1 : ℝ)) (measurable_const.indicator measurableSet_Ioo)
    (C := 1) (fun s ↦ by by_cases hs : s ∈ Ioo h h' <;> simp [hs]) h0 h'1
    (fun s hs ↦ by
      have hm := Set.mem_of_indicator_ne_zero hs
      exact ⟨hm.1.le, hm.2.le⟩) (hJ h h' h0)
  have hpt : ∀ p, (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) (dipoleLift p / 2) *
      eeBulkDensity ω p = S.indicator (eeBulkDensity ω) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem (show dipoleLift p / 2 ∈ Ioo h h' from
        ⟨by linarith [hp.1], by linarith [hp.2]⟩), indicator_of_mem hp, one_mul]
    · rw [indicator_of_notMem (show dipoleLift p / 2 ∉ Ioo h h' from
        fun hm ↦ hp ⟨by linarith [hm.1], by linarith [hm.2]⟩), indicator_of_notMem hp,
        zero_mul]
  have hst : ∀ s, (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) s *
      levelIntegral s (eeBulkDensity ω) = (Ioo h h').indicator
        (fun s ↦ levelIntegral s (eeBulkDensity ω)) s := by
    intro s
    by_cases hs : s ∈ Ioo h h' <;> simp [hs]
  simp_rw [hpt, hst] at hind
  rw [integral_indicator hS, Measure.restrict_restrict hS, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 Ioo_subset_Icc_self] at hind
  have hset : {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'} =
      S ∩ cellSquare := by
    ext p
    simp only [S, mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [hset, hind, intervalIntegral.integral_of_le hh'.le, integral_Ioc_eq_integral_Ioo,
    integral_const_mul]

/-! ### The level terms at the center -/

/-- If `∫₀¹ g < ∞`, then outside every null set there are levels `h_j → 1` with
    `(1 - h_j) g(h_j) → 0`: otherwise `g ≥ c/(1 - h)` near `1`, which is not integrable. -/
theorem exists_seq_one_sub_mul_tendsto_zero {g : ℝ → ℝ≥0∞} (hg : ∫⁻ h in Ioo 0 1, g h ≠ ∞)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Ioo 0 1 ∧ hs j ∉ N) ∧ Tendsto hs atTop (𝓝 1) ∧
      Tendsto (fun j ↦ ENNReal.ofReal (1 - hs j) * g (hs j)) atTop (𝓝 0) := by
  have key : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ h, h ∈ Ioo (1 - δ) 1 ∧ h ∉ N ∧
      ENNReal.ofReal (1 - h) * g h < ENNReal.ofReal δ := by
    intro δ hδ hδ1
    by_contra hcon
    push Not at hcon
    have hae : ∀ᵐ h ∂(volume.restrict (Ioo (1 - δ) 1)),
        ENNReal.ofReal δ * ENNReal.ofReal ((1 - h)⁻¹) ≤ g h := by
      have hNc : ∀ᵐ h ∂(volume.restrict (Ioo (1 - δ) 1)), h ∉ N :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN)
      filter_upwards [hNc, ae_restrict_mem measurableSet_Ioo] with h hhN hh
      have h1 : 0 < 1 - h := by linarith [hh.2]
      rw [ENNReal.ofReal_inv_of_pos h1]
      calc ENNReal.ofReal δ * (ENNReal.ofReal (1 - h))⁻¹
          ≤ ENNReal.ofReal (1 - h) * g h * (ENNReal.ofReal (1 - h))⁻¹ := by
            gcongr
            exact hcon h hh hhN
        _ = g h := by
          rw [mul_comm (ENNReal.ofReal (1 - h)), mul_assoc,
            ENNReal.mul_inv_cancel (by simpa using h1) ENNReal.ofReal_ne_top, mul_one]
    -- `1/(1 - h)` is not integrable near `1`.
    have hinf : ∫⁻ h in Ioo (1 - δ) 1, ENNReal.ofReal ((1 - h)⁻¹) = ∞ := by
      by_contra hfin
      have hint : IntegrableOn (fun h : ℝ ↦ (1 - h)⁻¹) (Ioo (1 - δ) 1) := by
        refine ⟨(by fun_prop : Measurable fun h : ℝ ↦ (1 - h)⁻¹).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal]
        · exact lt_top_iff_ne_top.2 hfin
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
          exact inv_nonneg.2 (by linarith [hh.2])
      have hii : IntervalIntegrable (fun x : ℝ ↦ (x - 1)⁻¹) volume (1 - δ) 1 := by
        rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
        refine hint.neg.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
        simp only [Pi.neg_apply, ← inv_neg, neg_sub]
      rcases intervalIntegrable_sub_inv_iff.1 hii with h | h
      · linarith
      · exact h (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, le_rfl⟩)
    have hle := lintegral_mono_ae hae
    rw [lintegral_const_mul _ (by fun_prop), hinf,
      ENNReal.mul_top (by simpa using hδ)] at hle
    exact hg (top_le_iff.1 (hle.trans (lintegral_mono_set (Ioo_subset_Ioo_left (by linarith)))))
  choose hs hmem hNs hlt using fun j : ℕ ↦
    key (1 / ((j : ℝ) + 2)) (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  have hδ : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun j ↦ by positivity) (fun j ↦ ?_) this
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hδ1 (j : ℕ) : 1 / ((j : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨hs, fun j ↦ ⟨⟨by linarith [(hmem j).1, hδ1 j], (hmem j).2⟩, hNs j⟩, ?_, ?_⟩
  · have hlow : Tendsto (fun j : ℕ ↦ 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hδ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun j ↦ (hmem j).1.le) (fun j ↦ (hmem j).2.le)
  · have hup : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 / ((j : ℝ) + 2))) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hδ
      rwa [ENNReal.ofReal_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun j ↦ zero_le) (fun j ↦ (hlt j).le)

/-- The level term near the center (`lem:ee-center-limit`): with
    `g = ∮ (|ψ|² + |ψₓ|² + |ψ_y|² + |ω|²) dt` and `|ψ| ≤ M` along the level `{Ψ = 2h}`,
    `|G(h)| ≤ M (128 (1 - h) g)^{1/2} + 10 (1 - h) g`. The first term uses Cauchy–Schwarz,
    `ρ² ≤ 2(2 - Ψ) = 4(1 - h)` and `S(h) = 8L(h) ≤ 8/h`. -/
theorem abs_eeLevelTerm_le (ω : L2) {M h : ℝ} (hM0 : 0 ≤ M) (hh : 1 / 2 < h) (h1 : h < 1)
    (hF : IntegrableOn (fun t ↦ ‖streamLift ω (dipoleOrbit h t)‖ ^ 2 +
      ‖streamLiftX ω (dipoleOrbit h t)‖ ^ 2 + ‖streamLiftY ω (dipoleOrbit h t)‖ ^ 2 +
      ‖liftL2 ω (dipoleOrbit h t)‖ ^ 2) (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) :
    |eeLevelTerm ω h| ≤
      M * √(128 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖streamLift ω (dipoleOrbit h t)‖ ^ 2 + ‖streamLiftX ω (dipoleOrbit h t)‖ ^ 2 +
          ‖streamLiftY ω (dipoleOrbit h t)‖ ^ 2 + ‖liftL2 ω (dipoleOrbit h t)‖ ^ 2))) +
      10 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖streamLift ω (dipoleOrbit h t)‖ ^ 2 + ‖streamLiftX ω (dipoleOrbit h t)‖ ^ 2 +
          ‖streamLiftY ω (dipoleOrbit h t)‖ ^ 2 + ‖liftL2 ω (dipoleOrbit h t)‖ ^ 2)) := by
  have h0 : 0 < h := by linarith
  have hL := eighthPeriod_pos h0 h1
  have hL2 : eighthPeriod h ≤ 2 :=
    (eighthPeriod_le_inv h0 h1).trans (by rw [div_le_iff₀ h0]; linarith)
  set I := Ico (-2 * eighthPeriod h) (6 * eighthPeriod h) with hI
  set γ : ℝ → ℝ × ℝ := fun t ↦ dipoleOrbit h t with hγ
  have hγm : Measurable γ :=
    (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have hmeas (g : L2) : Measurable (fun t ↦ liftL2 g (γ t)) :=
    ((Lp.stronglyMeasurable g).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable).comp hγm
  have hs := hmeas (invLap ω)
  have hx := hmeas (streamPartial 0 ω)
  have hy := hmeas (streamPartial 1 ω)
  have hw := hmeas ω
  set F : ℝ → ℝ := fun t ↦ ‖streamLift ω (γ t)‖ ^ 2 + ‖streamLiftX ω (γ t)‖ ^ 2 +
    ‖streamLiftY ω (γ t)‖ ^ 2 + ‖liftL2 ω (γ t)‖ ^ 2 with hFdef
  -- Pointwise bounds along the level.
  have hρ2 (t : ℝ) : gradNorm (γ t) ^ 2 ≤ 4 * (1 - h) := by
    have hΨ := dipoleLift_dipoleOrbit h0 h1 t
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    simp only [dipoleLift] at hΨ
    nlinarith [Real.sin_sq_add_cos_sq (γ t).1, Real.sin_sq_add_cos_sq (γ t).2,
      sq_nonneg (1 - Real.cos (γ t).1), sq_nonneg (1 - Real.cos (γ t).2)]
  have hρ0 (t : ℝ) : 0 ≤ gradNorm (γ t) := Real.sqrt_nonneg _
  have hρle (t : ℝ) : gradNorm (γ t) ≤ 2 := by nlinarith [hρ2 t, hρ0 t]
  have hn (t : ℝ) : ‖streamNormal ω (γ t)‖ ^ 2 ≤ 2 * F t := by
    have := norm_normalDeriv_le (streamLiftX ω) (streamLiftY ω) (γ t)
    have h0' := norm_nonneg (streamNormal ω (γ t))
    simp only [hFdef]
    nlinarith [sq_nonneg (‖streamLiftX ω (γ t)‖ - ‖streamLiftY ω (γ t)‖),
      norm_nonneg (streamLiftX ω (γ t)), norm_nonneg (streamLiftY ω (γ t)),
      sq_nonneg ‖streamLift ω (γ t)‖, sq_nonneg ‖liftL2 ω (γ t)‖]
  have htg (t : ℝ) : ‖streamTangent ω (γ t)‖ ^ 2 ≤ 2 * F t := by
    have := norm_tangentDeriv_le (streamLiftX ω) (streamLiftY ω) (γ t)
    have h0' := norm_nonneg (streamTangent ω (γ t))
    simp only [hFdef]
    nlinarith [sq_nonneg (‖streamLiftX ω (γ t)‖ - ‖streamLiftY ω (γ t)‖),
      norm_nonneg (streamLiftX ω (γ t)), norm_nonneg (streamLiftY ω (γ t)),
      sq_nonneg ‖streamLift ω (γ t)‖, sq_nonneg ‖liftL2 ω (γ t)‖]
  have hre (u v : ℂ) : |(u * (starRingEnd ℂ) v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hws (t : ℝ) : |(liftL2 ω (γ t) * (starRingEnd ℂ) (streamLift ω (γ t))).re| ≤ F t := by
    refine (hre _ _).trans ?_
    simp only [hFdef]
    nlinarith [sq_nonneg (‖liftL2 ω (γ t)‖ - ‖streamLift ω (γ t)‖),
      sq_nonneg ‖streamLiftX ω (γ t)‖, sq_nonneg ‖streamLiftY ω (γ t)‖]
  have hA (t : ℝ) : |gradNorm (γ t) * (streamLift ω (γ t) *
      (starRingEnd ℂ) (streamNormal ω (γ t))).re| ≤ 3 * F t := by
    rw [abs_mul, abs_of_nonneg (hρ0 t)]
    have h1' := hre (streamLift ω (γ t)) (streamNormal ω (γ t))
    have h2' := hn t
    have h3' : ‖streamLift ω (γ t)‖ ^ 2 ≤ F t := by
      simp only [hFdef]
      nlinarith [sq_nonneg ‖streamLiftX ω (γ t)‖, sq_nonneg ‖streamLiftY ω (γ t)‖,
        sq_nonneg ‖liftL2 ω (γ t)‖]
    nlinarith [mul_le_mul (hρle t) h1' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      sq_nonneg (‖streamLift ω (γ t)‖ - ‖streamNormal ω (γ t)‖)]
  -- Measurability along the level.
  have hρm : Measurable (fun t ↦ gradNorm (γ t)) := by
    simp only [gradNorm]
    fun_prop
  have hnm : Measurable (fun t ↦ streamNormal ω (γ t)) := by
    simp only [streamNormal, normalDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have htm : Measurable (fun t ↦ streamTangent ω (γ t)) := by
    simp only [streamTangent, tangentDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have hsm : Measurable (fun t ↦ streamLift ω (γ t)) := hs
  -- Integrability along the level.
  have iF : Integrable F (volume.restrict I) := hF
  have iN : Integrable (fun t ↦ ‖streamNormal ω (γ t)‖ ^ 2) (volume.restrict I) :=
    (iF.const_mul 2).mono' (hnm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (by positivity)]; exact hn t)
  have iT : Integrable (fun t ↦ ‖streamTangent ω (γ t)‖ ^ 2) (volume.restrict I) :=
    (iF.const_mul 2).mono' (htm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (by positivity)]; exact htg t)
  have iW : Integrable (fun t ↦ (liftL2 ω (γ t) * (starRingEnd ℂ) (streamLift ω (γ t))).re)
      (volume.restrict I) :=
    iF.mono' (by fun_prop) (Eventually.of_forall fun t ↦ hws t)
  have iA : Integrable (fun t ↦ gradNorm (γ t) * (streamLift ω (γ t) *
      (starRingEnd ℂ) (streamNormal ω (γ t))).re) (volume.restrict I) :=
    (iF.const_mul 3).mono' (by fun_prop) (Eventually.of_forall fun t ↦ hA t)
  have iρ : Integrable (fun t ↦ gradNorm (γ t) ^ 2) (volume.restrict I) :=
    (integrable_const (4 * (1 - h))).mono' (hρm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (by positivity)]; exact hρ2 t)
  have iρn : Integrable (fun t ↦ gradNorm (γ t) * ‖streamNormal ω (γ t)‖)
      (volume.restrict I) :=
    (iρ.add iN).mono' (hρm.mul hnm.norm).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
      rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (norm_nonneg _)), Pi.add_apply]
      nlinarith [sq_nonneg (gradNorm (γ t) - ‖streamNormal ω (γ t)‖)])
  -- The level term as integrals over `[-2L, 6L)`.
  have hG : eeLevelTerm ω h =
      (∫ t in I, gradNorm (γ t) * (streamLift ω (γ t) *
        (starRingEnd ℂ) (streamNormal ω (γ t))).re) +
      (2 - 2 * h) * ((∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2) -
        (∫ t in I, ‖streamTangent ω (γ t)‖ ^ 2) -
        ∫ t in I, (liftL2 ω (γ t) * (starRingEnd ℂ) (streamLift ω (γ t))).re) := by
    simp only [eeLevelTerm, levelIntegral_eq_setIntegral h0 h1, hI, hγ]
  set g := ∫ t in I, F t with hg
  have hg0 : 0 ≤ g := integral_nonneg fun t ↦ by positivity
  -- The three terms with the factor `2 - 2h`.
  have hB : |∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2| ≤ 2 * g := by
    rw [abs_of_nonneg (integral_nonneg fun t ↦ by positivity), ← integral_const_mul]
    exact integral_mono iN (iF.const_mul 2) hn
  have hC : |∫ t in I, ‖streamTangent ω (γ t)‖ ^ 2| ≤ 2 * g := by
    rw [abs_of_nonneg (integral_nonneg fun t ↦ by positivity), ← integral_const_mul]
    exact integral_mono iT (iF.const_mul 2) htg
  have hD : |∫ t in I, (liftL2 ω (γ t) * (starRingEnd ℂ) (streamLift ω (γ t))).re| ≤ g :=
    (abs_integral_le_integral_abs).trans (integral_mono iW.abs iF hws)
  -- The arclength term, by Cauchy–Schwarz.
  have hρI : ∫ t in I, gradNorm (γ t) ^ 2 ≤ 64 * (1 - h) := by
    calc ∫ t in I, gradNorm (γ t) ^ 2 ≤ ∫ t in I, 4 * (1 - h) :=
          integral_mono iρ (integrable_const _) hρ2
      _ = 8 * eighthPeriod h * (4 * (1 - h)) := by
          rw [setIntegral_const, hI, Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]
          ring
      _ ≤ 64 * (1 - h) := by nlinarith
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict I)
    Real.HolderConjugate.two_two (Eventually.of_forall fun t ↦ hρ0 t)
    (Eventually.of_forall fun t ↦ norm_nonneg (streamNormal ω (γ t)))
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hρm.aestronglyMeasurable).2 iρ)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hnm.norm.aestronglyMeasurable).2 iN)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hA' : |∫ t in I, gradNorm (γ t) * (streamLift ω (γ t) *
      (starRingEnd ℂ) (streamNormal ω (γ t))).re| ≤ M * √(128 * ((1 - h) * g)) := by
    calc _ ≤ ∫ t in I, |gradNorm (γ t) * (streamLift ω (γ t) *
          (starRingEnd ℂ) (streamNormal ω (γ t))).re| := abs_integral_le_integral_abs
      _ ≤ ∫ t in I, M * (gradNorm (γ t) * ‖streamNormal ω (γ t)‖) := by
          refine integral_mono_ae iA.abs (iρn.const_mul M) ?_
          filter_upwards [hM] with t ht
          rw [abs_mul, abs_of_nonneg (hρ0 t)]
          calc gradNorm (γ t) * |(streamLift ω (γ t) *
                (starRingEnd ℂ) (streamNormal ω (γ t))).re|
              ≤ gradNorm (γ t) * (‖streamLift ω (γ t)‖ * ‖streamNormal ω (γ t)‖) :=
                mul_le_mul_of_nonneg_left (hre _ _) (hρ0 t)
            _ ≤ gradNorm (γ t) * (M * ‖streamNormal ω (γ t)‖) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (hρ0 t)
            _ = M * (gradNorm (γ t) * ‖streamNormal ω (γ t)‖) := by ring
      _ = M * ∫ t in I, gradNorm (γ t) * ‖streamNormal ω (γ t)‖ := integral_const_mul _ _
      _ ≤ M * (√(∫ t in I, gradNorm (γ t) ^ 2) * √(∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2)) := by
          gcongr
      _ ≤ M * (√(64 * (1 - h)) * √(2 * g)) := by
          gcongr
          exact (le_abs_self _).trans hB
      _ = M * √(128 * ((1 - h) * g)) := by
          rw [← Real.sqrt_mul (by linarith)]
          congr 2
          ring
  rw [hG]
  calc _ ≤ |∫ t in I, gradNorm (γ t) * (streamLift ω (γ t) *
        (starRingEnd ℂ) (streamNormal ω (γ t))).re| +
      (2 - 2 * h) * (|∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2| +
        |∫ t in I, ‖streamTangent ω (γ t)‖ ^ 2| +
        |∫ t in I, (liftL2 ω (γ t) * (starRingEnd ℂ) (streamLift ω (γ t))).re|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - 2 * h)]
        exact mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) (by linarith)
    _ ≤ M * √(128 * ((1 - h) * g)) + (2 - 2 * h) * (2 * g + 2 * g + g) := by
        gcongr
        · linarith
    _ = M * √(128 * ((1 - h) * g)) + 10 * ((1 - h) * g) := by ring

/-- The level terms vanish at the center along a sequence (`lem:ee-center-limit`): for every
    null set `N` there are levels `h_j → 1` outside `N` with `G(h_j) → 0`. Both terms of `G`
    are bounded by `(1 - h)g(h)` or `((1 - h)g(h))^{1/2}` (`abs_eeLevelTerm_le`), and
    `∫ g < ∞` by coarea. Only `ω ∈ L²`, `ψ ∈ H²` and the coarea formula are used. -/
theorem ee_center_limit (ω : L2) {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Ioo 0 1 ∧ hs j ∉ N) ∧ Tendsto hs atTop (𝓝 1) ∧
      Tendsto (fun j ↦ eeLevelTerm ω (hs j)) atTop (𝓝 0) := by
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  -- `F = |ψ|² + |ψₓ|² + |ψ_y|² + |ω|²` is integrable on the cell.
  obtain ⟨F, hF⟩ : ∃ F : ℝ × ℝ → ℝ, F = fun p ↦ ‖streamLift ω p‖ ^ 2 +
      ‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 + ‖liftL2 ω p‖ ^ 2 := ⟨_, rfl⟩
  have hFm : Measurable F := by
    have h0 := hmeas (invLap ω)
    have h1 := hmeas ω
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    rw [hF]
    simp only [streamLift, streamLiftX, streamLiftY]
    fun_prop
  have hAs : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  have hFi : IntegrableOn F cellSquare := by
    rw [hF]
    exact (((hsq _).add (hsq _)).add (hsq _)).add (hsq _)
  -- `∫₀¹ g < ∞` for `g(h) = ∮ F dt`, by the coarea formula.
  have hg : ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      ENNReal.ofReal (F (dipoleOrbit h t)) ≠ ∞ := by
    intro htop
    have hc := lintegral_cellSquare_eq (ENNReal.measurable_ofReal.comp hFm)
    have hlt := hFi.lintegral_lt_top
    simp only [Function.comp_apply] at hc
    rw [hc, htop, ENNReal.mul_top (by norm_num)] at hlt
    exact lt_irrefl _ hlt
  -- `|ψ| ≤ M` almost everywhere, hence along almost every level.
  set M := ‖continuousRep (invLap ω)‖
  have hM : ∀ᵐ p ∂(volume.restrict cellSquare), ‖streamLift ω p‖ ≤ M := by
    refine ae_restrict_of_ae ?_
    filter_upwards [streamLift_ae_eq_contStream ω] with p hp
    rw [hp, contStream]
    exact (continuousRep (invLap ω)).norm_coe_le_norm _
  have hMlev := ae_level_of_ae_cellSquare (P := fun p ↦ ‖streamLift ω p‖ ≤ M)
    (measurableSet_le (hmeas (invLap ω)).norm measurable_const) hM
  -- The bound on almost every level close to the center.
  have hgood : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), 1 / 2 < h → h < 1 →
      |eeLevelTerm ω h| ≤ M * √(128 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h)
        (6 * eighthPeriod h), ENNReal.ofReal (F (dipoleOrbit h t))).toReal)) +
      10 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        ENNReal.ofReal (F (dipoleOrbit h t))).toReal) := by
    filter_upwards [hMlev, (integral_cellSquare_eq hFi).1] with h hMh hFh hh h1
    have hFh' := hFh
    rw [hF] at hFh'
    have hb := abs_eeLevelTerm_le ω (norm_nonneg _) hh h1 hFh' hMh
    have hint : ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), F (dipoleOrbit h t) =
        (∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
          ENNReal.ofReal (F (dipoleOrbit h t))).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t ↦ by
        simp only [hF]; positivity) hFh.aestronglyMeasurable
    rw [← hint]
    simp only [hF]
    exact hb
  -- Choose the levels outside `N` and outside the exceptional set of `hgood`.
  rw [ae_restrict_iff' measurableSet_Ioo] at hgood
  obtain ⟨hs, hmem, hlim, hprod⟩ := exists_seq_one_sub_mul_tendsto_zero hg
    (N := N ∪ {h | ¬(h ∈ Ioo 0 1 → 1 / 2 < h → h < 1 → _)})
    (measure_union_null hN (ae_iff.1 hgood))
  refine ⟨hs, fun j ↦ ⟨(hmem j).1, fun h ↦ (hmem j).2 (Or.inl h)⟩, hlim, ?_⟩
  -- `(1 - h_j) g(h_j) → 0` and the bound give `G(h_j) → 0`.
  have hpr : Tendsto (fun j ↦ (1 - hs j) * (∫⁻ t in Ico (-2 * eighthPeriod (hs j))
      (6 * eighthPeriod (hs j)), ENNReal.ofReal (F (dipoleOrbit (hs j) t))).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod
    simp only [ENNReal.toReal_zero] at this
    refine this.congr fun j ↦ ?_
    have h1 : (0 : ℝ) ≤ 1 - hs j := by linarith [(hmem j).1.2]
    simp only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1]
  have hup : Tendsto (fun j ↦ M * √(128 * ((1 - hs j) * (∫⁻ t in Ico (-2 * eighthPeriod (hs j))
      (6 * eighthPeriod (hs j)), ENNReal.ofReal (F (dipoleOrbit (hs j) t))).toReal)) +
      10 * ((1 - hs j) * (∫⁻ t in Ico (-2 * eighthPeriod (hs j))
      (6 * eighthPeriod (hs j)), ENNReal.ofReal (F (dipoleOrbit (hs j) t))).toReal))
      atTop (𝓝 0) := by
    have := ((hpr.const_mul 128).sqrt.const_mul M).add (hpr.const_mul 10)
    simpa using this
  have hev : ∀ᶠ j in atTop, 1 / 2 < hs j :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  refine squeeze_zero_norm' ?_ hup
  filter_upwards [hev] with j hj
  have hgj := (hmem j).2
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hgj
  exact hgj.2 (hmem j).1 hj (hmem j).1.2

/-- The truncated virial identity (`lem:ee-truncated-virial`), using `ε = 2h` so its null
    set can be combined with the boundary limits. Integrability of the bulk is explicit;
    the boundary integral is written as a difference of the three level integrals. -/
theorem ee_truncated_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 1)),
      IntegrableOn (eeBulkDensity ω) {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p} ∧
      ∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p}, eeBulkDensity ω p =
        levelIntegral h (fun p ↦
            gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) +
          (2 - 2 * h) * (levelIntegral h (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
            levelIntegral h (fun p ↦ ‖streamTangent ω p‖ ^ 2) -
            levelIntegral h (fun p ↦
              (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) := by
  obtain ⟨N, hN, hann⟩ := ee_annular_virial hlam hω
  -- `Ψ = 2` only where `cos x = cos y = 1`, a null set.
  have hlt2 : ∀ᵐ p : ℝ × ℝ, dipoleLift p < 2 := by
    filter_upwards [ae_cos_fst_ne_cos_snd] with p hp
    by_contra hge
    have h1 := Real.cos_le_one p.1
    have h2 := Real.cos_le_one p.2
    exact hp (by unfold dipoleLift at hge; linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN)] with h hh hhN
  have hint := integrableOn_eeBulkDensity ω hh.1
  refine ⟨hint, ?_⟩
  obtain ⟨hs, hsN, hs1, hG⟩ := ee_center_limit ω hN
  set A : Set (ℝ × ℝ) := {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p}
  have hB (c : ℝ) : MeasurableSet {p : ℝ × ℝ | dipoleLift p < c} :=
    measurableSet_lt (by unfold dipoleLift; fun_prop) measurable_const
  have hset (j : ℕ) : {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * hs j} =
      A ∩ {p | dipoleLift p < 2 * hs j} := by
    ext p
    simp only [A, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  have hev : ∀ᶠ j in atTop, h < hs j := hs1.eventually (lt_mem_nhds hh.2)
  have hlim1 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < 2 * hs j}, eeBulkDensity ω p)
      atTop (𝓝 (eeLevelTerm ω h)) := by
    have hd := (tendsto_const_nhds (x := eeLevelTerm ω h)).sub hG
    rw [sub_zero] at hd
    apply hd.congr'
    filter_upwards [hev] with j hj
    rw [← hset]
    exact (hann h (hs j) hh.1 hj (hsN j).1.2 hhN (hsN j).2).symm
  have hlim2 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < 2 * hs j}, eeBulkDensity ω p)
      atTop (𝓝 (∫ p in A, eeBulkDensity ω p)) := by
    have hind (j : ℕ) : ∫ p in A ∩ {p | dipoleLift p < 2 * hs j}, eeBulkDensity ω p =
        ∫ p in A, {p | dipoleLift p < 2 * hs j}.indicator (eeBulkDensity ω) p := by
      rw [Set.inter_comm A, ← Measure.restrict_restrict (hB _), integral_indicator (hB _)]
    simp_rw [hind]
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖eeBulkDensity ω p‖)
    · exact fun j ↦ hint.aestronglyMeasurable.indicator (hB _)
    · exact hint.norm
    · intro j
      filter_upwards with p
      by_cases hp : p ∈ {p : ℝ × ℝ | dipoleLift p < 2 * hs j}
      · simp [Set.indicator_of_mem hp]
      · simp [Set.indicator_of_notMem hp]
    · filter_upwards [ae_restrict_of_ae hlt2] with p hp
      apply tendsto_const_nhds.congr'
      have h2 : Tendsto (fun j ↦ 2 * hs j) atTop (𝓝 2) := by
        simpa using hs1.const_mul 2
      filter_upwards [h2.eventually (lt_mem_nhds hp)] with j hj
      exact (Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | dipoleLift p < 2 * hs j} from hj) _).symm
  exact tendsto_nhds_unique hlim2 hlim1

/-! ### Gradient traces at the separatrix -/

/-- The energy of the arc traces (`lem:ee-arc-energy`): for `ψ` even under both reflections,
    `∫ cosh² s |g_k'(s)|² ds < ∞` on each arc, with `g_k = ψ̃ ∘ γ_k`. Away from the saddles
    this is the line trace of `∇ψ ∈ H¹` (`lem:traces`); near a saddle `ds ≈ du/u` in the corner
    chart and the odd Hardy inequality bounds `∫ |ψ_u(u, 0)|² du/u`, since `ψ_u(·, 0)` is odd. -/
theorem ee_arc_energy {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω) :
    ∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2 := by
  sorry

/-- The hyperbola estimate (`lem:hyperbola-estimate`): if `v ↦ F(u, v)` is absolutely
    continuous on `[0, u₀]` with derivative `F_v` for almost every `u`, then on the
    half-hyperbola `v = h/u`, `√h ≤ u ≤ u₀`,
    `∫ |F(u, h/u) - F(u, 0)|² du/u ≤ ∫_{(0,u₀)²} |F_v|²`. Each vertical segment has length
    `h/u`, and Cauchy–Schwarz gives the factor `h/u² ≤ 1`. -/
theorem lintegral_hyperbola_le {F Fv : ℝ × ℝ → ℂ} (hFv : Measurable Fv) {u₀ h : ℝ}
    (hh : 0 < h) (hu : √h ≤ u₀)
    (hF : ∀ᵐ u ∂(volume.restrict (Ioo 0 u₀)),
      AbsolutelyContinuousOnInterval (fun v ↦ F (u, v)) 0 u₀ ∧
        ∀ᵐ v ∂(volume.restrict (Ioo 0 u₀)), HasDerivAt (fun v ↦ F (u, v)) (Fv (u, v)) v) :
    ∫⁻ u in Ioo (√h) u₀, ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u) ≤
      ∫⁻ p in Ioo 0 u₀ ×ˢ Ioo 0 u₀, ENNReal.ofReal (‖Fv p‖ ^ 2) := by
  have hsq : 0 < √h := Real.sqrt_pos.2 hh
  have hsub : Ioo (√h) u₀ ⊆ Ioo 0 u₀ := Ioo_subset_Ioo_left hsq.le
  -- The pointwise bound on almost every vertical segment.
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioo (√h) u₀)),
      ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u) ≤
        ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hF,
      ae_restrict_mem measurableSet_Ioo] with u hFu hum
    obtain ⟨hac, hder⟩ := hFu
    have hu0 : 0 < u := hsq.trans hum.1
    set c := h / u with hc_def
    have hc0 : 0 < c := div_pos hh hu0
    have hsh : √h * √h = h := Real.mul_self_sqrt hh.le
    have hcs : c ≤ √h := by
      rw [hc_def, div_le_iff₀ hu0]
      nlinarith [hum.1]
    have hcu : c ≤ u₀ := hcs.trans hu
    have hcu1 : c / u ≤ 1 := by
      rw [div_le_one hu0]
      exact hcs.trans hum.1.le
    have hmono : ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) ≤
        ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
      lintegral_mono_set (Ioo_subset_Ioo_right hcu)
    by_cases hfin : ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) = ⊤
    · rw [hfin, top_le_iff] at hmono
      rw [hmono]
      exact le_top
    have hmeas : Measurable fun v ↦ Fv (u, v) := hFv.comp (measurable_const.prodMk measurable_id)
    have hint2 : Integrable (fun v ↦ ‖Fv (u, v)‖ ^ 2) (volume.restrict (Ioo 0 c)) := by
      refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ by positivity)]
      exact lt_top_iff_ne_top.2 hfin
    have hL2 : MemLp (fun v ↦ Fv (u, v)) 2 (volume.restrict (Ioo 0 c)) :=
      (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 hint2
    have hL1 : IntegrableOn (fun v ↦ Fv (u, v)) (Ioo 0 c) := hL2.integrable (by norm_num)
    have hII : IntervalIntegrable (fun v ↦ Fv (u, v)) volume 0 c :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hc0.le).2 hL1
    -- The fundamental theorem of calculus on `[0, c]`.
    have hFTC : (∫ v in (0 : ℝ)..c, Fv (u, v)) = F (u, c) - F (u, 0) := by
      refine complex_integral_eq_sub_of_ac (hac.mono ?_) hII ?_
      · rw [uIcc_of_le hc0.le, uIcc_of_le (hc0.le.trans hcu)]
        exact Icc_subset_Icc le_rfl hcu
      · have h0 : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
        have h1 : ∀ᵐ v : ℝ, v ≠ u₀ := by simp [ae_iff, measure_singleton]
        filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hder, h0, h1] with v hv hv0 hv1 hvc
        rw [uIcc_of_le hc0.le] at hvc
        exact hv ⟨lt_of_le_of_ne hvc.1 (Ne.symm hv0),
          lt_of_le_of_ne (hvc.2.trans hcu) hv1⟩
    -- Cauchy–Schwarz on the segment.
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioo 0 c))
      Real.HolderConjugate.two_two (f := fun _ ↦ (1 : ℝ)) (g := fun v ↦ ‖Fv (u, v)‖)
      (Eventually.of_forall fun _ ↦ zero_le_one)
      (Eventually.of_forall fun v ↦ norm_nonneg _)
      (by rw [ENNReal.ofReal_ofNat]; exact memLp_const 1)
      (by rw [ENNReal.ofReal_ofNat]
          exact (memLp_two_iff_integrable_sq hmeas.norm.aestronglyMeasurable).2 hint2)
    have hvol : (volume.restrict (Ioo 0 c)).real univ = c := by
      simp [Measure.real, Real.volume_Ioo, hc0.le]
    simp only [one_mul, Real.rpow_two, ← Real.sqrt_eq_rpow, integral_const,
      hvol, one_pow, smul_eq_mul, mul_one] at hCS
    have hnorm : ‖F (u, c) - F (u, 0)‖ ≤ √c * √(∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) := by
      rw [← hFTC, intervalIntegral.integral_of_le hc0.le, integral_Ioc_eq_integral_Ioo]
      exact (norm_integral_le_integral_norm _).trans hCS
    have hI0 : 0 ≤ ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := integral_nonneg fun v ↦ by positivity
    have hsq' : ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
      calc ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ (√c * √(∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hI0]
    have hdiv : ‖F (u, c) - F (u, 0)‖ ^ 2 / u ≤ ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := by
      rw [div_le_iff₀ hu0]
      calc ‖F (u, c) - F (u, 0)‖ ^ 2 ≤ c * ∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2 := hsq'
        _ = (c / u) * (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) * u := by field_simp
        _ ≤ 1 * (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) * u := by gcongr
        _ = _ := by ring
    calc ENNReal.ofReal (‖F (u, c) - F (u, 0)‖ ^ 2 / u)
        ≤ ENNReal.ofReal (∫ v in Ioo 0 c, ‖Fv (u, v)‖ ^ 2) := ENNReal.ofReal_le_ofReal hdiv
      _ = ∫⁻ v in Ioo 0 c, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun v ↦ by positivity)
      _ ≤ _ := hmono
  have hFm : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (‖Fv p‖ ^ 2) := by fun_prop
  calc ∫⁻ u in Ioo (√h) u₀, ENNReal.ofReal (‖F (u, h / u) - F (u, 0)‖ ^ 2 / u)
      ≤ ∫⁻ u in Ioo (√h) u₀, ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
        lintegral_mono_ae hpt
    _ ≤ ∫⁻ u in Ioo 0 u₀, ∫⁻ v in Ioo 0 u₀, ENNReal.ofReal (‖Fv (u, v)‖ ^ 2) :=
        lintegral_mono_set hsub
    _ = ∫⁻ p in Ioo 0 u₀ ×ˢ Ioo 0 u₀, ENNReal.ofReal (‖Fv p‖ ^ 2) := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hFm.aemeasurable]

/-- Level traces at the separatrix (`lem:ee-level-traces`): for `ψ` even under both
    reflections, along levels `h → 0` outside a null set, `∮ |ψₙ|² dt → 0` and
    `∮ |ψₜ|² dt → ∑_k ∫ ½ cosh² s |g_k'(s)|² ds`. Away from the saddles the restrictions
    converge by the line traces of `lem:traces`, and the normal trace on the arcs vanishes
    because `ψₙ` is odd under the reflection across each arc (`lem:ee-neumann`); near the
    saddles the tails are uniformly small by the hyperbola estimate and the axis tail. On an
    arc `|ψₜ|² = ½ cosh² s |g'|²`. -/
theorem ee_level_traces {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamTangent ω p‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∑ k ∈ Finset.range 4,
          ∫ s, Real.cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2)) := by
  sorry

/-- `ρ²` is invariant under the quarter rotation, so its level integral is four quarter
    integrals: `∮ ρ² dt = 4 ∫_{-L}^{L} ρ²(γ_h(t)) dt`. -/
theorem levelIntegral_gradNorm_sq {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    levelIntegral h (fun p ↦ gradNorm p ^ 2) =
      4 * ∫ t in (-eighthPeriod h)..eighthPeriod h, gradNorm (dipoleOrbit h t) ^ 2 := by
  set f : ℝ → ℝ := fun t ↦ gradNorm (dipoleOrbit h t) ^ 2 with hf
  have hγ : Continuous fun t ↦ dipoleOrbit h t :=
    Continuous.comp (g := fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) continuous_dipoleOrbit
      (f := fun t : ℝ ↦ (h, t)) (by fun_prop)
  have hfc : Continuous f := by
    simp only [hf, gradNorm]
    fun_prop
  have hper : Function.Periodic f (2 * eighthPeriod h) := fun t ↦ by
    simp only [hf, dipoleOrbit_add_quarter h0 h1, gradNorm, Real.sin_neg, neg_sq, add_comm]
  have h4 := hper.intervalIntegral_add_zsmul_eq 4 0 fun t₁ t₂ ↦ hfc.intervalIntegrable t₁ t₂
  have hshift := hper.intervalIntegral_add_eq 0 (-eighthPeriod h)
  rw [levelIntegral, orbitPeriod]
  change ∫ t in (0 : ℝ)..8 * eighthPeriod h, f t =
    4 * ∫ t in (-eighthPeriod h)..eighthPeriod h, f t
  rw [show 8 * eighthPeriod h = 0 + (4 : ℤ) • (2 * eighthPeriod h) by simp; ring, h4,
    zsmul_eq_mul, hshift, show -eighthPeriod h + 2 * eighthPeriod h = eighthPeriod h by ring]
  push_cast
  ring

/-- `∮ ρ² dt` stays bounded as the levels approach the separatrix, although the period
    `S(h) → ∞`: `ρ ≤ C d` and `∫ d² dt ≤ C` on the quarter orbit. -/
theorem levelIntegral_gradNorm_sq_le : ∃ K h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioo 0 h₀, h < 1 →
    levelIntegral h (fun p ↦ gradNorm p ^ 2) ≤ K := by
  obtain ⟨Cρ, hCρ⟩ := gradNorm_le_saddleDist
  obtain ⟨Cd, h₀, hh₀, hCd⟩ := integral_saddleDist_rpow_pos_le (p := 2) two_pos
  refine ⟨4 * (4 * Cρ ^ 2 * Cd), h₀, hh₀, fun h hh h1 ↦ ?_⟩
  have h0 := hh.1
  have hL := (eighthPeriod_pos h0 h1).le
  have hγ : Continuous fun t ↦ dipoleOrbit h t :=
    Continuous.comp (g := fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) continuous_dipoleOrbit
      (f := fun t : ℝ ↦ (h, t)) (by fun_prop)
  rw [levelIntegral_gradNorm_sq h0 h1]
  gcongr
  have hd := hCd h hh
  simp only [Real.rpow_two] at hd
  calc ∫ t in (-eighthPeriod h)..eighthPeriod h, gradNorm (dipoleOrbit h t) ^ 2
      ≤ ∫ t in (-eighthPeriod h)..eighthPeriod h,
          4 * Cρ ^ 2 * saddleDist (dipoleOrbit h t) ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((by simp only [gradNorm]; fun_prop : Continuous fun t ↦
            gradNorm (dipoleOrbit h t) ^ 2).intervalIntegrable _ _)
          ((continuous_const.mul ((Metric.continuous_infDist_pt _).comp hγ |>.pow 2)
            ).intervalIntegrable _ _) fun t _ ↦ ?_
        have hc := hCρ _ (dipoleOrbit_mem_cellSquare h0 h1 t)
        have hg0 : 0 ≤ gradNorm (dipoleOrbit h t) := Real.sqrt_nonneg _
        nlinarith
    _ = 4 * Cρ ^ 2 * ∫ t in (-eighthPeriod h)..eighthPeriod h, saddleDist (dipoleOrbit h t) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ 4 * Cρ ^ 2 * Cd := by gcongr

/-- The first-order trace term on one level: if `|ψ| ≤ M` along the level and `∮ ρ² dt ≤ K`,
    then `|∮ Re(ψ ψ̄ₙ) dℓ| ≤ M (K ∮ |ψₙ|² dt)^{1/2}` (Cauchy–Schwarz). -/
theorem abs_levelIntegral_first_le (ω : L2) {M K h : ℝ} (hM0 : 0 ≤ M) (h0 : 0 < h) (h1 : h < 1)
    (hK : levelIntegral h (fun p ↦ gradNorm p ^ 2) ≤ K)
    (hn : IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) :
    |levelIntegral h fun p ↦
        gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re| ≤
      M * √(K * levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2) := by
  set I := Ico (-2 * eighthPeriod h) (6 * eighthPeriod h) with hI
  set γ : ℝ → ℝ × ℝ := fun t ↦ dipoleOrbit h t with hγ
  have hγm : Measurable γ :=
    (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have hρm : Measurable fun t ↦ gradNorm (γ t) := by
    simp only [gradNorm]
    fun_prop
  have hnm : Measurable fun t ↦ streamNormal ω (γ t) := by
    have hx := ((Lp.stronglyMeasurable (streamPartial 0 ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable).comp hγm
    have hy := ((Lp.stronglyMeasurable (streamPartial 1 ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable).comp hγm
    simp only [streamNormal, normalDeriv, gradNorm, streamLiftX, streamLiftY, liftL2]
    simp only [Function.comp_def] at hx hy
    fun_prop
  have hsm : Measurable fun t ↦ streamLift ω (γ t) :=
    ((Lp.stronglyMeasurable (invLap ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable).comp hγm
  have hρ0 (t : ℝ) : 0 ≤ gradNorm (γ t) := Real.sqrt_nonneg _
  have hρle (t : ℝ) : gradNorm (γ t) ^ 2 ≤ 2 := by
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    nlinarith [Real.sin_sq_le_one (γ t).1, Real.sin_sq_le_one (γ t).2]
  have hre (u v : ℂ) : |(u * (starRingEnd ℂ) v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have iρ : Integrable (fun t ↦ gradNorm (γ t) ^ 2) (volume.restrict I) :=
    (integrable_const (2 : ℝ)).mono' (hρm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (by positivity)]; exact hρle t)
  have iN : Integrable (fun t ↦ ‖streamNormal ω (γ t)‖ ^ 2) (volume.restrict I) := hn
  have iρn : Integrable (fun t ↦ gradNorm (γ t) * ‖streamNormal ω (γ t)‖) (volume.restrict I) :=
    (iρ.add iN).mono' (hρm.mul hnm.norm).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (norm_nonneg _)), Pi.add_apply]
        nlinarith [sq_nonneg (gradNorm (γ t) - ‖streamNormal ω (γ t)‖)])
  have hfm : AEStronglyMeasurable (fun t ↦ gradNorm (γ t) *
      (streamLift ω (γ t) * (starRingEnd ℂ) (streamNormal ω (γ t))).re) (volume.restrict I) :=
    (hρm.mul (Complex.measurable_re.comp
      (hsm.mul (Complex.continuous_conj.measurable.comp hnm)))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict I), ‖gradNorm (γ t) *
      (streamLift ω (γ t) * (starRingEnd ℂ) (streamNormal ω (γ t))).re‖ ≤
        M * (gradNorm (γ t) * ‖streamNormal ω (γ t)‖) := by
    filter_upwards [hM] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 t)]
    calc gradNorm (γ t) * |(streamLift ω (γ t) * (starRingEnd ℂ) (streamNormal ω (γ t))).re|
        ≤ gradNorm (γ t) * (‖streamLift ω (γ t)‖ * ‖streamNormal ω (γ t)‖) :=
          mul_le_mul_of_nonneg_left (hre _ _) (hρ0 t)
      _ ≤ gradNorm (γ t) * (M * ‖streamNormal ω (γ t)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (hρ0 t)
      _ = M * (gradNorm (γ t) * ‖streamNormal ω (γ t)‖) := by ring
  have iA := (iρn.const_mul M).mono' hfm hbound
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict I)
    Real.HolderConjugate.two_two (Eventually.of_forall fun t ↦ hρ0 t)
    (Eventually.of_forall fun t ↦ norm_nonneg (streamNormal ω (γ t)))
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hρm.aestronglyMeasurable).2 iρ)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq hnm.norm.aestronglyMeasurable).2 iN)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  rw [levelIntegral_eq_setIntegral h0 h1] at hK ⊢
  rw [levelIntegral_eq_setIntegral h0 h1]
  calc _ ≤ ∫ t in I, ‖gradNorm (γ t) *
        (streamLift ω (γ t) * (starRingEnd ℂ) (streamNormal ω (γ t))).re‖ :=
        (abs_integral_le_integral_abs).trans_eq rfl
    _ ≤ ∫ t in I, M * (gradNorm (γ t) * ‖streamNormal ω (γ t)‖) :=
        integral_mono_ae iA.norm (iρn.const_mul M) hbound
    _ = M * ∫ t in I, gradNorm (γ t) * ‖streamNormal ω (γ t)‖ := integral_const_mul _ _
    _ ≤ M * (√(∫ t in I, gradNorm (γ t) ^ 2) * √(∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2)) := by
        gcongr
    _ ≤ M * √(K * ∫ t in I, ‖streamNormal ω (γ t)‖ ^ 2) := by
        rw [Real.sqrt_mul' _ (integral_nonneg fun t ↦ by positivity)]
        gcongr

/-- The first-order trace term (`lem:ee-first-trace-limit`): if `∮ |ψₙ|² dt → 0` along levels
    outside `N`, then `∮ Re(ψ ψ̄ₙ) dℓ → 0` outside a larger null set, by Cauchy–Schwarz with
    `|ψ| ≤ ‖ψ̃‖_∞` and `∮ ρ² dt ≤ C` (`ρ ≤ C d` and `lem:orbit-time-integrals`). -/
theorem ee_first_trace_limit (ω : L2) {N : Set ℝ}
    (hn : Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
      (𝓝[Ioi 0 \ N] 0) (𝓝 0)) :
    ∃ N' : Set ℝ, volume N' = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦
          gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re)
        (𝓝[Ioi 0 \ (N ∪ N')] 0) (𝓝 0) := by
  have hmeas (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  -- `|ψ| ≤ M` and `|ψₙ|²` integrable along almost every level.
  set M := ‖continuousRep (invLap ω)‖
  have hM : ∀ᵐ p ∂(volume.restrict cellSquare), ‖streamLift ω p‖ ≤ M := by
    refine ae_restrict_of_ae ?_
    filter_upwards [streamLift_ae_eq_contStream ω] with p hp
    rw [hp, contStream]
    exact (continuousRep (invLap ω)).norm_coe_le_norm _
  have hMlev := ae_level_of_ae_cellSquare (P := fun p ↦ ‖streamLift ω p‖ ≤ M)
    (measurableSet_le (hmeas (invLap ω)).norm measurable_const) hM
  have hAs : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    simp only [mem_prod, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hAs
  have hnm : Measurable (streamNormal ω) := by
    have h2 := hmeas (streamPartial 0 ω)
    have h3 := hmeas (streamPartial 1 ω)
    change Measurable fun p ↦ normalDeriv (streamLiftX ω) (streamLiftY ω) p
    simp only [normalDeriv, gradNorm, streamLiftX, streamLiftY]
    fun_prop
  have hni : IntegrableOn (fun p ↦ ‖streamNormal ω p‖ ^ 2) cellSquare := by
    refine (((hsq (streamPartial 0 ω)).add (hsq (streamPartial 1 ω))).const_mul 2).mono'
      (hnm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    have := norm_normalDeriv_le (streamLiftX ω) (streamLiftY ω) p
    have h0 := norm_nonneg (streamNormal ω p)
    rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
    simp only [streamNormal, streamLiftX, streamLiftY] at this h0 ⊢
    nlinarith [sq_nonneg (‖liftL2 (streamPartial 0 ω) p‖ - ‖liftL2 (streamPartial 1 ω) p‖),
      norm_nonneg (liftL2 (streamPartial 0 ω) p), norm_nonneg (liftL2 (streamPartial 1 ω) p)]
  -- The exceptional levels.
  have hgood := hMlev.and (integral_cellSquare_eq hni).1
  set N' : Set ℝ := {h | h ∈ Ioo 0 1 ∧ ¬ ((∀ᵐ t ∂(volume.restrict
    (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))), ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) ∧
    IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))}
  have hN' : volume N' = 0 := by
    have := (ae_restrict_iff' measurableSet_Ioo).1 hgood
    rw [ae_iff] at this
    refine measure_mono_null (fun h hh ↦ ?_) this
    exact fun himp ↦ hh.2 (himp hh.1)
  refine ⟨N', hN', ?_⟩
  -- The bound `|∮ Re(ψ ψ̄ₙ) dℓ| ≤ M (K ∮ |ψₙ|² dt)^{1/2}` on good levels near the separatrix.
  obtain ⟨K, h₀, hh₀, hK⟩ := levelIntegral_gradNorm_sq_le
  have hfilt : 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  have hup : Tendsto (fun h ↦ M * √(K * levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2))
      (𝓝[Ioi 0 \ (N ∪ N')] 0) (𝓝 0) := by
    have := ((hn.mono_left hfilt).const_mul K).sqrt.const_mul M
    simpa using this
  refine squeeze_zero_norm' ?_ hup
  have hsmall : ∀ᶠ h in 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0, h ∈ Ioo 0 (min h₀ 1) := by
    have h1 : Ioo (0 : ℝ) (min h₀ 1) ∈ 𝓝[Ioi 0] 0 := Ioo_mem_nhdsGT (lt_min hh₀ one_pos)
    exact nhdsWithin_mono _ sdiff_subset h1
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hmem
  have h1 : h < 1 := hh.2.trans_le (min_le_right _ _)
  have hgh : (∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖streamLift ω (dipoleOrbit h t)‖ ≤ M) ∧
      IntegrableOn (fun t ↦ ‖streamNormal ω (dipoleOrbit h t)‖ ^ 2)
        (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)) := by
    by_contra hc
    exact hmem.2 (Or.inr ⟨⟨hh.1, h1⟩, hc⟩)
  obtain ⟨hMh, hnh⟩ := hgh
  rw [Real.norm_eq_abs]
  exact abs_levelIntegral_first_le ω (norm_nonneg _) hh.1 h1
    (hK h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩ h1) hnh hMh

/-- Weighted gradient traces (`lem:ee-gradient-traces`). For `ψ` even under both reflections,
    along levels `h → 0` outside a null set: `∮ |ψₙ|² dt → 0`,
    `∮ |ψₜ|² dt → ∑_γ ∫ ½ cosh² s |g_γ'(s)|² ds` with `g_γ = ψ̃ ∘ γ` the arc traces (on an arc
    `|ψₜ|² = ½ cosh² s |g'|²`), and `∮ Re(ψ ψ̄ₙ) dℓ → 0`. Assembled from `ee_arc_energy`,
    `ee_level_traces` and `ee_first_trace_limit`. -/
theorem ee_gradient_traces {ω : L2} (h0 : MeanZero ω) (hω : InSector true true ω) :
    (∀ k < 4, Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamNormal ω p‖ ^ 2)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦ ‖streamTangent ω p‖ ^ 2) (𝓝[Ioi 0 \ N] 0)
        (𝓝 (∑ k ∈ Finset.range 4,
          ∫ s, Real.cosh s ^ 2 / 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2)) ∧
      Tendsto (fun h ↦ levelIntegral h fun p ↦
          gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re)
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  obtain ⟨N, hN, hn, ht⟩ := ee_level_traces h0 hω
  obtain ⟨N', hN', hf⟩ := ee_first_trace_limit ω hn
  have hmono : 𝓝[Ioi (0 : ℝ) \ (N ∪ N')] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  exact ⟨ee_arc_energy h0 hω, N ∪ N', measure_union_null hN hN', hn.mono_left hmono,
    ht.mono_left hmono, hf⟩

/-! ### The trace of the stream function on the arcs -/

/-- Absolute continuity is preserved by an antitone Lipschitz change of variable: disjoint
    intervals are mapped to disjoint intervals of at most `K` times the length. -/
theorem AbsolutelyContinuousOnInterval.comp_antitoneOn {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {φ : ℝ → ℝ} {α β c d : ℝ} (hf : AbsolutelyContinuousOnInterval f α β)
    {K : NNReal} (hφL : LipschitzOnWith K φ (uIcc c d)) (hφa : AntitoneOn φ (uIcc c d))
    (hφm : MapsTo φ (uIcc c d) (uIcc α β)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) c d := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  have hK : (0 : ℝ) ≤ K := K.2
  refine ⟨δ / (K + 1), by positivity, fun E hE hlen ↦ ?_⟩
  obtain ⟨n, I⟩ := E
  set S := uIcc c d
  have hminS {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : min x y ∈ S := by
    rcases le_total x y with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hmaxS {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : max x y ∈ S := by
    rcases le_total x y with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hmax {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : max (φ x) (φ y) = φ (min x y) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_left (hφa hx hy h)]
    · rw [min_eq_right h, max_eq_right (hφa hy hx h)]
  have hmin {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : min (φ x) (φ y) = φ (max x y) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_right (hφa hx hy h)]
    · rw [max_eq_left h, min_eq_left (hφa hy hx h)]
  have hE' : (n, fun i ↦ (φ (I i).1, φ (I i).2)) ∈
      AbsolutelyContinuousOnInterval.disjWithin α β := by
    refine ⟨fun i hi ↦ ⟨hφm (hE.1 i hi).1, hφm (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    have hd := hE.2 hi hj hij
    obtain ⟨hi1, hi2⟩ := hE.1 i hi
    obtain ⟨hj1, hj2⟩ := hE.1 j hj
    simp only [Function.onFun, uIoc, Set.Ioc_disjoint_Ioc] at hd ⊢
    rw [hmax hi1 hi2, hmax hj1 hj2, hmin hi1 hi2, hmin hj1 hj2,
      hmin (hminS hi1 hi2) (hminS hj1 hj2), hmax (hmaxS hi1 hi2) (hmaxS hj1 hj2)]
    exact hφa (hminS (hmaxS hi1 hi2) (hmaxS hj1 hj2)) (hmaxS (hminS hi1 hi2) (hminS hj1 hj2)) hd
  refine hfδ _ hE' ?_
  calc ∑ i ∈ Finset.range n, dist (φ (I i).1) (φ (I i).2)
      ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 :=
        Finset.sum_le_sum fun i hi ↦ hφL.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (δ / (K + 1)) := by gcongr
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- Changing the left function on a null set preserves weak derivatives. -/
theorem HasWeakPartialOn.congr_left {U : Set (ℝ × ℝ)} {j : Fin 2} {g g' h : ℝ × ℝ → ℂ}
    (hgh : HasWeakPartialOn U j g h) (hg : g =ᵐ[volume] g') : HasWeakPartialOn U j g' h := by
  refine ⟨hgh.1.congr (ae_restrict_of_ae hg), hgh.2.1, fun φ hφ ↦ ?_⟩
  rw [← hgh.2.2 φ hφ]
  exact integral_congr_ae (hg.mono fun p hp ↦ by simp [hp])

/-- Changing a function on a null set preserves local Sobolev membership. -/
theorem MemSobolevOn.congr_ae {k : ℕ} {U : Set (ℝ × ℝ)} {g g' : ℝ × ℝ → ℂ}
    (h : MemSobolevOn k U g) (hg : g =ᵐ[volume] g') : MemSobolevOn k U g' := by
  cases k with
  | zero => exact MemLp.ae_eq (ae_restrict_of_ae hg) h
  | succ k =>
    obtain ⟨hL, hd⟩ := h
    refine ⟨MemLp.ae_eq (ae_restrict_of_ae hg) hL, fun j ↦ ?_⟩
    obtain ⟨d, hd1, hd2⟩ := hd j
    exact ⟨d, hd1.congr_left hg, hd2⟩

/-- The arc angle `2 arctan e^{-s}` lies in `(0, π)`. -/
theorem arcAngle_mem_Ioo (s : ℝ) : arcAngle s ∈ Ioo 0 Real.pi := by
  have h1 := Real.arctan_lt_pi_div_two (Real.exp (-s))
  have h0 := Real.arctan_pos.2 (Real.exp_pos (-s))
  exact ⟨by unfold arcAngle; linarith, by unfold arcAngle; linarith⟩

theorem antitone_arcAngle : Antitone arcAngle := fun s t hst ↦ by
  unfold arcAngle
  have := Real.arctan_strictMono.monotone (Real.exp_le_exp.2 (neg_le_neg hst))
  linarith

theorem lipschitzWith_arcAngle : LipschitzWith 1 arcAngle := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun s ↦ (hasDerivAt_arcAngle s).differentiableAt)
    fun s ↦ ?_
  rw [(hasDerivAt_arcAngle s).deriv, ← NNReal.coe_le_coe, coe_nnnorm, norm_neg, norm_div,
    norm_one, Real.norm_of_nonneg (Real.cosh_pos s).le, NNReal.coe_one,
    div_le_one (Real.cosh_pos s)]
  exact Real.one_le_cosh s

/-- The trace of `ψ̃` on the separatrix arc `γ₀` is locally absolutely continuous and
    differentiable almost everywhere (`lem:arc-trace-ac`). The arc is the segment of the line
    `b = π/2` with `a = arcAngle s - π/2`, and along this line the continuous `H²` function
    `ψ̃` is absolutely continuous (`lem:traces`); `s ↦ a` is antitone and `1`-Lipschitz. -/
theorem absolutelyContinuous_contStream_separatrixArc (ω : L2) :
    (∀ c d, AbsolutelyContinuousOnInterval (contStream ω ∘ separatrixArc) c d) ∧
    ∀ᵐ s, DifferentiableAt ℝ (contStream ω ∘ separatrixArc) s := by
  set U : Set (ℝ × ℝ) := diagRect (Ioo (-Real.pi) Real.pi) (Ioo 0 Real.pi) with hU_def
  have hdc : Continuous diagCoord := by unfold diagCoord; fun_prop
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage (continuous_fst.comp hdc)).inter
      (isOpen_Ioo.preimage (continuous_snd.comp hdc))
  have hb : Bornology.IsBounded U := by
    refine (isCompact_Icc (a := ((-2 * Real.pi, -2 * Real.pi) : ℝ × ℝ))
      (b := (2 * Real.pi, 2 * Real.pi))).isBounded.subset fun p hp ↦ ?_
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    simp only [diagCoord] at h1 h2 h3 h4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith [Real.pi_pos]
  have hrep := streamLift_ae_eq_contStream ω
  have hH2 : MemSobolevOn 2 U (contStream ω) :=
    (memSobolevOn_liftL2 (memSobolev_two_invLap ω) hU hb).congr_ae hrep
  have hx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0) hU).congr_left hrep
  have hy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1) hU).congr_left hrep
  obtain ⟨-, -, -, hac, -, -⟩ := absolutelyContinuous_trace_of_H2 hU (a₀ := -Real.pi)
    (a₁ := Real.pi) (b₁ := 0) (b₂ := Real.pi) (b₀ := Real.pi / 2) (by linarith [Real.pi_pos])
    subset_rfl ⟨by positivity, by linarith [Real.pi_pos]⟩ (continuous_contStream ω).continuousOn
    hH2 hx hy
  set f : ℝ → ℂ := fun a ↦ contStream ω (diagInv (a, Real.pi / 2)) with hf_def
  set φ : ℝ → ℝ := fun s ↦ arcAngle s - Real.pi / 2 with hφ_def
  have hcomp : contStream ω ∘ separatrixArc = f ∘ φ := by
    funext s
    simp only [Function.comp_apply, hf_def, hφ_def, diagInv_apply, separatrixArc]
    congr 2 <;> ring
  have hφa : Antitone φ := fun s t hst ↦ by simpa [hφ_def] using antitone_arcAngle hst
  have hφL : LipschitzWith 1 φ := LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa [hφ_def, Real.dist_eq] using lipschitzWith_arcAngle.dist_le_mul x y
  have hφr (s : ℝ) : φ s ∈ Ioo (-Real.pi) Real.pi := by
    have := arcAngle_mem_Ioo s
    exact ⟨by simp only [hφ_def]; linarith [this.1, Real.pi_pos],
      by simp only [hφ_def]; linarith [this.2, Real.pi_pos]⟩
  have hacs (c d : ℝ) : AbsolutelyContinuousOnInterval (contStream ω ∘ separatrixArc) c d := by
    rw [hcomp]
    have hle : φ (max c d) ≤ φ (min c d) := hφa (min_le_max)
    refine AbsolutelyContinuousOnInterval.comp_antitoneOn
      (hac _ _ (hφr _).1 hle (hφr _).2) hφL.lipschitzOnWith (hφa.antitoneOn _) fun s hs ↦ ?_
    rw [uIcc_of_le hle]
    exact ⟨hφa hs.2, hφa hs.1⟩
  refine ⟨hacs, ?_⟩
  have hn : ∀ n : ℕ, ∀ᵐ s, s ∈ uIcc (-(n : ℝ)) n →
      DifferentiableAt ℝ (contStream ω ∘ separatrixArc) s := fun n ↦
    (hacs _ _).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [ae_all_iff.2 hn] with s hs
  obtain ⟨n, hn⟩ := exists_nat_ge |s|
  exact hs n (by rw [uIcc_of_le (by linarith [abs_nonneg s])]; exact abs_le.1 hn)

/-- Absolute continuity is preserved by a monotone Lipschitz change of variable. -/
theorem AbsolutelyContinuousOnInterval.comp_monotoneOn {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {φ : ℝ → ℝ} {α β c d : ℝ} (hf : AbsolutelyContinuousOnInterval f α β)
    {K : NNReal} (hφL : LipschitzOnWith K φ (uIcc c d)) (hφm : MonotoneOn φ (uIcc c d))
    (hφs : MapsTo φ (uIcc c d) (uIcc α β)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) c d := by
  have hnm {a b x : ℝ} (h : x ∈ uIcc a b) : -x ∈ uIcc (-a) (-b) := by
    rw [mem_uIcc] at h ⊢
    rcases h with h | h
    · exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
  have hneg : AbsolutelyContinuousOnInterval (f ∘ Neg.neg) (-α) (-β) :=
    AbsolutelyContinuousOnInterval.comp_antitoneOn hf (K := 1) LipschitzWith.id.neg.lipschitzOnWith
      (fun x _ y _ h ↦ neg_le_neg h) fun x hx ↦ by
        simpa using hnm hx
  have h := AbsolutelyContinuousOnInterval.comp_antitoneOn hneg (φ := fun x ↦ -φ x) (K := K) hφL.neg
    (fun x hx y hy h ↦ neg_le_neg (hφm hx hy h)) fun x hx ↦ by
      exact hnm (hφs hx)
  convert h using 1
  funext x
  simp

/-! ### Functions of `ξ = tanh s` -/

/-- `artanh' = 1/(1 - ξ²)` on `(-1, 1)`. -/
theorem hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / boundaryWeight x) x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hq : DifferentiableAt ℝ (fun x : ℝ ↦ (1 + x) / (1 - x)) x :=
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).differentiableAt.div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).differentiableAt
      (by linarith [hx.2])
  have hc : ContinuousAt Real.artanh x := by
    have hd : DifferentiableAt ℝ (fun x : ℝ ↦ (1 / 2) * Real.log ((1 + x) / (1 - x))) x :=
      (hq.log hp.ne').const_mul _
    refine hd.continuousAt.congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
  have hw : boundaryWeight x ≠ 0 := by
    unfold boundaryWeight
    nlinarith [hx.1, hx.2]
  have h := (hasDerivAt_tanh (Real.artanh x)).of_local_left_inverse hc
    (by rw [Real.tanh_artanh hx]; unfold boundaryWeight at hw; exact hw)
    (by filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy; exact Real.tanh_artanh hy)
  rw [Real.tanh_artanh hx] at h
  simpa [boundaryWeight, one_div] using h

/-- Almost-everywhere statements in `s` hold at `artanh ξ` for almost every `ξ ∈ (-1, 1)`. -/
theorem ae_comp_artanh {P : ℝ → Prop} (hP : ∀ᵐ s, P s) :
    ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → P (Real.artanh x) := by
  rw [ae_iff] at hP ⊢
  have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (f := Real.tanh) (s := {s | ¬P s})
    (fun s _ ↦ (hasDerivAt_tanh s).differentiableAt.differentiableWithinAt) hP
  refine measure_mono_null (fun x hx ↦ ?_) him
  simp only [mem_ofPred_eq, not_imp] at hx
  exact ⟨Real.artanh x, hx.2, Real.tanh_artanh hx.1⟩

/-- Integrability on `(-1, 1)` in terms of `s = artanh ξ`, `dξ = ds / cosh² s`. -/
theorem integrableOn_Ioo_iff_tanh {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) :
    IntegrableOn f (Ioo (-1) 1) ↔ Integrable fun s ↦ (1 / Real.cosh s ^ 2) • f (Real.tanh s) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_tanh x).hasDerivWithinAt) Real.tanh_injective.injOn f
  rw [Real.tanh_bijOn.image_eq, integrableOn_univ] at h
  rw [h]
  refine integrable_congr (Eventually.of_forall fun s ↦ ?_)
  simp only
  rw [one_sub_tanh_sq, abs_of_pos (by have := Real.cosh_pos s; positivity)]

/-- Composition with `artanh` keeps local absolute continuity on `(-1, 1)`. -/
theorem absolutelyContinuousOnInterval_comp_artanh {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} (hf : ∀ c d, AbsolutelyContinuousOnInterval f c d) {c d : ℝ} (hc : -1 < c)
    (hcd : c ≤ d) (hd : d < 1) : AbsolutelyContinuousOnInterval (f ∘ Real.artanh) c d := by
  have hsub : uIcc c d ⊆ Ioo (-1) 1 := by
    rw [uIcc_of_le hcd]
    exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- On `[c, d]`, `1/(1 - x²) ≤ 1/m` with `m = min (1 - c²) (1 - d²) > 0`.
  set m := min (1 - c ^ 2) (1 - d ^ 2) with hm
  have hm0 : 0 < m := lt_min (by nlinarith) (by nlinarith)
  have hbound : ∀ x ∈ uIcc c d, ‖1 / boundaryWeight x‖₊ ≤ Real.toNNReal (1 / m) := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    have hw : m ≤ boundaryWeight x := by
      unfold boundaryWeight
      rcases le_total 0 x with h0 | h0
      · exact (min_le_right _ _).trans (by nlinarith [hx.2])
      · exact (min_le_left _ _).trans (by nlinarith [hx.1])
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity),
      Real.norm_of_nonneg (by have := hm0.trans_le hw; positivity)]
    exact one_div_le_one_div_of_le hm0 hw
  have hL := (convex_uIcc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx ↦ (hasDerivAt_artanh (hsub hx)).hasDerivWithinAt) hbound
  refine AbsolutelyContinuousOnInterval.comp_monotoneOn (hf (Real.artanh c) (Real.artanh d)) hL
    (fun x hx y hy h ↦ Real.artanh_le_artanh (hsub hx).1 (hsub hy).2 h) fun x hx ↦ ?_
  rw [uIcc_of_le hcd] at hx
  rw [uIcc_of_le (Real.artanh_le_artanh hc hd hcd)]
  exact ⟨Real.artanh_le_artanh hc (hsub (by rw [uIcc_of_le hcd]; exact hx)).2 hx.1,
    Real.artanh_le_artanh (hsub (by rw [uIcc_of_le hcd]; exact hx)).1 hd hx.2⟩

/-- The primitive of an integrable complex function is absolutely continuous on every
    interval (real and imaginary parts separately). -/
theorem absolutelyContinuousOnInterval_primitive {p : ℝ → ℂ} (hp : Integrable p) (c d : ℝ) :
    AbsolutelyContinuousOnInterval (fun s ↦ ∫ t in (0 : ℝ)..s, p t) c d := by
  have hR (q : ℝ → ℝ) (hq : Integrable q) :
      AbsolutelyContinuousOnInterval (fun s ↦ ((∫ t in (0 : ℝ)..s, q t : ℝ) : ℂ)) c d := by
    have h := IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (hq.intervalIntegrable (a := c) (b := d)) (c := c) left_mem_uIcc
    have heq : (fun s ↦ ∫ t in (0 : ℝ)..s, q t) =
        fun s ↦ (∫ t in (0 : ℝ)..c, q t) + ∫ t in c..s, q t := funext fun s ↦
      (intervalIntegral.integral_add_adjacent_intervals hq.intervalIntegrable
        hq.intervalIntegrable).symm
    have hac : AbsolutelyContinuousOnInterval (fun s ↦ ∫ t in (0 : ℝ)..s, q t) c d := by
      rw [heq]
      exact ((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval).add h
    exact Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval hac
  have heq : (fun s ↦ ∫ t in (0 : ℝ)..s, p t) = fun s ↦
      ((∫ t in (0 : ℝ)..s, (p t).re : ℝ) : ℂ) +
        Complex.I • ((∫ t in (0 : ℝ)..s, (p t).im : ℝ) : ℂ) := by
    funext s
    have hre : IntervalIntegrable (fun t ↦ ((p t).re : ℂ)) volume 0 s :=
      (hp.re.ofReal (𝕜 := ℂ)).intervalIntegrable
    have him : IntervalIntegrable (fun t ↦ ((p t).im : ℂ) * Complex.I) volume 0 s :=
      ((hp.im.ofReal (𝕜 := ℂ)).mul_const _).intervalIntegrable
    conv_lhs => rw [show p = fun t ↦ ((p t).re : ℂ) + ((p t).im : ℂ) * Complex.I from
      funext fun t ↦ (Complex.re_add_im _).symm]
    rw [intervalIntegral.integral_add hre him, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, smul_eq_mul, mul_comm]
  rw [heq]
  exact (hR _ hp.re).add ((hR _ hp.im).const_smul Complex.I)

theorem continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1) 1) := fun _ hx ↦
  (hasDerivAt_artanh hx).continuousAt.continuousWithinAt

theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

/-- `artanh ξ → ∞` as `ξ → 1⁻`. -/
theorem tendsto_artanh_nhdsLT_one : Tendsto Real.artanh (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  have hb : Real.tanh b < 1 := Real.tanh_lt_one b
  filter_upwards [Ioo_mem_nhdsLT hb] with x hx
  calc b = Real.artanh (Real.tanh b) := (Real.artanh_tanh b).symm
    _ ≤ Real.artanh x := Real.artanh_le_artanh (Real.neg_one_lt_tanh b) hx.2 hx.1.le

/-- `artanh ξ → -∞` as `ξ → -1⁺`. -/
theorem tendsto_artanh_nhdsGT_neg_one : Tendsto Real.artanh (𝓝[>] (-1)) atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  have hb : -1 < Real.tanh b := Real.neg_one_lt_tanh b
  filter_upwards [Ioo_mem_nhdsGT hb] with x hx
  calc Real.artanh x ≤ Real.artanh (Real.tanh b) :=
        Real.artanh_le_artanh hx.1 (Real.tanh_lt_one b) hx.2.le
    _ = b := Real.artanh_tanh b

/-- `L²` on `(-1, 1)` in terms of `s = artanh ξ`. -/
theorem memLp_two_Ioo_of_tanh {Φ : ℝ → ℂ}
    (hm : AEStronglyMeasurable Φ (volume.restrict (Ioo (-1) 1)))
    (h : Integrable fun s ↦ 1 / Real.cosh s ^ 2 * ‖Φ (Real.tanh s)‖ ^ 2) :
    MemLp Φ 2 (volume.restrict (Ioo (-1) 1)) :=
  (memLp_two_iff_integrable_sq_norm hm).2
    ((integrableOn_Ioo_iff_tanh (fun x ↦ ‖Φ x‖ ^ 2)).2 (by simpa only [smul_eq_mul] using h))

/-- Interval `H¹` data only depend on the values inside the open interval. -/
theorem HasIntervalH1.congr_Ioo {a b : ℝ} {F G D : ℝ → ℂ} (h : HasIntervalH1 a b F D)
    (hFG : EqOn F G (Ioo a b)) : HasIntervalH1 a b G D where
  memLp_value := h.memLp_value.ae_eq ((ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun x hx ↦ hFG hx))
  memLp_derivative := h.memLp_derivative
  locally_absolutelyContinuous c d hc hcd hd := by
    refine (h.locally_absolutelyContinuous c d hc hcd hd).congr fun x hx ↦ hFG ?_
    rw [uIcc_of_le hcd] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  hasDerivAt_ae := by
    filter_upwards [h.hasDerivAt_ae] with x hx hmem
    exact (hx hmem).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_Ioo.mem_nhds hmem) fun y hy ↦ (hFG hy).symm)

/-- Regularity of the boundary unknown (`lem:ee-boundary-regularity`). For an even–even
    eigenfunction with rotation character `κ`, on each arc `γ` the canonical transport unknown
    `z` of `g = ψ̃ ∘ γ`, written `F(ξ) = z(artanh ξ)`, lies in the weighted domain, `G =
    -iwF' - λF ∈ H¹(-1, 1)`, its endpoint values are `-c±/λ` with `c±` the saddle values of
    `ψ̃` at the ends of the arc, and `c₊ = κ c₋`. -/
theorem ee_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) {k : ℕ} (hk : k < 4) :
    ∃ D E : ℝ → ℂ,
      HasWeightedBoundaryH2 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D E ∧
      MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ -
        lam * canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D 1 = -contStream ω (rotLift^[k] (0, -Real.pi)) / lam ∧
      intervalH1Extension (-1) 1 (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k)
        (Real.artanh ξ)) D (-1) = -contStream ω (rotLift^[k] (Real.pi, 0)) / lam ∧
      contStream ω (rotLift^[k] (0, -Real.pi)) =
        paritySign κ * contStream ω (rotLift^[k] (Real.pi, 0)) := by
  -- Skeleton. Each `sorry` below names the result it is to come from.
  set g : ℝ → ℂ := contStream ω ∘ cellArc k with hg_def
  set cp : ℂ := contStream ω (rotLift^[k] (0, -Real.pi)) with hcp_def
  set cm : ℂ := contStream ω (rotLift^[k] (Real.pi, 0)) with hcm_def
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam
  /- (1) The trace `g = ψ̃ ∘ γ_k` on the arc. -/
  -- From the transport traces and the weighted gradient traces.
  have hg1 : Integrable (deriv g) := (ee_melnikov hlam hω hκ k).1
  have hg2 : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2 :=
    ee_arc_energy hω.1 hs k hk
  -- Bounded, since `ψ̃` is a continuous periodic function.
  have hgb : ∀ s, ‖g s‖ ≤ ‖continuousRep (invLap ω)‖ := fun s ↦
    (continuousRep (invLap ω)).norm_coe_le_norm _
  -- Absolute continuity on `γ₀` (`lem:arc-trace-ac`), and `g = κᵏ (ψ̃ ∘ γ₀)`.
  have hArc : g = fun s ↦ paritySign κ ^ k * (contStream ω ∘ separatrixArc) s :=
    funext fun s ↦ contStream_iterate_rotLift hκ k (separatrixArc s)
  obtain ⟨hac0, hd0⟩ := absolutelyContinuous_contStream_separatrixArc ω
  have hgac : ∀ c d, AbsolutelyContinuousOnInterval g c d := fun c d ↦ by
    rw [hArc]
    simpa only [smul_eq_mul] using (hac0 c d).const_smul (paritySign κ ^ k)
  have hgd : ∀ᵐ s, DifferentiableAt ℝ g s := by
    filter_upwards [hd0] with s hs
    rw [hArc]
    exact hs.const_mul _
  -- The Melnikov identity (`ee_melnikov`).
  have hM : ∫ t, profileIntegrand lam g t = 0 := (ee_melnikov hlam hω hκ k).2
  -- End values: `tendsto_separatrixArc_atTop/atBot`, continuity of `ψ̃` and `rotLift`.
  have hRc : Continuous fun p ↦ contStream ω (rotLift^[k] p) :=
    (continuous_contStream ω).comp (Continuous.iterate (by unfold rotLift; fun_prop) k)
  have hgp : Tendsto g atTop (𝓝 cp) := (hRc.tendsto _).comp tendsto_separatrixArc_atTop
  have hgm : Tendsto g atBot (𝓝 cm) := (hRc.tendsto _).comp tendsto_separatrixArc_atBot
  /- (2) The canonical profile `Ω`. -/
  set Ω : ℝ → ℂ := canonicalProfile lam g with hΩ_def
  have hΩp : Tendsto Ω atTop (𝓝 0) := tendsto_canonicalProfile_atTop hg1
  have hΩm : Tendsto Ω atBot (𝓝 0) := (tendsto_canonicalProfile_atBot_iff hg1).2 hM
  have hΩd : ∀ᵐ s, HasDerivAt Ω (Complex.I * lam * Ω s - deriv g s) s :=
    ae_hasDerivAt_canonicalProfile hg1
  have hzd : ∀ᵐ s, HasDerivAt (canonicalUnknown lam g) (Complex.I * -Ω s) s :=
    ae_hasDerivAt_canonicalUnknown hlam hg1 hgd
  -- The weighted bound, compared with `cosh` (`cosh ≤ e^{|s|} ≤ 2 cosh`).
  have hΩw := eLpNorm_exp_mul_canonicalProfile_le (lam := lam) hg1 hM
  have hexp (s : ℝ) : Real.cosh s ≤ Real.exp |s| ∧ Real.exp |s| ≤ 2 * Real.cosh s := by
    rw [Real.cosh_eq]
    have h1 := Real.exp_pos s
    have h2 := Real.exp_pos (-s)
    rcases abs_cases s with ⟨hs, h0⟩ | ⟨hs, h0⟩ <;> rw [hs]
    · have := Real.exp_le_exp.2 (show -s ≤ s by linarith)
      constructor <;> linarith
    · have := Real.exp_le_exp.2 (show s ≤ -s by linarith)
      constructor <;> linarith
  have hΩc : Continuous Ω := continuous_canonicalProfile hg1
  have hgm' : Measurable (deriv g) := measurable_deriv g
  have hRHS : MemLp (fun s ↦ (Real.exp |s| : ℂ) * deriv g s) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 ((hg2.const_mul 4).mono'
      (by fun_prop) (Eventually.of_forall fun s ↦ ?_))
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have := (hexp s).2
    have h0 := (Real.exp_pos |s|).le
    nlinarith [sq_nonneg ‖deriv g s‖, mul_le_mul this this h0 (by linarith)]
  have hLHS : MemLp (fun s ↦ (Real.exp |s| : ℂ) * Ω s) 2 volume := hΩw.trans_lt hRHS
  have hΩ2 : Integrable fun s ↦ Real.cosh s ^ 2 * ‖Ω s‖ ^ 2 := by
    refine ((memLp_two_iff_integrable_sq_norm (by fun_prop)).1 hLHS).mono' (by fun_prop)
      (Eventually.of_forall fun s ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have := (hexp s).1
    have h0 := (Real.cosh_pos s).le
    nlinarith [sq_nonneg ‖Ω s‖, mul_le_mul this this h0 (by linarith [Real.exp_pos |s|])]
  -- `|Ω(s)| ≤ ‖g'‖_{L¹}`, from the definition.
  have hΩb : ∀ s, ‖Ω s‖ ≤ ∫ t, ‖deriv g t‖ := by
    intro s
    rw [hΩ_def, norm_canonicalProfile]
    calc ‖∫ t in Ioi s, profileIntegrand lam g t‖
        ≤ ∫ t in Ioi s, ‖profileIntegrand lam g t‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Ioi s, ‖deriv g t‖ := by
          congr 1
          funext t
          rw [profileIntegrand, norm_mul, norm_exp_neg_I_mul, mul_one]
      _ ≤ ∫ t, ‖deriv g t‖ :=
          setIntegral_le_integral hg1.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
  -- `Ω` is an exponential times an indefinite integral of an integrable function.
  have hΩac : ∀ c d, AbsolutelyContinuousOnInterval Ω c d := by
    intro c d
    have heq : Ω = (fun s : ℝ ↦ Complex.exp (Complex.I * lam * s)) •
        fun s ↦ (∫ t in Ioi 0, profileIntegrand lam g t) -
          ∫ t in (0 : ℝ)..s, profileIntegrand lam g t := by
      funext s
      rw [hΩ_def, canonicalProfile, integral_Ioi_profileIntegrand hg1 s]
      rfl
    rw [heq]
    refine AbsolutelyContinuousOnInterval.smul ?_ ?_
    · have hexpc : ContDiff ℝ 1 (fun s : ℝ ↦ Complex.exp (Complex.I * lam * s)) :=
        (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
      exact ContDiffOn.absolutelyContinuousOnInterval hexpc.contDiffOn
    · exact ((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval).sub
        (absolutelyContinuousOnInterval_primitive (integrable_profileIntegrand hg1) c d)
  /- (3) The functions in `ξ = tanh s`: `F = z ∘ artanh`, `D = F'`, `E = D'`. With
     `w = 1 - ξ² = sech² s`: `wF' = z' = -iΩ` and `w²D' = -i((iλ + 2ξ)Ω - g')`. -/
  set F : ℝ → ℂ := fun ξ ↦ canonicalUnknown lam g (Real.artanh ξ) with hF_def
  set D : ℝ → ℂ := fun ξ ↦ -Complex.I * Ω (Real.artanh ξ) / boundaryWeight ξ with hD_def
  set E : ℝ → ℂ := fun ξ ↦ -Complex.I * ((Complex.I * lam + 2 * ξ) * Ω (Real.artanh ξ) -
    deriv g (Real.artanh ξ)) / (boundaryWeight ξ : ℂ) ^ 2 with hE_def
  -- Common facts: `w > 0` on `(-1, 1)`, `w(tanh s) = 1/cosh² s`, and `z` is continuous,
  -- locally absolutely continuous and bounded.
  have hw (ξ : ℝ) (hξ : ξ ∈ Ioo (-1 : ℝ) 1) : 0 < boundaryWeight ξ := by
    unfold boundaryWeight
    nlinarith [hξ.1, hξ.2]
  have hwt (s : ℝ) : boundaryWeight (Real.tanh s) = 1 / Real.cosh s ^ 2 := boundaryWeight_tanh s
  have hmemt (s : ℝ) : Real.tanh s ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩
  have hgc : Continuous g := hRc.comp (continuous_iff_continuousAt.2 fun s ↦
    (hasDerivAt_separatrixArc s).continuousAt)
  have hz_eq : canonicalUnknown lam g = fun s ↦ -(lam : ℂ)⁻¹ * (Ω s + g s) := by
    funext s
    rw [canonicalUnknown, hΩ_def]
    field_simp
  have hzc : Continuous (canonicalUnknown lam g) := by
    rw [hz_eq]
    exact continuous_const.mul (hΩc.add hgc)
  have hzac (c d : ℝ) : AbsolutelyContinuousOnInterval (canonicalUnknown lam g) c d := by
    rw [hz_eq]
    convert ((hΩac c d).add (hgac c d)).const_smul (-(lam : ℂ)⁻¹) using 1
  set B : ℝ := ∫ t, ‖deriv g t‖
  set M : ℝ := ‖continuousRep (invLap ω)‖
  have hzb (s : ℝ) : ‖canonicalUnknown lam g s‖ ≤ ‖(lam : ℂ)⁻¹‖ * (B + M) := by
    rw [hz_eq, norm_mul, norm_neg]
    gcongr
    exact (norm_add_le _ _).trans (add_le_add (hΩb s) (hgb s))
  -- `F` is bounded, `∫|D|² dξ = ∫ cosh² |Ω|² ds`, and the chain rule under `artanh`.
  have hDt (s : ℝ) : D (Real.tanh s) = -Complex.I * Ω s * (Real.cosh s ^ 2 : ℝ) := by
    simp only [hD_def, Real.artanh_tanh, hwt]
    have := (Real.cosh_pos s).ne'
    push_cast
    field_simp
  have hDc : ContinuousOn D (Ioo (-1) 1) := by
    refine ((continuous_const.mul hΩc).comp_continuousOn continuousOn_artanh).div
      (Complex.continuous_ofReal.comp (by unfold boundaryWeight; fun_prop)).continuousOn
      fun ξ hξ ↦ ?_
    exact Complex.ofReal_ne_zero.2 (hw ξ hξ).ne'
  have hFH1 : HasIntervalH1 (-1) 1 F D := by
    refine ⟨?_, ?_, fun c d hc hcd hd ↦ absolutelyContinuousOnInterval_comp_artanh hzac hc hcd hd,
      ?_⟩
    · exact MemLp.of_bound ((hzc.comp_continuousOn continuousOn_artanh).aestronglyMeasurable
        measurableSet_Ioo) _ (Eventually.of_forall fun ξ ↦ hzb _)
    · refine memLp_two_Ioo_of_tanh (hDc.aestronglyMeasurable measurableSet_Ioo)
        (hΩ2.congr (Eventually.of_forall fun s ↦ ?_))
      have hc := (Real.cosh_pos s).ne'
      beta_reduce
      rw [hDt, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      field_simp
    · filter_upwards [ae_comp_artanh hzd] with ξ hξ hmem
      have h := (hξ hmem).scomp ξ (hasDerivAt_artanh hmem)
      convert h using 1
      · rfl
      · simp only [hD_def, Complex.real_smul]
        push_cast
        ring
  -- `D = (1/w) • (-iΩ ∘ artanh)`, with `1/w` smooth on compact subintervals.
  have hDeq : D = fun ξ ↦ ((1 / boundaryWeight ξ : ℝ) : ℂ) * (-Complex.I * Ω (Real.artanh ξ)) := by
    funext ξ
    simp only [hD_def]
    push_cast
    ring
  have hwd (ξ : ℝ) : HasDerivAt boundaryWeight (-2 * ξ) ξ := by
    unfold boundaryWeight
    simpa using ((hasDerivAt_id ξ).pow 2).const_sub 1
  have hDac : ∀ c d, -1 < c → c ≤ d → d < 1 → AbsolutelyContinuousOnInterval D c d := by
    intro c d hc hcd hd
    have hsub : uIcc c d ⊆ Ioo (-1) 1 := by
      rw [uIcc_of_le hcd]
      exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : AbsolutelyContinuousOnInterval (fun ξ ↦ -Complex.I * Ω (Real.artanh ξ)) c d := by
      convert (absolutelyContinuousOnInterval_comp_artanh hΩac hc hcd hd).const_smul
        (-Complex.I) using 1
      funext ξ
      rfl
    have h2 : AbsolutelyContinuousOnInterval
        (fun ξ ↦ ((1 / boundaryWeight ξ : ℝ) : ℂ)) c d := by
      refine ContDiffOn.absolutelyContinuousOnInterval ?_
      refine Complex.ofRealCLM.contDiff.comp_contDiffOn
        (contDiffOn_const.div (by unfold boundaryWeight; fun_prop) fun x hx ↦ ?_)
      exact (hw x (hsub hx)).ne'
    rw [hDeq]
    exact h2.smul h1
  have hDd : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt D (E x) x := by
    filter_upwards [ae_comp_artanh hΩd] with ξ hξ hmem
    have hw0 := (hw ξ hmem).ne'
    have hΩ' := ((hξ hmem).scomp ξ (hasDerivAt_artanh hmem)).const_mul (-Complex.I)
    have hinv := ((hasDerivAt_const ξ (1 : ℝ)).div (hwd ξ) hw0).ofReal_comp
    have hprod := hinv.mul hΩ'
    rw [hDeq]
    convert hprod using 1
    · rfl
    · simp only [hE_def, Complex.real_smul, Function.comp_apply, Pi.div_apply]
      have hw0' : (boundaryWeight ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw0
      push_cast
      field_simp
      ring_nf
  -- `|wE(tanh s)|² / cosh² s = cosh² s |(iλ + 2 tanh s)Ω - g'|²`.
  have hEm : Measurable E := by
    have := measurable_artanh
    have := hΩc.measurable
    simp only [hE_def, boundaryWeight]
    fun_prop
  have hwE : MemLp (fun x ↦ (boundaryWeight x : ℂ) * E x) 2 (volume.restrict (Ioo (-1) 1)) := by
    refine memLp_two_Ioo_of_tanh (by unfold boundaryWeight; fun_prop) ?_
    have hbound : Integrable fun s ↦ 2 * ((|lam| + 2) ^ 2 * (Real.cosh s ^ 2 * ‖Ω s‖ ^ 2)) +
        2 * (Real.cosh s ^ 2 * ‖deriv g s‖ ^ 2) :=
      ((hΩ2.const_mul _).const_mul 2).add (hg2.const_mul 2)
    have hmeasL : Measurable fun s ↦ 1 / Real.cosh s ^ 2 *
        ‖(boundaryWeight (Real.tanh s) : ℂ) * E (Real.tanh s)‖ ^ 2 := by
      have htm : Measurable Real.tanh :=
        (continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_tanh s).continuousAt).measurable
      unfold boundaryWeight
      fun_prop
    refine hbound.mono' hmeasL.aestronglyMeasurable (Eventually.of_forall fun s ↦ ?_)
    have hc := Real.cosh_pos s
    have hval : (boundaryWeight (Real.tanh s) : ℂ) * E (Real.tanh s) =
        -Complex.I * ((Complex.I * lam + 2 * Real.tanh s) * Ω s - deriv g s) *
          (Real.cosh s ^ 2 : ℝ) := by
      simp only [hE_def, Real.artanh_tanh, hwt]
      push_cast
      field_simp
    have hcoef : ‖Complex.I * lam + 2 * (Real.tanh s : ℂ)‖ ≤ |lam| + 2 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
        have := abs_lt.2 ⟨Real.neg_one_lt_tanh s, Real.tanh_lt_one s⟩
        nlinarith [abs_nonneg (Real.tanh s)]
    rw [Real.norm_of_nonneg (by positivity), hval, norm_mul, norm_mul, norm_neg, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    set a := ‖(Complex.I * lam + 2 * (Real.tanh s : ℂ)) * Ω s - deriv g s‖
    have ha : a ≤ (|lam| + 2) * ‖Ω s‖ + ‖deriv g s‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have ha0 : 0 ≤ a := norm_nonneg _
    have hsq : a ^ 2 ≤ 2 * ((|lam| + 2) ^ 2 * ‖Ω s‖ ^ 2) + 2 * ‖deriv g s‖ ^ 2 := by
      nlinarith [sq_nonneg ((|lam| + 2) * ‖Ω s‖ - ‖deriv g s‖), norm_nonneg (Ω s),
        norm_nonneg (deriv g s), abs_nonneg lam]
    have hc2 : 0 < Real.cosh s ^ 2 := by positivity
    calc 1 / Real.cosh s ^ 2 * (a * Real.cosh s ^ 2) ^ 2 = Real.cosh s ^ 2 * a ^ 2 := by
          field_simp
      _ ≤ Real.cosh s ^ 2 * (2 * ((|lam| + 2) ^ 2 * ‖Ω s‖ ^ 2) + 2 * ‖deriv g s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hc2.le
      _ = _ := by ring
  have hW : HasWeightedBoundaryH2 F D E := ⟨hFH1, hDac, hDd, hwE⟩
  /- (4) `G = -iwD - λF` is the trace `g ∘ artanh` on `(-1, 1)`, and
     `∫|G'|² dξ = ∫ cosh² |g'|² ds` (`hg2`, `hgac`, `integral_tanh_subst`). -/
  have hG : MemIntervalH1 (-1) 1 (fun ξ ↦ -Complex.I * boundaryWeight ξ * D ξ - lam * F ξ) := by
    set Dg : ℝ → ℂ := fun ξ ↦ deriv g (Real.artanh ξ) / boundaryWeight ξ with hDg_def
    have hgH1 : HasIntervalH1 (-1) 1 (fun ξ ↦ g (Real.artanh ξ)) Dg := by
      refine ⟨?_, ?_,
        fun c d hc hcd hd ↦ absolutelyContinuousOnInterval_comp_artanh hgac hc hcd hd, ?_⟩
      · exact MemLp.of_bound ((hgc.comp_continuousOn continuousOn_artanh).aestronglyMeasurable
          measurableSet_Ioo) _ (Eventually.of_forall fun ξ ↦ hgb _)
      · have hDgm : Measurable Dg := by
          have := measurable_artanh
          simp only [hDg_def, boundaryWeight]
          fun_prop
        refine memLp_two_Ioo_of_tanh hDgm.aestronglyMeasurable
          (hg2.congr (Eventually.of_forall fun s ↦ ?_))
        have hc := (Real.cosh_pos s).ne'
        beta_reduce
        rw [hDg_def]
        simp only [Real.artanh_tanh, hwt]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        field_simp
      · filter_upwards [ae_comp_artanh hgd] with ξ hξ hmem
        have h := (hξ hmem).hasDerivAt.scomp ξ (hasDerivAt_artanh hmem)
        convert h using 1
        · rfl
        · simp only [hDg_def, Complex.real_smul]
          push_cast
          ring
    refine ⟨Dg, hgH1.congr_Ioo fun ξ hξ ↦ ?_⟩
    have hw0' : (boundaryWeight ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hw ξ hξ).ne'
    simp only [hD_def, hF_def, hz_eq]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  /- (5) End values: the extension is continuous up to `±1` (`HasIntervalH1.continuousOn_
     extension`) and equals `F` inside, while `z(s) → -(0 + c±)/λ` (`hΩp`, `hΩm`, `hgp`, `hgm`). -/
  have hcont := hFH1.continuousOn_extension (by norm_num : (-1 : ℝ) < 1)
  have hext := hFH1.extension_eq (by norm_num : (-1 : ℝ) < 1)
  have hzlim {l : Filter ℝ} {c : ℂ} (hΩl : Tendsto Ω l (𝓝 0)) (hgl : Tendsto g l (𝓝 c)) :
      Tendsto (canonicalUnknown lam g) l (𝓝 (-c / lam)) := by
    rw [hz_eq]
    convert (hΩl.add hgl).const_mul (-(lam : ℂ)⁻¹) using 2
    field_simp
    ring
  have hend1 : intervalH1Extension (-1) 1 F D 1 = -cp / lam := by
    have hlimF : Tendsto F (𝓝[<] 1) (𝓝 (-cp / lam)) :=
      (hzlim hΩp hgp).comp tendsto_artanh_nhdsLT_one
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT (by norm_num)
    have hlimE : Tendsto (intervalH1Extension (-1) 1 F D) (𝓝[<] 1)
        (𝓝 (intervalH1Extension (-1) 1 F D 1)) :=
      (hcont 1 ⟨by norm_num, le_rfl⟩).tendsto.mono_left
        (nhdsWithin_le_of_mem (mem_of_superset hmem fun x hx ↦ ⟨hx.1.le, hx.2.le⟩))
    refine tendsto_nhds_unique hlimE (hlimF.congr' ?_)
    filter_upwards [hmem] with x hx
    exact (hext hx).symm
  have hend2 : intervalH1Extension (-1) 1 F D (-1) = -cm / lam := by
    have hlimF : Tendsto F (𝓝[>] (-1)) (𝓝 (-cm / lam)) :=
      (hzlim hΩm hgm).comp tendsto_artanh_nhdsGT_neg_one
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[>] (-1) := Ioo_mem_nhdsGT (by norm_num)
    have hlimE : Tendsto (intervalH1Extension (-1) 1 F D) (𝓝[>] (-1))
        (𝓝 (intervalH1Extension (-1) 1 F D (-1))) :=
      (hcont (-1) ⟨le_rfl, by norm_num⟩).tendsto.mono_left
        (nhdsWithin_le_of_mem (mem_of_superset hmem fun x hx ↦ ⟨hx.1.le, hx.2.le⟩))
    refine tendsto_nhds_unique hlimE (hlimF.congr' ?_)
    filter_upwards [hmem] with x hx
    exact (hext hx).symm
  /- (6) The rotation maps one saddle to the other: `R(π, 0) = (0, -π)`. -/
  have hκc : cp = paritySign κ * cm := by
    rw [hcp_def, hcm_def, show ((0 : ℝ), -Real.pi) = rotLift (Real.pi, 0) by simp [rotLift],
      ← Function.iterate_succ_apply, Function.iterate_succ_apply', contStream_rotLift hκ]
  exact ⟨D, E, hW, hG, hend1, hend2, hκc⟩

/-- A symmetry/measure bridge: vanishing on a positive-cell lift forces an even vorticity
    to vanish on both torus cells. It needs no eigenvalue or stream-function hypothesis. -/
theorem InSector.eq_zero_of_lift_ae_zero_on_cellSquare {ω : L2}
    (hs : InSector true true ω)
    (hz : ∀ᵐ p ∂(volume.restrict cellSquare), liftL2 ω p = 0) : ω = 0 := by
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  let I : Set ℝ := Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)
  let F : Set (ℝ × ℝ) := I ×ˢ I
  have hI : MeasurableSet I := measurableSet_Ioc
  have hF : MeasurableSet F := hI.prod hI
  have hproj : MeasurePreserving torusProj (volume.restrict F) volume := by
    change MeasurePreserving (Prod.map (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi)))
      (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi)))) (volume.restrict F)
      (volume : Measure (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)))
    have hm := AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)
    refine ⟨by fun_prop, ?_⟩
    have hp := (hm.prod hm).map_eq
    simpa only [F, I, Measure.prod_restrict, ← Measure.volume_eq_prod,
      torusProj, Real.Angle.coe, Prod.map] using hp
  have hsub : cellSquare ⊆ F := by
    intro p hp
    change |(p.1 + p.2) / 2| < Real.pi / 2 ∧
      |(p.1 - p.2) / 2| < Real.pi / 2 at hp
    obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
    obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hinj : InjOn torusProj F := by
    intro p hp q hq heq
    apply Prod.ext
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hp.1 hq.1).1 (congrArg Prod.fst heq)
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hp.2 hq.2).1 (congrArg Prod.snd heq)
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hz' := (ae_restrict_iff' hcell).1 hz
  have hpos : ∀ᵐ t : Torus, 0 < Ψ t → ω t = 0 := by
    have hequiv := ae_map_iff (μ := volume.restrict F) hproj.measurable.aemeasurable
      (p := fun t : Torus ↦ 0 < Ψ t → ω t = 0)
      (by
        simp only [imp_iff_not_or]
        exact (measurableSet_lt measurable_const hΨ.measurable).compl.union
          ((Lp.stronglyMeasurable ω).measurable (measurableSet_singleton 0)))
    simp only [hproj.map_eq] at hequiv
    apply hequiv.2
    filter_upwards [ae_restrict_of_ae hz', ae_restrict_mem hF] with p hp hpF hpt
    obtain ⟨q, hq, hqp⟩ := exists_mem_cellSquare hpt
    have hqp' : q = p := hinj (hsub hq) hpF hqp
    subst q
    exact hp hq
  have hsingle (x : Real.Angle) : volume ({x} : Set Real.Angle) = 0 := by
    change (volume : Measure (AddCircle (2 * Real.pi))) {x} = 0
    have hx := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
    have hx0 : (volume : Measure (AddCircle (2 * Real.pi))) (Metric.closedBall x 0) = 0 := by
      simpa only [mul_zero, min_eq_right (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        ENNReal.ofReal_zero] using hx
    exact measure_mono_null
      (singleton_subset_iff.mpr (Metric.mem_closedBall_self (by norm_num))) hx0
  have hnull : ∀ᵐ t : Torus, Ψ t ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq hΨ continuous_const).isOpen_compl.measurableSet).2
    exact Eventually.of_forall fun x ↦ by
      rw [ae_iff]
      simp only [not_not]
      have hsub' : {y : Real.Angle | Ψ (x, y) = 0} ⊆
          {((Real.pi : ℝ) : Real.Angle) - x, x - ((Real.pi : ℝ) : Real.Angle)} := by
        intro y hy
        rcases Ψ_eq_zero_iff (x, y) |>.mp hy with hy | hy
        · exact Or.inl (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hy))
        · exact Or.inr (eq_sub_iff_add_eq.mpr
            (by simpa [add_comm] using (sub_eq_iff_eq_add.mp hy).symm))
      have hpair := measure_union_null (hsingle (((Real.pi : ℝ) : Real.Angle) - x))
        (hsingle (x - ((Real.pi : ℝ) : Real.Angle)))
      exact measure_mono_null hsub' (by simpa only [singleton_union] using hpair)
  have href : reflect₁ ω = ω := by simpa [paritySign] using hs.1
  have hraw := Lp.coeFn_compMeasurePreserving ω measurePreserving_S₁
  change (reflect₁ ω : Torus → ℂ) =ᵐ[volume] (fun t ↦ ω (S₁ t)) at hraw
  rw [href] at hraw
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hpos, measurePreserving_S₁.quasiMeasurePreserving.ae hpos, hraw, hnull]
    with t hp hpn ht hn
  by_cases hpt : 0 < Ψ t
  · exact hp hpt
  · have hsneg : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    rw [ht]
    apply hpn
    rw [hsneg]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpt) hn)

/-- Unlike the gradient argument, exclusion only needs strict positivity of the vorticity
    coefficient away from a null set. -/
theorem normalCoeff_pos_of_cos_ne {p : ℝ × ℝ} (h0 : 0 < dipoleLift p)
    (hne : Real.cos p.1 ≠ Real.cos p.2) : 0 < normalCoeff p := by
  have hx := Real.cos_le_one p.1
  have hy := Real.cos_le_one p.2
  have h2 : dipoleLift p < 2 := by
    unfold dipoleLift
    by_contra hn
    exact hne (by linarith)
  have hρ := gradSq_dipoleLift_pos h0 h2
  unfold normalCoeff
  exact div_pos (mul_pos (mul_pos h0 (by linarith)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)))
    (sq_pos_of_pos hρ)

/-- Zero bulk density forces the vorticity itself to vanish on the cell. -/
theorem lift_ae_zero_of_eeBulkDensity_ae_zero {ω : L2}
    (hz : ∀ᵐ p ∂(volume.restrict cellSquare), eeBulkDensity ω p = 0) :
    ∀ᵐ p ∂(volume.restrict cellSquare), liftL2 ω p = 0 := by
  filter_upwards [hz, ae_restrict_of_ae ae_cos_fst_ne_cos_snd,
    ae_restrict_mem (show MeasurableSet cellSquare by unfold cellSquare diagCoord; measurability)]
    with p hp hne hcell
  have h0 : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hcell
  have hf := normalCoeff_pos_of_cos_ne h0 hne
  have h2 : dipoleLift p < 2 := by
    have hx := Real.cos_le_one p.1
    have hy := Real.cos_le_one p.2
    unfold dipoleLift
    by_contra hn
    exact hne (by linarith)
  obtain ⟨hc0, hc1⟩ := normalC_pos_le_one h0 h2
  have hnc : 0 ≤ 2 - normalC p := by linarith
  have hgrad : 0 ≤ (2 - normalC p) * ‖streamNormal ω p‖ ^ 2 +
      normalC p * ‖streamTangent ω p‖ ^ 2 := by positivity
  have hprod : normalCoeff p * ‖liftL2 ω p‖ ^ 2 = 0 := by
    change normalCoeff p * ‖liftL2 ω p‖ ^ 2 +
      (2 - normalC p) * ‖streamNormal ω p‖ ^ 2 +
      normalC p * ‖streamTangent ω p‖ ^ 2 = 0 at hp
    have hn : 0 ≤ normalCoeff p * ‖liftL2 ω p‖ ^ 2 := by positivity
    linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left hf.ne'))

/-- Nonnegative bulk integrals tending to a nonpositive limit vanish on every truncated
    set, hence on their union. No integrability on the full set is assumed. -/
theorem ae_zero_of_truncated_integral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {r J : α → ℝ}
    (hr : Measurable r) (hrpos : ∀ x ∈ s, 0 < r x) (hJ : ∀ x ∈ s, 0 ≤ J x)
    {ts : ℕ → ℝ} (htpos : ∀ n, 0 < ts n) (ht : Tendsto ts atTop (𝓝 0))
    (hi : ∀ n, IntegrableOn J {x | x ∈ s ∧ ts n < r x} μ)
    {b : ℝ} (hb : b ≤ 0)
    (hlim : Tendsto (fun n ↦ ∫ x in {x | x ∈ s ∧ ts n < r x}, J x ∂μ) atTop (𝓝 b)) :
    ∀ᵐ x ∂(μ.restrict s), J x = 0 := by
  let S : ℕ → Set α := fun n ↦ {x | x ∈ s ∧ ts n < r x}
  have hSm n : MeasurableSet (S n) := hs.inter (measurableSet_lt measurable_const hr)
  have hSn n : 0 ≤ᵐ[μ.restrict (S n)] J :=
    ae_restrict_of_forall_mem (hSm n) fun x hx ↦ hJ x hx.1
  have hzero n : (∫ x in S n, J x ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae (hSn n))
    apply le_trans _ hb
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [ht.eventually (gt_mem_nhds (htpos n))] with m hm
    exact setIntegral_mono_set (hi m) (hSn m)
      (Eventually.of_forall fun x hx ↦ ⟨hx.1, hm.trans hx.2⟩)
  have hza : ∀ n, ∀ᵐ x ∂μ, x ∈ S n → J x = 0 := fun n ↦
    (ae_restrict_iff' (hSm n)).1 ((integral_eq_zero_iff_of_nonneg_ae (hSn n) (hi n)).1 (hzero n))
  apply (ae_restrict_iff' hs).2
  filter_upwards [ae_all_iff.2 hza] with x hx hxs
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (hrpos x hxs))).exists
  exact hx n ⟨hxs, hn⟩

/-- Positivity on each canonical arc, from the weighted-domain positivity theorem. -/
theorem ee_canonicalArcForm_nonneg {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) {k : ℕ} (hk : k < 4)
    (hg : Integrable (deriv (contStream ω ∘ cellArc k)))
    (he : Integrable fun s ↦ Real.cosh s ^ 2 * ‖deriv (contStream ω ∘ cellArc k) s‖ ^ 2) :
    0 ≤ canonicalArcForm lam (contStream ω ∘ cellArc k) := by
  obtain ⟨D, E, hF, _, hp, hm, hc⟩ := ee_boundary_regularity hlam hω hs hκ hk
  rw [canonicalArcForm_eq_flowBoundaryForm hlam hg he hF]
  apply hF.flowBoundaryForm_nonneg
  have hends : intervalH1Extension (-1) 1
      (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) D 1 =
      paritySign κ * intervalH1Extension (-1) 1
        (fun ξ ↦ canonicalUnknown lam (contStream ω ∘ cellArc k) (Real.artanh ξ)) D (-1) := by
    rw [hp, hm, hc]
    ring
  cases κ
  · exact Or.inr (by simpa [paritySign] using hends)
  · exact Or.inl (by simpa [paritySign] using hends)

/-- Exclusion for a fixed rotation character, by the vorticity coefficient of the bulk. -/
theorem even_even_character_exclusion {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) : ω = 0 := by
  obtain ⟨he, Ng, hNg, hn, ht, hf⟩ := ee_gradient_traces hω.1 hs
  obtain ⟨hd, hpairs⟩ := ee_transport_traces hlam hω hs hκ
  let B : ℝ → ℝ := fun h ↦
    levelIntegral h (fun p ↦
      gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) +
      (2 - 2 * h) * (levelIntegral h (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
        levelIntegral h (fun p ↦ ‖streamTangent ω p‖ ^ 2) -
        levelIntegral h (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re))
  let P : ℝ → Prop := fun h ↦
    IntegrableOn (eeBulkDensity ω) {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p} ∧
      (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p}, eeBulkDensity ω p) = B h
  have hv : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), P h := ee_truncated_virial hlam hω
  let Nv : Set ℝ := {h | h ∈ Ioo 0 1 ∧ ¬P h}
  have hNv : volume Nv = 0 := by
    have hv' := (ae_restrict_iff' measurableSet_Ioo).1 hv
    simpa only [ae_iff, not_imp] using hv'
  obtain ⟨seq, hseq, hlim, hpair⟩ :=
    hpairs (Ng ∪ Nv) (measure_union_null hNg hNv)
  have hP (j : ℕ) : P (seq j) := by
    by_contra hj
    exact (hseq j).2 (Or.inr ⟨(hseq j).1, hj⟩)
  have hwithin : Tendsto seq atTop (𝓝[Ioi 0 \ Ng] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun j ↦
      ⟨(hseq j).1.1, fun hj ↦ (hseq j).2 (Or.inl hj)⟩⟩
  have hsum : 0 ≤ ∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k) :=
    Finset.sum_nonneg fun k hk ↦ ee_canonicalArcForm_nonneg hlam hω hs hκ
      (Finset.mem_range.mp hk) (hd k (Finset.mem_range.mp hk)) (he k (Finset.mem_range.mp hk))
  have hscaled : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 : ℝ)
  have hfactor : Tendsto (fun j ↦ 2 - 2 * seq j) atTop (𝓝 2) := by
    simpa using hscaled.const_sub (2 : ℝ)
  have hlimB : Tendsto (fun j ↦ B (seq j)) atTop
      (𝓝 (-2 * ∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k))) := by
    have hx := (hf.comp hwithin).add
      (hfactor.mul (((hn.comp hwithin).sub (ht.comp hwithin)).sub hpair))
    convert hx using 1
    · rfl
    · congr 1
      simp only [canonicalArcForm, Finset.sum_add_distrib, Function.comp_apply]
      ring
  apply hs.eq_zero_of_lift_ae_zero_on_cellSquare
  apply lift_ae_zero_of_eeBulkDensity_ae_zero
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  apply ae_zero_of_truncated_integral_tendsto hcell
    (show Measurable dipoleLift by unfold dipoleLift; fun_prop)
    (fun p hp ↦ by simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
    (fun _ hp ↦ eeBulkDensity_nonneg hp)
    (fun j ↦ mul_pos two_pos (hseq j).1.1) hscaled
    (fun j ↦ (hP j).1) (by linarith : -2 *
      (∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k)) ≤ 0)
  exact hlimB.congr fun j ↦ (hP j).2.symm

/-- An eigenfunction even under both separatrix reflections vanishes at every nonzero
    real spectral parameter. The remaining admissions are in its named analytic inputs. -/
theorem even_even_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true true ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, even_even_character_exclusion hlam hep hsp hkp,
    even_even_character_exclusion hlam hem hsm hkm, add_zero]

end NoEmbeddedEigenvalues
