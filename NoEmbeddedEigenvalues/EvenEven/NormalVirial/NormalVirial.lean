import NoEmbeddedEigenvalues.EvenEven.NormalVirial.NormalField
import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport
import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.LevelTraces
import NoEmbeddedEigenvalues.Virial.OriginalDomain.VirialL2
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.DuBoisReymond

/-!
# The normal-field virial on truncated cells

Blueprint: `def:ee-bulk-density`, `def:ee-level-term`, `def:ee-boundary-density`,
`lem:ee-bulk-integrable`, `lem:ee-boundary-integrable`, `lem:ee-cutoff-identity`,
`lem:ee-annular-virial`, `lem:ee-center-limit`, `lem:ee-truncated-virial`,
`lem:ee-bulk-density-nonneg` and `lem:cos-diagonal-null`.

The normal field gives a nonnegative bulk density. Apply the L² virial to annular
cutoffs, recover the level identity by coarea and du Bois-Reymond, then remove
the center boundary along levels where its contribution tends to zero.
The truncated identity includes integrability and needs no reflection-sector
hypothesis. Boundary limits specific to even–even eigenfunctions are in
`EvenEvenBoundary.lean`; the exclusion assembly is in `EvenEven.lean`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set
open scoped ENNReal

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


end NoEmbeddedEigenvalues
