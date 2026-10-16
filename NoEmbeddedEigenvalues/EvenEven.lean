import NoEmbeddedEigenvalues.Sectors
import NoEmbeddedEigenvalues.NormalField
import NoEmbeddedEigenvalues.CanonicalBoundaryForm
import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.VirialL2

/-!
# Even–even exclusion

The exclusion theorem and its fixed-rotation-character version are proved from named
analytic inputs, which remain admitted. The endgame uses `f > 0` almost everywhere to
force the vorticity itself to vanish, rather than a weak-gradient constant-function theorem.

Proved here: `lem:ee-neumann`, `lem:ee-bulk-integrable`, `lem:ee-truncated-virial` (from
the annular identity and the center limit), `lem:ee-cell-vanishing`, `lem:cos-diagonal-null`,
`lem:ee-vorticity-from-density`, `lem:nonnegative-exhaustion`,
`lem:ee-canonical-arc-nonneg`, `lem:ee-character-exclusion`, `thm:ee-exclusion`.
Inputs: `lem:ee-annular-virial`, `lem:ee-center-limit`,
`lem:ee-gradient-traces` and `lem:ee-boundary-regularity`. The interfaces
`lem:canonical-arc-form` and `lem:ee-transport-traces` are proved in
`CanonicalBoundaryForm.lean` and `EigenfunctionTransport.lean`. Levels are handled in orbit
coordinates, and one sequence avoids the null sets of both the virial and trace statements.
The center is cut out of the virial identity, so it is only needed for fields supported in
an annulus.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set

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

/-- The virial identity on an annulus (`lem:ee-annular-virial`): outside one null set of
    levels, for all `0 < h < h' < 1`, `∫_{2h < Ψ < 2h'} 𝒥 = G(h) - G(h')` with `G` the level
    terms `eeLevelTerm`. From `lem:virial-l2` with the cutoff field `χ(Ψ)W`,
    `χ → 𝟙_{(2h, 2h')}`. -/
theorem ee_annular_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
      ∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'},
        eeBulkDensity ω p = eeLevelTerm ω h - eeLevelTerm ω h' := by
  sorry

/-- The level terms vanish at the center along a sequence (`lem:ee-center-limit`): for every
    null set `N` there are levels `h_j → 1` outside `N` with `G(h_j) → 0`. Both terms of `G`
    are bounded by `(1 - h)g(h)` or `((1 - h)g(h))^{1/2}` with `∫ g < ∞` by coarea, since
    `ρ² ~ 2(2 - Ψ)` at the center. Only `ω ∈ L²` and `ψ ∈ H²` are used. -/
theorem ee_center_limit (ω : L2) {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Ioo 0 1 ∧ hs j ∉ N) ∧ Tendsto hs atTop (𝓝 1) ∧
      Tendsto (fun j ↦ eeLevelTerm ω (hs j)) atTop (𝓝 0) := by
  sorry

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

/-- Weighted gradient traces (`lem:ee-gradient-traces`). For `ψ` even under both reflections,
    along levels `h → 0` outside a null set: `∮ |ψₙ|² dt → 0`,
    `∮ |ψₜ|² dt → ∑_γ ∫ ½ cosh² s |g_γ'(s)|² ds` with `g_γ = ψ̃ ∘ γ` the arc traces (on an arc
    `|ψₜ|² = ½ cosh² s |g'|²`), and `∮ Re(ψ ψ̄ₙ) dℓ → 0`. -/
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
  sorry

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
  sorry

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
