module

public import EulerDipoleEigenvalues.Virial.OriginalDomain.CellPeriodization
public import EulerDipoleEigenvalues.Analysis.TorusSobolev.LiftPeriodization

/-!
# From local Sobolev functions to the torus

Blueprint: `lem:local-to-global`.

* `compactPeriodize F`: the element `∑ₙ F(p + 2πn)` of `L²(𝕋²)` for `F` with compact support,
  read off on the box `(-π, π]²`. Its Fourier coefficients are integrals of `F` over the plane
  against the conjugate characters (`fourierCoeff_compactPeriodize`), by unfolding.
* Weak derivatives on `ℝ²` of compactly supported functions become Fourier derivatives of
  their periodizations (`hasFourierPartial_compactPeriodize`), tested against the characters
  cut off near the support as in `hasFourierPartial_boxPeriodize`; hence `Hᵏ(ℝ²)` functions
  with compact support periodize to `Hᵏ(𝕋²)`.
* `exists_memSobolev_periodize`: for `u ∈ Hᵏ_loc(U)` and a test function `χ` on `U`, the
  periodization of `χu` lies in `Hᵏ(𝕋²)`. Injectivity of the projection on `U` is used only to
  identify the lift with `χu` on `U`: no other translate of the support meets `U`.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff Real

/-! ### Translates -/

theorem torusProj_liftShift (n : ℤ × ℤ) (p : ℝ × ℝ) : torusProj (liftShift n p) = torusProj p := by
  have h (x : ℝ) (m : ℤ) : ((x + m * (2 * π) : ℝ) : Real.Angle) = x :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨m, by ring⟩
  simp only [torusProj, liftShift, h]

/-- Points with the same projection differ by a translate. -/
theorem exists_liftShift_of_torusProj_eq {p q : ℝ × ℝ} (h : torusProj p = torusProj q) :
    ∃ n, q = liftShift n p := by
  obtain ⟨m₁, h₁⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (congrArg Prod.fst h).symm
  obtain ⟨m₂, h₂⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (congrArg Prod.snd h).symm
  refine ⟨(m₁, m₂), Prod.ext ?_ ?_⟩ <;> simp only [liftShift] <;> linarith

theorem liftShift_zero (p : ℝ × ℝ) : liftShift 0 p = p := by
  simp [liftShift]

theorem liftShift_liftShift (n m : ℤ × ℤ) (p : ℝ × ℝ) :
    liftShift n (liftShift m p) = liftShift (n + m) p := by
  simp only [liftShift, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ext <;> simp only <;> ring

theorem liftPeriodize_liftShift (F : ℝ × ℝ → ℂ) (m : ℤ × ℤ) (p : ℝ × ℝ) :
    liftPeriodize F (liftShift m p) = liftPeriodize F p := by
  unfold liftPeriodize
  simp_rw [liftShift_liftShift]
  exact finsum_comp_equiv (Equiv.addRight m) (f := fun n ↦ F (liftShift n p))

theorem liftPeriodize_torusRep (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    liftPeriodize F (torusRep (torusProj p)) = liftPeriodize F p := by
  obtain ⟨n, hn⟩ := exists_liftShift_of_torusProj_eq (torusProj_torusRep (torusProj p)).symm
  rw [hn, liftPeriodize_liftShift]

theorem norm_le_of_mem_periodBox {p : ℝ × ℝ} (hp : p ∈ periodBox) : ‖p‖ ≤ π := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

/-- Unfolding over the box `(-π, π]²`: translate it to `(0, 2π]²`. -/
theorem setIntegral_periodBox_liftPeriodize {f : ℝ × ℝ → ℂ} (hf : Integrable f) {R : ℝ}
    (hR : ∀ q, f q ≠ 0 → ‖q‖ ≤ R) :
    ∫ q in periodBox, liftPeriodize f q = ∫ q, f q := by
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.addRight (-π)).prodCongr (MeasurableEquiv.addRight (-π))
  have he (q : ℝ × ℝ) : e q = (q.1 + -π, q.2 + -π) := rfl
  have hmp : MeasurePreserving e volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume _).prod (measurePreserving_add_right volume _)
  have hR' : ∀ q, f (e q) ≠ 0 → ‖q‖ ≤ R + π := fun q hq ↦ by
    have h := hR _ hq
    rw [he, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := (le_max_left _ _).trans h
    have h2 := (le_max_right _ _).trans h
    have := Real.pi_pos
    refine max_le ?_ ?_
    · calc |q.1| = |(q.1 + -π) + π| := by ring_nf
        _ ≤ |q.1 + -π| + |π| := abs_add_le _ _
        _ ≤ R + π := by rw [abs_of_pos Real.pi_pos]; linarith
    · calc |q.2| = |(q.2 + -π) + π| := by ring_nf
        _ ≤ |q.2 + -π| + |π| := abs_add_le _ _
        _ ≤ R + π := by rw [abs_of_pos Real.pi_pos]; linarith
  have hfe : Integrable fun q ↦ f (e q) := (hmp.integrable_comp hf.aestronglyMeasurable).mpr hf
  have h1 := integral_liftPeriodize hfe hR'
  rw [hmp.integral_comp' (g := f)] at h1
  rw [h1]
  have hshift (n : ℤ × ℤ) (q : ℝ × ℝ) : e (liftShift n q) = liftShift n (e q) := by
    rw [he, he]
    simp only [liftShift]
    ext <;> simp only <;> ring
  have hP (q : ℝ × ℝ) : liftPeriodize (fun q ↦ f (e q)) q = liftPeriodize f (e q) := by
    unfold liftPeriodize
    simp only [hshift]
  simp_rw [hP]
  have hpre : e ⁻¹' periodBox = liftSquare 0 := by
    ext q
    rw [liftSquare_zero]
    simp only [periodBox, mem_preimage, he, mem_prod, mem_Ioc, zero_add]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hi := hmp.setIntegral_preimage_emb e.measurableEmbedding (liftPeriodize f) periodBox
  rw [hpre] at hi
  exact hi.symm

theorem norm_char (k : ℤ × ℤ) (t : Torus) : ‖char k t‖ = 1 := by
  change AddCircle (2 * π) × AddCircle (2 * π) at t
  change ‖fourier k.1 t.1 * fourier k.2 t.2‖ = 1
  simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-! ### Periodization of compactly supported functions -/

/-- The element `∑ₙ F(· + 2πn)` of `L²(𝕋²)`, read off on the box. -/
def compactPeriodize (F : ℝ × ℝ → ℂ) : L2 := boxPeriodize (liftPeriodize F)

section Periodize

variable {F : ℝ × ℝ → ℂ} {K : Set (ℝ × ℝ)}

theorem exists_norm_bound_of_isCompact (hK : IsCompact K) (hF0 : ∀ p ∉ K, F p = 0) :
    ∃ R, ∀ q, F q ≠ 0 → ‖q‖ ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact ⟨R, fun q hq ↦ mem_closedBall_zero_iff.1 (hR (by_contra fun h ↦ hq (hF0 q h)))⟩

theorem memLp_liftPeriodize_periodBox (hK : IsCompact K) (hF0 : ∀ p ∉ K, F p = 0)
    (hF : MemLp F 2 volume) : MemLp (liftPeriodize F) 2 (volume.restrict periodBox) := by
  obtain ⟨R, hR⟩ := exists_norm_bound_of_isCompact hK hF0
  obtain ⟨N, hN⟩ := exists_nat_gt (R + π)
  have hs : MemLp (fun p ↦ ∑ n ∈ shiftBox N, F (liftShift n p)) 2 (volume.restrict periodBox) :=
    memLp_finsetSum _ fun n _ ↦
      (hF.comp_measurePreserving (measurePreserving_liftShift n)).restrict _
  refine hs.ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_periodBox] with p hp
  exact (liftPeriodize_eq_sum hR hN.le (norm_le_of_mem_periodBox hp)).symm

/-- The Fourier coefficients of a periodization are integrals over the plane. -/
theorem fourierCoeff_compactPeriodize (hK : IsCompact K) (hF0 : ∀ p ∉ K, F p = 0)
    (hF : MemLp F 2 volume) (k : ℤ × ℤ) :
    fourierCoeff (compactPeriodize F) k =
      ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, char (-k) (torusProj p) * F p := by
  have hG := memLp_liftPeriodize_periodBox hK hF0 hF
  rw [fourierCoeff_eq_integral_char_neg]
  congr 1
  have hc : Continuous torusProj := isOpenQuotientMap_torusProj.continuous
  have e1 : ∫ t, char (-k) t * compactPeriodize F t =
      ∫ t, (fun p ↦ char (-k) (torusProj p) * liftPeriodize F p) (torusRep t) := by
    apply integral_congr_ae
    filter_upwards [coeFn_boxPeriodize hG] with t ht
    simp only [compactPeriodize, ht, torusProj_torusRep]
  have hm : AEStronglyMeasurable (fun p ↦ char (-k) (torusProj p) * liftPeriodize F p)
      (Measure.map torusRep volume) := by
    rw [measurePreserving_torusRep.map_eq]
    exact ((char (-k)).continuous.comp hc).aestronglyMeasurable.mul hG.aestronglyMeasurable
  rw [e1, ← integral_map measurable_torusRep.aemeasurable hm, measurePreserving_torusRep.map_eq]
  -- Unfold the periodization of `e F`.
  obtain ⟨R, hR⟩ := exists_norm_bound_of_isCompact hK hF0
  have hFi : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset fun p hp ↦ by_contra fun h ↦ hp (hF0 p h)).1
      ((hF.locallyIntegrable one_le_two).integrableOn_isCompact hK)
  have hi : Integrable fun p ↦ char (-k) (torusProj p) * F p := by
    refine hFi.mono (((char (-k)).continuous.comp hc).aestronglyMeasurable.mul
      hFi.aestronglyMeasurable) (Eventually.of_forall fun p ↦ ?_)
    rw [norm_mul, norm_char, one_mul]
  have hR' : ∀ q, char (-k) (torusProj q) * F q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (right_ne_zero_of_mul hq)
  rw [← setIntegral_periodBox_liftPeriodize hi hR']
  refine setIntegral_congr_fun measurableSet_periodBox fun p _ ↦ ?_
  unfold liftPeriodize
  simp_rw [torusProj_liftShift]
  exact mul_finsum _ _

/-- Weak derivatives on the plane of compactly supported functions become Fourier derivatives
of the periodizations. -/
theorem hasFourierPartial_compactPeriodize {j : Fin 2} {d : ℝ × ℝ → ℂ} (hK : IsCompact K)
    (hF0 : ∀ p ∉ K, F p = 0) (hd0 : ∀ p ∉ K, d p = 0) (hF : MemLp F 2 volume)
    (hd2 : MemLp d 2 volume) (hd : HasWeakPartialOn univ j F d) :
    HasFourierPartial j (compactPeriodize F) (compactPeriodize d) := by
  -- A cutoff `θ` equal to `1` near `K` with compact support.
  obtain ⟨V₂, hV₂o, hKV₂, -, hV₂k⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  obtain ⟨V₁, hV₁o, hKV₁, hV₁c, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₂o isClosed_closure hV₁c
  have hθc : HasCompactSupport θ := by
    rw [HasCompactSupport, tsupport, hθs]
    exact hV₂k
  have hθ1' (p : ℝ × ℝ) (hp : p ∈ V₁) : θ p = 1 := (hθ1 p).1 (subset_closure hp)
  intro k
  -- The conjugate character on the plane.
  set a : ℂ := ((-k).1 : ℂ)
  set b : ℂ := ((-k).2 : ℂ)
  let e : ℝ × ℝ → ℂ := fun p ↦ exp (I * (a * p.1 + b * p.2))
  have he (p : ℝ × ℝ) : char (-k) (torusProj p) = e p := char_coe (-k) p.1 p.2
  have hes : ContDiff ℝ ∞ e := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.1 : ℝ) : ℂ)) := ofRealCLM.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.2 : ℝ) : ℂ)) := ofRealCLM.contDiff.comp contDiff_snd
    exact Complex.contDiff_exp.comp (contDiff_const.mul ((contDiff_const.mul h1).add
      (contDiff_const.mul h2)))
  have hed : coordPartial j e = fun p ↦ -(I * frequencyComponent k j) * e p := by
    funext p
    unfold coordPartial
    split_ifs with hj
    · have hd : HasDerivAt (fun t : ℝ ↦ e (t, p.2)) (e p * (I * a)) p.1 := by
        have := (((hasDerivAt_id p.1).ofReal_comp.const_mul a).add_const (b * p.2)).const_mul I
        simpa [e] using this.cexp
      rw [partialX, hd.deriv]
      simp [frequencyComponent, hj, a]
      ring
    · have hd : HasDerivAt (fun t : ℝ ↦ e (p.1, t)) (e p * (I * b)) p.2 := by
        have := (((hasDerivAt_id p.2).ofReal_comp.const_mul b).const_add (a * p.1)).const_mul I
        simpa [e] using this.cexp
      rw [partialY, hd.deriv]
      simp [frequencyComponent, hj, b]
      ring
  -- The test function `θ e`.
  let θc : ℝ × ℝ → ℂ := fun p ↦ (θ p : ℂ)
  have hθcs : ContDiff ℝ ∞ θc := ofRealCLM.contDiff.comp hθ
  have hφ : IsTestFunctionOn univ (fun p ↦ θc p * e p) :=
    ⟨hθcs.mul hes, (hθc.comp_left ofReal_zero).mul_right, subset_univ _⟩
  have hw := hd.2.2 _ hφ
  rw [coordPartial_mul j (hθcs.differentiable (by simp)) (hes.differentiable (by simp)), hed]
    at hw
  have hl : (fun p ↦ F p * (coordPartial j θc p * e p + θc p * (-(I * frequencyComponent k j) *
      e p))) = fun p ↦ -(I * frequencyComponent k j) * (e p * F p) := by
    funext p
    by_cases hp : p ∈ K
    · have h1 : θc =ᶠ[𝓝 p] fun _ ↦ 1 := by
        filter_upwards [hV₁o.mem_nhds (hKV₁ hp)] with q hq
        simp [θc, hθ1' q hq]
      rw [coordPartial_eq_zero_of_eventuallyEq h1, h1.eq_of_nhds]
      ring
    · simp [hF0 p hp]
  have hr : (fun p ↦ d p * (θc p * e p)) = fun p ↦ e p * d p := by
    funext p
    by_cases hpK : p ∈ K
    · simp [θc, hθ1' p (hKV₁ hpK), mul_comm]
    · simp [hd0 p hpK]
  rw [hl, hr, integral_const_mul] at hw
  rw [fourierCoeff_compactPeriodize hK hd0 hd2, fourierCoeff_compactPeriodize hK hF0 hF]
  simp only [he]
  linear_combination (((2 * π : ℂ) ^ 2)⁻¹) * hw

/-- Compactly supported `Hᵏ(ℝ²)` functions periodize to `Hᵏ(𝕋²)`. -/
theorem memSobolev_compactPeriodize (k : ℕ) {F : ℝ × ℝ → ℂ} (hK : IsCompact K)
    (hF0 : ∀ p ∉ K, F p = 0) (hF : MemSobolevOn k univ F) :
    MemSobolev k (compactPeriodize F) := by
  induction k generalizing F with
  | zero => simpa using memSobolev_zero (compactPeriodize F)
  | succ k ih =>
    have hL : MemLp F 2 volume := by simpa using hF.1
    -- Derivatives, redefined to vanish off `K`.
    have hder (j : Fin 2) : ∃ d, (∀ p ∉ K, d p = 0) ∧
        HasFourierPartial j (compactPeriodize F) (compactPeriodize d) ∧
        MemSobolev k (compactPeriodize d) := by
      obtain ⟨d, hd, hdk⟩ := hF.2 j
      have hd0 : ∀ᵐ p, p ∉ K → d p = 0 :=
        (hd.mono (subset_univ Kᶜ)).ae_eq_zero hK.isClosed.isOpen_compl fun p hp ↦ hF0 p hp
      have hdd : K.indicator d =ᵐ[volume] d := by
        filter_upwards [hd0] with p hp
        by_cases hpK : p ∈ K
        · simp [hpK]
        · simp [hpK, hp hpK]
      have hd' : HasWeakPartialOn univ j F (K.indicator d) := by
        refine ⟨hd.1, hd.2.1.congr (ae_restrict_of_ae hdd.symm), fun φ hφ ↦ ?_⟩
        rw [hd.2.2 φ hφ]
        congr 1
        exact integral_congr_ae (hdd.mono fun p hp ↦ by simp [hp])
      have hdk' : MemSobolevOn k univ (K.indicator d) :=
        MemSobolevOn.congr_ae (k := k) hdk hdd.symm
      have hd2 : MemLp (K.indicator d) 2 volume := by simpa using hdk'.memLp
      have h0 : ∀ p ∉ K, K.indicator d p = 0 := fun p hp ↦ indicator_of_notMem hp d
      exact ⟨K.indicator d, h0, hasFourierPartial_compactPeriodize hK hF0 h0 hL hd2 hd',
        ih h0 hdk'⟩
    obtain ⟨d₀, -, hd₀, hs₀⟩ := hder 0
    obtain ⟨d₁, -, hd₁, hs₁⟩ := hder 1
    have hg : MemSobolev k (compactPeriodize F) := ih hF0 (MemSobolevOnWith.of_succ hF)
    push_cast
    exact memSobolev_add_one_of_hasFourierPartial hg hd₀ hd₁ hs₀ hs₁

/-- The lift of a periodization is the periodization on the plane. -/
theorem liftL2_compactPeriodize (hK : IsCompact K) (hF0 : ∀ p ∉ K, F p = 0)
    (hF : MemLp F 2 volume) : ∀ᵐ p, liftL2 (compactPeriodize F) p = liftPeriodize F p := by
  filter_upwards [ae_torusProj (coeFn_boxPeriodize (memLp_liftPeriodize_periodBox hK hF0 hF))]
    with p hp
  rw [liftL2, compactPeriodize, hp, liftPeriodize_torusRep]

end Periodize

/-! ### Localization (`lem:local-to-global`) -/

/-- Periodization of cut-off local functions: if `U` projects injectively to the torus,
    `u ∈ Hᵏ_loc(U)` and `χ` is a test function on `U`, then there is `g ∈ Hᵏ(𝕋²)` whose lift is
    `χu` on `U` and vanishes off the translates of the support of `χ`. -/
theorem exists_memSobolev_periodize {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hinj : Set.InjOn torusProj U) {u χ : ℝ × ℝ → ℂ} (hu : MemSobolevLocOn k U u)
    (hχ : IsTestFunctionOn U χ) :
    ∃ g : L2, MemSobolev k g ∧ (∀ᵐ p ∂(volume.restrict U), liftL2 g p = χ p * u p) ∧
      ∀ᵐ p, torusProj p ∉ torusProj '' tsupport χ → liftL2 g p = 0 := by
  set F : ℝ × ℝ → ℂ := fun p ↦ χ p * u p
  have hK : IsCompact (tsupport χ) := hχ.hasCompactSupport
  have hF0 : ∀ p ∉ tsupport χ, F p = 0 := fun p hp ↦ by
    simp [F, image_eq_zero_of_notMem_tsupport hp]
  have hFs : MemSobolevOn k univ F :=
    hu.cutoff k hU hχ.contDiff hχ.hasCompactSupport hχ.tsupport_subset
  have hFL : MemLp F 2 volume := by simpa using hFs.memLp
  refine ⟨compactPeriodize F, memSobolev_compactPeriodize k hK hF0 hFs, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae (liftL2_compactPeriodize hK hF0 hFL),
      ae_restrict_mem hU.measurableSet] with p hp hpU
    rw [hp, liftPeriodize]
    refine (finsum_eq_single _ 0 fun n hn ↦ ?_).trans (by rw [liftShift_zero])
    by_contra hne
    have hmem : liftShift n p ∈ tsupport χ := by_contra fun h ↦ hne (hF0 _ h)
    have heq := hinj (hχ.tsupport_subset hmem) hpU (torusProj_liftShift n p)
    apply hn
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    simp only [liftShift] at h1 h2
    have hpi : (2 * π) ≠ 0 := by positivity
    ext
    · simpa [hpi] using h1
    · simpa [hpi] using h2
  · filter_upwards [liftL2_compactPeriodize hK hF0 hFL] with p hp hnot
    rw [hp, liftPeriodize]
    refine finsum_eq_zero_of_forall_eq_zero fun n ↦ hF0 _ fun hmem ↦ hnot ?_
    exact ⟨_, hmem, torusProj_liftShift n p⟩

end EulerDipoleEigenvalues
