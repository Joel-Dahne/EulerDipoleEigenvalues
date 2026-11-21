module

public import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalBasis
public import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalCutoff
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal

/-!
# Weak testing with zonal fluxes

Compactly supported smooth tests exhaust the diagonal square. The mode
flux vanishes cubically at its weighted endpoints. For the cutoff errors,
it is enough that the mode derivative has a cosine factor: its product with
the cutoff derivative is uniformly bounded and tends pointwise to zero.
Dominated convergence uses only weighted L¹ of the value and derivatives.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Density of the normalized weighted measure. -/
def zonalDensity (p : ℝ × ℝ) : ℝ :=
  4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2)

theorem integral_zonalMeasure_complex (f : ℝ × ℝ → ℂ) :
    ∫ p, f p ∂zonalMeasure = ∫ p in zonalSquare, (zonalDensity p : ℂ) * f p := by
  change (∫ p, f p ∂(volume.restrict zonalSquare).withDensity
    (fun p ↦ ENNReal.ofReal (zonalDensity p))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (zonalDensity p)) by
      apply Measurable.ennreal_ofReal; unfold zonalDensity; fun_prop) (by simp)]
  simp only [zonalDensity, ENNReal.toReal_ofReal (by positivity :
    0 ≤ 4 / Real.pi ^ 2 * (Real.cos _ ^ 2 * Real.cos _ ^ 2)), Complex.real_smul,
    Complex.ofReal_mul]

private def squareCutoff (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (zonalCutoff n p.1 * zonalCutoff n p.2 : ℝ)

private theorem smooth_squareCutoff (n : ℕ) : ContDiff ℝ ∞ (squareCutoff n) :=
  Complex.ofRealCLM.contDiff.comp
    (((contDiff_zonalCutoff n).comp contDiff_fst).mul
      ((contDiff_zonalCutoff n).comp contDiff_snd))

private theorem partial_squareCutoff (n : ℕ) (j : Fin 2) (p : ℝ × ℝ) :
    coordPartial j (squareCutoff n) p =
      (if j = 0 then deriv (zonalCutoff n) p.1 * zonalCutoff n p.2
      else zonalCutoff n p.1 * deriv (zonalCutoff n) p.2 : ℝ) := by
  fin_cases j
  · change deriv (fun t : ℝ ↦ ((zonalCutoff n t * zonalCutoff n p.2 : ℝ) : ℂ)) p.1 = _
    exact (((contDiff_zonalCutoff n).differentiable (by simp) p.1).hasDerivAt.mul_const
      (zonalCutoff n p.2)).ofReal_comp.deriv
  · change deriv (fun t : ℝ ↦ ((zonalCutoff n p.1 * zonalCutoff n t : ℝ) : ℂ)) p.2 = _
    exact (((contDiff_zonalCutoff n).differentiable (by simp) p.2).hasDerivAt.const_mul
      (zonalCutoff n p.1)).ofReal_comp.deriv

private theorem squareCutoff_test (n : ℕ) : IsTestFunctionOn zonalSquare (squareCutoff n) := by
  have hs : tsupport (squareCutoff n) ⊆ tsupport (zonalCutoff n) ×ˢ tsupport (zonalCutoff n) := by
    apply closure_minimal
    · intro p hp
      change squareCutoff n p ≠ 0 at hp
      simp only [squareCutoff, ne_eq, Complex.ofReal_eq_zero, mul_eq_zero,
        not_or] at hp
      exact ⟨subset_closure hp.1, subset_closure hp.2⟩
    · exact (isClosed_tsupport _).prod (isClosed_tsupport _)
  exact ⟨smooth_squareCutoff n,
    ((hasCompactSupport_zonalCutoff n).prod (hasCompactSupport_zonalCutoff n)).of_isClosed_subset
      (isClosed_tsupport _) hs,
    hs.trans (prod_mono (tsupport_zonalCutoff_subset n) (tsupport_zonalCutoff_subset n))⟩

private theorem norm_squareCutoff_le (n : ℕ) (p : ℝ × ℝ) : ‖squareCutoff n p‖ ≤ 1 := by
  have ha := zonalCutoff_mem_Icc n p.1
  have hb := zonalCutoff_mem_Icc n p.2
  simp only [squareCutoff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ha.1, abs_of_nonneg hb.1]
  exact (mul_le_mul_of_nonneg_left hb.2 ha.1).trans (by simpa using ha.2)

private theorem squareCutoff_eventually (j : Fin 2) {p : ℝ × ℝ} (hp : p ∈ zonalSquare) :
    ∀ᶠ n : ℕ in atTop, squareCutoff n p = 1 ∧ coordPartial j (squareCutoff n) p = 0 := by
  filter_upwards [zonalCutoff_eventually hp.1, zonalCutoff_eventually hp.2] with n ha hb
  simp [squareCutoff, partial_squareCutoff, ha.1, ha.2, hb.1, hb.2]

private theorem bound_on_zonalSquare {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ zonalSquare, |f p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-Real.pi / 2) (Real.pi / 2) ×ˢ
      Icc (-Real.pi / 2) (Real.pi / 2))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hp ↦ ?_⟩
  have hb := hC p ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
  exact (show |f p| ≤ C by simpa only [Real.norm_eq_abs] using hb).trans (le_max_left _ _)

private theorem integrable_mul_coefficient {z : ℝ × ℝ → ℂ} (hz : Integrable z zonalMeasure)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun p ↦ z p * (f p : ℂ)) zonalMeasure := by
  obtain ⟨C, _, hC⟩ := bound_on_zonalSquare hf
  apply hz.mul_bdd (c := C) (Complex.continuous_ofReal.comp hf).aestronglyMeasurable
  filter_upwards [ae_mem_zonalSquare] with p hp
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hC p hp

private theorem tendsto_integral_squareCutoff {f : ℝ × ℝ → ℂ}
    (hf : Integrable f zonalMeasure) :
    Tendsto (fun n ↦ ∫ p, squareCutoff n p * f p ∂zonalMeasure) atTop
      (𝓝 (∫ p, f p ∂zonalMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖f p‖)
  · intro n
    exact ((smooth_squareCutoff n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · exact hf.norm
  · intro n
    exact ae_of_all _ fun p ↦ by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_squareCutoff_le n p)
  · filter_upwards [ae_mem_zonalSquare] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [squareCutoff_eventually 0 hp] with n hn
    simp [hn.1]

private theorem bound_cutoff_error (j : Fin 2) {f : ℝ × ℝ → ℝ}
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ zonalSquare,
      |f p| ≤ C * |Real.cos (if j = 0 then p.1 else p.2)|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n p, p ∈ zonalSquare →
      ‖coordPartial j (squareCutoff n) p * (f p : ℂ)‖ ≤ C := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cd, hCd, hd⟩ := zonalCutoff_deriv_cos_bound
  refine ⟨Cf * Cd, mul_nonneg hCf hCd, fun n p hp ↦ ?_⟩
  have hc1 : |zonalCutoff n p.1| ≤ 1 := by
    rw [abs_of_nonneg (zonalCutoff_mem_Icc n p.1).1]; exact (zonalCutoff_mem_Icc n p.1).2
  have hc2 : |zonalCutoff n p.2| ≤ 1 := by
    rw [abs_of_nonneg (zonalCutoff_mem_Icc n p.2).1]; exact (zonalCutoff_mem_Icc n p.2).2
  rw [partial_squareCutoff, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  fin_cases j
  · calc
      |deriv (zonalCutoff n) p.1 * zonalCutoff n p.2 * f p| =
          |deriv (zonalCutoff n) p.1| * |zonalCutoff n p.2| * |f p| := by simp [abs_mul]
      _ ≤ |deriv (zonalCutoff n) p.1| * 1 * (Cf * |Real.cos p.1|) := by gcongr; exact hf p hp
      _ = Cf * (|deriv (zonalCutoff n) p.1| * |Real.cos p.1|) := by ring
      _ ≤ Cf * Cd := mul_le_mul_of_nonneg_left (hd n p.1 hp.1) hCf
  · calc
      |zonalCutoff n p.1 * deriv (zonalCutoff n) p.2 * f p| =
          |zonalCutoff n p.1| * |deriv (zonalCutoff n) p.2| * |f p| := by simp [abs_mul]
      _ ≤ 1 * |deriv (zonalCutoff n) p.2| * (Cf * |Real.cos p.2|) := by gcongr; exact hf p hp
      _ = Cf * (|deriv (zonalCutoff n) p.2| * |Real.cos p.2|) := by ring
      _ ≤ Cf * Cd := mul_le_mul_of_nonneg_left (hd n p.2 hp.2) hCf

private theorem cutoff_error_limit (j : Fin 2) {z : ℝ × ℝ → ℂ}
    (hz : Integrable z zonalMeasure) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ zonalSquare,
      |f p| ≤ C * |Real.cos (if j = 0 then p.1 else p.2)|) :
    (∀ n, Integrable (fun p ↦ z p * (coordPartial j (squareCutoff n) p * (f p : ℂ)))
      zonalMeasure) ∧
    Tendsto (fun n ↦ ∫ p, z p * (coordPartial j (squareCutoff n) p * (f p : ℂ)) ∂zonalMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := bound_cutoff_error j hb
  have hm n : AEStronglyMeasurable
      (fun p ↦ coordPartial j (squareCutoff n) p * (f p : ℂ)) zonalMeasure :=
    ((squareCutoff_test n).continuous_coordPartial j).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hf).aestronglyMeasurable
  have hbound n : ∀ᵐ p ∂zonalMeasure,
      ‖coordPartial j (squareCutoff n) p * (f p : ℂ)‖ ≤ C :=
    ae_mem_zonalSquare.mono fun p hp ↦ hb n p hp
  have hi n := hz.mul_bdd (hm n) (hbound n)
  refine ⟨hi, ?_⟩
  have ht : Tendsto
      (fun n ↦ ∫ p, z p * (coordPartial j (squareCutoff n) p * (f p : ℂ)) ∂zonalMeasure)
      atTop (𝓝 (∫ _p, (0 : ℂ) ∂zonalMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖z p‖ * C)
    · intro n; exact (hi n).aestronglyMeasurable
    · exact hz.norm.mul_const C
    · intro n
      filter_upwards [hbound n] with p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    · filter_upwards [ae_mem_zonalSquare] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [squareCutoff_eventually j hp] with n hn
      simp [hn.2]
  simpa using ht

/-- Weak integration by parts for a smooth flux with a vanishing cosine factor.
Only weighted L¹ of the value and its specified weak derivative is required. -/
theorem HasWeakPartialOn.zonal_flux {j : Fin 2} {z h : ℝ × ℝ → ℂ}
    (hw : HasWeakPartialOn zonalSquare j z h)
    (hz : Integrable z zonalMeasure) (hh : Integrable h zonalMeasure)
    {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hflux : ContDiff ℝ ∞ (fun p ↦ ((zonalDensity p * f p : ℝ) : ℂ)))
    (hderiv : ∀ p, coordPartial j (fun p ↦ ((zonalDensity p * f p : ℝ) : ℂ)) p =
      (zonalDensity p * g p : ℝ))
    (hboundary : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ zonalSquare,
      |f p| ≤ C * |Real.cos (if j = 0 then p.1 else p.2)|) :
    Integrable (fun p ↦ h p * (f p : ℂ)) zonalMeasure ∧
      Integrable (fun p ↦ z p * (g p : ℂ)) zonalMeasure ∧
      (∫ p, h p * (f p : ℂ) ∂zonalMeasure) =
        -(∫ p, z p * (g p : ℂ) ∂zonalMeasure) := by
  have ih := integrable_mul_coefficient hh hf
  have iz := integrable_mul_coefficient hz hg
  obtain ⟨ierror, herror⟩ := cutoff_error_limit j hz hf hboundary
  have hκ n : Integrable (fun p ↦ squareCutoff n p * (z p * (g p : ℂ))) zonalMeasure :=
    iz.bdd_mul (smooth_squareCutoff n).continuous.aestronglyMeasurable
      (ae_of_all _ (norm_squareCutoff_le n))
  have hid (n : ℕ) :
      (∫ p, squareCutoff n p * (z p * (g p : ℂ)) ∂zonalMeasure) +
        (∫ p, z p * (coordPartial j (squareCutoff n) p * (f p : ℂ)) ∂zonalMeasure) =
      -(∫ p, squareCutoff n p * (h p * (f p : ℂ)) ∂zonalMeasure) := by
    let φ : ℝ × ℝ → ℂ := fun p ↦ squareCutoff n p * (zonalDensity p * f p : ℝ)
    have hφ : IsTestFunctionOn zonalSquare φ :=
      ⟨(smooth_squareCutoff n).mul hflux, (squareCutoff_test n).hasCompactSupport.mul_right,
        tsupport_mul_subset_left.trans (squareCutoff_test n).tsupport_subset⟩
    have hφderiv (p : ℝ × ℝ) : coordPartial j φ p =
        (zonalDensity p : ℂ) * (squareCutoff n p * (g p : ℂ) +
          coordPartial j (squareCutoff n) p * (f p : ℂ)) := by
      change coordPartial j
        (fun p ↦ squareCutoff n p * ((zonalDensity p * f p : ℝ) : ℂ)) p = _
      rw [coordPartial_mul j ((smooth_squareCutoff n).differentiable (by simp))
        (hflux.differentiable (by simp))]
      dsimp only
      rw [hderiv]
      simp only [Complex.ofReal_mul]
      ring
    have hU : MeasurableSet zonalSquare := measurableSet_Ioo.prod measurableSet_Ioo
    have eL : (∫ p, z p * coordPartial j φ p) =
        ∫ p, z p * (squareCutoff n p * (g p : ℂ) +
          coordPartial j (squareCutoff n) p * (f p : ℂ)) ∂zonalMeasure := by
      rw [integral_zonalMeasure_complex, ← integral_indicator hU]
      apply integral_congr_ae
      apply ae_of_all
      intro p
      change z p * coordPartial j φ p = _
      by_cases hp : p ∈ zonalSquare
      · rw [indicator_of_mem hp, hφderiv]; ring
      · rw [indicator_of_notMem hp, image_eq_zero_of_notMem_tsupport
          (fun ht ↦ hp (hφ.tsupport_subset (tsupport_coordPartial_subset j φ ht))), mul_zero]
    have eR : (∫ p, h p * φ p) =
        ∫ p, squareCutoff n p * (h p * (f p : ℂ)) ∂zonalMeasure := by
      rw [integral_zonalMeasure_complex, ← integral_indicator hU]
      apply integral_congr_ae
      apply ae_of_all
      intro p
      change h p * φ p = _
      by_cases hp : p ∈ zonalSquare
      · rw [indicator_of_mem hp]
        simp only [φ, Complex.ofReal_mul]
        ring
      · rw [indicator_of_notMem hp,
          image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hφ.tsupport_subset ht)), mul_zero]
    have he := hw.2.2 φ hφ
    rw [eL, eR] at he
    rw [← integral_add (hκ n) (ierror n)]
    convert he using 1
    congr 1
    funext p
    ring
  have hlim := (tendsto_integral_squareCutoff iz).add herror
  have hlim' := (tendsto_integral_squareCutoff ih).neg
  have heq := tendsto_nhds_unique hlim
    (hlim'.congr' (Filter.Eventually.of_forall fun n ↦ (hid n).symm))
  refine ⟨ih, iz, ?_⟩
  simpa using congrArg Neg.neg heq.symm

/-- The two real coordinate derivatives of a product mode. -/
def zonalProductPartial (k : ℕ × ℕ) (j : Fin 2) (p : ℝ × ℝ) : ℝ :=
  if j = 0 then deriv (zonalMode k.1) p.1 * zonalMode k.2 p.2
  else zonalMode k.1 p.1 * deriv (zonalMode k.2) p.2

theorem contDiff_zonalProductPartial (k : ℕ × ℕ) (j : Fin 2) :
    ContDiff ℝ ∞ (zonalProductPartial k j) := by
  unfold zonalProductPartial
  split_ifs
  · exact (((contDiff_zonalMode k.1).deriv').comp contDiff_fst).mul
      ((contDiff_zonalMode k.2).comp contDiff_snd)
  · exact ((contDiff_zonalMode k.1).comp contDiff_fst).mul
      (((contDiff_zonalMode k.2).deriv').comp contDiff_snd)

theorem coordPartial_zonalProduct (k : ℕ × ℕ) (j : Fin 2) :
    coordPartial j (zonalProduct k) = zonalProductPartial k j := by
  funext p
  fin_cases j
  · exact (((contDiff_zonalMode k.1).differentiable (by simp) p.1).hasDerivAt.mul_const
      (zonalMode k.2 p.2)).deriv
  · exact (((contDiff_zonalMode k.2).differentiable (by simp) p.2).hasDerivAt.const_mul
      (zonalMode k.1 p.1)).deriv

private theorem bound_zonalProductPartial (k : ℕ × ℕ) (j : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ zonalSquare,
      |zonalProductPartial k j p| ≤ C * |Real.cos (if j = 0 then p.1 else p.2)| := by
  fin_cases j
  · obtain ⟨Cd, hCd, hd⟩ := zonalMode_deriv_bound k.1
    obtain ⟨Cq, hCq, hq⟩ := bound_on_zonalSquare
      ((contDiff_zonalMode k.2).continuous.comp continuous_snd)
    refine ⟨Cd * Cq, mul_nonneg hCd hCq, fun p hp ↦ ?_⟩
    change |deriv (zonalMode k.1) p.1 * zonalMode k.2 p.2| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (Cd * |Real.cos p.1|) * Cq :=
        mul_le_mul (hd p.1) (hq p hp) (abs_nonneg _) (by positivity)
      _ = _ := by norm_num; ring
  · obtain ⟨Cd, hCd, hd⟩ := zonalMode_deriv_bound k.2
    obtain ⟨Cq, hCq, hq⟩ := bound_on_zonalSquare
      ((contDiff_zonalMode k.1).continuous.comp continuous_fst)
    refine ⟨Cd * Cq, mul_nonneg hCd hCq, fun p hp ↦ ?_⟩
    change |zonalMode k.1 p.1 * deriv (zonalMode k.2) p.2| ≤ _
    rw [abs_mul]
    calc
      _ ≤ Cq * (Cd * |Real.cos p.2|) :=
        mul_le_mul (hq p hp) (hd p.2) (abs_nonneg _) hCq
      _ = _ := by norm_num; ring

private theorem zonalProduct_flux_deriv (k : ℕ × ℕ) (j : Fin 2) (p : ℝ × ℝ) :
    coordPartial j (fun p ↦ ((zonalDensity p * zonalProductPartial k j p : ℝ) : ℂ)) p =
      (zonalDensity p * (-((if j = 0 then k.1 else k.2 : ℕ) : ℝ) *
        (((if j = 0 then k.1 else k.2 : ℕ) : ℝ) + 2) * zonalProduct k p) : ℝ) := by
  fin_cases j
  · change deriv (fun a : ℝ ↦ ((zonalDensity (a, p.2) * zonalProductPartial k 0 (a, p.2) : ℝ) : ℂ))
      p.1 = _
    have heq : (fun a : ℝ ↦ ((zonalDensity (a, p.2) * zonalProductPartial k 0 (a, p.2) : ℝ) : ℂ)) =
        (fun a ↦ ((4 / Real.pi ^ 2 * (Real.cos a ^ 2 * deriv (zonalMode k.1) a) *
          (Real.cos p.2 ^ 2 * zonalMode k.2 p.2) : ℝ) : ℂ)) := by
      funext a; congr 1; simp only [zonalDensity, zonalProductPartial, ↓reduceIte]; ring
    rw [heq, (((hasDerivAt_zonalMode_flux k.1 p.1).const_mul (4 / Real.pi ^ 2)).mul_const
      (Real.cos p.2 ^ 2 * zonalMode k.2 p.2)).ofReal_comp.deriv]
    congr 1
    norm_num [zonalDensity, zonalProduct]
    ring
  · change deriv (fun b : ℝ ↦ ((zonalDensity (p.1, b) * zonalProductPartial k 1 (p.1, b) : ℝ) : ℂ))
      p.2 = _
    have heq : (fun b : ℝ ↦ ((zonalDensity (p.1, b) * zonalProductPartial k 1 (p.1, b) : ℝ) : ℂ)) =
        (fun b ↦ ((4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * zonalMode k.1 p.1) *
          (Real.cos b ^ 2 * deriv (zonalMode k.2) b) : ℝ) : ℂ)) := by
      funext b; congr 1
      simp only [zonalDensity, zonalProductPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      ring
    rw [heq, ((hasDerivAt_zonalMode_flux k.2 p.2).const_mul
      (4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * zonalMode k.1 p.1))).ofReal_comp.deriv]
    congr 1
    norm_num [zonalDensity, zonalProduct]
    ring

private theorem integral_mul_real_coefficient (z : ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℝ) (c : ℝ) :
    (∫ p, z p * (c * f p : ℝ) ∂zonalMeasure) =
      (c : ℂ) * (∫ p, z p * (f p : ℂ) ∂zonalMeasure) := by
  calc
    _ = ∫ p, (c : ℂ) * (z p * (f p : ℂ)) ∂zonalMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun p ↦ by push_cast; ring
    _ = _ := integral_const_mul _ _

/-- Weak mode pairing on the full diagonal weighted domain, with absolute
integrability of both gradient pairings and the value pairing. -/
theorem zonal_weak_pairing_square {z za zb : ℝ × ℝ → ℂ}
    (ha : HasWeakPartialOn zonalSquare 0 z za) (hb : HasWeakPartialOn zonalSquare 1 z zb)
    (hz : MemLp z 2 zonalMeasure) (hza : MemLp za 2 zonalMeasure)
    (hzb : MemLp zb 2 zonalMeasure) (k : ℕ × ℕ) :
    Integrable (fun p ↦ za p * (zonalProductPartial k 0 p : ℂ)) zonalMeasure ∧
      Integrable (fun p ↦ zb p * (zonalProductPartial k 1 p : ℂ)) zonalMeasure ∧
      Integrable (fun p ↦ z p * (zonalProduct k p : ℂ)) zonalMeasure ∧
      (∫ p, za p * (zonalProductPartial k 0 p : ℂ) +
        zb p * (zonalProductPartial k 1 p : ℂ) ∂zonalMeasure) =
        (2 * zonalEigenvalue k.1 k.2 : ℝ) *
          (∫ p, z p * (zonalProduct k p : ℂ) ∂zonalMeasure) := by
  have hQ : ContDiff ℝ ∞ (zonalProduct k) :=
    ((contDiff_zonalMode k.1).comp contDiff_fst).mul
      ((contDiff_zonalMode k.2).comp contDiff_snd)
  have hdensity : ContDiff ℝ ∞ zonalDensity := by unfold zonalDensity; fun_prop
  have hcoord (j : Fin 2) (h : ℝ × ℝ → ℂ) (hw : HasWeakPartialOn zonalSquare j z h)
      (hh : MemLp h 2 zonalMeasure) :=
    hw.zonal_flux (hz.integrable (by norm_num)) (hh.integrable (by norm_num))
      (contDiff_zonalProductPartial k j).continuous
      ((continuous_const.mul continuous_const).mul hQ.continuous)
      (Complex.ofRealCLM.contDiff.comp (hdensity.mul (contDiff_zonalProductPartial k j)))
      (zonalProduct_flux_deriv k j) (bound_zonalProductPartial k j)
  have hx := hcoord 0 za ha hza
  have hy := hcoord 1 zb hb hzb
  refine ⟨hx.1, hy.1, integrable_mul_coefficient (hz.integrable (by norm_num)) hQ.continuous, ?_⟩
  rw [integral_add hx.1 hy.1, hx.2.2, hy.2.2]
  simp only [Pi.mul_apply, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  rw [integral_mul_real_coefficient, integral_mul_real_coefficient]
  push_cast
  unfold zonalEigenvalue
  push_cast
  ring

end NoEmbeddedEigenvalues
