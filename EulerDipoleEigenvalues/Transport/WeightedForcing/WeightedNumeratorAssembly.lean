module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.EndpointNumeratorBounds
public import EulerDipoleEigenvalues.Transport.WeightedForcing.WeightedFirstNumerator
public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterForcingPullback

/-!
# Quantitative numerator assembly from a canonical boundary estimate

Blueprint: `lem:weighted-numerator-assembly`.

The one separate input is the levelwise bound for the first-bulk boundary
potential by the canonical affine-gradient energy. The fixed-time second
bulk and the differentiated endpoint-value flux are controlled separately.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- The actual H² numerator, derivative norms and quantitative estimates are
compatible with the supplied ordered jet if its first-bulk boundary trace
has the indicated pointwise energy bound. -/
theorem IsTransportPair.weighted_numerator_data_of_boundary_bound
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hD : HasWeakJetOn 2 U g D)
    (hf : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D [j] p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {d Kd : ℝ} (hd : 0 < d) (hKd : 0 ≤ Kd)
    (hbd : ∀ᵐ (h : ℝ) ∂(volume.restrict (Ioo 0 d)),
      ‖(h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ) *
        (quarterFirstBulkTrace lam D (1 / 8) h - quarterFirstBulkTrace lam D (-1 / 8) h)‖ ^ 2 ≤
          Kd * quarterEndpointGradientEnergy (quarterGradientTrace (fun j ↦ D [j])) h) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧ Nonempty (WeightedQuarterNumeratorData lam U g D h₀) := by
  have hU := hp.isOrbitUnion.1
  have hcell' := subset_closure.trans hcell
  have hfg' := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hgs := hp.memSobolevOn.congr_ae_on hU.measurableSet hfg'
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (D [j]) := by
    simpa only [hD.1] using hD.2 [] (by simp) j
  have hDf' (j : Fin 2) : HasWeakPartialOn U j f (D [j]) :=
    (hDg j).congr_ae_on hU.measurableSet (hfg'.mono fun _ he hin ↦ (he hin).symm)
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hDL := hgs.memLp_weakJet hU hD
  have hDLc (w : List (Fin 2)) (hw : w.length ≤ 2) :=
    (hDL w hw).mono_measure (Measure.restrict_mono_set _ hcell')
  obtain ⟨a, Ka, ha, has, hKa, hGa, hA⟩ := weighted_first_numerator_fiber_bounds g hDf
  obtain ⟨b, Kb, hb, hbh, hKb, hGb, _, hB⟩ := second_numerator_bulk_estimates hDLc
  obtain ⟨c, Kc, hc, _, hKc, hC⟩ :=
    hp.quarterNumeratorEndpointDerivative_sq_le hcell hg hfg hDf' lam
  let r := min a (min b (min c d))
  have hr : 0 < r := lt_min ha (lt_min hb (lt_min hc hd))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrd : r ≤ d := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrs : r ≤ 1 / 256 := hra.trans has
  have hrh : r < 1 / 2 := hrb.trans_lt hbh
  have hr1 : r < 1 := by linarith
  have hρ : quarterEndpointRadius r < 1 / 2 := by
    have hs : Real.sqrt r ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hr hr1]
  have hV := weighted_quarter_endpoint_values hU hcell hg hDg hf hDf hr hrs
  obtain ⟨hT, _, hTL⟩ := hgs.weighted_gradient_endpoint_traces hU hcell hDg hDf hr hrs
  let T := quarterGradientTrace (fun j ↦ D [j])
  let N₁ := deriv (quarterNumerator lam g)
  let N₂ := quarterNumeratorSecondDerivative lam g D
  let M₁ := quarterHalfNumeratorDerivative lam g D
  have hN : HasIntervalH2Loc 0 r (quarterNumerator lam g) N₁ N₂ :=
    fun _ _ hx hxy hy ↦ hp.quarterNumerator_hasIntervalH2_derivative_of_rep_jet
      hcell hg hfg hD hx hxy hy hr1 lam
  have hF := quarterNumerator_derivative_h1Loc (lam := lam) hU hg hgs.1 hDg
    (fun j ↦ hDL [j] (by simp)) hcell' hr1
  have hM := quarterHalfNumerator_derivative_h1Loc (lam := lam) hU hg hgs.1 hDg
    (fun j ↦ hDL [j] (by simp)) hcell' hr1
  have hN₁ : quarterNumeratorDerivative lam g D =ᵐ[volume.restrict (Ioo 0 r)] N₁ :=
    hF.hasDerivAt_ae.mono fun _ hh ↦ hh.deriv.symm
  have hN₁loc : HasIntervalH1Loc 0 r (quarterNumerator lam g) N₁ :=
    fun x y hx hxy hy ↦ (hN x y hx hxy hy).1
  have hN₂loc : HasIntervalH1Loc 0 r N₁ N₂ :=
    fun x y hx hxy hy ↦ (hN x y hx hxy hy).2
  have hGw := hGa.mono_set (Ioo_subset_Ioo le_rfl hra)
  have hG (k : ℕ) (hk : k ≤ 2) : IntegrableOn (quarterJetEnergy k 0 D) (Ioo 0 r) := by
    apply (quarterJet_energy_integrable hr1.le (D := D) (k := k) (s := 0) ?_).1
    intro w hw
    simpa only [Real.rpow_eq_pow, Real.rpow_zero, Complex.ofReal_one, div_one]
      using hDLc w (hw.le.trans hk)
  have hVG : IntegrableOn (quarterEndpointValueEnergy g) (Ioo 0 r) := by
    have h := integrable_finsetSum (Finset.univ : Finset Bool) fun side _ ↦
      (hV side).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    change Integrable (fun x ↦ (∑ side : Bool,
      ‖g (quarterEndpointRay side (quarterEndpointRadius x))‖ ^ 2) / x ^ 2)
        (volume.restrict (Ioo 0 r))
    simpa only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← Finset.sum_div] using h
  have hTG := quarterEndpointGradientEnergy_integrable hTL
  let K := Ka + 4 * (Kb + Kc + Kd)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKaK : Ka ≤ K := by dsimp [K]; linarith only [hKb.le, hKc.le, hKd]
  have hm {e : ℝ} (he : r ≤ e) :=
    ae_mono (Measure.restrict_mono_set volume (Ioo_subset_Ioo (le_refl (0 : ℝ)) he))
  have hFib := hA.filter_mono (hm hra)
  have hBulk := hB.filter_mono (hm hrb)
  have hFlux := hC.filter_mono (hm hrc)
  have hBoundary := hbd.filter_mono (hm hrd)
  have hFirst : ∀ᵐ h ∂(volume.restrict (Ioo 0 r)), ‖N₁ h‖ ^ 2 + ‖M₁ h‖ ^ 2 ≤ K *
      (quarterJetEnergy 1 (3 / 2) D h + quarterEndpointValueEnergy g h) := by
    filter_upwards [hFib, hN₁] with h hf hn
    rw [← hn]
    apply ((hf.2.2 lam).2).trans
    apply mul_le_mul_of_nonneg_right hKaK
    exact add_nonneg (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _))
  have hSecond : ∀ᵐ (h : ℝ) ∂(volume.restrict (Ioo 0 r)),
      ‖(h : ℂ) * N₂ h‖ ^ 2 ≤ K * (quarterJetEnergy 2 0 D h + quarterJetEnergy 1 0 D h +
        quarterEndpointGradientEnergy T h + quarterEndpointValueEnergy g h) := by
    filter_upwards [hBulk, hFlux, hBoundary, ae_restrict_mem measurableSet_Ioo] with h hB hC hT hh
    have hnonneg : 0 ≤ h := hh.1.le
    let E := quarterJetEnergy 2 0 D h + quarterJetEnergy 1 0 D h +
        quarterEndpointGradientEnergy T h + quarterEndpointValueEnergy g h
    have hGp (k : ℕ) : 0 ≤ quarterJetEnergy k 0 D h :=
      integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hTp : 0 ≤ quarterEndpointGradientEnergy T h :=
      div_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hnonneg
    have hVp : 0 ≤ quarterEndpointValueEnergy g h :=
      div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
    have hA' : ‖(h : ℂ) * quarterSecondBulk lam D h‖ ^ 2 ≤ Kb * E := by
      have he := (hB.2.2 lam).2
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact he.trans (mul_le_mul_of_nonneg_left (by dsimp [E]; linarith) hKb.le)
    have hC' := hC.trans (mul_le_mul_of_nonneg_left
      (show quarterEndpointGradientEnergy T h + quarterEndpointValueEnergy g h ≤ E by
        dsimp [E]; linarith [hGp 1, hGp 2]) hKc.le)
    have hT' := hT.trans (mul_le_mul_of_nonneg_left
      (show quarterEndpointGradientEnergy T h ≤ E by dsimp [E]; linarith [hGp 1, hGp 2]) hKd)
    let X := (h : ℂ) * quarterSecondBulk lam D h
    let Y := (h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ) *
        (quarterFirstBulkTrace lam D (1 / 8) h - quarterFirstBulkTrace lam D (-1 / 8) h)
    let Z := (h : ℂ) * quarterNumeratorEndpointDerivative lam g D h
    have he : (h : ℂ) * N₂ h = (X + Y) + Z := by
      simp only [N₂, quarterNumeratorSecondDerivative, X, Y, Z, mul_add, mul_assoc]
    rw [he]
    calc
      _ ≤ 2 * (‖X + Y‖ ^ 2 + ‖Z‖ ^ 2) := norm_add_sq_le _ _
      _ ≤ 2 * (2 * (Kb * E + Kd * E) + Kc * E) := by
        gcongr
        exact (norm_add_sq_le _ _).trans (by gcongr)
      _ ≤ _ := by
        change _ ≤ K * E
        have hEp : 0 ≤ E := by dsimp [E]; positivity [hGp 1, hGp 2, hTp, hVp]
        calc
          _ = (4 * Kb + 4 * Kd + 2 * Kc) * E := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hEp
  have hInt₁ := (hGw.add hVG).const_mul K
  have hInt₂ := ((((hG 2 le_rfl).add (hG 1 (by omega))).add hTG).add hVG).const_mul K
  have hLp (F : ℝ → ℂ) (hm : AEStronglyMeasurable F (volume.restrict (Ioo 0 r)))
      (hE : ∃ E : ℝ → ℝ, IntegrableOn E (Ioo 0 r) ∧
        ∀ᵐ h ∂(volume.restrict (Ioo 0 r)), ‖F h‖ ^ 2 ≤ E h) :
      MemLp F 2 (volume.restrict (Ioo 0 r)) := by
    obtain ⟨E, hi, he⟩ := hE
    apply (memLp_two_iff_integrable_sq_norm hm).2
    apply hi.mono' (hm.norm.pow 2)
    filter_upwards [he] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨r, hr, hrh, ⟨{
    first := N₁, second := N₂, halfFirst := M₁, numerator_h2 := hN, half_h1 := hM
    first_lp := hLp N₁ hN₁loc.aestronglyMeasurable_derivative ⟨_, hInt₁, hFirst.mono ?_⟩
    half_lp := hLp M₁ hM.aestronglyMeasurable_derivative ⟨_, hInt₁, hFirst.mono ?_⟩
    second_lp := hLp _ ((by fun_prop : Measurable (fun h : ℝ ↦ (h : ℂ))).aestronglyMeasurable.mul
      hN₂loc.aestronglyMeasurable_derivative) ⟨_, hInt₂, hSecond⟩
    radius := 1 / 2, radius_pos := by norm_num, radius_lt := by norm_num
    endpoint_radius_lt := hρ, gradientTrace := T, ray_trace := hT
    endpoint_value_lp := hV, endpoint_gradient_lp := hTL
    fibers_integrable := hFib.mp (hBulk.mono fun _ hB hF ↦ ⟨hF.1, hB.1, hB.2.1, hF.2.1⟩)
    mass_integrable := ⟨hGw, hG 1 (by omega), hG 2 le_rfl⟩
    forcing_level_weak := ?_
    bound := K, bound_pos := hK
    subinterval_bound := hFib.mono ?_
    first_bound := hFirst
    second_bound := hSecond.mono ?_
  }⟩⟩
  · exact fun _ he ↦ (le_add_of_nonneg_right (sq_nonneg _)).trans he
  · exact fun _ he ↦ (le_add_of_nonneg_left (sq_nonneg _)).trans he
  · exact HasWeakPartialOn.comp_quarterOrbit hr1.le
      (fun _ hp ↦ hcell' hp.1.1.1) hDg (hgs.1.mono_measure (Measure.restrict_mono_set _ hcell'))
      (fun j ↦ hDLc [j] (by simp)) 0
  · intro h hh a b ha hab hb
    exact ((hh.2.2 lam).1 a b ha hab hb).trans (mul_le_mul_of_nonneg_right hKaK
      (integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  · intro h hh
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

end EulerDipoleEigenvalues
