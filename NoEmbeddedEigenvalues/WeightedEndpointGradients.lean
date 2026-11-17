import NoEmbeddedEigenvalues.Analysis.CanonicalConeTrace
import NoEmbeddedEigenvalues.WeightedEndpointValues

/-!
# Canonical gradient traces at the moving quarter endpoints

Blueprint: `lem:weighted-gradient-ray-traces`,
`lem:gradient-endpoint-change-variables`.

Only canonical interior Sobolev traces are evaluated on the rays. The radial
Jacobian transports their r⁻¹ mass to h⁻¹ mass. It also supplies measurability
of the composed trace, without continuous gradient representatives.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Canonical interior-section trace of the supplied Cartesian first derivative.
Regularity and weighted norms are established separately. -/
def quarterGradientTrace (D : Fin 2 → ℝ × ℝ → ℂ) (side : Bool) (j : Fin 2) : ℝ → ℂ :=
  interiorChartTrace (rotatedQuarterEndpointChart 0 side) (D j)

/-- H¹ and the supplied weighted value norm give a canonical endpoint-ray
trace with finite r⁻¹ mass, on every admissible transverse window. -/
theorem MemSobolevOn.weighted_quarter_ray_trace
    {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevOn 1 U F) (hU : IsOpen U) (hcell : closure cellSquare ⊆ U)
    (hFw : MemLp (fun p ↦ F p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) (side : Bool) :
    HasQuarterRayTrace U (1 / 2) 0 side F
      (interiorChartTrace (rotatedQuarterEndpointChart 0 side) F) ∧
    MemLp (fun r ↦ interiorChartTrace (rotatedQuarterEndpointChart 0 side) F r /
      (Real.sqrt r : ℂ)) 2 (volume.restrict (Ioo 0 (1 / 2))) := by
  refine ⟨hF.memSobolevLocOn.quarterRayTrace (1 / 2) 0 side, ?_⟩
  let C := cartesianRayCone (1 / 2)
  let Φ := quarterEndpointChart side
  let j : Fin 2 := if side then 0 else 1
  choose E hE hEL using hF.2
  have hCm : MeasurableSet C :=
    (measurable_fst measurableSet_Ioo).inter
      (measurableSet_lt continuous_snd.abs.measurable measurable_fst)
  have hCU : C ⊆ Φ ⁻¹' U := fun q hq ↦ hcell (subset_closure (quarterEndpointChart_cone side hq).1)
  have hCC : C ⊆ Φ ⁻¹' cellSquare := fun q hq ↦ (quarterEndpointChart_cone side hq).1
  have hmp : MeasurePreserving
      (planeAffine (endpointRayLinear side) (quarterEndpointRay side 0)) := by
    rw [planeAffine_endpointRayLinear]
    exact measurePreserving_quarterEndpointChart side
  have hw : HasWeakPartialOn (Φ ⁻¹' U) 1 (F ∘ Φ) (E j ∘ Φ) := by
    have h := HasWeakPartialOn.comp_planeAffine _ _ hmp hU hE 1
    rw [planeAffine_endpointRayLinear] at h
    cases side <;>
      simpa [j, Φ, affineCoeff, planeDirection, endpointRayLinear, axisCoord,
        rotLinear, rotLift, Function.comp_def] using h
  have hPull {f : ℝ × ℝ → ℂ} (h : MemLp f 2 (volume.restrict cellSquare)) :
      MemLp (f ∘ Φ) 2 (volume.restrict C) :=
    (h.comp_measurePreserving ((measurePreserving_quarterEndpointChart side).restrict_preimage
      isOpen_cellSquare.measurableSet)).mono_measure (Measure.restrict_mono_set _ hCC)
  have hS : MemLp (fun q : ℝ × ℝ ↦ (Real.sqrt q.1 : ℂ)) ⊤ (volume.restrict C) := by
    apply memLp_top_of_bound (by fun_prop) 1
    filter_upwards [ae_restrict_mem hCm] with q hq
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by linarith [hq.1.2])
  have hDL : MemLp (fun q ↦ F (Φ q) / (q.1 : ℂ)) 2 (volume.restrict C) := by
    apply (hS.mul (hPull hFw)).ae_eq
    filter_upwards [ae_restrict_mem hCm] with q hq
    have he : Real.rpow q.1 (3 / 2) = q.1 * Real.sqrt q.1 := by
      simp only [Real.rpow_eq_pow]
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hq.1.1.ne',
        ← Real.sqrt_eq_rpow]
      ring
    dsimp only [Function.comp_def, Pi.mul_apply]
    rw [(quarterEndpointChart_cone side hq).2, he]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.1.1.ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq.1.1).ne']
  have hEU : MemLp (E j) 2 (volume.restrict U) := hEL j
  have hEC := hEU.mono_measure
    (Measure.restrict_mono_set _ (subset_closure.trans hcell))
  have ht := (canonical_weighted_cone_trace (by norm_num : (0 : ℝ) < 1 / 2)
    (hw.mono hCU) hDL (hPull hEC)).1
  exact ht

/-- The endpoint-radius Jacobian transfers canonical r⁻¹ trace mass to h⁻¹
mass. Integrability of a complex pullback establishes its measurability. -/
theorem memLp_endpoint_gradient_of_ray {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {T : ℝ → ℂ}
    (hray : MemLp (fun r ↦ T r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 ρ))) :
    MemLp (fun h ↦ T (quarterEndpointRadius h) / (Real.sqrt h : ℂ)) 2
      (volume.restrict (Ioo 0 b)) := by
  have hder (h : ℝ) (hh : h ∈ Ioo 0 b) :=
    (hasDerivAt_quarterEndpointRadius hh.1 (hh.2.trans hb)).hasDerivWithinAt (s := Ioo 0 b)
  have hinj : InjOn quarterEndpointRadius (Ioo 0 b) := by
    intro x hx y hy he
    have hs : Real.arcsin (Real.sqrt x) = Real.arcsin (Real.sqrt y) := by
      unfold quarterEndpointRadius at he
      linarith
    have hs' := congrArg Real.sin hs
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg x])
        (Real.sqrt_le_one.mpr (hx.2.trans hb).le),
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg y])
        (Real.sqrt_le_one.mpr (hy.2.trans hb).le)] at hs'
    have heq := congrArg (fun z : ℝ ↦ z ^ 2) hs'
    simpa only [Real.sq_sqrt hx.1.le, Real.sq_sqrt hy.1.le] using heq
  have hsub : quarterEndpointRadius '' Ioo 0 b ⊆ Ioo 0 ρ := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨quarterEndpointRadius_pos hh.1,
      (monotone_quarterEndpointRadius hh.2.le).trans_lt hρ⟩
  have hsq (r : ℝ) (hr : 0 < r) :
      ‖T r / (Real.sqrt r : ℂ)‖ ^ 2 = ‖T r‖ ^ 2 / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hr.le]
  have hi : IntegrableOn (fun r ↦ ‖T r‖ ^ 2 / r) (Ioo 0 ρ) :=
    (hray.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
      ((ae_restrict_mem measurableSet_Ioo).mono fun r hr ↦ hsq r hr.1)
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    hder hinj _).mp (hi.mono_set hsub)
  have hiC : IntegrableOn (fun r ↦ T r / (Real.sqrt r : ℂ)) (Ioo 0 ρ) :=
    hray.integrable (by norm_num)
  have hjC := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    hder hinj _).mp (hiC.mono_set hsub)
  let δ := fun h : ℝ ↦ 1 / (Real.sqrt h * Real.sqrt (1 - h))
  have hδ (h : ℝ) (hh : h ∈ Ioo 0 b) : 0 < δ h := by
    dsimp only [δ]
    exact div_pos zero_lt_one (mul_pos (Real.sqrt_pos.mpr hh.1)
      (Real.sqrt_pos.mpr (sub_pos.mpr (hh.2.trans hb))))
  have hmcoef : Measurable (fun h : ℝ ↦ (Real.sqrt (quarterEndpointRadius h) : ℂ) /
      ((δ h : ℂ) * (Real.sqrt h : ℂ))) := by
    dsimp only [δ, quarterEndpointRadius]
    fun_prop
  have hm : AEStronglyMeasurable
      (fun h ↦ T (quarterEndpointRadius h) / (Real.sqrt h : ℂ))
      (volume.restrict (Ioo 0 b)) := by
    apply (hjC.aestronglyMeasurable.mul hmcoef.aestronglyMeasurable).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    change (|δ h| • (T (quarterEndpointRadius h) /
      (Real.sqrt (quarterEndpointRadius h) : ℂ))) *
        ((Real.sqrt (quarterEndpointRadius h) : ℂ) / ((δ h : ℂ) *
          (Real.sqrt h : ℂ))) = _
    rw [abs_of_pos (hδ h hh), Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr (hδ h hh).ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (quarterEndpointRadius_pos hh.1)).ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hh.1).ne']
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply (hj.const_mul 4).mono' (hm.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hh1 := hh.2.trans hb
  have hs := Real.sqrt_pos.mpr hh.1
  have ht := Real.sqrt_pos.mpr (sub_pos.mpr hh1)
  have hr := quarterEndpointRadius_pos hh.1
  have hjlow : Real.sqrt h ≤ h * δ h := by
    dsimp only [δ]
    rw [mul_one_div]
    apply (le_div_iff₀ (mul_pos hs ht)).mpr
    nlinarith [Real.sq_sqrt hh.1.le,
      mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr (by linarith [hh.1] : 1 - h ≤ 1)) hh.1.le]
  have hjac : quarterEndpointRadius h ≤ 4 * h * δ h := by
    linarith [quarterEndpointRadius_le_four_sqrt hh.1 hh1]
  have hratio : 1 / h ≤ 4 * δ h / quarterEndpointRadius h :=
    (div_le_div_iff₀ hh.1 hr).2 (by nlinarith [hjac])
  change |‖T (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _), norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hh.1.le]
  change ‖T (quarterEndpointRadius h)‖ ^ 2 / h ≤
    4 * (|δ h| • (‖T (quarterEndpointRadius h)‖ ^ 2 / quarterEndpointRadius h))
  rw [abs_of_pos (hδ h hh), smul_eq_mul]
  convert mul_le_mul_of_nonneg_right hratio
    (sq_nonneg ‖T (quarterEndpointRadius h)‖) using 1 <;> ring

/-- H² identifies the given weak first derivatives as H¹ functions. Their
canonical traces have both radial and actual moving-endpoint gradient mass. -/
theorem MemSobolevOn.weighted_gradient_endpoint_traces
    {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} (hs : MemSobolevOn 2 U f)
    (hU : IsOpen U) (hcell : closure cellSquare ⊆ U) {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 256) :
    (∀ side j, HasQuarterRayTrace U (1 / 2) 0 side (D j) (quarterGradientTrace D side j)) ∧
    (∀ side j, MemLp (fun r ↦ quarterGradientTrace D side j r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 (1 / 2)))) ∧
    (∀ side j, MemLp (fun h ↦ quarterGradientTrace D side j (quarterEndpointRadius h) /
      (Real.sqrt h : ℂ)) 2 (volume.restrict (Ioo 0 b))) := by
  have hgrad (j : Fin 2) : MemSobolevOn 1 U (D j) := by
    obtain ⟨G, hG, hGs⟩ := hs.2 j
    exact (show MemSobolevOn 1 U G from hGs).congr_ae_on
      hU.measurableSet (hG.ae_eq hU (hD j))
  have htrace (side : Bool) (j : Fin 2) :=
    (hgrad j).weighted_quarter_ray_trace hU hcell (hDw j) side
  have hb1 : b < 1 := by linarith
  have hρ : quarterEndpointRadius b < 1 / 2 := by
    have hsqrt : Real.sqrt b ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hb hb1]
  refine ⟨fun side j ↦ (htrace side j).1, fun side j ↦ (htrace side j).2, ?_⟩
  intro side j
  exact memLp_endpoint_gradient_of_ray hb1 hρ (htrace side j).2

/-- The original transport hypotheses produce gradient traces; they are not an
additional ray or pointwise-gradient premise. The supplied derivatives are retained. -/
theorem IsTransportPair.weighted_gradient_endpoint_traces
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 256) :
    (∀ side j, HasQuarterRayTrace U (1 / 2) 0 side (D j) (quarterGradientTrace D side j)) ∧
    (∀ side j, MemLp (fun r ↦ quarterGradientTrace D side j r / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 (1 / 2)))) ∧
    (∀ side j, MemLp (fun h ↦ quarterGradientTrace D side j (quarterEndpointRadius h) /
      (Real.sqrt h : ℂ)) 2 (volume.restrict (Ioo 0 b))) :=
  hp.memSobolevOn.weighted_gradient_endpoint_traces hp.isOrbitUnion.1 hcell hD hDw hb hb'

/-- The endpoint-gradient energy is genuinely integrable once its four
canonical components have their actual weighted L² norms. -/
theorem quarterEndpointGradientEnergy_integrable {b : ℝ}
    {T : Bool → Fin 2 → ℝ → ℂ}
    (hT : ∀ side j, MemLp (fun h ↦ T side j (quarterEndpointRadius h) /
      (Real.sqrt h : ℂ)) 2 (volume.restrict (Ioo 0 b))) :
    IntegrableOn (quarterEndpointGradientEnergy T) (Ioo 0 b) := by
  have hi : IntegrableOn (fun h ↦ ∑ side : Bool, ∑ j : Fin 2,
      ‖T side j (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2) (Ioo 0 b) := by
    exact integrable_finsetSum _ fun side _ ↦ integrable_finsetSum _ fun j _ ↦
      (hT side j).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  simp only [quarterEndpointGradientEnergy, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hh.1.le, Finset.sum_div]

/-- Actual canonical gradient endpoint energy follows from precisely the
original weighted first-gradient input and the standing transport pair. -/
theorem IsTransportPair.weighted_gradient_endpoint_energy
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 256) :
    IntegrableOn (quarterEndpointGradientEnergy (quarterGradientTrace D)) (Ioo 0 b) :=
  quarterEndpointGradientEnergy_integrable
    (hp.weighted_gradient_endpoint_traces hcell hD hDw hb hb').2.2

end NoEmbeddedEigenvalues
