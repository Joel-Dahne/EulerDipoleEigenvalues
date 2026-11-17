import NoEmbeddedEigenvalues.Analysis.WeightedConeTrace
import NoEmbeddedEigenvalues.QuarterRayCharts
import NoEmbeddedEigenvalues.SaddleDistance
import NoEmbeddedEigenvalues.LogarithmicRayTransport

/-!
# Weighted continuous forcing values on the quarter endpoint rays

Blueprint: `lem:quarter-endpoint-cones`, `lem:weighted-quarter-ray-values`,
`lem:weighted-endpoint-value-transport`.

The small Cartesian endpoint cone lies in the cell and its first coordinate
is exactly saddle distance in the product metric. Shrinking-rectangle traces
therefore use the original weighted forcing and supplied weak gradient.
Only the continuous forcing is evaluated on a ray, never its raw gradient.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real
open scoped Topology

/-- On the interior endpoint cone the product-metric saddle distance is exactly
its radial coordinate. The whole cone lies in the positive physical cell. -/
theorem quarterEndpointChart_cone (side : Bool) {q : ℝ × ℝ}
    (hq : q ∈ cartesianRayCone (1 / 2)) :
    quarterEndpointChart side q ∈ cellSquare ∧
      saddleDist (quarterEndpointChart side q) = q.1 := by
  have ht := abs_lt.mp hq.2
  have hp := Real.pi_gt_three
  have hs : quarterEndpointRay side 0 ∈ saddleSet := by
    simpa only [rotatedQuarterEndpointRay, Fin.val_zero, Function.iterate_zero, id_eq]
      using quarterRayCenter_mem_saddleSet 0 side
  have hd : dist (quarterEndpointChart side q) (quarterEndpointRay side 0) = q.1 := by
    cases side
    · simp only [quarterEndpointChart, quarterEndpointRay, Bool.false_eq_true,
        ↓reduceIte, sub_zero, Prod.dist_eq, Real.dist_eq]
      rw [show Real.pi - q.1 - Real.pi = -q.1 by ring, abs_neg, abs_of_pos hq.1.1,
        max_eq_left hq.2.le]
    · simp only [quarterEndpointChart, quarterEndpointRay, ↓reduceIte,
        add_zero, sub_zero, Prod.dist_eq, Real.dist_eq]
      rw [show -Real.pi + q.1 - -Real.pi = q.1 by ring,
        abs_of_pos hq.1.1, max_eq_right hq.2.le]
  refine ⟨?_, ?_⟩
  · cases side <;>
      simp [quarterEndpointChart, cellSquare, diagCoord, abs_lt]
    all_goals constructor <;> constructor <;> linarith [hq.1.1, hq.1.2]
  · rw [saddleDist_eq_dist hs (by rw [hd]; linarith [hq.1.2]), hd]

/-- Actual weighted bulk norms control the continuous forcing on either ray.
The derivative is the original specified Cartesian weak derivative. -/
theorem weighted_quarter_ray_values {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {g : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ContinuousOn g U) (hD : ∀ j, HasWeakPartialOn U j g (D j))
    (hf : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) (side : Bool) :
    MemLp (fun r ↦ g (quarterEndpointRay side r) / (r : ℂ) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 (1 / 2))) := by
  let C := cartesianRayCone (1 / 2)
  let Φ := quarterEndpointChart side
  let j : Fin 2 := if side then 0 else 1
  have hCm : MeasurableSet C :=
    (measurable_fst measurableSet_Ioo).inter
      (measurableSet_lt continuous_snd.abs.measurable measurable_fst)
  have hΦ : Continuous Φ := by
    change Continuous (quarterEndpointChart side)
    rw [← planeAffine_endpointRayLinear]
    exact (planeAffine _ _).continuous
  have hCU : C ⊆ Φ ⁻¹' U := fun q hq ↦ hcell (subset_closure (quarterEndpointChart_cone side hq).1)
  have hCC : C ⊆ Φ ⁻¹' cellSquare := fun q hq ↦ (quarterEndpointChart_cone side hq).1
  have hmp : MeasurePreserving
      (planeAffine (endpointRayLinear side) (quarterEndpointRay side 0)) := by
    rw [planeAffine_endpointRayLinear]
    exact measurePreserving_quarterEndpointChart side
  have hw : HasWeakPartialOn (Φ ⁻¹' U) 1 (g ∘ Φ) (D j ∘ Φ) := by
    have h := HasWeakPartialOn.comp_planeAffine _ _ hmp hU hD 1
    rw [planeAffine_endpointRayLinear] at h
    cases side <;>
      simpa [j, Φ, affineCoeff, planeDirection, endpointRayLinear, axisCoord,
        rotLinear, rotLift, Function.comp_def] using h
  have hPull {f : ℝ × ℝ → ℂ} (h : MemLp f 2 (volume.restrict cellSquare)) :
      MemLp (f ∘ Φ) 2 (volume.restrict C) :=
    (h.comp_measurePreserving ((measurePreserving_quarterEndpointChart side).restrict_preimage
      isOpen_cellSquare.measurableSet)).mono_measure (Measure.restrict_mono_set _ hCC)
  have hF : MemLp (fun q ↦ g (Φ q) / (q.1 : ℂ) ^ 2) 2 (volume.restrict C) := by
    apply (hPull hf).ae_eq
    filter_upwards [ae_restrict_mem hCm] with q hq
    dsimp only [Function.comp_def]
    rw [(quarterEndpointChart_cone side hq).2]
  have hS : MemLp (fun q : ℝ × ℝ ↦ (Real.sqrt q.1 : ℂ)) ⊤ (volume.restrict C) := by
    apply memLp_top_of_bound (by fun_prop) 1
    filter_upwards [ae_restrict_mem hCm] with q hq
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by linarith [hq.1.2])
  have hDL : MemLp (fun q ↦ D j (Φ q) / (q.1 : ℂ)) 2 (volume.restrict C) := by
    apply (hS.mul (hPull (hDf j))).ae_eq
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
  have htrace := (weighted_cone_trace (by norm_num : (0 : ℝ) < 1 / 2) (hw.mono hCU)
    (hg.comp hΦ.continuousOn hCU) hF hDL).1
  have hz (r : ℝ) : Φ (r, 0) = quarterEndpointRay side r := by cases side <;> rfl
  simpa only [Function.comp_def, hz] using htrace

/-- The radial-to-level map transfers actual r⁻³ value mass to actual h⁻²
value mass. Continuity supplies measurability before the Jacobian comparison. -/
theorem memLp_endpoint_value_of_ray {b ρ : ℝ} (hb : b < 1)
    (hρ : quarterEndpointRadius b < ρ) {B : ℝ → ℂ}
    (hc : ContinuousOn B (Ioo 0 ρ))
    (hray : MemLp (fun r ↦ B r / (r : ℂ) / (Real.sqrt r : ℂ)) 2
      (volume.restrict (Ioo 0 ρ))) :
    MemLp (fun h ↦ B (quarterEndpointRadius h) / (h : ℂ)) 2
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
      ‖B r / (r : ℂ) / (Real.sqrt r : ℂ)‖ ^ 2 = ‖B r‖ ^ 2 / r ^ 3 := by
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hr),
      div_pow, div_pow, Real.sq_sqrt hr.le, div_div]
    congr 1
  have hi : IntegrableOn (fun r ↦ ‖B r‖ ^ 2 / r ^ 3) (Ioo 0 ρ) :=
    (hray.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
      ((ae_restrict_mem measurableSet_Ioo).mono fun r hr ↦ hsq r hr.1)
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    hder hinj _).mp (hi.mono_set hsub)
  have hrad : ContinuousOn quarterEndpointRadius (Ioo 0 b) :=
    fun h hh ↦ (hder h hh).continuousWithinAt
  have hmC : ContinuousOn (fun h ↦ B (quarterEndpointRadius h) / (h : ℂ)) (Ioo 0 b) :=
    (hc.comp hrad (fun h hh ↦ hsub ⟨h, hh, rfl⟩)).div
      Complex.continuous_ofReal.continuousOn (fun h hh ↦ Complex.ofReal_ne_zero.mpr hh.1.ne')
  have hm : AEStronglyMeasurable (fun h ↦ B (quarterEndpointRadius h) / (h : ℂ))
      (volume.restrict (Ioo 0 b)) := hmC.aestronglyMeasurable measurableSet_Ioo
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply (hj.const_mul 64).mono' (hm.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hh0 : 0 < h := hh.1
  have hh1 := hh.2.trans hb
  have hs := Real.sqrt_pos.mpr hh.1
  have ht := Real.sqrt_pos.mpr (sub_pos.mpr hh1)
  have hr := quarterEndpointRadius_pos hh.1
  have hJ : 0 < 1 / (Real.sqrt h * Real.sqrt (1 - h)) := by positivity
  have hjlow : Real.sqrt h ≤ h * (1 / (Real.sqrt h * Real.sqrt (1 - h))) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (mul_pos hs ht)).mpr
    nlinarith [Real.sq_sqrt hh.1.le,
      mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr (by linarith : 1 - h ≤ 1)) hh.1.le]
  have hjac : quarterEndpointRadius h ^ 3 ≤
      64 * h ^ 2 * (1 / (Real.sqrt h * Real.sqrt (1 - h))) := by
    have hcube := pow_le_pow_left₀ hr.le (quarterEndpointRadius_le_four_sqrt hh.1 hh1) 3
    have hm := mul_le_mul_of_nonneg_left hjlow (by positivity : 0 ≤ 64 * h)
    nlinarith [Real.sq_sqrt hh.1.le]
  have hratio : 1 / h ^ 2 ≤
      64 * (1 / (Real.sqrt h * Real.sqrt (1 - h))) / quarterEndpointRadius h ^ 3 :=
    (div_le_div_iff₀ (sq_pos_of_pos hh.1) (pow_pos hr 3)).2 (by nlinarith [hjac])
  change |‖B (quarterEndpointRadius h) / (h : ℂ)‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _), norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh.1, div_pow]
  change ‖B (quarterEndpointRadius h)‖ ^ 2 / h ^ 2 ≤
    64 * (|1 / (Real.sqrt h * Real.sqrt (1 - h))| •
      (‖B (quarterEndpointRadius h)‖ ^ 2 / quarterEndpointRadius h ^ 3))
  rw [abs_of_pos hJ, smul_eq_mul]
  convert mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖B (quarterEndpointRadius h)‖) using 1 <;>
    ring

/-- The original weighted forcing and specified first gradient give actual
moving-endpoint value norms, with one frequency-independent collar. -/
theorem weighted_quarter_endpoint_values {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {g : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ContinuousOn g U) (hD : ∀ j, HasWeakPartialOn U j g (D j))
    (hf : MemLp (fun p ↦ g p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 256) :
    ∀ side : Bool, MemLp (fun h ↦ g (quarterEndpointRay side (quarterEndpointRadius h)) /
      (h : ℂ)) 2 (volume.restrict (Ioo 0 b)) := by
  have hb1 : b < 1 := by linarith
  have hρ : quarterEndpointRadius b < 1 / 2 := by
    have hs : Real.sqrt b ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hb hb1]
  intro side
  apply memLp_endpoint_value_of_ray hb1 hρ _
    (weighted_quarter_ray_values hU hcell hg hD hf hDf side)
  have hΦ : Continuous (quarterEndpointRay side) := by
    cases side
    · change Continuous (fun r : ℝ ↦ (Real.pi - r, (0 : ℝ)))
      fun_prop
    · change Continuous (fun r : ℝ ↦ ((0 : ℝ), -Real.pi + r))
      fun_prop
  exact hg.comp hΦ.continuousOn (fun r hr ↦ hcell (subset_closure
    (quarterEndpointChart_cone side (q := (r, 0)) ⟨hr, by simpa using hr.1⟩).1))

/-- The canonical moving orbit endpoints lie on the fixed Cartesian rays. -/
theorem dipoleOrbit_quarterEndpointRay {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (side : Bool) :
    dipoleOrbit h (if side then eighthPeriod h else -eighthPeriod h) =
      quarterEndpointRay side (quarterEndpointRadius h) := by
  obtain ⟨hp, hm⟩ := diagCoord_dipoleOrbit_eighthPeriod h0 h1
  cases side
  · have hx := congrArg Prod.fst hm
    have hy := congrArg Prod.snd hm
    dsimp only [diagCoord] at hx hy
    rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hx hy
    ext <;> simp only [quarterEndpointRay, quarterEndpointRadius, Bool.false_eq_true,
      ↓reduceIte] <;> linarith
  · have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp only [diagCoord] at hx hy
    rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hx hy
    ext <;> simp only [quarterEndpointRay, quarterEndpointRadius, ↓reduceIte] <;> linarith

end NoEmbeddedEigenvalues
