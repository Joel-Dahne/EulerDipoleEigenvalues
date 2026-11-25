module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.InteriorTrace
public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterCoordinates
public import EulerDipoleEigenvalues.Transport.WeightedForcing.RotationWeakGradient

/-!
# Affine Cartesian charts for the quarter endpoint rays

Blueprint: `lem:quarter-ray-affine-chart`, `lem:quarter-ray-interior-trace`.

The existing ray charts are volume-preserving affine maps. Pulling back local
H¹ therefore supplies canonical transverse traces on every admissible compact
window. The continuous-section germ fixes one trace across all these windows.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Linear part of an endpoint chart before quarter rotation. -/
def endpointRayLinear (side : Bool) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  if side then ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  else rotLinear.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

/-- Linear part after any number of Cartesian quarter rotations. -/
def rotatedRayLinear (side : Bool) : ℕ → (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)
  | 0 => endpointRayLinear side
  | n + 1 => (rotatedRayLinear side n).trans rotLinear

theorem planeAffine_endpointRayLinear (side : Bool) :
    (planeAffine (endpointRayLinear side) (quarterEndpointRay side 0) :
      (ℝ × ℝ) → ℝ × ℝ) = quarterEndpointChart side := by
  funext q
  cases side <;> ext <;>
    simp [planeAffine, endpointRayLinear, quarterEndpointRay, quarterEndpointChart,
      rotLinear, rotLift] <;> ring

theorem planeAffine_rotatedRayLinear (side : Bool) (n : ℕ) :
    (planeAffine (rotatedRayLinear side n) (rotLift^[n] (quarterEndpointRay side 0)) :
      (ℝ × ℝ) → ℝ × ℝ) = fun q ↦ rotLift^[n] (quarterEndpointChart side q) := by
  induction n with
  | zero => exact planeAffine_endpointRayLinear side
  | succ n ih =>
    funext q
    change rotLinear (rotatedRayLinear side n q) +
      rotLift^[n + 1] (quarterEndpointRay side 0) =
      rotLift^[n + 1] (quarterEndpointChart side q)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change rotLinear (rotatedRayLinear side n q) +
      rotLinear (rotLift^[n] (quarterEndpointRay side 0)) = _
    rw [← map_add]
    exact congrArg rotLift (congrFun ih q)

theorem planeAffine_quarterRayChart (k : Fin 4) (side : Bool) :
    (planeAffine (rotatedRayLinear side k.val) (rotatedQuarterEndpointRay k side 0) :
      (ℝ × ℝ) → ℝ × ℝ) = rotatedQuarterEndpointChart k side :=
  planeAffine_rotatedRayLinear side k.val

theorem measurePreserving_quarterEndpointChart (side : Bool) :
    MeasurePreserving (quarterEndpointChart side) volume volume := by
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hlin : MeasurePreserving (endpointRayLinear side) volume volume := by
    cases side
    · exact hswap.comp measurePreserving_rotLift
    · exact hswap
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h := (measurePreserving_add_right volume (quarterEndpointRay side 0)).comp hlin
  change MeasurePreserving (planeAffine (endpointRayLinear side)
    (quarterEndpointRay side 0)) volume volume at h
  rwa [planeAffine_endpointRayLinear] at h

theorem measurePreserving_rotatedQuarterEndpointChart (k : Fin 4) (side : Bool) :
    MeasurePreserving (rotatedQuarterEndpointChart k side) volume volume :=
  (measurePreserving_rotLift.iterate k.val).comp (measurePreserving_quarterEndpointChart side)

theorem continuous_rotatedQuarterEndpointChart (k : Fin 4) (side : Bool) :
    Continuous (rotatedQuarterEndpointChart k side) := by
  rw [← planeAffine_quarterRayChart]
  exact (planeAffine _ _).continuous

theorem quarterRayChart_zero (k : Fin 4) (side : Bool) (r : ℝ) :
    rotatedQuarterEndpointChart k side (r, 0) = rotatedQuarterEndpointRay k side r := by
  cases side <;> rfl

theorem localRadius_quarterRayChart (k : Fin 4) (side : Bool) (q : ℝ × ℝ) :
    localRadius (rotatedQuarterEndpointRay k side 0)
      (rotatedQuarterEndpointChart k side q) = localRadius 0 q := by
  fin_cases k <;> cases side <;>
    simp [rotatedQuarterEndpointChart, rotatedQuarterEndpointRay, quarterEndpointChart,
      quarterEndpointRay, Function.iterate_succ_apply', rotLift, localRadius] <;>
    congr 1 <;> ring

theorem localRadius_quarterEndpointRay (k : Fin 4) (side : Bool) (r : ℝ) :
    localRadius (rotatedQuarterEndpointRay k side 0)
      (rotatedQuarterEndpointRay k side r) = |r| := by
  rw [← quarterRayChart_zero k side r, localRadius_quarterRayChart]
  simp [localRadius, Real.sqrt_sq_eq_abs]

theorem quarterRayCenter_mem_saddleSet (k : Fin 4) (side : Bool) :
    rotatedQuarterEndpointRay k side 0 ∈ saddleSet := by
  have h1 : (Real.pi, (0 : ℝ)) ∈ saddleSet := ⟨1, 0, by decide, by simp⟩
  have hm1 : (-Real.pi, (0 : ℝ)) ∈ saddleSet := ⟨-1, 0, by decide, by simp⟩
  have h2 : ((0 : ℝ), Real.pi) ∈ saddleSet := ⟨0, 1, by decide, by simp⟩
  have hm2 : ((0 : ℝ), -Real.pi) ∈ saddleSet := ⟨0, -1, by decide, by simp⟩
  fin_cases k <;> cases side
  all_goals first
    | simpa [rotatedQuarterEndpointRay, quarterEndpointRay, Function.iterate_succ_apply',
        rotLift] using h1
    | simpa [rotatedQuarterEndpointRay, quarterEndpointRay, Function.iterate_succ_apply',
        rotLift] using hm1
    | simpa [rotatedQuarterEndpointRay, quarterEndpointRay, Function.iterate_succ_apply',
        rotLift] using h2
    | simpa [rotatedQuarterEndpointRay, quarterEndpointRay, Function.iterate_succ_apply',
        rotLift] using hm2

theorem quarterRayRectangle_subset_disk {R δ : ℝ} (hδ : 0 < δ) (hR : 2 * δ < R)
    (k : Fin 4) (side : Bool) :
    rotatedQuarterEndpointChart k side '' (Icc 0 δ ×ˢ Icc (-δ) δ) ⊆
      localDisk (rotatedQuarterEndpointRay k side 0) R := by
  rintro _ ⟨q, hq, rfl⟩
  change localRadius _ _ < R
  rw [localRadius_quarterRayChart]
  have hRp : 0 < R := by linarith
  apply (Real.sqrt_lt' hRp).2
  have hx : q.1 ^ 2 ≤ δ ^ 2 := (sq_le_sq₀ hq.1.1 hδ.le).2 hq.1.2
  have hy : q.2 ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg q.2) hδ.le).2 (abs_le.mpr hq.2)
  have hbig := (sq_lt_sq₀ (by positivity : 0 ≤ 2 * δ) hRp.le).2 hR
  dsimp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
  nlinarith only [hx, hy, hbig, sq_nonneg δ]

theorem MemSobolevOn.comp_quarterRayChart {m : ℕ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn m U F)
    (k : Fin 4) (side : Bool) :
    MemSobolevOn m (rotatedQuarterEndpointChart k side ⁻¹' U)
      (fun q ↦ F (rotatedQuarterEndpointChart k side q)) := by
  have hm : MeasurePreserving
      (planeAffine (rotatedRayLinear side k.val) (rotatedQuarterEndpointRay k side 0)) := by
    rw [planeAffine_quarterRayChart]
    exact measurePreserving_rotatedQuarterEndpointChart k side
  simpa only [planeAffine_quarterRayChart, Function.comp_def] using
    hF.comp_planeAffine _ _ hm hU

theorem MemSobolevLocOn.comp_quarterRayChart {m : ℕ} {U : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn m U F) (k : Fin 4) (side : Bool) :
    MemSobolevLocOn m (rotatedQuarterEndpointChart k side ⁻¹' U)
      (fun q ↦ F (rotatedQuarterEndpointChart k side q)) := by
  have hm : MeasurePreserving
      (planeAffine (rotatedRayLinear side k.val) (rotatedQuarterEndpointRay k side 0)) := by
    rw [planeAffine_quarterRayChart]
    exact measurePreserving_rotatedQuarterEndpointChart k side
  simpa only [planeAffine_quarterRayChart, Function.comp_def] using
    hF.comp_planeAffine _ _ hm

/-- One canonical trace works for every admissible transverse rectangle, including
rectangles wider than the particular strip used to estimate its radial norm. -/
theorem MemSobolevLocOn.quarterRayTrace {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevLocOn 1 U F) (ρ : ℝ) (k : Fin 4) (side : Bool) :
    HasQuarterRayTrace U ρ k side F
      (interiorChartTrace (rotatedQuarterEndpointChart k side) F) := by
  intro a b ha hab hb w hw hrect
  have hcl : closure (Ioo a b ×ˢ Ioo (-w) w) = Icc a b ×ˢ Icc (-w) w := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo (by linarith : -w ≠ w)]
  have hH1 := hF.comp_quarterRayChart k side (Ioo a b ×ˢ Ioo (-w) w)
    (isOpen_Ioo.prod isOpen_Ioo) (by rw [hcl]; exact isCompact_Icc.prod isCompact_Icc)
    (by rw [hcl]; exact image_subset_iff.mp hrect)
  exact (hH1.hasInteriorChartTrace hab (neg_neg_of_pos hw) hw).1

end EulerDipoleEigenvalues
