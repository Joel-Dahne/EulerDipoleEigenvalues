module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets

/-!
# Affine pullback of specified weak jets

Blueprint: `def:affine-jet`, `lem:affine-jet-pullback`.

Derivative indices transform with the linear part of the affine chart. The
recursive formula expands every derivative into its two Cartesian components.
Measure-preserving affine charts preserve square integrability; a radius identity
then transfers radial weights without differentiating them.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff Topology

/-- The affine chart with linear part A and translation c. -/
def planeAffine (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := A.toHomeomorph.trans (Homeomorph.addRight c)

@[simp] theorem planeAffine_apply (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c p : ℝ × ℝ) :
    planeAffine A c p = A p + c := rfl

theorem contDiff_planeAffine (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) :
    ContDiff ℝ ∞ (planeAffine A c) := A.contDiff.add contDiff_const

theorem contDiff_planeAffine_symm (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) :
    ContDiff ℝ ∞ (planeAffine A c).symm :=
  A.symm.contDiff.comp (contDiff_id.sub contDiff_const)

/-- Unit absolute determinant suffices for preservation of planar volume. -/
theorem measurePreserving_planeAffine (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ)
    (hdet : |LinearMap.det (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| = 1) :
    MeasurePreserving (planeAffine A c) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hne : LinearMap.det (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 := by
    intro h
    simp [h] at hdet
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  change Measure.map A volume = _ at hm
  have hA : MeasurePreserving A volume volume := by
    refine ⟨A.continuous.measurable, ?_⟩
    simpa only [abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul] using hm
  exact (measurePreserving_add_right volume c).comp hA

/-- Cartesian unit direction. -/
def planeDirection (j : Fin 2) : ℝ × ℝ := if j = 0 then (1, 0) else (0, 1)

/-- Matrix coefficient of the linear part of the chart. -/
def affineCoeff (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (i j : Fin 2) : ℂ :=
  (axisCoord i (A (planeDirection j)) : ℂ)

private theorem coordPartial_fderiv {u : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u p) (j : Fin 2) :
    coordPartial j u p = fderiv ℝ u p (planeDirection j) := by
  unfold coordPartial planeDirection
  split_ifs
  · exact partialX_eq_fderiv hu
  · exact partialY_eq_fderiv hu

/-- Classical chain rule for an affine chart. -/
theorem coordPartial_comp_planeAffine {u : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u)
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) (j : Fin 2) (p : ℝ × ℝ) :
    coordPartial j (u ∘ planeAffine A c) p =
      affineCoeff A 0 j * coordPartial 0 u (planeAffine A c p) +
        affineCoeff A 1 j * coordPartial 1 u (planeAffine A c p) := by
  have hT := A.hasFDerivAt.add_const c (x := p)
  have hc := (hu (planeAffine A c p)).hasFDerivAt.comp p hT
  rw [coordPartial_fderiv hc.differentiableAt, hc.fderiv,
    ContinuousLinearMap.comp_apply, coordPartial_fderiv (hu _) 0,
    coordPartial_fderiv (hu _) 1]
  have he : A (planeDirection j) =
      (A (planeDirection j)).1 • planeDirection 0 +
        (A (planeDirection j)).2 • planeDirection 1 := by
    ext <;> simp [planeDirection]
  change (fderiv ℝ u (planeAffine A c p)) (A (planeDirection j)) = _
  rw [he, map_add, map_smul, map_smul]
  simp [affineCoeff, axisCoord, Complex.real_smul]

/-- Pullback of a jet, with every derivative index transformed by A. -/
def affineJet (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : List (Fin 2) → ℝ × ℝ → ℂ
  | [] => D [] ∘ planeAffine A c
  | j :: w => fun p ↦
      affineCoeff A 0 j * affineJet A c (fun v ↦ D (0 :: v)) w p +
        affineCoeff A 1 j * affineJet A c (fun v ↦ D (1 :: v)) w p

section Pullback
variable (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ)
variable (hmp : MeasurePreserving (planeAffine A c))
include hmp

/-- Affine pullback preserves L² on the preimage domain. -/
theorem memLp_comp_planeAffine {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (f ∘ planeAffine A c) 2 (volume.restrict (planeAffine A c ⁻¹' U)) := by
  apply (planeAffine A c).measurableEmbedding.memLp_map_measure_iff.1
  rw [← Measure.restrict_map (planeAffine A c).continuous.measurable hU, hmp.map_eq]
  exact hf

/-- Local integrability is preserved by the affine chart. -/
theorem locallyIntegrableOn_comp_planeAffine {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : LocallyIntegrableOn f U) :
    LocallyIntegrableOn (f ∘ planeAffine A c) (planeAffine A c ⁻¹' U) := by
  apply (locallyIntegrableOn_iff (hU.preimage (planeAffine A c).continuous).isLocallyClosed).2
  intro K hKU hK
  have hi := hf.integrableOn_compact_subset (image_subset_iff.2 hKU)
    (hK.image (planeAffine A c).continuous)
  have him : IntegrableOn f ((planeAffine A c) '' K)
      (Measure.map (planeAffine A c) volume) := by rwa [hmp.map_eq]
  have hp := (integrableOn_map_equiv (planeAffine A c).toMeasurableEquiv).1 him
  simpa only [Homeomorph.toMeasurableEquiv_coe,
    (planeAffine A c).injective.preimage_image] using hp

/-- Weak affine chain rule, mixing both derivative components. -/
theorem HasWeakPartialOn.comp_planeAffine {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {d : Fin 2 → ℝ × ℝ → ℂ}
    (hd : ∀ i, HasWeakPartialOn U i f (d i)) (j : Fin 2) :
    HasWeakPartialOn (planeAffine A c ⁻¹' U) j (f ∘ planeAffine A c)
      (fun p ↦ affineCoeff A 0 j * d 0 (planeAffine A c p) +
        affineCoeff A 1 j * d 1 (planeAffine A c p)) := by
  let a := affineCoeff A 0 j
  let b := affineCoeff A 1 j
  have hder : LocallyIntegrableOn (fun p ↦ a * d 0 p + b * d 1 p) U := by
    simpa only [Pi.smul_def, Pi.add_def, smul_eq_mul] using
      ((hd 0).2.1.smul a).add ((hd 1).2.1.smul b)
  refine ⟨locallyIntegrableOn_comp_planeAffine A c hmp hU (hd 0).1,
    locallyIntegrableOn_comp_planeAffine A c hmp hU hder, ?_⟩
  intro φ hφ
  let ψ := φ ∘ (planeAffine A c).symm
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨hφ.contDiff.comp (contDiff_planeAffine_symm A c),
      hφ.hasCompactSupport.comp_homeomorph (planeAffine A c).symm, ?_⟩
    intro p hp
    have ht : (planeAffine A c).symm p ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ (planeAffine A c).symm) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    simpa only [mem_preimage, (planeAffine A c).apply_symm_apply] using hφ.tsupport_subset ht
  have hchain (q : ℝ × ℝ) :
      a * coordPartial 0 ψ (planeAffine A c q) +
        b * coordPartial 1 ψ (planeAffine A c q) = coordPartial j φ q := by
    have he := coordPartial_comp_planeAffine (hψ.contDiff.differentiable (by simp)) A c j q
    have hc : ψ ∘ planeAffine A c = φ :=
      funext fun p ↦ congrArg φ ((planeAffine A c).symm_apply_apply p)
    simpa only [hc, a, b] using he.symm
  have ix (i : Fin 2) : Integrable (fun p ↦ f p * coordPartial i ψ p) :=
    integrable_mul_of_tsupport_subset (hd i).1 (hψ.continuous_coordPartial i)
      (hψ.hasCompactSupport_coordPartial i)
      ((tsupport_coordPartial_subset i ψ).trans hψ.tsupport_subset)
  have iy (i : Fin 2) : Integrable (fun p ↦ d i p * ψ p) :=
    integrable_mul_of_tsupport_subset (hd i).2.1 hψ.contDiff.continuous
      hψ.hasCompactSupport hψ.tsupport_subset
  have hleft : (∫ p, f p * (a * coordPartial 0 ψ p + b * coordPartial 1 ψ p)) =
      a * (∫ p, f p * coordPartial 0 ψ p) + b * (∫ p, f p * coordPartial 1 ψ p) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((ix 0).const_mul a)
      ((ix 1).const_mul b)]
    congr 1
    funext p
    ring
  have hright : (∫ p, (a * d 0 p + b * d 1 p) * ψ p) =
      a * (∫ p, d 0 p * ψ p) + b * (∫ p, d 1 p * ψ p) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((iy 0).const_mul a)
      ((iy 1).const_mul b)]
    congr 1
    funext p
    ring
  have hw : (∫ p, f p * (a * coordPartial 0 ψ p + b * coordPartial 1 ψ p)) =
      -(∫ p, (a * d 0 p + b * d 1 p) * ψ p) := by
    rw [hleft, hright, (hd 0).2.2 ψ hψ, (hd 1).2.2 ψ hψ]
    ring
  rw [← hmp.integral_comp (planeAffine A c).measurableEmbedding
    (fun p ↦ f p * (a * coordPartial 0 ψ p + b * coordPartial 1 ψ p)),
    ← hmp.integral_comp (planeAffine A c).measurableEmbedding
      (fun p ↦ (a * d 0 p + b * d 1 p) * ψ p)] at hw
  simpa only [hchain, ψ, Function.comp_apply, (planeAffine A c).symm_apply_apply, a, b] using hw

/-- Differentiation of a transformed jet is linear in the supplied derivatives.
No commutation of mixed weak derivatives is needed. -/
private theorem affineJet_deriv {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (w : List (Fin 2)) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    {E : Fin 2 → List (Fin 2) → ℝ × ℝ → ℂ}
    (hd : ∀ v, v.length = w.length → ∀ i, HasWeakPartialOn U i (D v) (E i v))
    (j : Fin 2) :
    HasWeakPartialOn (planeAffine A c ⁻¹' U) j (affineJet A c D w)
      (fun p ↦ affineCoeff A 0 j * affineJet A c (E 0) w p +
        affineCoeff A 1 j * affineJet A c (E 1) w p) := by
  induction w generalizing D E with
  | nil =>
    exact HasWeakPartialOn.comp_planeAffine A c hmp hU (hd [] rfl) j
  | cons l w ih =>
    have h0 := ih (D := fun v ↦ D (0 :: v)) (E := fun i v ↦ E i (0 :: v))
      (fun v hv i ↦ hd (0 :: v) (by simpa using hv) i)
    have h1 := ih (D := fun v ↦ D (1 :: v)) (E := fun i v ↦ E i (1 :: v))
      (fun v hv i ↦ hd (1 :: v) (by simpa using hv) i)
    convert (h0.const_mul (affineCoeff A 0 l)).add
      (h1.const_mul (affineCoeff A 1 l)) using 1 <;> funext p
    all_goals simp only [affineJet]
    ring

/-- A specified weak jet pulls back with all derivative indices transformed. -/
theorem HasWeakJetOn.comp_planeAffine {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) :
    HasWeakJetOn n (planeAffine A c ⁻¹' U) (f ∘ planeAffine A c) (affineJet A c D) := by
  refine ⟨by simp only [affineJet, hD.1], fun w hw j ↦ ?_⟩
  exact affineJet_deriv A c hmp hU w (fun v hv i ↦ hD.2 v (hv ▸ hw) i) j

/-- Integer-order Sobolev membership pulls back under a volume-preserving affine chart. -/
theorem MemSobolevOn.comp_planeAffine {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevOn k U f) :
    MemSobolevOn k (planeAffine A c ⁻¹' U) (f ∘ planeAffine A c) := by
  induction k generalizing f with
  | zero => exact memLp_comp_planeAffine A c hmp hU.measurableSet hf
  | succ k ih =>
    choose d hd hk using hf.2
    refine ⟨memLp_comp_planeAffine A c hmp hU.measurableSet hf.1, fun j ↦ ?_⟩
    exact ⟨_, HasWeakPartialOn.comp_planeAffine A c hmp hU hd j,
      MemSobolevOnWith.add ((ih (hk 0)).const_mul (affineCoeff A 0 j))
        ((ih (hk 1)).const_mul (affineCoeff A 1 j))⟩

/-- Local Sobolev regularity also pulls back under the affine chart. -/
theorem MemSobolevLocOn.comp_planeAffine {k : ℕ} {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevLocOn k U f) :
    MemSobolevLocOn k (planeAffine A c ⁻¹' U) (f ∘ planeAffine A c) := by
  intro V hV hc hVU
  have ho : IsOpen (planeAffine A c '' V) := (planeAffine A c).isOpenMap V hV
  have hcl := (planeAffine A c).image_closure V
  have hW : MemSobolevOn k (planeAffine A c '' V) f := hf _ ho
    (hcl ▸ hc.image (planeAffine A c).continuous) (by
      rw [← hcl]
      exact image_subset_iff.mpr hVU)
  simpa only [(planeAffine A c).injective.preimage_image] using
    hW.comp_planeAffine A c hmp ho

/-- The inverse chart is affine as well. -/
theorem MemSobolevOn.comp_planeAffine_symm {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevOn k U f) :
    MemSobolevOn k ((planeAffine A c).symm ⁻¹' U) (f ∘ (planeAffine A c).symm) := by
  have heq : ((planeAffine A c).symm : (ℝ × ℝ) → ℝ × ℝ) =
      planeAffine A.symm (-A.symm c) := by
    funext p
    change A.symm (p - c) = A.symm p + -A.symm c
    simpa only [sub_eq_add_neg] using A.symm.map_sub p c
  have hmi : MeasurePreserving (planeAffine A.symm (-A.symm c)) := by
    rw [← heq]
    exact MeasurePreserving.symm (planeAffine A c).toMeasurableEquiv hmp
  simpa only [← heq] using hf.comp_planeAffine A.symm (-A.symm c) hmi hU

private theorem memLp_affineJet_div_radius {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    (w : List (Fin 2)) {s : ℕ} {c₀ c₁ : ℝ × ℝ}
    (hrad : ∀ p, localRadius c₀ (planeAffine A c p) = localRadius c₁ p)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ v, v.length = w.length →
      MemLp (fun p ↦ D v p / (localRadius c₀ p ^ s : ℂ)) 2 (volume.restrict U)) :
    MemLp (fun p ↦ affineJet A c D w p / (localRadius c₁ p ^ s : ℂ)) 2
      (volume.restrict (planeAffine A c ⁻¹' U)) := by
  induction w generalizing D with
  | nil =>
    have hm := memLp_comp_planeAffine A c hmp hU (hD [] rfl)
    simpa only [affineJet, Function.comp_def, hrad] using hm
  | cons l w ih =>
    have h0 := ih (D := fun v ↦ D (0 :: v))
      (fun v hv ↦ hD (0 :: v) (by simpa using hv))
    have h1 := ih (D := fun v ↦ D (1 :: v))
      (fun v hv ↦ hD (1 :: v) (by simpa using hv))
    refine ((h0.const_mul (affineCoeff A 0 l)).add
      (h1.const_mul (affineCoeff A 1 l))).ae_eq ?_
    exact Filter.Eventually.of_forall fun p ↦ by
      simp only [Pi.add_apply, affineJet, div_eq_mul_inv]
      ring

/-- Radius-preserving affine charts transfer radial L² bounds for the full transformed jet. -/
theorem RadialJetLp.comp_planeAffine {k s : ℕ} {U : Set (ℝ × ℝ)}
    (hU : MeasurableSet U) {c₀ c₁ : ℝ × ℝ}
    (hrad : ∀ p, localRadius c₀ (planeAffine A c p) = localRadius c₁ p)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hD : RadialJetLp k s U c₀ D) :
    RadialJetLp k s (planeAffine A c ⁻¹' U) c₁ (affineJet A c D) := by
  intro w hw
  exact memLp_affineJet_div_radius A c hmp hU w hrad (fun v hv ↦ hD v (hv.trans hw))

end Pullback
end NoEmbeddedEigenvalues
