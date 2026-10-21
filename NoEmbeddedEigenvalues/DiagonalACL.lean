import NoEmbeddedEigenvalues.ACLSlicing

/-!
# Transverse ACL representatives in diagonal coordinates

Blueprint: `lem:trace-acl`.

The linear change of variables transfers the two weak partial derivatives to
`∂_a = ∂ₓ + ∂_y` and `∂_b = ∂ₓ - ∂_y`, and preserves L² membership. Directional slicing then supplies a jointly measurable
representative, without a fractional trace estimate or Sobolev approximation.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The diagonal inverse sends Lebesgue measure to one half of Lebesgue measure. -/
theorem map_diagInv_volume :
    Measure.map diagInv volume = ENNReal.ofReal (1 / 2) • volume := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  change Measure.map (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) volume = _
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (show LinearMap.det (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 by
      rw [det_diagInvLinear]; norm_num)
  simpa only [det_diagInvLinear, show |(-2 : ℝ)⁻¹| = 1 / 2 by norm_num] using h

/-- Local integrability is preserved by the diagonal linear change of variables. -/
theorem locallyIntegrableOn_comp_diagInv {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : LocallyIntegrableOn F U) (hU : IsOpen U) :
    LocallyIntegrableOn (F ∘ diagInv) (diagInv ⁻¹' U) := by
  apply (locallyIntegrableOn_iff (hU.preimage diagInv.continuous).isLocallyClosed).2
  intro K hKU hK
  have hi := hF.integrableOn_compact_subset (image_subset_iff.2 hKU)
    (hK.image diagInv.continuous)
  have him : IntegrableOn F (diagInv '' K) (Measure.map diagInv volume) := by
    rw [map_diagInv_volume, IntegrableOn, Measure.restrict_smul]
    exact hi.smul_measure (by finiteness)
  have hp := (integrableOn_map_equiv diagInv.toHomeomorph.toMeasurableEquiv).1 him
  simpa only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    diagInv.injective.preimage_image] using hp

/-- The transverse weak derivative in diagonal coordinates is `Fₓ - Fᵧ`. -/
theorem HasWeakPartialOn.comp_diagInv_snd {U : Set (ℝ × ℝ)} {F Fx Fy : ℝ × ℝ → ℂ}
    (hU : IsOpen U) (hx : HasWeakPartialOn U 0 F Fx) (hy : HasWeakPartialOn U 1 F Fy) :
    HasWeakPartialOn (diagInv ⁻¹' U) 1 (F ∘ diagInv) ((fun p ↦ Fx p - Fy p) ∘ diagInv) := by
  refine ⟨locallyIntegrableOn_comp_diagInv hx.1 hU,
    locallyIntegrableOn_comp_diagInv (hx.2.1.sub hy.2.1) hU, ?_⟩
  intro φ hφ
  let ψ := φ ∘ diagInv.symm
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨hφ.contDiff.comp diagInv.symm.contDiff,
      hφ.hasCompactSupport.comp_homeomorph diagInv.symm.toHomeomorph, ?_⟩
    intro p hp
    have ht : diagInv.symm p ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ diagInv.symm.toHomeomorph) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    simpa only [mem_preimage, diagInv.apply_symm_apply] using hφ.tsupport_subset ht
  have hchain : ∀ q, partialX ψ (diagInv q) - partialY ψ (diagInv q) = partialY φ q := by
    intro q
    have he := congrFun (partialY_comp_diagInv (hψ.contDiff.differentiable (by simp))) q
    have hc : ψ ∘ diagInv = φ := by
      funext p
      exact congrArg φ (diagInv.symm_apply_apply p)
    simpa only [hc, Function.comp_apply] using he.symm
  have ix := integrable_mul_of_tsupport_subset hx.1 (hψ.continuous_coordPartial 0)
    (hψ.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 ψ).trans hψ.tsupport_subset)
  have iy := integrable_mul_of_tsupport_subset hy.1 (hψ.continuous_coordPartial 1)
    (hψ.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 ψ).trans hψ.tsupport_subset)
  have iFx := integrable_mul_of_tsupport_subset hx.2.1 hψ.contDiff.continuous
    hψ.hasCompactSupport hψ.tsupport_subset
  have iFy := integrable_mul_of_tsupport_subset hy.2.1 hψ.contDiff.continuous
    hψ.hasCompactSupport hψ.tsupport_subset
  have hw : (∫ p, F p * (partialX ψ p - partialY ψ p)) =
      -(∫ p, (Fx p - Fy p) * ψ p) := by
    simp only [mul_sub, sub_mul]
    rw [integral_sub (by simpa [coordPartial] using ix) (by simpa [coordPartial] using iy),
      integral_sub iFx iFy]
    have hxx := hx.2.2 ψ hψ
    have hyy := hy.2.2 ψ hψ
    simp only [coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at hxx hyy
    rw [hxx, hyy]
    ring
  rw [integral_eq_two_smul_integral_diagInv (fun p ↦ F p * (partialX ψ p - partialY ψ p)),
    integral_eq_two_smul_integral_diagInv (fun p ↦ (Fx p - Fy p) * ψ p)] at hw
  simp only [hchain, ψ, Function.comp_apply, diagInv.symm_apply_apply] at hw
  have hh := congrArg (fun z : ℂ ↦ (1 / 2 : ℝ) • z) hw
  simpa only [smul_neg, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
    coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, Function.comp_apply] using hh

/-- Square integrability is preserved by the diagonal coordinate change. -/
theorem memLp_comp_diagInv {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict U)) :
    MemLp (F ∘ diagInv) 2 (volume.restrict (diagInv ⁻¹' U)) := by
  apply diagInv.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.1
  change MemLp F 2 (Measure.map diagInv (volume.restrict (diagInv ⁻¹' U)))
  rw [← Measure.restrict_map diagInv.continuous.measurable hU, map_diagInv_volume,
    Measure.restrict_smul]
  exact hF.smul_measure (by finiteness)

/-- The tangential weak derivative in diagonal coordinates is `Fₓ + Fᵧ`. -/
theorem HasWeakPartialOn.comp_diagInv_fst {U : Set (ℝ × ℝ)} {F Fx Fy : ℝ × ℝ → ℂ}
    (hU : IsOpen U) (hx : HasWeakPartialOn U 0 F Fx) (hy : HasWeakPartialOn U 1 F Fy) :
    HasWeakPartialOn (diagInv ⁻¹' U) 0 (F ∘ diagInv) ((fun p ↦ Fx p + Fy p) ∘ diagInv) := by
  refine ⟨locallyIntegrableOn_comp_diagInv hx.1 hU,
    locallyIntegrableOn_comp_diagInv (hx.2.1.add hy.2.1) hU, ?_⟩
  intro φ hφ
  let ψ := φ ∘ diagInv.symm
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨hφ.contDiff.comp diagInv.symm.contDiff,
      hφ.hasCompactSupport.comp_homeomorph diagInv.symm.toHomeomorph, ?_⟩
    intro p hp
    have ht : diagInv.symm p ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ diagInv.symm.toHomeomorph) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    simpa only [mem_preimage, diagInv.apply_symm_apply] using hφ.tsupport_subset ht
  have hchain : ∀ q, partialX ψ (diagInv q) + partialY ψ (diagInv q) = partialX φ q := by
    intro q
    have he := congrFun (partialX_comp_diagInv (hψ.contDiff.differentiable (by simp))) q
    have hc : ψ ∘ diagInv = φ := by
      funext p
      exact congrArg φ (diagInv.symm_apply_apply p)
    simpa only [hc, Function.comp_apply] using he.symm
  have ix := integrable_mul_of_tsupport_subset hx.1 (hψ.continuous_coordPartial 0)
    (hψ.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 ψ).trans hψ.tsupport_subset)
  have iy := integrable_mul_of_tsupport_subset hy.1 (hψ.continuous_coordPartial 1)
    (hψ.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 ψ).trans hψ.tsupport_subset)
  have iFx := integrable_mul_of_tsupport_subset hx.2.1 hψ.contDiff.continuous
    hψ.hasCompactSupport hψ.tsupport_subset
  have iFy := integrable_mul_of_tsupport_subset hy.2.1 hψ.contDiff.continuous
    hψ.hasCompactSupport hψ.tsupport_subset
  have hw : (∫ p, F p * (partialX ψ p + partialY ψ p)) =
      -(∫ p, (Fx p + Fy p) * ψ p) := by
    simp only [mul_add, add_mul]
    rw [integral_add (by simpa [coordPartial] using ix) (by simpa [coordPartial] using iy),
      integral_add iFx iFy]
    have hxx := hx.2.2 ψ hψ
    have hyy := hy.2.2 ψ hψ
    simp only [coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at hxx hyy
    rw [hxx, hyy]
    ring
  rw [integral_eq_two_smul_integral_diagInv (fun p ↦ F p * (partialX ψ p + partialY ψ p)),
    integral_eq_two_smul_integral_diagInv (fun p ↦ (Fx p + Fy p) * ψ p)] at hw
  simp only [hchain, ψ, Function.comp_apply, diagInv.symm_apply_apply] at hw
  have hh := congrArg (fun z : ℂ ↦ (1 / 2 : ℝ) • z) hw
  simpa only [smul_neg, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
    coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, Function.comp_apply] using hh

/-- A jointly measurable transverse ACL representative (`lem:trace-acl`).
Only local integrability of the function and its weak partials is needed. The
representative agrees with the original function a.e. on all of `U`, not just
on the diagonal rectangle. -/
theorem exists_diagonal_acl_rep {U : Set (ℝ × ℝ)} {F Fx Fy : ℝ × ℝ → ℂ}
    {a₀ a₁ b₁ b₂ : ℝ} (hU : IsOpen U) (ha : a₀ < a₁) (hb : b₁ < b₂)
    (hQ : diagRect (Ioo a₀ a₁) (Ioo b₁ b₂) ⊆ U)
    (hx : HasWeakPartialOn U 0 F Fx) (hy : HasWeakPartialOn U 1 F Fy) :
    ∃ G : ℝ × ℝ → ℂ, Measurable G ∧ G =ᵐ[volume.restrict U] F ∧
      ∀ᵐ a ∂(volume.restrict (Ioo a₀ a₁)),
        (∀ c d, b₁ < c → c ≤ d → d < b₂ →
          AbsolutelyContinuousOnInterval (fun b ↦ G (diagInv (a, b))) c d) ∧
        ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)),
          HasDerivAt (fun b ↦ G (diagInv (a, b)))
            (Fx (diagInv (a, b)) - Fy (diagInv (a, b))) b := by
  classical
  let R := Ioo a₀ a₁ ×ˢ Ioo b₁ b₂
  let Q := diagInv.symm ⁻¹' R
  have hRm : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hQm : MeasurableSet Q := hRm.preimage diagInv.symm.continuous.measurable
  have hRU : R ⊆ diagInv ⁻¹' U := by
    intro q hq
    apply hQ
    simpa only [R, mem_prod, diagRect, mem_ofPred_eq, diagCoord_diagInv] using hq
  obtain ⟨H, hHm, hHF, hH⟩ := ((hx.comp_diagInv_snd hU hy).mono hRU).exists_acl_sections
    isOpen_Ioo (ordConnected_Ioo) (nonempty_Ioo.2 ha)
    isOpen_Ioo (ordConnected_Ioo) (nonempty_Ioo.2 hb)
  have heq : ∀ᵐ p, p ∈ Q → H (diagInv.symm p) = F p := by
    have hr := (ae_restrict_iff' hRm).1 hHF
    have hm : ∀ᵐ p ∂(Measure.map diagInv volume), p ∈ Q → H (diagInv.symm p) = F p :=
      diagInv.toHomeomorph.measurableEmbedding.ae_map_iff.2 (by
        simpa only [Q, mem_preimage, ContinuousLinearEquiv.coe_toHomeomorph,
          diagInv.symm_apply_apply, Function.comp_apply] using hr)
    rwa [map_diagInv_volume, Measure.ae_ennreal_smul_measure_iff
      (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0)] at hm
  let Fm := hx.1.aestronglyMeasurable.mk F
  let G : ℝ × ℝ → ℂ := Q.piecewise (H ∘ diagInv.symm) Fm
  have hGm : Measurable G := (hHm.comp diagInv.symm.continuous.measurable).piecewise hQm
    hx.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hGdiag : ∀ a ∈ Ioo a₀ a₁, ∀ b ∈ Ioo b₁ b₂, G (diagInv (a, b)) = H (a, b) := by
    intro a ha b hb
    have hmem : diagInv (a, b) ∈ Q := by
      simpa only [Q, mem_preimage, diagInv.symm_apply_apply] using (show (a, b) ∈ R from ⟨ha, hb⟩)
    change Q.piecewise (H ∘ diagInv.symm) Fm (diagInv (a, b)) = _
    rw [piecewise_eq_of_mem Q _ _ hmem]
    exact congrArg H (diagInv.symm_apply_apply (a, b))
  refine ⟨G, hGm, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae heq, hx.1.aestronglyMeasurable.ae_eq_mk] with p hp hpm
    by_cases hpQ : p ∈ Q
    · exact (piecewise_eq_of_mem Q _ _ hpQ).trans (hp hpQ)
    · exact (piecewise_eq_of_notMem Q _ _ hpQ).trans hpm.symm
  · filter_upwards [hH, ae_restrict_mem measurableSet_Ioo] with a hline haI
    refine ⟨?_, ?_⟩
    · intro c d hc hcd hd
      have hsub : uIcc c d ⊆ Ioo b₁ b₂ := by
        rw [uIcc_of_le hcd]
        exact Icc_subset_Ioo hc hd
      exact (hline.1 c d hsub).congr (fun b hb ↦ (hGdiag a haI b (hsub hb)).symm)
    · filter_upwards [hline.2, ae_restrict_mem measurableSet_Ioo] with b hb hbI
      apply hb.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hbI] with t ht
      exact hGdiag a haI t ht

end NoEmbeddedEigenvalues
