module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.DiagonalH1

/-!
# Recovering Cartesian H¹ from diagonal weak derivatives

Blueprint: `lem:diagonal-h1-inverse`.

The sum and difference of the two specified diagonal derivatives give the
Cartesian derivatives divided by two. In weak testing, the same factor two
is the Jacobian of the diagonal map. Actual L² transport precedes the identities.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Ordinary diagonal H¹ gives ordinary Cartesian H¹ of the same raw function. -/
theorem MemSobolevOn.of_comp_diagInv {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (h : MemSobolevOn 1 (diagInv ⁻¹' U) (F ∘ diagInv)) (hU : IsOpen U) :
    MemSobolevOn 1 U F := by
  obtain ⟨A, hA, hAL⟩ := h.2 0
  obtain ⟨B, hB, hBL⟩ := h.2 1
  change MemLp A 2 (volume.restrict (diagInv ⁻¹' U)) at hAL
  change MemLp B 2 (volume.restrict (diagInv ⁻¹' U)) at hBL
  let σ := fun j : Fin 2 ↦ if j = 0 then (1 : ℂ) else -1
  let D := fun (j : Fin 2) p ↦ (A (diagCoord p) + σ j * B (diagCoord p)) / 2
  have hF := memLp_of_comp_diagInv hU.measurableSet h.1
  have hD (j : Fin 2) : MemLp (D j) 2 (volume.restrict U) := by
    apply memLp_of_comp_diagInv hU.measurableSet
    convert ((hAL.add (hBL.const_mul (σ j))).const_mul ((2 : ℂ)⁻¹)) using 1
    funext q
    simp only [D, Function.comp_apply, diagCoord_diagInv, Pi.add_apply]
    ring
  refine ⟨hF, fun j ↦ ⟨D j, ?_, hD j⟩⟩
  have hFl : LocallyIntegrableOn F U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have hDl : LocallyIntegrableOn (D j) U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hD j).locallyIntegrable (by norm_num))
  refine ⟨hFl, hDl, fun φ hφ ↦ ?_⟩
  let ψ := φ ∘ diagInv
  have hψ : IsTestFunctionOn (diagInv ⁻¹' U) ψ := by
    refine ⟨hφ.contDiff.comp diagInv.contDiff,
      hφ.hasCompactSupport.comp_homeomorph diagInv.toHomeomorph, ?_⟩
    intro q hq
    change q ∈ tsupport (φ ∘ diagInv.toHomeomorph) at hq
    rw [tsupport_comp_eq_preimage] at hq
    exact hφ.tsupport_subset hq
  have hi (i : Fin 2) : Integrable (fun q ↦ F (diagInv q) * coordPartial i ψ q) :=
    integrable_mul_of_tsupport_subset hA.1 (hψ.continuous_coordPartial i)
      (hψ.hasCompactSupport_coordPartial i)
      ((tsupport_coordPartial_subset i ψ).trans hψ.tsupport_subset)
  have hiA : Integrable (fun q ↦ A q * ψ q) :=
    integrable_mul_of_tsupport_subset hA.2.1 hψ.contDiff.continuous
      hψ.hasCompactSupport hψ.tsupport_subset
  have hiB : Integrable (fun q ↦ B q * ψ q) :=
    integrable_mul_of_tsupport_subset hB.2.1 hψ.contDiff.continuous
      hψ.hasCompactSupport hψ.tsupport_subset
  have hc (q : ℝ × ℝ) : coordPartial 0 ψ q + σ j * coordPartial 1 ψ q =
      (2 : ℂ) * coordPartial j φ (diagInv q) := by
    have hx := congrFun (partialX_comp_diagInv (hφ.contDiff.differentiable (by simp))) q
    have hy := congrFun (partialY_comp_diagInv (hφ.contDiff.differentiable (by simp))) q
    fin_cases j
    · change partialX ψ q + (1 : ℂ) * partialY ψ q = 2 * partialX φ (diagInv q)
      rw [hx, hy]
      dsimp only [Function.comp_apply]
      ring
    · change partialX ψ q + (-1 : ℂ) * partialY ψ q = 2 * partialY φ (diagInv q)
      rw [hx, hy]
      dsimp only [Function.comp_apply]
      ring
  have hleft : (∫ p, F p * coordPartial j φ p) =
      ∫ q, F (diagInv q) * (coordPartial 0 ψ q + σ j * coordPartial 1 ψ q) := by
    rw [integral_eq_two_smul_integral_diagInv, ← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun q ↦ by
      dsimp only
      rw [hc]
      simp only [Complex.real_smul, Complex.ofReal_ofNat]
      ring
  have hright : (∫ p, D j p * φ p) = ∫ q, (A q + σ j * B q) * ψ q := by
    rw [integral_eq_two_smul_integral_diagInv, ← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun q ↦ by
      simp only [D, diagCoord_diagInv, Complex.real_smul, Complex.ofReal_ofNat, ψ,
        Function.comp_apply]
      ring
  have hsleft : (∫ q, F (diagInv q) *
      (coordPartial 0 ψ q + σ j * coordPartial 1 ψ q)) =
      (∫ q, F (diagInv q) * coordPartial 0 ψ q) +
        σ j * ∫ q, F (diagInv q) * coordPartial 1 ψ q := by
    rw [← integral_const_mul, ← integral_add (hi 0) ((hi 1).const_mul (σ j))]
    congr 1
    funext q
    ring
  have hsright : (∫ q, (A q + σ j * B q) * ψ q) =
      (∫ q, A q * ψ q) + σ j * ∫ q, B q * ψ q := by
    rw [← integral_const_mul, ← integral_add hiA (hiB.const_mul (σ j))]
    congr 1
    funext q
    ring
  have hwA := hA.2.2 ψ hψ
  have hwB := hB.2.2 ψ hψ
  simp only [Function.comp_apply] at hwA hwB
  rw [hleft, hright, hsleft, hsright, hwA, hwB]
  ring

/-- Either normal/tangential ordering gives Cartesian H¹. -/
theorem MemSobolevOn.of_comp_diagonalTraceChart {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (j : Fin 2) (h : MemSobolevOn 1 (diagonalTraceChart j ⁻¹' U)
      (F ∘ diagonalTraceChart j)) (hU : IsOpen U) : MemSobolevOn 1 U F := by
  fin_cases j
  · let A := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    have hm : MeasurePreserving (planeAffine A 0) volume volume := by
      have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
        rw [Measure.volume_eq_prod]
        exact Measure.measurePreserving_swap
      convert hs using 1
      funext q
      simp [planeAffine_apply, A]
    have hc : Continuous (diagonalTraceChart (0 : Fin 2)) :=
      diagInv.continuous.comp continuous_swap
    have hs := h.comp_planeAffine A 0 hm (hU.preimage hc)
    have hd : MemSobolevOn 1 (diagInv ⁻¹' U) (F ∘ diagInv) := by
      simpa [Set.preimage, planeAffine_apply, A, diagonalTraceChart, Function.comp_def] using hs
    exact hd.of_comp_diagInv hU
  · exact h.of_comp_diagInv hU

/-- H¹ of the actual pullback on an open parameter set gives H¹ on its
physical diagonal-chart image. -/
theorem MemSobolevOn.diagonalTraceChart_image {Q : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    {j : Fin 2} (h : MemSobolevOn 1 Q (F ∘ diagonalTraceChart j)) (hQ : IsOpen Q) :
    MemSobolevOn 1 (diagonalTraceChart j '' Q) F := by
  have hi : Function.Injective (diagonalTraceChart j) := by
    fin_cases j
    · exact diagInv.injective.comp Prod.swap_injective
    · exact diagInv.injective
  have ho := isOpenMap_diagonalTraceChart j Q hQ
  apply MemSobolevOn.of_comp_diagonalTraceChart j (hU := ho)
  rwa [hi.preimage_image]

end NoEmbeddedEigenvalues
