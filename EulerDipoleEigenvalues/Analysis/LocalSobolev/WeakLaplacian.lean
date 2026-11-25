module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.AffineJets
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.WeakJetOperations
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Compact-test Laplacians of specified ordered weak jets

Two integrations by parts use only the two repeated-coordinate entries.
Neither mixed-derivative commutation nor a choice of new Sobolev witnesses
is needed. Integrability is proved before splitting the test pairings.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- The Cartesian Laplacian, without an inner product on the max-norm product. -/
def planeLaplacian (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  coordPartial 0 (coordPartial 0 f) p + coordPartial 1 (coordPartial 1 f) p

/-- A coordinate derivative of a genuine compact test is again a compact test. -/
theorem IsTestFunctionOn.coordPartial {U : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) (j : Fin 2) :
    IsTestFunctionOn U (coordPartial j φ) :=
  ⟨contDiff_coordPartial_top j hφ.contDiff, hφ.hasCompactSupport_coordPartial j,
    (tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset⟩

/-- The Laplacian preserves compact source tests. -/
theorem IsTestFunctionOn.planeLaplacian {U : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) : IsTestFunctionOn U (planeLaplacian φ) := by
  have h0 := (hφ.coordPartial 0).coordPartial 0
  have h1 := (hφ.coordPartial 1).coordPartial 1
  exact ⟨h0.contDiff.add h1.contDiff, h0.hasCompactSupport.add h1.hasCompactSupport,
    (tsupport_add _ _).trans (union_subset h0.tsupport_subset h1.tsupport_subset)⟩

/-- The diagonal trace of the same specified weak jet is its distributional
Laplacian. This statement does not assert smoothness of the raw function. -/
theorem HasWeakJetOn.integral_laplacian_test {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 U f D) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) :
    (∫ p, f p * planeLaplacian φ p) =
      ∫ p, (D [0, 0] p + D [1, 1] p) * φ p := by
  have hnil (j : Fin 2) : HasWeakPartialOn U j f (D [j]) := by
    simpa only [hD.1] using hD.2 [] (by decide) j
  have hjj (j : Fin 2) : HasWeakPartialOn U j (D [j]) (D [j, j]) :=
    hD.2 [j] (by simp) j
  have heq (j : Fin 2) :
      (∫ p, f p * coordPartial j (coordPartial j φ) p) =
        ∫ p, D [j, j] p * φ p := by
    rw [(hnil j).2.2 _ (hφ.coordPartial j), (hjj j).2.2 _ hφ, neg_neg]
  have hleft (j : Fin 2) :
      Integrable (fun p ↦ f p * coordPartial j (coordPartial j φ) p) :=
    integrable_mul_of_tsupport_subset (hnil j).1
      ((hφ.coordPartial j).coordPartial j).contDiff.continuous
      ((hφ.coordPartial j).coordPartial j).hasCompactSupport
      ((hφ.coordPartial j).coordPartial j).tsupport_subset
  have hright (j : Fin 2) : Integrable (fun p ↦ D [j, j] p * φ p) :=
    integrable_mul_of_tsupport_subset (hjj j).2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
  simp only [planeLaplacian, mul_add, add_mul]
  rw [integral_add (hleft 0) (hleft 1), integral_add (hright 0) (hright 1),
    heq 0, heq 1]

/-- Classical smooth Laplacians can be identified by their compact test pairings. -/
theorem planeLaplacian_eq_zero_of_test {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ φ, IsTestFunctionOn U φ → ∫ p, f p * planeLaplacian φ p = 0) :
    ∀ p ∈ U, planeLaplacian f p = 0 := by
  have hc : Continuous (planeLaplacian f) :=
    ((contDiff_coordPartial_top 0 (contDiff_coordPartial_top 0 hf)).add
      (contDiff_coordPartial_top 1 (contDiff_coordPartial_top 1 hf))).continuous
  have hae : ∀ᵐ p, p ∈ U → planeLaplacian f p = 0 := by
    apply ae_eq_zero_of_forall_test hU (hc.locallyIntegrable.locallyIntegrableOn U)
    intro φ hφ
    have hi := (classicalComplexJet_weak hf 2 U).integral_laplacian_test hφ
    change (∫ p, f p * planeLaplacian φ p) = ∫ p, planeLaplacian f p * φ p at hi
    exact hi.symm.trans (h φ hφ)
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hae)
    hU hc.continuousOn continuousOn_const

/-- Coordinate derivatives are evaluations of the real Fréchet derivative. -/
theorem coordPartial_eq_fderiv_plane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (j : Fin 2) :
    coordPartial j f p = fderiv ℝ f p (planeDirection j) := by
  unfold coordPartial planeDirection
  split_ifs
  · exact partialX_eq_fderiv hf
  · exact partialY_eq_fderiv hf

/-- Repeated coordinate derivatives agree with the actual second Fréchet jet. -/
theorem coordPartial_two_eq_iteratedFDeriv {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (i j : Fin 2) (p : ℝ × ℝ) :
    coordPartial i (coordPartial j f) p =
      iteratedFDeriv ℝ 2 f p ![planeDirection i, planeDirection j] := by
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have he : coordPartial j f = fun q ↦ fderiv ℝ f q (planeDirection j) := by
    funext q
    exact coordPartial_eq_fderiv_plane (hf.differentiable (by simp) q) j
  rw [he, coordPartial_eq_fderiv_plane
    ((hd.differentiable (by simp) p).clm_apply
      (differentiableAt_const (planeDirection j)))]
  rw [fderiv_clm_apply (hd.differentiable (by simp) p)
    (differentiableAt_const (planeDirection j))]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  simp [bilinearIteratedFDerivTwo]

/-- The Cartesian trace uses the Euclidean directions, not the product norm. -/
theorem planeLaplacian_eq_iteratedFDeriv {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    planeLaplacian f p = iteratedFDeriv ℝ 2 f p ![(1, 0), (1, 0)] +
      iteratedFDeriv ℝ 2 f p ![(0, 1), (0, 1)] := by
  simp only [planeLaplacian, coordPartial_two_eq_iteratedFDeriv hf, planeDirection]
  rfl

/-- The native complex-plane Laplacian equals the specified Cartesian trace. -/
theorem laplacian_complex_of_plane {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    Laplacian.laplacian (f ∘ Complex.equivRealProdCLM) z =
      planeLaplacian f (Complex.equivRealProdCLM z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    planeLaplacian_eq_iteratedFDeriv hf]
  have hcomp := Complex.equivRealProdCLM.toContinuousLinearMap.iteratedFDeriv_comp_right
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by simp)) z (i := 2) le_rfl
  change iteratedFDeriv ℝ 2 (f ∘ Complex.equivRealProdCLM) z =
    (iteratedFDeriv ℝ 2 f (Complex.equivRealProdCLM z)).compContinuousLinearMap
      (fun _ ↦ Complex.equivRealProdCLM.toContinuousLinearMap) at hcomp
  dsimp only
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> simp

/-- The first-coordinate sign of a reflected translated function. -/
theorem coordPartial_comp_sub_left {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f)
    (j : Fin 2) (x p : ℝ × ℝ) :
    coordPartial j (fun y ↦ f (x - y)) p = -coordPartial j f (x - p) := by
  have hd := (hf (x - p)).hasFDerivAt.comp p
    ((hasFDerivAt_const x p).sub (hasFDerivAt_id p))
  calc
    _ = fderiv ℝ (fun y ↦ f (x - y)) p (planeDirection j) :=
      coordPartial_eq_fderiv_plane hd.differentiableAt j
    _ = -coordPartial j f (x - p) := by
      rw [show fderiv ℝ (fun y ↦ f (x - y)) p =
        (fderiv ℝ f (x - p)).comp (0 - ContinuousLinearMap.id ℝ (ℝ × ℝ)) from hd.fderiv,
        coordPartial_eq_fderiv_plane (hf (x - p))]
      simp

/-- Negation of a differentiable coordinate section. -/
theorem coordPartial_neg_of_differentiable {f : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (j : Fin 2) :
    coordPartial j (fun q ↦ -f q) p = -coordPartial j f p := by
  fin_cases j
  · exact (hasDerivAt_partialX hf).neg.deriv
  · exact (hasDerivAt_partialY hf).neg.deriv

/-- Two sign changes cancel in the Laplacian of a reflected translated test. -/
theorem planeLaplacian_comp_sub_left {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (x p : ℝ × ℝ) :
    planeLaplacian (fun y ↦ f (x - y)) p = planeLaplacian f (x - p) := by
  have he (j : Fin 2) : coordPartial j (fun y ↦ f (x - y)) =
      fun y ↦ -coordPartial j f (x - y) :=
    funext (coordPartial_comp_sub_left (hf.differentiable (by simp)) j x)
  have htwo (j : Fin 2) :
      coordPartial j (coordPartial j (fun y ↦ f (x - y))) p =
        coordPartial j (coordPartial j f) (x - p) := by
    rw [he]
    have hd := (contDiff_coordPartial_top j hf).differentiable (by simp)
    have hsub := hd.comp (differentiable_const x |>.sub differentiable_id)
    calc
      _ = -coordPartial j (fun y ↦ coordPartial j f (x - y)) p :=
        coordPartial_neg_of_differentiable (hsub p) j
      _ = _ := by rw [coordPartial_comp_sub_left hd, neg_neg]
  exact congrArg₂ (· + ·) (htwo 0) (htwo 1)

end EulerDipoleEigenvalues
