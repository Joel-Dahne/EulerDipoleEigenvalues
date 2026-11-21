import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Locality of a specified weak partial derivative

Blueprint: `lem:weak-partial-locality`.

A finite smooth partition of a test function combines local weak identities.
Both the function and its specified derivative are unchanged between patches.
No square-integrability or Sobolev density assumption is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff Manifold Topology

/-- A specified weak derivative can be checked on open neighbourhoods of points. -/
theorem hasWeakPartialOn_of_locally {U : Set (ℝ × ℝ)} {j : Fin 2}
    {F D : ℝ × ℝ → ℂ}
    (hloc : ∀ p ∈ U, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧
      HasWeakPartialOn W j F D) : HasWeakPartialOn U j F D := by
  have hF : LocallyIntegrableOn F U := by
    intro p hp
    obtain ⟨W, hW, hpW, hd⟩ := hloc p hp
    have hi := hd.1 p hpW
    rw [hW.nhdsWithin_eq hpW] at hi
    exact IntegrableAtFilter.filter_mono nhdsWithin_le_nhds hi
  have hD : LocallyIntegrableOn D U := by
    intro p hp
    obtain ⟨W, hW, hpW, hd⟩ := hloc p hp
    have hi := hd.2.1 p hpW
    rw [hW.nhdsWithin_eq hpW] at hi
    exact IntegrableAtFilter.filter_mono nhdsWithin_le_nhds hi
  refine ⟨hF, hD, ?_⟩
  intro φ hφ
  classical
  choose W hW hpW hd using fun p : tsupport φ ↦ hloc p (hφ.tsupport_subset p.property)
  obtain ⟨s, hs⟩ := hφ.hasCompactSupport.elim_finite_subcover W hW
    (fun p hp ↦ mem_iUnion_of_mem ⟨p, hp⟩ (hpW ⟨p, hp⟩))
  have hcover : tsupport φ ⊆ ⋃ p : s, W p.val := by
    intro p hp
    obtain ⟨q, hqs, hpq⟩ := mem_iUnion₂.mp (hs hp)
    exact mem_iUnion_of_mem ⟨q, hqs⟩ hpq
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity s 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (tsupport φ),
      ρ.IsSubordinate (fun p ↦ W p.val) :=
    SmoothPartitionOfUnity.exists_isSubordinate _ (isClosed_tsupport φ) _
      (fun p ↦ hW p.val) hcover
  let χ (i : s) (p : ℝ × ℝ) : ℂ := (ρ i p : ℂ)
  let ψ (i : s) (p : ℝ × ℝ) : ℂ := χ i p * φ p
  have hχ (i : s) : ContDiff ℝ ∞ (χ i) :=
    Complex.ofRealCLM.contDiff.comp (ρ i).contMDiff.contDiff
  have hψ (i : s) : ContDiff ℝ ∞ (ψ i) := (hχ i).mul hφ.contDiff
  have htU (i : s) : IsTestFunctionOn U (ψ i) :=
    ⟨hψ i, hφ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_right (f := χ i) (g := φ)).trans hφ.tsupport_subset⟩
  have htW (i : s) : IsTestFunctionOn (W i.val) (ψ i) :=
    ⟨hψ i, hφ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_left (f := χ i) (g := φ)).trans
        ((tsupport_comp_subset Complex.ofReal_zero (ρ i)).trans (hρ i))⟩
  have heq : φ = fun p ↦ ∑ i : s, ψ i p := by
    funext p
    dsimp [ψ]
    rw [← Finset.sum_mul]
    by_cases hp : p ∈ tsupport φ
    · have hsum := ρ.sum_eq_one hp
      simp only [finsum_eq_sum_of_fintype] at hsum
      have hc : ∑ i : s, χ i p = 1 := by
        simp only [χ, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]
      change φ p = (∑ i : s, χ i p) * φ p
      rw [hc, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  have hder : coordPartial j φ = fun p ↦ ∑ i : s, coordPartial j (ψ i) p := by
    calc
      _ = coordPartial j (fun p ↦ ∑ i : s, ψ i p) := congrArg (coordPartial j) heq
      _ = _ := by
        funext p
        unfold coordPartial
        split_ifs
        · change deriv (fun x ↦ ∑ i : s, ψ i (x, p.2)) p.1 =
            ∑ i : s, deriv (fun x ↦ ψ i (x, p.2)) p.1
          simpa only [Finset.sum_fn] using
            (deriv_sum (u := Finset.univ) (A := fun i x ↦ ψ i (x, p.2))
              (x := p.1) (fun i _ ↦ (((hψ i).differentiable (by simp)).comp
                (differentiable_id.prodMk (differentiable_const p.2))).differentiableAt))
        · change deriv (fun y ↦ ∑ i : s, ψ i (p.1, y)) p.2 =
            ∑ i : s, deriv (fun y ↦ ψ i (p.1, y)) p.2
          simpa only [Finset.sum_fn] using
            (deriv_sum (u := Finset.univ) (A := fun i y ↦ ψ i (p.1, y))
              (x := p.2) (fun i _ ↦ (((hψ i).differentiable (by simp)).comp
                ((differentiable_const p.1).prodMk differentiable_id)).differentiableAt))
  have hiF (i : s) : Integrable (fun p ↦ F p * coordPartial j (ψ i) p) :=
    integrable_mul_of_tsupport_subset hF ((htU i).continuous_coordPartial j)
      ((htU i).hasCompactSupport_coordPartial j)
      ((tsupport_coordPartial_subset j (ψ i)).trans (htU i).tsupport_subset)
  have hiD (i : s) : Integrable (fun p ↦ D p * ψ i p) :=
    integrable_mul_of_tsupport_subset hD (hψ i).continuous
      (htU i).hasCompactSupport (htU i).tsupport_subset
  calc
    _ = ∫ p, F p * ∑ i : s, coordPartial j (ψ i) p :=
      congrArg (fun f : ℝ × ℝ → ℂ ↦ ∫ p, F p * f p) hder
    _ = -(∫ p, D p * ∑ i : s, ψ i p) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ ↦ hiF i),
        integral_finsetSum _ (fun i _ ↦ hiD i)]
      simp_rw [(hd _).2.2 _ (htW _), Finset.sum_neg_distrib]
    _ = _ := congrArg (fun f : ℝ × ℝ → ℂ ↦ -(∫ p, D p * f p)) heq.symm

end NoEmbeddedEigenvalues
