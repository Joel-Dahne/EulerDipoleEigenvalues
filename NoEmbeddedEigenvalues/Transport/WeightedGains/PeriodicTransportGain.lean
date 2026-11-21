module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.QuotientLocal
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleBootstrapMass

/-!
# Periodic first transport gain

The torus transport equation supplies a pair on each bounded invariant
neighbourhood. Apply the positive-cell gain to the original and reflected
data, then use a finite reflected-periodic cover for the bounded lift norm.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- A periodic weak transport relation gives a transport pair with continuous forcing
on any bounded open union of orbits (`lem:periodic-transport-pair`). -/
theorem isTransportPair_continuousRep {lam : ℝ} (hlam : lam ≠ 0) {ν φ : L2}
    (hφ : MemSobolev 2 φ) (h : HasL0 (ν + φ) ((Complex.I * lam) • ν))
    {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U) (hb : Bornology.IsBounded U) :
    IsTransportPair lam U (liftL2 ν) (fun p ↦ continuousRep φ (torusProj p)) := by
  have heq : liftL2 φ =ᵐ[volume] (fun p ↦ continuousRep φ (torusProj p)) :=
    ae_torusProj (coeFn_eq_continuousRep hφ)
  refine ⟨hlam, hU, memLp_liftL2 ν hb, (memSobolevOn_liftL2 hφ hb).congr_ae heq, ?_⟩
  refine ((hasWeakL0On_liftL2 h U).congr_value ?_).congr_deriv ?_
  · filter_upwards [liftL2_add_ae ν φ, heq] with p hp hφp
    rw [hp, hφp]
  · filter_upwards [liftL2_smul_ae (Complex.I * lam) ν] with p hp
    rw [hp, mul_assoc]

/-- The first reflection preserves every Fourier Sobolev class. -/
private theorem memSobolev_reflect₁ {s : ℝ} {φ : L2} (hφ : MemSobolev s φ) :
    MemSobolev s (reflect₁ φ) := by
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun k ↦ (-k.2, -k.1)
      invFun := fun k ↦ (-k.2, -k.1)
      left_inv := by intro k; simp
      right_inv := by intro k; simp }
  have hn (k : ℤ × ℤ) :
      ‖fourierCoeff (reflect₁ φ) (e k)‖ = ‖fourierCoeff φ k‖ := by
    have hp : ‖reflectionPhase k‖ = 1 := by
      change ‖fourier k.1 (Real.pi : AddCircle (2 * Real.pi)) *
        fourier k.2 (Real.pi : AddCircle (2 * Real.pi))‖ = 1
      simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    have hc := congrArg norm (symmetry₁.coefficient φ k)
    change ‖(starRingEnd ℂ) (reflectionPhase k) * fourierCoeff (reflect₁ φ) (e k)‖ = _ at hc
    simpa only [norm_mul, Complex.norm_conj, hp, one_mul] using hc
  apply e.summable_iff.mp
  exact hφ.congr fun k ↦ by
    dsimp only [Function.comp_apply]
    rw [hn]
    congr 1
    exact congrArg (fun n : ℤ ↦ (1 + (n : ℝ)) ^ s) (symmetry₁.normSq_eq k).symm

/-- Periodic first transport gain on the full fixed lift neighbourhood
(`cor:transport-first-gain-periodic`), including reflection and periodic cell covering.
No parity, elliptic relation or vanishing saddle value of the forcing is assumed. -/
theorem transport_first_gain_periodic {lam : ℝ} (hlam : lam ≠ 0) {ν φ : L2}
    (hφ : MemSobolev 2 φ) (h : HasL0 (ν + φ) ((Complex.I * lam) • ν)) :
    MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
  have hpos := transport_first_gain
    (isTransportPair_continuousRep hlam hφ h
      isOrbitUnion_cellNeighbourhood isBounded_cellNeighbourhood)
    isBounded_cellNeighbourhood closure_cellSquare_subset_cellNeighbourhood
  have hr : HasL0 (reflect₁ ν + reflect₁ φ) ((Complex.I * lam) • reflect₁ ν) := by
    simpa only [map_add, map_smul, reflect₁] using symmetry₁.hasL0 h
  have href := transport_first_gain
    (isTransportPair_continuousRep hlam (memSobolev_reflect₁ hφ) hr
      isOrbitUnion_cellNeighbourhood isBounded_cellNeighbourhood)
    isBounded_cellNeighbourhood closure_cellSquare_subset_cellNeighbourhood
  have ht := ae_comp_of_pullback_eq
    (show pullback S₁ measurePreserving_S₁ ν = reflect₁ ν from rfl)
  have hlift : ∀ᵐ p : ℝ × ℝ, liftL2 ν (separatrixReflect p) = liftL2 (reflect₁ ν) p := by
    filter_upwards [ae_torusProj ht] with p hp
    simpa only [liftL2, separatrixReflect, torusProj, S₁, Real.Angle.coe_sub] using hp
  have hneg : MemLp (fun p ↦ liftL2 ν (separatrixReflect p) / (saddleDist p : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply href.ae_eq
    filter_upwards [ae_restrict_of_ae hlift] with p hp
    rw [hp]
  simpa only [Real.rpow_eq_pow, Real.rpow_one] using
    memLp_saddleDist_of_reflected_cells (ω := ν) (t := 1)
      (by simpa only [Real.rpow_eq_pow, Real.rpow_one] using hpos)
      (by simpa only [Real.rpow_eq_pow, Real.rpow_one] using hneg) isBounded_cellNeighbourhood

end NoEmbeddedEigenvalues
