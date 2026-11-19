import NoEmbeddedEigenvalues.Regularity.OddOddQuotient

/-! # Quantitative divided Laplacian and full odd–odd quotient domain -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped Topology

/-- Uniform H² bound for the divided Laplacian of the product of the dipole with an
even function. Any L² representative of the quotient has this bound. -/
theorem even_h2_dipole_laplacian_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ ψ ζ ν : L2}, MemSobolev 2 φ → InSector true true φ →
      (∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t) → HasFourierLaplacian ψ ζ →
      (∀ᵐ t, ζ t = (Ψ t : ℂ) * ν t) → ‖ν‖ ≤ C * Real.sqrt (sobolevNormSq 2 φ) := by
  sorry

/-- The full odd–odd quotient domain, including the periodic transport equation,
the global vorticity weight and the two local corner weights. The global weight is
tested over one period box; the corner weights use physical orthonormal coordinates. -/
theorem dd_quotient_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ φ ν : L2, MemSobolev 2 φ ∧ InSector true true φ ∧
      (∀ᵐ t, invLap ω t = (Ψ t : ℂ) * φ t) ∧
      (∀ᵐ t, ω t = (Ψ t : ℂ) * ν t) ∧
      HasL0 (ν + φ) ((Complex.I * lam) • ν) ∧
      MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2 (volume.restrict periodBox) ∧
      ∀ P ∈ saddleSet, ∃ r : ℝ, 0 < r ∧
        ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
          let F := fun q ↦ continuousRep φ (torusProj (saddleOrthoChart P q))
          HasWeakJetOn 2 (localDisk 0 r) F D ∧
          RadialJetLp 1 1 (localDisk 0 r) 0 D ∧
          MemLp (fun q ↦ (F q - continuousRep φ (torusProj P)) / (localRadius 0 q ^ 2 : ℂ)) 2
            (volume.restrict (localDisk 0 r)) := by
  sorry

end NoEmbeddedEigenvalues
