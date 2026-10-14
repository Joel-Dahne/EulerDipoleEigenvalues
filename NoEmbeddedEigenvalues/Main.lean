import NoEmbeddedEigenvalues.EvenEven
import NoEmbeddedEigenvalues.OddOdd
import NoEmbeddedEigenvalues.Mixed

/-!
# Absence of nonzero embedded eigenvalues

The main theorem is assembled from the three sector exclusions and the proved
sector decomposition. There is no local `sorry` here, but the theorem depends
on the three admitted exclusions. It is not yet an unconditional formal proof.
-/

namespace NoEmbeddedEigenvalues

open Complex

/-- **Main theorem.** The linearized operator has no nonzero purely imaginary eigenvalues
`iλ`, `λ ≠ 0` (blueprint: `thm:main`). Conditional on the three sector exclusions. -/
theorem main (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (h : HasL ω ((I * lam) • ω)) : ω = 0 := by
  have hω := (hasL_iff_isEigenSolution lam ω).mp h
  have hee := even_even_exclusion lam hlam (sectorProjection true true ω)
    (hω.sectorProjection true true) (sectorProjection_mem true true ω)
  have hoo := odd_odd_exclusion lam hlam (sectorProjection false false ω)
    (hω.sectorProjection false false) (sectorProjection_mem false false ω)
  have hoe := mixed_exclusion lam hlam (sectorProjection false true ω)
    (hω.sectorProjection false true) (sectorProjection_mem false true ω)
  have heo := mixed_other_exclusion lam hlam (sectorProjection true false ω)
    (hω.sectorProjection true false) (sectorProjection_mem true false ω)
  calc
    ω = sectorProjection true true ω + sectorProjection false false ω +
        sectorProjection false true ω + sectorProjection true false ω :=
      (sectorProjection_sum ω).symm
    _ = 0 := by rw [hee, hoo, hoe, heo]; simp

end NoEmbeddedEigenvalues
