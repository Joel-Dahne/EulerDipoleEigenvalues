import NoEmbeddedEigenvalues.Regularity.QuotientLocal
import NoEmbeddedEigenvalues.WeightedTraces
import NoEmbeddedEigenvalues.Regularity.CylinderInverse
import NoEmbeddedEigenvalues.Regularity.SaddleNormalForm
import NoEmbeddedEigenvalues.SaddleForcingMass
import NoEmbeddedEigenvalues.SaddleDistance
import NoEmbeddedEigenvalues.StreamParity

/-!
# Odd–odd saddle and weighted forcing interfaces

These inputs precede ordinary separatrix H¹, logarithmic forcing and weighted
vorticity gradients. The ordinary whole-lift endpoint is in OddOddSeparatrix;
its cellwise ingredients depend on the forcing input here, not on logarithmic
forcing or the weighted-gradient theorem.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- First eigenfunction saddle gain (`prop:saddle-first-gain`), expressed on the
fixed bounded lift neighbourhood rather than taking a global norm on ℝ². -/
theorem saddle_first_gain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) :
    MemLp (fun p ↦ liftL2 ω p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
  sorry

/-- Weighted vorticity and unique quadratic jet (`prop:saddle-dd`). -/
theorem saddle_dd {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    MemLp (fun p ↦ liftL2 ω p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellNeighbourhood) ∧
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃! a : ℂ,
      ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 2 (localDisk c ρ) (fun p ↦ contStream ω p - saddleQuadratic c a p) D ∧
        ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D := by
  sorry

/-- On every saddle disk, the original jet supplies the ordinary forcing
weights for the continuous stream and its fixed Fourier first derivatives. -/
theorem dd_saddle_forcing_mass {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧
      MemLp (fun p ↦ contStream ω p / (localRadius c p ^ 2 : ℂ)) 2
        (volume.restrict (localDisk c ρ)) ∧
      ∀ j : Fin 2, MemLp (fun p ↦ liftL2 (streamPartial j ω) p /
        (Real.rpow (localRadius c p) (3 / 2) : ℂ)) 2
        (volume.restrict (localDisk c ρ)) := by
  intro c hc
  obtain ⟨ρ, hρ, a, ⟨D, hD, hDw⟩, _⟩ := (saddle_dd hlam hω hs).2 c hc
  have hQ := saddleQuadratic_forcing_mass c a ρ
  have hR0 := memLp_div_localRadius_rpow (m := 4) (t := 2) (by norm_num)
    (hDw 0 (by norm_num) [] rfl)
  have hRval : MemLp (fun p ↦ (contStream ω p - saddleQuadratic c a p) /
      (localRadius c p ^ 2 : ℂ)) 2 (volume.restrict (localDisk c ρ)) := by
    simpa only [hD.1, Real.rpow_eq_pow, Real.rpow_ofNat, Complex.ofReal_pow] using hR0
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  refine ⟨ρ, hρ, ?_, fun j ↦ ?_⟩
  · apply (hRval.add hQ.1).ae_eq
    exact Filter.Eventually.of_forall fun p ↦ by
      dsimp only [Pi.add_apply]
      ring
  · have hRj := memLp_div_localRadius_rpow (m := 3) (t := 3 / 2) (by norm_num)
      (hDw 1 (by norm_num) [j] rfl)
    apply (hRj.add (hQ.2 j)).ae_eq
    filter_upwards [ae_restrict_of_ae (hD.canonical_saddle_first j),
      ae_restrict_mem hU.measurableSet] with p hp hpU
    dsimp only [Pi.add_apply]
    rw [hp hpU]
    change (liftL2 (streamPartial j ω) p - _) / _ + _ / _ = _
    ring

/-- Weaker forcing weights and zero continuous stream values (`lem:dd-weighted-forcing`).
Away from the saddles the weights are bounded, and ordinary H² controls these norms. -/
theorem dd_weighted_forcing {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    MemLp (fun p ↦ contStream ω p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellNeighbourhood) ∧
    (∀ j, MemLp (fun p ↦ liftL2 (streamPartial j ω) p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellNeighbourhood)) ∧
    ∀ p, dipoleLift p = 0 → contStream ω p = 0 := by
  have hlocal := dd_saddle_forcing_mass hlam hω hs
  have hF : MemSobolevLocOn 0 univ (contStream ω) := by
    intro V hV hVc _
    exact memLp_two_restrict_of_continuous (continuous_contStream ω) hV hVc
  have hval := hF.div_saddleDist (s := 2) (by norm_num) (fun c hc ↦ by
    obtain ⟨ρ, hρ, hv, _⟩ := hlocal c hc
    exact ⟨ρ, hρ, by
      simpa only [Real.rpow_eq_pow, Real.rpow_ofNat, Complex.ofReal_pow] using hv⟩)
  refine ⟨?_, fun j ↦ ?_, fun p hp ↦ contStream_eq_zero_on_separatrix hs hp⟩
  · simpa only [Real.rpow_eq_pow, Real.rpow_ofNat, Complex.ofReal_pow] using
      hval.zero_memLp_of_isBounded isBounded_cellNeighbourhood
  · have hj : MemSobolevLocOn 0 univ (liftL2 (streamPartial j ω)) := by
      intro V _ hVc _
      exact memLp_liftL2 _ (hVc.isBounded.subset subset_closure)
    have hgrad := hj.div_saddleDist (s := 3 / 2) (by norm_num) (fun c hc ↦ by
      obtain ⟨ρ, hρ, _, hg⟩ := hlocal c hc
      exact ⟨ρ, hρ, hg j⟩)
    exact hgrad.zero_memLp_of_isBounded isBounded_cellNeighbourhood

end NoEmbeddedEigenvalues
