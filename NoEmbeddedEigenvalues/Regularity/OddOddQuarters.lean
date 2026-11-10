import NoEmbeddedEigenvalues.Regularity.OddOddQuarterTime
import NoEmbeddedEigenvalues.QuarterRotation

/-!
# Strong weighted derivatives on all recentered quarters

Blueprint: `lem:dd-quarter-weighted-derivatives`.

The same base-quarter cutoff works for all four rotations. Joint a.e.
character identities transfer weak derivatives of the actual raw pullbacks;
invariance of the saddle distance transfers the time-derivative weight.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Every separately recentered quarter has specified weak coordinate derivatives
with the two different weights needed for Cartesian gradient reconstruction. -/
theorem dd_quarter_weighted_derivatives {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧
      ∃ H T : Fin 4 → (ℝ × ℝ → ℂ), ∀ k : Fin 4,
        HasWeakPartialOn (quarterOrbitStrip b) 0
          (fun q ↦ liftL2 ω (recenteredQuarterMap k q)) (H k) ∧
        HasWeakPartialOn (quarterOrbitStrip b) 1
          (fun q ↦ liftL2 ω (recenteredQuarterMap k q)) (T k) ∧
        MemLp (H k) 2 (volume.restrict (quarterOrbitStrip b)) ∧
        MemLp (fun q ↦ T k q / (saddleDist (recenteredQuarterMap k q) ^ 2 : ℂ)) 2
          (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨b, hb, hbhalf, H, T, hH, hT, hHl, hTl⟩ :=
    dd_base_quarter_weighted_derivatives hlam hω hs hκ
  refine ⟨b, hb, hbhalf, (fun k q ↦ paritySign κ ^ k.val * H q),
    (fun k q ↦ paritySign κ ^ k.val * T q), ?_⟩
  intro k
  have hchar : ∀ᵐ q, q ∈ quarterOrbitStrip b →
      paritySign κ ^ k.val * liftL2 ω (dipoleOrbit q.1 q.2) =
        liftL2 ω (recenteredQuarterMap k q) :=
    (ae_restrict_iff' (measurableSet_quarterOrbitStrip b)).1
      (liftL2_recenteredQuarterMap_ae (by linarith : b ≤ 1) hκ k).symm
  refine ⟨(hH.const_mul _).congr_ae_on (measurableSet_quarterOrbitStrip b)
      hchar (Eventually.of_forall fun _ _ ↦ rfl),
    (hT.const_mul _).congr_ae_on (measurableSet_quarterOrbitStrip b)
      hchar (Eventually.of_forall fun _ _ ↦ rfl), hHl.const_mul _, ?_⟩
  apply (hTl.const_mul (paritySign κ ^ k.val)).ae_eq
  exact Eventually.of_forall fun q ↦ by
    simp only [recenteredQuarterMap, saddleDist_rotLift_iterate]
    ring

end NoEmbeddedEigenvalues
