import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Finite sums in local Sobolev spaces -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff Manifold

/-- The zero function is in every integer-order local-domain Sobolev space. -/
theorem MemSobolevOn.zero (k : ℕ) (U : Set (ℝ × ℝ)) :
    MemSobolevOn k U (fun _ ↦ (0 : ℂ)) := by
  induction k with
  | zero => exact MemLp.zero'
  | succ k ih =>
    exact ⟨MemLp.zero', fun _ ↦
      ⟨_, ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by simp⟩, ih⟩⟩

/-- A finite sum of Sobolev functions has the same Sobolev order. -/
theorem MemSobolevOn.finset_sum {ι : Type*} {k : ℕ} {U : Set (ℝ × ℝ)}
    {f : ι → ℝ × ℝ → ℂ} (s : Finset ι) (hf : ∀ i ∈ s, MemSobolevOn k U (f i)) :
    MemSobolevOn k U (fun p ↦ ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MemSobolevOn.zero k U
  | @insert i s hi ih =>
    simpa only [MemSobolevOn, Finset.sum_insert hi] using
      MemSobolevOnWith.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end NoEmbeddedEigenvalues
