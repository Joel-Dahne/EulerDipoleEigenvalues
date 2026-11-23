module

public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1

/-!
# Descending interval partitions

Blueprint: `lem:complete-phase-cells`.

Consecutive cells of a strictly decreasing positive sequence accumulating at
zero are disjoint and cover the interval up to the countable set of endpoints.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Filter MeasureTheory
open scoped Topology

/-- Distinct open cells in a descending sequence are disjoint. -/
theorem descending_cells_disjoint {e : ℕ → ℝ} (he : StrictAnti e) :
    Pairwise fun i j ↦ Disjoint (Ioo (e (i + 1)) (e i)) (Ioo (e (j + 1)) (e j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact disjoint_left.2 fun x hx hy ↦
      (not_lt_of_ge (he.antitone (by omega : i + 1 ≤ j))) (hx.1.trans hy.2)
  · exact disjoint_left.2 fun x hx hy ↦
      (not_lt_of_ge (he.antitone (by omega : j + 1 ≤ i))) (hy.1.trans hx.2)

/-- A positive interior point is either an endpoint or lies in an open cell. -/
theorem mem_descending_cell_or_endpoint {e : ℕ → ℝ} (ht : Tendsto e atTop (𝓝 0))
    {x : ℝ} (hx : x ∈ Ioo 0 (e 0)) :
    (∃ n, x ∈ Ioo (e (n + 1)) (e n)) ∨ x ∈ range e := by
  classical
  by_cases hxe : x ∈ range e
  · exact Or.inr hxe
  left
  have hex : ∃ n, e n < x := (ht.eventually (gt_mem_nhds hx.1)).exists
  let k := Nat.find hex
  have hk : e k < x := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    rw [this] at hk
    linarith [hx.2]
  refine ⟨k - 1, ?_, ?_⟩
  · simpa only [show k - 1 + 1 = k by omega] using hk
  · have hle : x ≤ e (k - 1) := not_lt.1 (Nat.find_min hex (by dsimp [k] at hk0 ⊢; omega))
    exact lt_of_le_of_ne hle (fun h ↦ hxe ⟨k - 1, h.symm⟩)

/-- The missing endpoints form a null set. -/
theorem descending_cells_ae_cover {e : ℕ → ℝ} (he : StrictAnti e)
    (hpos : ∀ n, 0 < e n) (ht : Tendsto e atTop (𝓝 0)) :
    (⋃ n, Ioo (e (n + 1)) (e n)) =ᵐ[volume] Ioo 0 (e 0) := by
  have hn : ∀ᵐ x ∂volume, x ∉ range e := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using (countable_range e).measure_zero volume
  filter_upwards [hn] with x hx
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hn⟩
    exact ⟨(hpos (n + 1)).trans hn.1, hn.2.trans_le (he.antitone (Nat.zero_le n))⟩
  · intro hi
    obtain h | h := mem_descending_cell_or_endpoint ht hi
    · exact mem_iUnion.2 h
    · exact (hx h).elim

end NoEmbeddedEigenvalues
