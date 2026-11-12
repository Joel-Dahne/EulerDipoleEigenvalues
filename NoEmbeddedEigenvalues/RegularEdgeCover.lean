import NoEmbeddedEigenvalues.CellFolding
import NoEmbeddedEigenvalues.DiagonalH1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Regular separatrix points in reflected-periodic edge windows

Blueprint: `lem:periodic-regular-edge-cover`.

A Cartesian period representative in `(-π,π]²` lies on a closed cell edge
when its dipole vanishes. Excluding the saddle lattice excludes the corners.
Small one-sided normal windows lie in any prescribed positive strip; joining
such a window to its reflection gives an open physical patch about the point.
This is a spatial cover, not an inference of weak identities from nullity.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Real

private theorem exists_centered_period (x : ℝ) :
    ∃ n : ℤ, x - (n : ℝ) * (2 * π) ∈ Ioc (-π) π := by
  refine ⟨toIocDiv two_pi_pos (-π) x, ?_⟩
  have hm := toIocMod_mem_Ioc two_pi_pos (-π) x
  have he := self_sub_toIocDiv_zsmul two_pi_pos (-π) x
  rw [zsmul_eq_mul] at he
  rw [he]
  simpa only [show -π + 2 * π = π by ring] using hm

private theorem abs_eq_half_pi_of_cos_eq_zero {x : ℝ} (hx : |x| ≤ π)
    (hc : cos x = 0) : |x| = π / 2 := by
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hc
  have hb := abs_le.mp hx
  have hlo : (-2 : ℝ) < (k : ℝ) := by nlinarith [pi_pos]
  have hhi : (k : ℝ) < 1 := by nlinarith [pi_pos]
  have hlo' : -2 < k := by exact_mod_cast hlo
  have hhi' : k < 1 := by exact_mod_cast hhi
  have hk' : k = -1 ∨ k = 0 := by omega
  rcases hk' with rfl | rfl <;> rw [hk] <;>
    norm_num [abs_div, abs_mul, abs_of_pos pi_pos]

private theorem mem_saddleSet_of_corner {q : ℝ × ℝ}
    (ha : |(diagCoord q).1| = π / 2) (hb : |(diagCoord q).2| = π / 2) :
    q ∈ saddleSet := by
  rcases torusProj_corner ha hb with h | h
  · obtain ⟨n, hn⟩ := exists_liftShift_eq (p := (π, 0)) (by simpa [torusProj] using h)
    rw [← hn]
    have hc : (π, (0 : ℝ)) ∈ saddleSet := ⟨1, 0, by decide, by simp⟩
    simpa only [cellFold_apply, Bool.false_eq_true, ite_false] using
      cellFold_mem_saddleSet false n hc
  · obtain ⟨n, hn⟩ := exists_liftShift_eq (p := (0, π)) (by simpa [torusProj] using h)
    rw [← hn]
    have hc : ((0 : ℝ), π) ∈ saddleSet := ⟨0, 1, by decide, by simp⟩
    simpa only [cellFold_apply, Bool.false_eq_true, ite_false] using
      cellFold_mem_saddleSet false n hc

/-- Every nonsaddle separatrix point is a period translate of an open cell edge.
Cartesian period reduction automatically gives compatible diagonal shift parities. -/
theorem exists_periodic_regular_edge {p : ℝ × ℝ} (hp : dipoleLift p = 0)
    (hps : p ∉ saddleSet) :
    ∃ (j : Fin 2) (side : Bool) (n : ℤ × ℤ) (s : ℝ),
      s ∈ Ioo (-π / 2) (π / 2) ∧
      liftShift n (diagonalTraceChart j (s, cellEdgeNormal side)) = p := by
  obtain ⟨m, hm⟩ := exists_centered_period p.1
  obtain ⟨n, hn⟩ := exists_centered_period p.2
  let q := (p.1 - (m : ℝ) * (2 * π), p.2 - (n : ℝ) * (2 * π))
  have he : liftShift (m, n) q = p := by ext <;> simp [liftShift, q]
  have hq : dipoleLift q = 0 := by rw [← dipoleLift_liftShift (m, n) q, he, hp]
  have hqs : q ∉ saddleSet := by
    intro hs
    apply hps
    rw [← he]
    simpa only [cellFold_apply, Bool.false_eq_true, ite_false] using
      cellFold_mem_saddleSet false (m, n) hs
  have hsize : |(diagCoord q).1| + |(diagCoord q).2| ≤ π := by
    dsimp [diagCoord, q]
    rcases abs_cases ((p.1 - (m : ℝ) * (2 * π) +
      (p.2 - (n : ℝ) * (2 * π))) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases ((p.1 - (m : ℝ) * (2 * π) -
        (p.2 - (n : ℝ) * (2 * π))) / 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        linarith [hm.1, hm.2, hn.1, hn.2]
  have hcos : cos (diagCoord q).1 = 0 ∨ cos (diagCoord q).2 = 0 := by
    rw [dipoleLift_eq_diag] at hq
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left (by norm_num))
    · exact Or.inr h
  have hside {x : ℝ} (hx : |x| = π / 2) : ∃ side, x = cellEdgeNormal side := by
    rcases (abs_eq (by positivity)).mp hx with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, by simpa only [cellEdgeNormal, Bool.false_eq_true, ite_false,
        neg_div] using h⟩
  rcases hcos with ha | hb
  · have ha' := abs_eq_half_pi_of_cos_eq_zero
      (by linarith [abs_nonneg (diagCoord q).2]) ha
    have hb' : |(diagCoord q).2| < π / 2 := by
      have hb0 : |(diagCoord q).2| ≤ π / 2 := by linarith
      exact lt_of_le_of_ne hb0 (fun h ↦ hqs (mem_saddleSet_of_corner ha' h))
    obtain ⟨side, hside⟩ := hside ha'
    refine ⟨0, side, (m, n), (diagCoord q).2,
      by simpa only [mem_Ioo, neg_div] using abs_lt.mp hb', ?_⟩
    simp only [diagonalTraceChart, ite_true]
    rw [← hside]
    exact (congrArg (liftShift (m, n)) (diagInv_diagCoord q)).trans he
  · have hb' := abs_eq_half_pi_of_cos_eq_zero
      (by linarith [abs_nonneg (diagCoord q).1]) hb
    have ha' : |(diagCoord q).1| < π / 2 := by
      have ha0 : |(diagCoord q).1| ≤ π / 2 := by linarith
      exact lt_of_le_of_ne ha0 (fun h ↦ hqs (mem_saddleSet_of_corner h hb'))
    obtain ⟨side, hside⟩ := hside hb'
    refine ⟨1, side, (m, n), (diagCoord q).1,
      by simpa only [mem_Ioo, neg_div] using abs_lt.mp ha', ?_⟩
    simp only [diagonalTraceChart, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    rw [← hside]
    exact (congrArg (liftShift (m, n)) (diagInv_diagCoord q)).trans he

/-- Diagonal trace ordering does not change the product factorization. -/
theorem dipoleLift_diagonalTraceChart (j : Fin 2) (q : ℝ × ℝ) :
    dipoleLift (diagonalTraceChart j q) = 2 * cos q.1 * cos q.2 := by
  rw [dipoleLift_eq_diag]
  fin_cases j
  · change 2 * cos (diagCoord (diagInv (q.2, q.1))).1 *
      cos (diagCoord (diagInv (q.2, q.1))).2 = _
    rw [diagCoord_diagInv]
    dsimp
    ring
  · change 2 * cos (diagCoord (diagInv q)).1 * cos (diagCoord (diagInv q)).2 = _
    rw [diagCoord_diagInv]

/-- The exact geometric inputs consumed by the Cartesian edge H¹ producer.
The reflected full window contains the original physical point. -/
theorem exists_regular_edge_window {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : dipoleLift p = 0) (hps : p ∉ saddleSet) :
    ∃ (j : Fin 2) (side : Bool) (n : ℤ × ℤ) (l r a b : ℝ),
      l < r ∧ a < b ∧ Icc l r ⊆ Ioo (-π / 2) (π / 2) ∧
      (if side then b = cellEdgeNormal side else a = cellEdgeNormal side) ∧
      diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ cellSeparatrixStrip ε ∧
      p ∈ (liftShift n ∘ diagonalTraceChart j) ''
        (Ioo l r ×ˢ Ioo (if side then a else 2 * cellEdgeNormal side - b)
          (if side then 2 * cellEdgeNormal side - a else b)) := by
  obtain ⟨j, side, n, s, hs, he⟩ := exists_periodic_regular_edge hp hps
  let δ := min (ε / 4) (π / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδπ : δ ≤ π / 4 := min_le_right _ _
  let l := (-π / 2 + s) / 2
  let r := (s + π / 2) / 2
  let e := cellEdgeNormal side
  let a := if side then e - δ else e
  let b := if side then e else e + δ
  have hl : l < s := by dsimp [l]; linarith [hs.1]
  have hr : s < r := by dsimp [r]; linarith [hs.2]
  have hI : Icc l r ⊆ Ioo (-π / 2) (π / 2) := by
    intro t ht
    dsimp [l, r] at ht
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have hab : a < b := by cases side <;> dsimp [a, b] <;> linarith
  have hedge : (if side then b = cellEdgeNormal side else a = cellEdgeNormal side) := by
    cases side <;> rfl
  have hcos : cos e = 0 := by cases side <;> simp [e, cellEdgeNormal, neg_div]
  refine ⟨j, side, n, l, r, a, b, hl.trans hr, hab, hI, hedge, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hqt : q.1 ∈ Ioo (-π / 2) (π / 2) := hI (Ioo_subset_Icc_self hq.1)
    have hqn : q.2 ∈ Ioo (-π / 2) (π / 2) := by
      cases side <;> dsimp [a, b, e, cellEdgeNormal] at hq ⊢ <;>
        constructor <;> linarith [hq.2.1, hq.2.2, pi_pos]
    have hdist : |q.2 - e| < δ := by
      rw [abs_lt]
      cases side <;> dsimp [a, b] at hq <;> constructor <;>
        linarith [hq.2.1, hq.2.2]
    have hcell : diagonalTraceChart j q ∈ cellSquare := by
      have ht : |q.1| < π / 2 := abs_lt.mpr (by simpa only [mem_Ioo, neg_div] using hqt)
      have hn : |q.2| < π / 2 := abs_lt.mpr (by simpa only [mem_Ioo, neg_div] using hqn)
      fin_cases j
      · change |(diagCoord (diagInv (q.2, q.1))).1| < π / 2 ∧
          |(diagCoord (diagInv (q.2, q.1))).2| < π / 2
        simpa only [diagCoord_diagInv] using And.intro hn ht
      · change |(diagCoord (diagInv q)).1| < π / 2 ∧
          |(diagCoord (diagInv q)).2| < π / 2
        simpa only [diagCoord_diagInv] using And.intro ht hn
    have hpos : 0 < dipoleLift (diagonalTraceChart j q) := by
      simpa only [positiveCell, mem_ofPred_eq, Ψ_torusProj] using
        torusProj_mem_positiveCell hcell
    refine ⟨hcell, hpos, ?_⟩
    have hc := abs_cos_sub_cos_le q.2 e
    rw [hcos, sub_zero] at hc
    have hnpos : 0 < cos q.2 := cos_pos_of_mem_Ioo (by
      simpa only [neg_div] using hqn)
    have hu : cos q.2 ≤ |q.2 - e| := (le_abs_self _).trans hc
    rw [dipoleLift_diagonalTraceChart]
    nlinarith [cos_le_one q.1]
  · refine ⟨(s, e), ⟨⟨hl, hr⟩, ?_⟩, he⟩
    cases side <;> dsimp [a, b] <;> constructor <;> linarith

end NoEmbeddedEigenvalues
