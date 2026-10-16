import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import NoEmbeddedEigenvalues.LiftTorus

/-!
# Cells, separatrix and critical points of the dipole

Blueprint: `def:cells`, `lem:dipole-product`, `lem:separatrix-lines`,
`lem:dipole-critical-points`, `lem:cell-square`; `lem:cell-periodic-integral` (stated).

In the diagonal coordinates `a = (x + y)/2`, `b = (x - y)/2` the dipole is
`Ψ = 2 cos a cos b`. Hence the separatrix `{Ψ = 0}` is the union of the lines
`x + y ≡ π` and `x - y ≡ π`, the fixed lines of `S₁` and `S₂`, and the positive cell
`{Ψ > 0}` is the image of the open square `|a|, |b| < π/2`, on which the covering
map is injective.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real

/-- The positive cell `{Ψ > 0}`. -/
def positiveCell : Set Torus := {t | 0 < Ψ t}

/-- The negative cell `{Ψ < 0}`. -/
def negativeCell : Set Torus := {t | Ψ t < 0}

/-- The separatrix `{Ψ = 0}`. -/
def separatrix : Set Torus := {t | Ψ t = 0}

/-- The diagonal coordinates `a = (x + y)/2`, `b = (x - y)/2` on the lift. -/
def diagCoord (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + p.2) / 2, (p.1 - p.2) / 2)

/-- The open square `|a|, |b| < π/2` in diagonal coordinates, as a subset of the lift. -/
def cellSquare : Set (ℝ × ℝ) := {p | |(diagCoord p).1| < π / 2 ∧ |(diagCoord p).2| < π / 2}

/-- `Ψ = 2 cos a cos b`. -/
theorem dipoleLift_eq_diag (p : ℝ × ℝ) :
    dipoleLift p = 2 * cos (diagCoord p).1 * cos (diagCoord p).2 := by
  simp only [dipoleLift, diagCoord]
  rw [cos_add_cos]

theorem Ψ_torusProj (p : ℝ × ℝ) : Ψ (torusProj p) = dipoleLift p := Ψ_coe p.1 p.2

/-- The separatrix is the union of the lines `x + y ≡ π` and `x - y ≡ π`. -/
theorem Ψ_eq_zero_iff (t : Torus) : Ψ t = 0 ↔ t.1 + t.2 = π ∨ t.1 - t.2 = π := by
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
  rw [Ψ_torusProj, dipoleLift_eq_diag]
  simp only [torusProj, diagCoord, ← Angle.coe_add, ← Angle.coe_sub,
    Angle.angle_eq_iff_two_pi_dvd_sub]
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rw [mul_assoc, mul_eq_zero, mul_eq_zero, or_iff_right h2, cos_eq_zero_iff, cos_eq_zero_iff]
  refine or_congr (exists_congr fun k ↦ ?_) (exists_congr fun k ↦ ?_) <;>
    constructor <;> intro h <;> linarith

/-- `S₁` fixes exactly the line `x + y ≡ π`. -/
theorem S₁_eq_self_iff (t : Torus) : S₁ t = t ↔ t.1 + t.2 = π := by
  constructor
  · intro h
    have h1 : π - t.2 = t.1 := congrArg Prod.fst h
    rw [← h1]
    abel
  · intro h
    ext
    · change π - t.2 = t.1
      rw [← h]
      abel
    · change π - t.1 = t.2
      rw [← h]
      abel

/-- `S₂` fixes exactly the line `x - y ≡ π`. -/
theorem S₂_eq_self_iff (t : Torus) : S₂ t = t ↔ t.1 - t.2 = π := by
  constructor
  · intro h
    have h1 : π + t.2 = t.1 := congrArg Prod.fst h
    rw [← h1]
    abel
  · intro h
    ext
    · change π + t.2 = t.1
      rw [← h]
      abel
    · change π + t.1 = t.2
      calc (π : Angle) + t.1 = -(π : Angle) + t.1 := by rw [Angle.neg_coe_pi]
        _ = -(t.1 - t.2) + t.1 := by rw [h]
        _ = t.2 := by abel

/-- The separatrix is the union of the fixed lines of the two reflections. -/
theorem mem_separatrix_iff (t : Torus) : t ∈ separatrix ↔ S₁ t = t ∨ S₂ t = t := by
  rw [separatrix, Set.mem_ofPred_eq, Ψ_eq_zero_iff, S₁_eq_self_iff, S₂_eq_self_iff]

/-! ### Critical points -/

/-- On the lift, `∇Ψ = 0` exactly where `sin x = sin y = 0`. -/
theorem gradSq_dipoleLift_eq_zero_iff (p : ℝ × ℝ) :
    gradSq dipoleLift p = 0 ↔ sin p.1 = 0 ∧ sin p.2 = 0 := by
  rw [gradSq_dipoleLift]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (sin p.1), sq_nonneg (sin p.2)]
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-- The critical points of `Ψ` on the torus: the centers `(0,0)`, `(π,π)` and the saddles
    `(π,0)`, `(0,π)`. -/
theorem critical_points_iff (t : Torus) :
    t.1.sin = 0 ∧ t.2.sin = 0 ↔
      t = (0, 0) ∨ t = ((π : Angle), (π : Angle)) ∨ t = ((π : Angle), 0) ∨
        t = (0, (π : Angle)) := by
  rw [Angle.sin_eq_zero_iff, Angle.sin_eq_zero_iff]
  obtain ⟨a, b⟩ := t
  simp only [Prod.mk.injEq]
  tauto

theorem Ψ_center : Ψ (0, 0) = 2 := by norm_num [Ψ]

theorem Ψ_anticenter : Ψ ((π : Angle), (π : Angle)) = -2 := by norm_num [Ψ, Angle.cos_coe_pi]

theorem Ψ_saddle₁ : Ψ ((π : Angle), 0) = 0 := by norm_num [Ψ, Angle.cos_coe_pi]

theorem Ψ_saddle₂ : Ψ (0, (π : Angle)) = 0 := by norm_num [Ψ, Angle.cos_coe_pi]

theorem Ψ_le_two (t : Torus) : Ψ t ≤ 2 := by
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
  rw [Ψ_torusProj, dipoleLift]
  linarith [cos_le_one x, cos_le_one y]

theorem neg_two_le_Ψ (t : Torus) : -2 ≤ Ψ t := by
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
  rw [Ψ_torusProj, dipoleLift]
  linarith [neg_one_le_cos x, neg_one_le_cos y]

/-- The maximum `2` is attained only at the center `(0,0)`. -/
theorem Ψ_eq_two_iff (t : Torus) : Ψ t = 2 ↔ t = (0, 0) := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
    rw [Ψ_torusProj, dipoleLift] at h
    have hx : cos x = 1 := by linarith [cos_le_one x, cos_le_one y]
    have hy : cos y = 1 := by linarith [cos_le_one x, cos_le_one y]
    have ex : ((x : Angle)).cos = (0 : Angle).cos := by rw [Angle.cos_coe, hx, Angle.cos_zero]
    have ey : ((y : Angle)).cos = (0 : Angle).cos := by rw [Angle.cos_coe, hy, Angle.cos_zero]
    rw [Angle.cos_eq_iff_eq_or_eq_neg, neg_zero, or_self] at ex ey
    simp [torusProj, ex, ey]
  · rintro rfl
    exact Ψ_center

/-- The minimum `-2` is attained only at `(π,π)`. -/
theorem Ψ_eq_neg_two_iff (t : Torus) : Ψ t = -2 ↔ t = ((π : Angle), (π : Angle)) := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
    rw [Ψ_torusProj, dipoleLift] at h
    have hx : cos x = -1 := by linarith [neg_one_le_cos x, neg_one_le_cos y]
    have hy : cos y = -1 := by linarith [neg_one_le_cos x, neg_one_le_cos y]
    have ex : ((x : Angle)).cos = (π : Angle).cos := by rw [Angle.cos_coe, hx, Angle.cos_coe_pi]
    have ey : ((y : Angle)).cos = (π : Angle).cos := by rw [Angle.cos_coe, hy, Angle.cos_coe_pi]
    rw [Angle.cos_eq_iff_eq_or_eq_neg, Angle.neg_coe_pi, or_self] at ex ey
    simp [torusProj, ex, ey]
  · rintro rfl
    exact Ψ_anticenter

/-! ### The cell as a square -/

/-- An integer multiple of `π` of absolute value less than `π` vanishes. -/
theorem int_eq_zero_of_abs_mul_pi_lt {n : ℤ} (h : |(n : ℝ) * π| < π) : n = 0 := by
  rw [abs_lt] at h
  have h1 : (n : ℝ) < 1 := by nlinarith [pi_pos]
  have h2 : (-1 : ℝ) < n := by nlinarith [pi_pos]
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : -1 < n := by exact_mod_cast h2
  omega

/-- The covering map is injective on the open square. -/
theorem injOn_torusProj_cellSquare : Set.InjOn torusProj cellSquare := by
  rintro ⟨x, y⟩ ⟨hpa, hpb⟩ ⟨x', y'⟩ ⟨hqa, hqb⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨k, hk⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.1 h1
  obtain ⟨m, hm⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.1 h2
  simp only [diagCoord, abs_lt] at hpa hpb hqa hqb
  have hkm : k + m = 0 := int_eq_zero_of_abs_mul_pi_lt (by
    rw [abs_lt]; push_cast; constructor <;> nlinarith)
  have hkm' : k - m = 0 := int_eq_zero_of_abs_mul_pi_lt (by
    rw [abs_lt]; push_cast; constructor <;> nlinarith)
  have hk0 : k = 0 := by omega
  have hm0 : m = 0 := by omega
  subst hk0 hm0
  simp only [Int.cast_zero, mul_zero, sub_eq_zero] at hk hm
  rw [hk, hm]

/-- Points of the open square lie in the positive cell. -/
theorem torusProj_mem_positiveCell {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    torusProj p ∈ positiveCell := by
  obtain ⟨ha, hb⟩ := hp
  rw [abs_lt] at ha hb
  have hca := cos_pos_of_mem_Ioo ⟨ha.1, ha.2⟩
  have hcb := cos_pos_of_mem_Ioo ⟨hb.1, hb.2⟩
  change 0 < Ψ (torusProj p)
  rw [Ψ_torusProj, dipoleLift_eq_diag]
  positivity

/-- Every point of the positive cell lifts to the open square. -/
theorem exists_mem_cellSquare {t : Torus} (ht : t ∈ positiveCell) :
    ∃ p ∈ cellSquare, torusProj p = t := by
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
  have hpos : 0 < dipoleLift (x, y) := by
    have h := ht
    change 0 < Ψ (torusProj (x, y)) at h
    rwa [Ψ_torusProj] at h
  have hπ := pi_pos
  have h2π : 0 < 2 * π := by positivity
  set a := (x + y) / 2
  set b := (x - y) / 2
  -- Reduce `a` modulo `π` and then `b` modulo `2π`.
  set z := toIocDiv hπ (-(π / 2)) a
  set a' := toIocMod hπ (-(π / 2)) a
  have ha' : a' = a - z * π := by
    have h := (self_sub_toIocDiv_zsmul hπ (-(π / 2)) a).symm
    rw [zsmul_eq_mul] at h
    exact h
  have ha'mem : a' ∈ Set.Ioc (-(π / 2)) (-(π / 2) + π) := toIocMod_mem_Ioc hπ (-(π / 2)) a
  set w := toIcoDiv h2π (-(π / 2)) (b - z * π)
  set b' := toIcoMod h2π (-(π / 2)) (b - z * π)
  have hb' : b' = b - z * π - w * (2 * π) := by
    have h := (self_sub_toIcoDiv_zsmul h2π (-(π / 2)) (b - z * π)).symm
    rw [zsmul_eq_mul] at h
    exact h
  have hb'mem : b' ∈ Set.Ico (-(π / 2)) (-(π / 2) + 2 * π) :=
    toIcoMod_mem_Ico h2π (-(π / 2)) (b - z * π)
  -- The shifted lift.
  refine ⟨(x - 2 * π * (z + w), y + 2 * π * w), ?_, ?_⟩
  · have hda : (diagCoord (x - 2 * π * (z + w), y + 2 * π * w)).1 = a' := by
      simp only [diagCoord, ha', a]; ring
    have hdb : (diagCoord (x - 2 * π * (z + w), y + 2 * π * w)).2 = b' := by
      simp only [diagCoord, hb', b]; ring
    have hψ : dipoleLift (x - 2 * π * (z + w), y + 2 * π * w) = dipoleLift (x, y) := by
      simp only [dipoleLift]
      rw [show x - 2 * π * (z + w) = x + ((-(z + w) : ℤ) : ℝ) * (2 * π) by push_cast; ring,
        show y + 2 * π * w = y + (w : ℝ) * (2 * π) by ring, cos_add_int_mul_two_pi,
        cos_add_int_mul_two_pi]
    rw [← hψ, dipoleLift_eq_diag, hda, hdb] at hpos
    rw [Set.mem_Ioc] at ha'mem
    rw [Set.mem_Ico] at hb'mem
    have ha'lt : a' < π / 2 := by
      rcases lt_or_eq_of_le ha'mem.2 with hlt | heq
      · linarith
      · exfalso
        have : cos a' = 0 := by rw [heq, show -(π / 2) + π = π / 2 by ring, cos_pi_div_two]
        rw [this] at hpos
        simp at hpos
    have hca : 0 < cos a' := cos_pos_of_mem_Ioo ⟨ha'mem.1, ha'lt⟩
    have hcb : 0 < cos b' := by
      by_contra hneg
      have := not_lt.1 hneg
      nlinarith
    have hb'hi : b' < π / 2 := by
      by_contra hge
      have := cos_nonpos_of_pi_div_two_le_of_le (not_lt.1 hge) (by linarith [hb'mem.2])
      linarith
    have hb'lo : -(π / 2) < b' := by
      rcases lt_or_eq_of_le hb'mem.1 with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq, cos_neg, cos_pi_div_two] at hcb
        exact lt_irrefl 0 hcb
    refine ⟨?_, ?_⟩
    · rw [hda, abs_lt]
      exact ⟨ha'mem.1, ha'lt⟩
    · rw [hdb, abs_lt]
      exact ⟨hb'lo, hb'hi⟩
  · simp only [torusProj, Prod.mk.injEq]
    constructor
    · rw [Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨-(z + w), by push_cast; ring⟩
    · rw [Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨w, by ring⟩

/-- The positive cell is the image of the open square `|a|, |b| < π/2`, and the covering map
    is injective there. -/
theorem image_torusProj_cellSquare : torusProj '' cellSquare = positiveCell := by
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact torusProj_mem_positiveCell hp
  · intro ht
    obtain ⟨p, hp, rfl⟩ := exists_mem_cellSquare ht
    exact ⟨p, hp, rfl⟩

/-! ### Edges and corners of the square -/

theorem coe_eq_pi_of_eq_pi_or_neg {θ : ℝ} (h : θ = π ∨ θ = -π) : (θ : Angle) = π := by
  rcases h with rfl | rfl
  · rfl
  · rw [Angle.coe_neg, Angle.neg_coe_pi]

/-- The edges `a = ±π/2` of the square lie on the fixed line of `S₁`. -/
theorem S₁_torusProj_of_edge {p : ℝ × ℝ}
    (h : (diagCoord p).1 = π / 2 ∨ (diagCoord p).1 = -(π / 2)) :
    S₁ (torusProj p) = torusProj p := by
  rw [S₁_eq_self_iff]
  change ((p.1 : Angle) + (p.2 : Angle)) = π
  rw [← Angle.coe_add]
  apply coe_eq_pi_of_eq_pi_or_neg
  simp only [diagCoord] at h
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- The edges `b = ±π/2` of the square lie on the fixed line of `S₂`. -/
theorem S₂_torusProj_of_edge {p : ℝ × ℝ}
    (h : (diagCoord p).2 = π / 2 ∨ (diagCoord p).2 = -(π / 2)) :
    S₂ (torusProj p) = torusProj p := by
  rw [S₂_eq_self_iff]
  change ((p.1 : Angle) - (p.2 : Angle)) = π
  rw [← Angle.coe_sub]
  apply coe_eq_pi_of_eq_pi_or_neg
  simp only [diagCoord] at h
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- The four corners `a, b = ±π/2` of the square project to the two saddles. -/
theorem torusProj_corner {p : ℝ × ℝ} (ha : |(diagCoord p).1| = π / 2)
    (hb : |(diagCoord p).2| = π / 2) :
    torusProj p = ((π : Angle), 0) ∨ torusProj p = (0, (π : Angle)) := by
  have hπ := pi_pos
  simp only [diagCoord] at ha hb
  obtain ⟨x, y⟩ := p
  simp only [torusProj, Prod.mk.injEq]
  rcases abs_eq (by positivity) |>.1 ha with ha | ha <;>
    rcases abs_eq (by positivity) |>.1 hb with hb | hb
  · have h1 : x = π := by linarith
    have h2 : y = 0 := by linarith
    left
    simp [h1, h2]
  · have h1 : x = 0 := by linarith
    have h2 : y = π := by linarith
    right
    simp [h1, h2]
  · have h1 : x = 0 := by linarith
    have h2 : y = -π := by linarith
    right
    simp [h1, h2, Angle.coe_neg, Angle.neg_coe_pi]
  · have h1 : x = -π := by linarith
    have h2 : y = 0 := by linarith
    left
    simp [h1, h2, Angle.coe_neg, Angle.neg_coe_pi]

/-- Integrals of periodic functions supported in the cells (`lem:cell-periodic-integral`): if
    `F` is periodic, a.e. strongly measurable and vanishes where `Ψ ≤ 0`, its integral over the
    period square equals its integral over the cell square. In `(-π, π]²` the set `{Ψ > 0}`
    is exactly the cell square, and both squares are fundamental domains. -/
theorem squareIntegral_eq_setIntegral_cellSquare {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × ℝ → E} (hF : IsPeriodicLift F)
    (hm : MeasureTheory.AEStronglyMeasurable F)
    (h0 : ∀ p, dipoleLift p ≤ 0 → F p = 0) :
    squareIntegral F = ∫ p in cellSquare, F p ∂MeasureTheory.volume := by
  sorry

end NoEmbeddedEigenvalues
