module

public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBTrace.Centered
public import NoEmbeddedEigenvalues.Certificates.Inequalities.MixedOddBLog

/-! # From scaled strip interval bounds to endpoint signs -/

@[expose] public section

namespace NoEmbeddedEigenvalues.MixedOddBTrace.Scaled

open Set
open Finset hiding Icc

private theorem logTaylor_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    certificateLogTaylor y ≤ certificateLogTaylor x := by
  unfold certificateLogTaylor
  apply neg_le_neg
  gcongr

private theorem logTail_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x ^ 15 / (15 * (1 - x)) ≤ y ^ 15 / (15 * (1 - y)) := by
  have hxp : 0 ≤ x ^ 15 := pow_nonneg hx _
  have hn : x ^ 15 ≤ y ^ 15 := by gcongr
  exact div_le_div₀ (hxp.trans hn) hn (by linarith) (by linarith)

-- Freeze rational log-two bounds once, before evaluating the endpoint series.
private theorem logTwoLower :
    (6931471805599453 / 10 ^ 16 : ℝ) ≤ (certificateLogTwoLower : ℝ) := by
  have h : (6931471805599453 / 10 ^ 16 : ℚ) ≤ certificateLogTwoLower := by
    norm_num [certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

private theorem logTwoUpper :
    (certificateLogTwoUpper : ℝ) ≤ (6931471805599454 / 10 ^ 16 : ℝ) := by
  have h : certificateLogTwoUpper ≤ (6931471805599454 / 10 ^ 16 : ℚ) := by
    norm_num [certificateLogTwoUpper, certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

noncomputable def X (j : ℕ) (h : ℝ) : ℝ := 1 - (2 : ℝ) ^ j * h

noncomputable def lo (j : ℕ) (h : ℝ) : ℝ :=
  -(j : ℝ) * (certificateLogTwoUpper : ℝ) + certificateLogTaylor (X j h) -
    (X j h) ^ 15 / (15 * (1 - X j h))

noncomputable def hi (j : ℕ) (h : ℝ) : ℝ :=
  -(j : ℝ) * (certificateLogTwoLower : ℝ) + certificateLogTaylor (X j h)

/-- The scaled horizontal interval stays inside the range of the Taylor bound. -/
def Valid (j : ℕ) (a b : ℝ) : Prop := 1 / 2 ≤ (2 : ℝ) ^ j * a ∧ (2 : ℝ) ^ j * b ≤ 1

private theorem x_anti (j : ℕ) {a b : ℝ} (h : a ≤ b) : X j b ≤ X j a :=
  sub_le_sub_left (mul_le_mul_of_nonneg_left h (by positivity)) _

private theorem x_range {j : ℕ} {a b h : ℝ} (hv : Valid j a b) (hh : h ∈ Icc a b) :
    X j h ∈ Icc 0 (1 / 2) := by
  have h₁ : 0 ≤ X j b := sub_nonneg.mpr hv.2
  have h₂ : X j a ≤ 1 / 2 := by unfold X; linarith only [hv.1]
  exact ⟨h₁.trans (x_anti j hh.2), (x_anti j hh.1).trans h₂⟩

private theorem pos_left {j : ℕ} {a b : ℝ} (hv : Valid j a b) : 0 < a :=
  pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hv.1) (by positivity)

private theorem log_mem {j : ℕ} {a b h : ℝ} (hv : Valid j a b)
    (hh : h ∈ Icc a b) : Real.log h ∈ Icc (lo j h) (hi j h) := by
  have hx := x_range hv hh
  have hpos : 0 < 1 - X j h := by linarith only [hx.2]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have he : Real.log h = -(j : ℝ) * Real.log 2 + Real.log (1 - X j h) := by
    have hs : h = (2 : ℝ)⁻¹ ^ j * (1 - X j h) := by
      rw [inv_pow]
      unfold X
      rw [sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    conv_lhs => rw [hs, Real.log_mul (by positivity) hpos.ne', Real.log_pow, Real.log_inv]
    ring
  rw [he]
  obtain ⟨hl, hu⟩ := certificate_log_one_sub_bounds hx
  obtain ⟨h₂l, h₂u⟩ := certificate_log_two_bounds
  have hl₂ := mul_le_mul_of_nonneg_left h₂u hj
  have hu₂ := mul_le_mul_of_nonneg_left h₂l hj
  constructor
  · unfold lo; linarith only [hl, hl₂]
  · unfold hi; linarith only [hu, hu₂]

def Window (j : ℕ) (a b L U : ℝ) : Prop :=
  ∀ h ∈ Icc a b, L ≤ lo j h ∧ hi j h ≤ U

theorem window {j : ℕ} {a b L U : ℝ} (hv : Valid j a b)
    (hL : L ≤ -(j : ℝ) * (6931471805599454 / 10 ^ 16) + certificateLogTaylor (X j a) -
      (X j a) ^ 15 / (15 * (1 - X j a)))
    (hU : -(j : ℝ) * (6931471805599453 / 10 ^ 16) + certificateLogTaylor (X j b) ≤ U) :
    Window j a b L U := by
  intro h hh
  have hx := x_range hv hh
  have hxa : X j h ≤ X j a := x_anti j hh.1
  have hxb : X j b ≤ X j h := x_anti j hh.2
  have hx₀ : 0 ≤ X j b := sub_nonneg.mpr hv.2
  have hxa₁ : X j a < 1 := by unfold X; linarith only [hv.1]
  have ht₁ := logTaylor_anti hx.1 hxa
  have ht₂ := logTaylor_anti hx₀ hxb
  have htail := logTail_mono hx.1 hxa hxa₁
  have hl := mul_le_mul_of_nonneg_left logTwoUpper (Nat.cast_nonneg (α := ℝ) j)
  have hu := mul_le_mul_of_nonneg_left logTwoLower (Nat.cast_nonneg (α := ℝ) j)
  exact ⟨by unfold lo; linarith only [hL, ht₁, htail, hl],
    by unfold hi; linarith only [hU, ht₂, hu]⟩

theorem window_wide {j : ℕ} {a b L U L' U' e : ℝ} (hv : Valid j a b)
    (hw : Window j a b L U) (hl : L' ≤ L - e) (hu : U + e ≤ U')
    {h off : ℝ} (hh : h ∈ Icc a b) (he : |off| ≤ e) :
    Real.log h + off ∈ Icc L' U' := by
  have hlog := log_mem hv hh
  obtain ⟨hl', hu'⟩ := hw h hh
  obtain ⟨hel, heu⟩ := abs_le.mp he
  exact ⟨by linarith only [hl, hl', hlog.1, hel], by linarith only [hu, hu', hlog.2, heu]⟩

def Gap (j : ℕ) (a b e : ℝ) : Prop := ∀ h ∈ Icc a b, hi j h - lo j h ≤ e

theorem gap {j : ℕ} {a b e : ℝ} (hv : Valid j a b)
    (he : (j : ℝ) * ((6931471805599454 - 6931471805599453) / 10 ^ 16 : ℝ) +
      (X j a) ^ 15 / (15 * (1 - X j a)) ≤ e) :
    Gap j a b e := by
  intro h hh
  have hx := x_range hv hh
  have hxa : X j h ≤ X j a := x_anti j hh.1
  have hxa₁ : X j a < 1 := by unfold X; linarith only [hv.1]
  have htail := logTail_mono hx.1 hxa hxa₁
  unfold lo hi
  have hl := mul_le_mul_of_nonneg_left logTwoUpper (Nat.cast_nonneg (α := ℝ) j)
  have hu := mul_le_mul_of_nonneg_left logTwoLower (Nat.cast_nonneg (α := ℝ) j)
  linarith only [he, htail, hl, hu]

def Box (j : ℕ) (a b c d : ℝ) : Prop :=
  ∀ {h k : ℝ}, h ∈ Icc a b → k ∈ Icc c d →
    0 ≤ mixedOddBCleared h k (lo j h) ∧ 0 ≤ mixedOddBCleared h k (hi j h)

theorem splitH {j : ℕ} {a b c d m : ℝ} (hl : Box j a m c d) (hr : Box j m b c d) :
    Box j a b c d := by
  intro h k hh hk
  rcases le_or_gt h m with hm | hm
  · exact hl ⟨hh.1, hm⟩ hk
  · exact hr ⟨hm.le, hh.2⟩ hk

theorem splitK {j : ℕ} {a b c d m : ℝ} (hl : Box j a b c m) (hr : Box j a b m d) :
    Box j a b c d := by
  intro h k hh hk
  rcases le_or_gt k m with hm | hm
  · exact hl hh ⟨hk.1, hm⟩
  · exact hr hh ⟨hm.le, hk.2⟩

theorem plain {j : ℕ} {a b c d L U : ℝ} (hv : Valid j a b)
    (hw : Window j a b L U)
    (hp : ∀ {h k l : ℝ}, h ∈ Icc a b → k ∈ Icc c d → l ∈ Icc L U →
      0 ≤ mixedOddBCleared h k l) : Box j a b c d := by
  intro h k hh hk
  have hlog := log_mem hv hh
  have hle := hlog.1.trans hlog.2
  obtain ⟨hl, hu⟩ := hw h hh
  exact ⟨hp hh hk ⟨hl, hle.trans hu⟩, hp hh hk ⟨hl.trans hle, hu⟩⟩

theorem divide {v h a b l u L U : ℝ} (ha : 0 < a) (hh : h ∈ Icc a b)
    (hv : v ∈ Icc l u) (hl₁ : L * a ≤ l) (hl₂ : L * b ≤ l)
    (hu₁ : u ≤ U * a) (hu₂ : u ≤ U * b) :
    v / h ∈ Icc L U := by
  have hh₀ := ha.trans_le hh.1
  refine ⟨(le_div_iff₀ hh₀).2 ?_, (div_le_iff₀ hh₀).2 ?_⟩
  · rcases le_or_gt 0 L with hL | hL
    · exact (mul_le_mul_of_nonneg_left hh.2 hL).trans (hl₂.trans hv.1)
    · exact (mul_le_mul_of_nonpos_left hh.1 hL.le).trans (hl₁.trans hv.1)
  · rcases le_or_gt 0 U with hU | hU
    · exact (hv.2.trans hu₁).trans (mul_le_mul_of_nonneg_left hh.1 hU)
    · exact (hv.2.trans hu₂).trans (mul_le_mul_of_nonpos_left hh.2 hU.le)

theorem abs_sum_bound {x y xl xu yl yu D : ℝ}
    (hx : x ∈ Icc xl xu) (hy : y ∈ Icc yl yu)
    (hl : -D ≤ xl + yl) (hu : xu + yu ≤ D) : |x + y| ≤ D :=
  abs_le.mpr ⟨hl.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hu⟩

theorem centered {j : ℕ} {a b c d m n ε lb D E r s L U LM UM : ℝ}
    (hv : Valid j a b)
    (hm : m ∈ Icc a b) (hn : n ∈ Icc c d)
    (hg : Gap j a b ε)
    (hW : ∀ {h e : ℝ}, h ∈ Icc a b → |e| ≤ ε → Real.log h + e ∈ Icc L U)
    (hM : ∀ {e : ℝ}, |e| ≤ ε → Real.log m + e ∈ Icc LM UM)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hr₁ : -r ≤ a - m) (hr₂ : b - m ≤ r)
    (hs₁ : -s ≤ c - n) (hs₂ : d - n ≤ s)
    (hp : 0 ≤ lb - D * r - E * s)
    (value : ∀ {l : ℝ}, l ∈ Icc LM UM → lb ≤ mixedOddBCleared m n l)
    (dh : ∀ {x l : ℝ}, x ∈ Icc a b → l ∈ Icc L U →
      |groupedDH x n l + groupedB x n / x| ≤ D)
    (dk : ∀ {h k l : ℝ}, h ∈ Icc a b → k ∈ Icc c d → l ∈ Icc L U →
      |groupedDK h k l| ≤ E) : Box j a b c d := by
  intro h k hh hk
  have hr : |h - m| ≤ r := abs_le.mpr
    ⟨by linarith only [hr₁, hh.1], by linarith only [hr₂, hh.2]⟩
  have hs : |k - n| ≤ s := abs_le.mpr
    ⟨by linarith only [hs₁, hk.1], by linarith only [hs₂, hk.2]⟩
  have hlog := log_mem hv hh
  have gap' := hg h hh
  have hsign {l : ℝ} (hl : l ∈ Icc (lo j h) (hi j h)) : 0 ≤ mixedOddBCleared h k l := by
    let e := l - Real.log h
    have he : |e| ≤ ε := abs_le.mpr
      ⟨by dsimp [e]; linarith only [hl.1, hlog.2, gap'],
        by dsimp [e]; linarith only [hl.2, hlog.1, gap']⟩
    have hbound := centeredHK (pos_left hv)
      hh hk hm hn hD hE hr hs (value (hM he))
      (fun _ hx => dh hx (hW hx he)) (fun _ hy => dk hh hy (hW hh he))
    rw [show Real.log h + e = l by dsimp [e]; ring] at hbound
    exact hp.trans hbound
  have hle := hlog.1.trans hlog.2
  exact ⟨hsign ⟨le_rfl, hle⟩, hsign ⟨hle, le_rfl⟩⟩

theorem endpoints {j : ℕ} {a b : ℝ}
    (ha : a = (1 / 2 : ℝ) ^ j / 2) (hb : b = (1 / 2 : ℝ) ^ j)
    (root : Box j a b 0 1) {z k : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hk : k ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedOddBStripLower j z k ∧ 0 ≤ mixedOddBStripUpper j z k := by
  let h := mixedOddBStripH j z
  have hs : h = (1 / 2 : ℝ) ^ j * (1 - z / 2) := rfl
  have hp : 0 < (1 / 2 : ℝ) ^ j := by positivity
  have hx : X j h = z / 2 := by
    rw [hs]
    unfold X
    rw [← mul_assoc, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, one_mul]
    ring
  have hh : h ∈ Icc a b := by
    rw [hs, ha, hb]
    constructor
    · rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by linarith only [hz.2]) hp.le
    · exact mul_le_of_le_one_right hp.le (by linarith only [hz.1])
  obtain ⟨hl, hu⟩ := root hh hk
  have hn : 0 < 1 - z / 2 := by linarith only [hz.2]
  have he : mixedOddBStripLower j z k = h * mixedOddBCleared h k (lo j h) := by
    change h * mixedOddBCleared h k _ - _ = _
    simp only [lo, hx, mixed_odd_b_cleared_affine]
    generalize mixedOddBA h k = A
    generalize mixedOddBB h k = B
    rw [hs]
    generalize hw : 1 - z / 2 = w
    have hw' : w ≠ 0 := (hw ▸ hn).ne'
    field_simp [hw']
    ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact mul_nonneg (hs ▸ (mul_pos hp hn).le) hl
  · simpa only [hi, hx, mixedOddBStripUpper, h] using hu

end NoEmbeddedEigenvalues.MixedOddBTrace.Scaled
