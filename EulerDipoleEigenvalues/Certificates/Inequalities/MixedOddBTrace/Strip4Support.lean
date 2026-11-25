module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Centered
public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBLog

/-! # From strip-4 interval bounds to endpoint signs -/

@[expose] public section

namespace EulerDipoleEigenvalues.MixedOddBTrace.Strip4

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

-- The two endpoint expressions already used in the strip theorem.
-- Freeze rational log-two bounds once, before evaluating the endpoint series.
private theorem stripNineLogTwoLower :
    (6931471805599453 / 10 ^ 16 : ℝ) ≤ (certificateLogTwoLower : ℝ) := by
  have h : (6931471805599453 / 10 ^ 16 : ℚ) ≤ certificateLogTwoLower := by
    norm_num [certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

private theorem stripNineLogTwoUpper :
    (certificateLogTwoUpper : ℝ) ≤ (6931471805599454 / 10 ^ 16 : ℝ) := by
  have h : certificateLogTwoUpper ≤ (6931471805599454 / 10 ^ 16 : ℚ) := by
    norm_num [certificateLogTwoUpper, certificateLogTwoLower, Finset.sum_range_succ]
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

-- The same scalar Taylor bounds apply to the true logarithm after rescaling.
private theorem stripFour_log_mem {x : ℝ} (hx : x ∈ Icc 0 (1 / 2)) :
    Real.log ((1 / 16 : ℝ) * (1 - x)) ∈
      Icc (-4 * (certificateLogTwoUpper : ℝ) + certificateLogTaylor x -
          x ^ 15 / (15 * (1 - x)))
        (-4 * (certificateLogTwoLower : ℝ) + certificateLogTaylor x) := by
  have hx₁ : 0 < 1 - x := by linarith only [hx.2]
  have he : Real.log ((1 / 16 : ℝ) * (1 - x)) = -4 * Real.log 2 + Real.log (1 - x) := by
    have hpow : (1 / 16 : ℝ) = (2 : ℝ)⁻¹ ^ 4 := by norm_num
    rw [Real.log_mul (by norm_num) hx₁.ne', hpow, Real.log_pow, Real.log_inv]
    ring
  rw [he]
  obtain ⟨hl, hu⟩ := certificate_log_one_sub_bounds hx
  obtain ⟨h₂l, h₂u⟩ := certificate_log_two_bounds
  exact ⟨by linarith only [hl, h₂u], by linarith only [hu, h₂l]⟩

noncomputable def X (h : ℝ) : ℝ := 1 - 16 * h

noncomputable def lo (h : ℝ) : ℝ :=
  -4 * (certificateLogTwoUpper : ℝ) + certificateLogTaylor (X h) -
    (X h) ^ 15 / (15 * (1 - X h))

noncomputable def hi (h : ℝ) : ℝ :=
  -4 * (certificateLogTwoLower : ℝ) + certificateLogTaylor (X h)

private theorem x_range {a b h : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hh : h ∈ Icc a b) : X h ∈ Icc 0 (1 / 2) :=
  ⟨by unfold X; linarith only [hh.2, hb], by unfold X; linarith only [ha, hh.1]⟩

private theorem log_mem {a b h : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hh : h ∈ Icc a b) : Real.log h ∈ Icc (lo h) (hi h) := by
  have hhx : (1 / 16 : ℝ) * (1 - X h) = h := by unfold X; ring
  simpa only [lo, hi, hhx] using stripFour_log_mem (x_range ha hb hh)

def Window (a b L U : ℝ) : Prop :=
  ∀ h ∈ Icc a b, L ≤ lo h ∧ hi h ≤ U

theorem window {a b L U : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hL : L ≤ -4 * (6931471805599454 / 10 ^ 16) + certificateLogTaylor (X a) -
      (X a) ^ 15 / (15 * (1 - X a)))
    (hU : -4 * (6931471805599453 / 10 ^ 16) + certificateLogTaylor (X b) ≤ U) :
    Window a b L U := by
  intro h hh
  have hx := x_range ha hb hh
  have hxa : X h ≤ X a := by unfold X; linarith only [hh.1]
  have hxb : X b ≤ X h := by unfold X; linarith only [hh.2]
  have hx₀ : 0 ≤ X b := by unfold X; linarith only [hb]
  have hxa₁ : X a < 1 := by unfold X; linarith only [ha]
  have ht₁ := logTaylor_anti hx.1 hxa
  have ht₂ := logTaylor_anti hx₀ hxb
  have htail := logTail_mono hx.1 hxa hxa₁
  exact ⟨by unfold lo; linarith only [hL, ht₁, htail, stripNineLogTwoUpper],
    by unfold hi; linarith only [hU, ht₂, stripNineLogTwoLower]⟩

theorem window_wide {a b L U L' U' e : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hw : Window a b L U) (hl : L' ≤ L - e) (hu : U + e ≤ U')
    {h off : ℝ} (hh : h ∈ Icc a b) (he : |off| ≤ e) :
    Real.log h + off ∈ Icc L' U' := by
  have hlog := log_mem ha hb hh
  obtain ⟨hl', hu'⟩ := hw h hh
  obtain ⟨hel, heu⟩ := abs_le.mp he
  exact ⟨by linarith only [hl, hl', hlog.1, hel], by linarith only [hu, hu', hlog.2, heu]⟩

def Gap (a b e : ℝ) : Prop := ∀ h ∈ Icc a b, hi h - lo h ≤ e

theorem gap {a b e : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (he : 4 * ((6931471805599454 - 6931471805599453) / 10 ^ 16 : ℝ) +
      (X a) ^ 15 / (15 * (1 - X a)) ≤ e) :
    Gap a b e := by
  intro h hh
  have hx := x_range ha hb hh
  have hxa : X h ≤ X a := by unfold X; linarith only [hh.1]
  have hxa₁ : X a < 1 := by unfold X; linarith only [ha]
  have htail := logTail_mono hx.1 hxa hxa₁
  unfold lo hi
  linarith only [he, htail, stripNineLogTwoLower, stripNineLogTwoUpper]

def Box (a b c d : ℝ) : Prop :=
  ∀ {h k : ℝ}, h ∈ Icc a b → k ∈ Icc c d →
    0 ≤ mixedOddBCleared h k (lo h) ∧ 0 ≤ mixedOddBCleared h k (hi h)

theorem splitH {a b c d m : ℝ} (hl : Box a m c d) (hr : Box m b c d) : Box a b c d := by
  intro h k hh hk
  rcases le_or_gt h m with hm | hm
  · exact hl ⟨hh.1, hm⟩ hk
  · exact hr ⟨hm.le, hh.2⟩ hk

theorem splitK {a b c d m : ℝ} (hl : Box a b c m) (hr : Box a b m d) : Box a b c d := by
  intro h k hh hk
  rcases le_or_gt k m with hm | hm
  · exact hl hh ⟨hk.1, hm⟩
  · exact hr hh ⟨hm.le, hk.2⟩

theorem plain {a b c d L U : ℝ} (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hw : Window a b L U)
    (hp : ∀ {h k l : ℝ}, h ∈ Icc a b → k ∈ Icc c d → l ∈ Icc L U →
      0 ≤ mixedOddBCleared h k l) : Box a b c d := by
  intro h k hh hk
  have hlog := log_mem ha hb hh
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

theorem centered {a b c d m n ε lb D E r s L U LM UM : ℝ}
    (ha : 1 / 32 ≤ a) (hb : b ≤ 1 / 16)
    (hm : m ∈ Icc a b) (hn : n ∈ Icc c d)
    (hg : Gap a b ε)
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
      |groupedDK h k l| ≤ E) : Box a b c d := by
  intro h k hh hk
  have hr : |h - m| ≤ r := abs_le.mpr
    ⟨by linarith only [hr₁, hh.1], by linarith only [hr₂, hh.2]⟩
  have hs : |k - n| ≤ s := abs_le.mpr
    ⟨by linarith only [hs₁, hk.1], by linarith only [hs₂, hk.2]⟩
  have hlog := log_mem ha hb hh
  have gap' := hg h hh
  have hsign {l : ℝ} (hl : l ∈ Icc (lo h) (hi h)) : 0 ≤ mixedOddBCleared h k l := by
    let e := l - Real.log h
    have he : |e| ≤ ε := abs_le.mpr
      ⟨by dsimp [e]; linarith only [hl.1, hlog.2, gap'],
        by dsimp [e]; linarith only [hl.2, hlog.1, gap']⟩
    have hbound := centeredHK ((by norm_num : (0 : ℝ) < 1 / 32).trans_le ha)
      hh hk hm hn hD hE hr hs (value (hM he))
      (fun _ hx => dh hx (hW hx he)) (fun _ hy => dk hh hy (hW hh he))
    rw [show Real.log h + e = l by dsimp [e]; ring] at hbound
    exact hp.trans hbound
  have hle := hlog.1.trans hlog.2
  exact ⟨hsign ⟨le_rfl, hle⟩, hsign ⟨hle, le_rfl⟩⟩

theorem endpoints (root : Box (1 / 32) (1 / 16) 0 1) {z k : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hk : k ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedOddBStripLower 4 z k ∧ 0 ≤ mixedOddBStripUpper 4 z k := by
  let h := mixedOddBStripH 4 z
  have hs : h = (1 / 16 : ℝ) * (1 - z / 2) := by norm_num [h, mixedOddBStripH]
  have hx : X h = z / 2 := by rw [hs]; unfold X; ring
  have hh : h ∈ Icc (1 / 32 : ℝ) (1 / 16) := by
    rw [hs]
    constructor <;> linarith only [hz.1, hz.2]
  obtain ⟨hl, hu⟩ := root hh hk
  have he : mixedOddBStripLower 4 z k = h * mixedOddBCleared h k (lo h) := by
    change h * mixedOddBCleared h k _ - _ = _
    simp only [lo, hx, mixed_odd_b_cleared_affine, Nat.cast_ofNat]
    generalize mixedOddBA h k = a
    generalize mixedOddBB h k = b
    rw [hs]
    generalize hw : 1 - z / 2 = w
    have hn : 0 < 1 - z / 2 := by linarith only [hz.2]
    have hw' : w ≠ 0 := (hw ▸ hn).ne'
    field_simp [hw']
    ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 32).trans hh.1) hl
  · simpa only [hi, hx, mixedOddBStripUpper, h, Nat.cast_ofNat] using hu

end EulerDipoleEigenvalues.MixedOddBTrace.Strip4
