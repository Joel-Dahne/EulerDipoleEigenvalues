module

public import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedRobinCurrent
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The regular rectangle inequality for mixed Robin comparison

This step keeps the signed currents on the artificial faces. It uses the
ordinary fundamental theorem of calculus on normal sections; it does not
take a trace of the gradient of the trial function.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory
open scoped ContDiff

private theorem contDiffAt_partialX_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {q : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f q) :
    ContDiffAt ℝ 1 (partialX f) q := by
  apply ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := ((1, 0) : ℝ × ℝ)))).congr_of_eventuallyEq
  filter_upwards [hf.eventually (by norm_num)] with p hp
  exact partialX_eq_fderiv (hp.differentiableAt (by norm_num))

private theorem contDiffAt_partialY_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {q : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f q) :
    ContDiffAt ℝ 1 (partialY f) q := by
  apply ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := ((0, 1) : ℝ × ℝ)))).congr_of_eventuallyEq
  filter_upwards [hf.eventually (by norm_num)] with p hp
  exact partialY_eq_fderiv (hp.differentiableAt (by norm_num))

/-- The two regular Picone currents are classically differentiable right
up to a regular boundary face. -/
theorem mixed_robin_current_contDiffAt (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 1 z)
    {q : ℝ × ℝ} (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2))
    (haxis : 0 < if oddA then q.1 else q.2) :
    let g := mixedRobinComparison oddA ρ
    ContDiffAt ℝ 1 (mixedRobinCurrentA g z) q ∧
      ContDiffAt ℝ 1 (mixedRobinCurrentB g z) q := by
  dsimp only
  let g := mixedRobinComparison oddA ρ
  have hgg : ContDiffAt ℝ 2 g q :=
    (mixed_robin_ground_contDiffAt oddA hρ hq).of_le (by simp)
  have hpos := mixed_robin_ground_pos oddA hρ hq haxis
  have ⟨hd, hj⟩ := mixed_robin_coefficients_contDiffAt (n := 1) hq
  have hx := contDiffAt_partialX_one hgg
  have hy := contDiffAt_partialY_one hgg
  have hh : ContDiffAt ℝ 1 g q := hgg.of_le (by norm_num)
  have hn := (hz.contDiffAt (x := q)).norm_sq ℂ
  constructor
  · exact (((hd.mul hx).add (hj.mul hy)).div hh hpos.ne').mul hn
  · exact (((hj.mul hx).add (hd.mul hy)).div hh hpos.ne').mul hn

private theorem continuousAt_partialX {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContinuousAt (partialX f) p := by
  apply ((hf.continuousAt_fderiv (by simp)).clm_apply
    (continuousAt_const (y := ((1, 0) : ℝ × ℝ)))).congr_of_eventuallyEq
  filter_upwards [hf.eventually (by norm_num)] with q hq
  exact partialX_eq_fderiv (hq.differentiableAt (by norm_num))

private theorem continuousAt_partialY {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContinuousAt (partialY f) p := by
  apply ((hf.continuousAt_fderiv (by simp)).clm_apply
    (continuousAt_const (y := ((0, 1) : ℝ × ℝ)))).congr_of_eventuallyEq
  filter_upwards [hf.eventually (by norm_num)] with q hq
  exact partialY_eq_fderiv (hq.differentiableAt (by norm_num))

private theorem rectangle_partialY {a A b B : ℝ} (hb : b ≤ B) {F : ℝ × ℝ → ℝ}
    (hF : ∀ q ∈ Icc a A ×ˢ Icc b B, ContDiffAt ℝ 1 F q) :
    (∫ q in Ioo a A ×ˢ Ioo b B, partialY F q) =
      ∫ x in Ioo a A, F (x, B) - F (x, b) := by
  have hc : ContinuousOn (partialY F) (Icc a A ×ˢ Icc b B) :=
    fun q hq ↦ (continuousAt_partialY (hF q hq)).continuousWithinAt
  rw [Measure.volume_eq_prod, setIntegral_prod _
    (by
      rw [← Measure.volume_eq_prod]
      exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
  have hs : MapsTo (fun y : ℝ ↦ (x, y)) (Icc b B) (Icc a A ×ˢ Icc b B) :=
    fun y hy ↦ ⟨Ioo_subset_Icc_self hx, hy⟩
  have hcont : ContinuousOn (fun y ↦ partialY F (x, y)) (uIcc b B) := by
    rw [uIcc_of_le hb]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y ↦ F (x, y))
    (fun y hy ↦ hasDerivAt_partialY ((hF _ (hs (uIcc_of_le hb ▸ hy))).differentiableAt
      (by norm_num))) (hcont.intervalIntegrable)
  simpa only [intervalIntegral.integral_of_le hb, integral_Ioc_eq_integral_Ioo] using ht

private theorem rectangle_partialX {a A b B : ℝ} (ha : a ≤ A) {F : ℝ × ℝ → ℝ}
    (hF : ∀ q ∈ Icc a A ×ˢ Icc b B, ContDiffAt ℝ 1 F q) :
    (∫ q in Ioo a A ×ˢ Ioo b B, partialX F q) =
      ∫ y in Ioo b B, F (A, y) - F (a, y) := by
  have hs (q : ℝ × ℝ) (hq : q ∈ Icc b B ×ˢ Icc a A) :
      ContDiffAt ℝ 1 (fun p ↦ F p.swap) q :=
    (hF q.swap ⟨hq.2, hq.1⟩).comp q
      (show ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ (p.2, p.1)) q by fun_prop)
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap]
  rw [← Measure.volume_eq_prod]
  exact rectangle_partialY ha hs

theorem mixed_robin_potential_continuousAt {q : ℝ × ℝ}
    (hq : q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2))
    (hn : 0 < q.1 ∨ 0 < q.2) : ContinuousAt mixedComparisonPotential q := by
  have hh : 0 < Real.cos q.1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩
  have hk : 0 ≤ Real.cos q.2 :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩
  have hsum := add_pos_of_pos_of_nonneg hh hk
  have hs : 0 < Real.sin q.1 ^ 2 + Real.sin q.2 ^ 2 := by
    rcases hn with hn | hn
    · have hp := Real.sin_pos_of_pos_of_lt_pi hn (hq.1.2.trans (half_lt_self Real.pi_pos))
      positivity
    · have hp := Real.sin_pos_of_pos_of_lt_pi hn (hq.2.2.trans_lt (half_lt_self Real.pi_pos))
      positivity
  have hden : 0 < 2 - Real.cos q.1 ^ 2 - Real.cos q.2 ^ 2 := by
    linarith only [hs, Real.sin_sq_add_cos_sq q.1, Real.sin_sq_add_cos_sq q.2]
  unfold mixedComparisonPotential mixedV
  fun_prop (disch := positivity)

/-- Picone comparison on a regular rectangle. The three non-Robin sides
retain their signed currents. The rectangle stays away from the odd axis
and from `a = π/2` but may touch the even axis. -/
theorem mixed_robin_rectangle (oddA : Bool) {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    (hrobin : ∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ mixedRobinNumerator oddA ρ h)
    {z : ℝ × ℝ → ℂ} (hz : ContDiff ℝ 2 z) {a A b : ℝ}
    (ha : 0 ≤ a) (haA : a < A) (hA : A < Real.pi / 2) (hb : 0 ≤ b)
    (hbB : b < Real.pi / 2) (haxis : 0 < if oddA then a else b) :
    let B := Real.pi / 2
    let R := Ioo a A ×ˢ Ioo b B
    let g := mixedRobinComparison oddA ρ
    c * (∫ q in R, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) +
        (∫ y in Ioo b B, mixedRobinCurrentA g z (A, y) - mixedRobinCurrentA g z (a, y)) -
        (∫ x in Ioo a A, mixedRobinCurrentB g z (x, b)) ≤
      (∫ q in R, mixedRobinBulk z (partialX z) (partialY z) q) +
        ∫ x in Ioo a A, Real.cos x * ‖z (x, B)‖ ^ 2 := by
  dsimp only
  let B := Real.pi / 2
  let R := Ioo a A ×ˢ Ioo b B
  let K := Icc a A ×ˢ Icc b B
  let g := mixedRobinComparison oddA ρ
  let Jx := mixedRobinCurrentA g z
  let Jy := mixedRobinCurrentB g z
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hQ : R ⊆ mixedQuarterCell := fun _ hq ↦
    ⟨⟨ha.trans_lt hq.1.1, hq.1.2.trans hA⟩, ⟨hb.trans_lt hq.2.1, hq.2.2⟩⟩
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hreg (q : ℝ × ℝ) (hq : q ∈ K) :
      q ∈ Ico 0 (Real.pi / 2) ×ˢ Icc 0 (Real.pi / 2) :=
    ⟨⟨ha.trans hq.1.1, hq.1.2.trans_lt hA⟩, ⟨hb.trans hq.2.1, hq.2.2⟩⟩
  have hp (q : ℝ × ℝ) (hq : q ∈ K) : 0 < if oddA then q.1 else q.2 := by
    cases oddA
    · exact haxis.trans_le hq.2.1
    · exact haxis.trans_le hq.1.1
  have hJ (q : ℝ × ℝ) (hq : q ∈ K) : ContDiffAt ℝ 1 Jx q ∧ ContDiffAt ℝ 1 Jy q := by
    exact mixed_robin_current_contDiffAt oddA hρ (hz.of_le (by norm_num))
      (hreg q hq) (hp q hq)
  have hint {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f K) : IntegrableOn f R :=
    (hf.integrableOn_compact hK).mono_set hRK
  have hiX : IntegrableOn (partialX Jx) R := hint fun q hq ↦
    (continuousAt_partialX (hJ q hq).1).continuousWithinAt
  have hiY : IntegrableOn (partialY Jy) R := hint fun q hq ↦
    (continuousAt_partialY (hJ q hq).2).continuousWithinAt
  have hiMass : IntegrableOn (fun q ↦ c * (Real.cos q.1 ^ 2 * ‖z q‖ ^ 2)) R := by
    have hzc : Continuous z := hz.continuous
    have hc : Continuous (fun q ↦ c * (Real.cos q.1 ^ 2 * ‖z q‖ ^ 2)) := by fun_prop
    exact hint hc.continuousOn
  have hiBulk : IntegrableOn (mixedRobinBulk z (partialX z) (partialY z)) R := by
    apply hint
    intro q hq
    have ⟨hd, hj⟩ := mixed_robin_coefficients_contDiffAt (n := 1) (hreg q hq)
    have hD := hd.continuousAt
    have hE := hj.continuousAt
    have hV := mixed_robin_potential_continuousAt (hreg q hq)
      (by
        cases oddA
        · exact Or.inr (hp q hq)
        · exact Or.inl (hp q hq))
    have hx := (contDiff_partialX (n := 1) hz).continuous.continuousAt (x := q)
    have hy := (contDiff_partialY (n := 1) hz).continuous.continuousAt (x := q)
    have hzc := hz.continuous.continuousAt (x := q)
    apply ContinuousAt.continuousWithinAt
    unfold mixedRobinBulk
    fun_prop
  have hintTop {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f K) :
      IntegrableOn (fun x ↦ f (x, B)) (Ioo a A) :=
    ((hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx ↦ ⟨hx, hbB.le, le_rfl⟩)).integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hiTop : IntegrableOn (fun x ↦ Jy (x, B)) (Ioo a A) :=
    hintTop fun q hq ↦ (hJ q hq).2.continuousAt.continuousWithinAt
  have hiBottom : IntegrableOn (fun x ↦ Jy (x, b)) (Ioo a A) := by
    have hcJ : ContinuousOn Jy K := fun q hq ↦ (hJ q hq).2.continuousAt.continuousWithinAt
    apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
    exact (hcJ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx ↦ ⟨hx, le_rfl, hbB.le⟩)).integrableOn_compact isCompact_Icc
  have hiRobin : IntegrableOn (fun x ↦ Real.cos x * ‖z (x, B)‖ ^ 2) (Ioo a A) := by
    have hzc : Continuous z := hz.continuous
    have hc : Continuous (fun x ↦ Real.cos x * ‖z (x, B)‖ ^ 2) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hTop : 0 ≤ (∫ x in Ioo a A, Jy (x, B)) + ∫ x in Ioo a A, Real.cos x * ‖z (x, B)‖ ^ 2 := by
    rw [← integral_add hiTop hiRobin]
    apply setIntegral_nonneg measurableSet_Ioo
    intro x hx
    have hxQ : x ∈ Ioo 0 (Real.pi / 2) := ⟨ha.trans_lt hx.1, hx.2.trans hA⟩
    have hxCos : Real.cos x ∈ Ioc 0 1 :=
      ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hxQ.1, Real.pi_pos], hxQ.2⟩, Real.cos_le_one _⟩
    change 0 ≤ Jy (x, B) + Real.cos x * ‖z (x, B)‖ ^ 2
    rw [mixed_robin_top_current oddA hρ hxQ z]
    exact mul_nonneg (div_nonneg (hrobin _ hxCos) (hρ.pos ⟨hxCos, by simp⟩).le) (sq_nonneg _)
  have hI := setIntegral_mono_on (hiMass.add (hiX.add hiY)) hiBulk
    (measurableSet_Ioo.prod measurableSet_Ioo) (fun q hq ↦ by
      simpa only [Pi.add_apply, ← mul_assoc, divergence, Jx, Jy, g] using
        mixed_robin_picone oddA hρ hinterior (hz.of_le (by norm_num)).contDiffOn (hQ hq))
  have he : (∫ q in R, ((fun p ↦ c * (Real.cos p.1 ^ 2 * ‖z p‖ ^ 2)) +
      (partialX Jx + partialY Jy)) q) =
      (∫ q in R, c * (Real.cos q.1 ^ 2 * ‖z q‖ ^ 2)) +
        (∫ q in R, partialX Jx q) + (∫ q in R, partialY Jy q) := by
    exact (integral_add hiMass (hiX.add hiY)).trans
      ((congrArg ((∫ q in R, c * (Real.cos q.1 ^ 2 * ‖z q‖ ^ 2)) + ·)
        (integral_add hiX hiY)).trans (add_assoc _ _ _).symm)
  rw [he, integral_const_mul,
    rectangle_partialX haA.le (fun q hq ↦ (hJ q hq).1),
    rectangle_partialY hbB.le (fun q hq ↦ (hJ q hq).2), integral_sub hiTop hiBottom] at hI
  change _ + (_ - ∫ x in Ioo a A, Jy (x, b)) ≤ _ at hI
  change c * (∫ q in R, _) + (∫ y in Ioo b B, Jx (A, y) - Jx (a, y)) - _ ≤ _
  linarith only [hI, hTop]

end NoEmbeddedEigenvalues
