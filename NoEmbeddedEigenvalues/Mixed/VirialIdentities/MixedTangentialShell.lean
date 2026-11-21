module

public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedTangentialCurrent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Uniform mass of mixed virial level shells -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped ENNReal Topology

local notation "Plane" => ℝ × ℝ
local notation "c" => (Real.pi / 2)

private def edgeDist (x : ℝ) : ℝ := c - |x|

private theorem edgeDist_cos {x : ℝ} (hx : x ∈ Ioo (-c) c) :
    0 < edgeDist x ∧ edgeDist x / 2 ≤ Real.cos x ∧ Real.cos x ≤ edgeDist x := by
  have hp : 0 < edgeDist x := sub_pos.mpr (abs_lt.mpr hx)
  have hle : edgeDist x ≤ c := sub_le_self _ (abs_nonneg _)
  have hs : Real.sin (edgeDist x) = Real.cos x := by
    rw [edgeDist, ← Real.cos_pi_div_two_sub]
    have he : c - (c - |x|) = |x| := by ring
    rw [he, Real.cos_abs]
  have hπ : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four]
  refine ⟨hp, ?_, hs ▸ Real.sin_le hp.le⟩
  rw [← hs, div_eq_inv_mul]
  simpa only [one_div] using
    (mul_le_mul_of_nonneg_right hπ hp.le).trans (Real.mul_le_sin hp.le hle)

private theorem edgeDist_sublevel (B : ℝ) (hB : 0 ≤ B) :
    volume {x : ℝ | 0 < edgeDist x ∧ edgeDist x < B} ≤ ENNReal.ofReal (2 * B) := by
  have hsub : {x : ℝ | 0 < edgeDist x ∧ edgeDist x < B} ⊆
      Ioo (-c) (-c + B) ∪ Ioo (c - B) c := by
    intro x hx
    change 0 < c - |x| ∧ c - |x| < B at hx
    rcases le_total x 0 with h | h
    · rw [abs_of_nonpos h] at hx
      exact Or.inl ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [abs_of_nonneg h] at hx
      exact Or.inr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by
      rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

private theorem tail_mass {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ x : ℝ, (Ioi (Real.sqrt ε)).indicator (fun t ↦ ENNReal.ofReal (512 * ε / t ^ 3))
      (edgeDist x)) ≤ 512 := by
  let F := (Ioi (Real.sqrt ε)).indicator (fun t ↦ ENNReal.ofReal (512 * ε / t ^ 3))
  have hm : Measurable F := (by fun_prop : Measurable
    (fun t : ℝ ↦ ENNReal.ofReal (512 * ε / t ^ 3))).indicator measurableSet_Ioi
  have hi : (∫⁻ t, F t) = 256 := by
    have he (t : ℝ) : t ^ (-(3 : ℝ)) = (t ^ 3)⁻¹ := by
      rw [Real.rpow_neg_eq_inv_rpow]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    have his : IntegrableOn (fun t : ℝ ↦ t ^ (-(3 : ℝ))) (Ioi (Real.sqrt ε)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (Real.sqrt_pos.2 hε)
    have hInt := integral_Ioi_rpow_of_lt (a := -(3 : ℝ)) (by norm_num) (Real.sqrt_pos.2 hε)
    have hpos : ∀ᵐ x ∂volume.restrict (Ioi (Real.sqrt ε)), 0 ≤ 512 * ε * x ^ (-(3 : ℝ)) :=
      (ae_restrict_mem (μ := volume) measurableSet_Ioi).mono fun x hx ↦
        mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt ((Real.sqrt_pos.2 hε).trans hx)) _)
    rw [show F = (Ioi (Real.sqrt ε)).indicator
      (fun x ↦ ENNReal.ofReal (512 * ε * x ^ (-(3 : ℝ)))) by
        dsimp only [F]
        congr 1
        funext t
        rw [he, div_eq_mul_inv], lintegral_indicator measurableSet_Ioi,
      ← ofReal_integral_eq_lintegral_ofReal (his.const_mul _) hpos, integral_const_mul, hInt]
    have hr (t : ℝ) : t ^ (-(3 : ℝ) + 1) = (t ^ 2)⁻¹ := by
      rw [show -(3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow,
        Real.rpow_natCast, inv_pow]
    rw [hr, Real.sq_sqrt hε.le]
    rw [show 512 * ε * (-(ε⁻¹) / (-(3 : ℝ) + 1)) = 256 by field_simp; ring]
    norm_num
  have h₁ : (∫⁻ x, F (c - x)) = ∫⁻ x, F x :=
    (Measure.measurePreserving_sub_left volume c).lintegral_comp_emb
      (MeasurableEquiv.subLeft c).measurableEmbedding F
  have h₂ : (∫⁻ x, F (x + c)) = ∫⁻ x, F x :=
    (measurePreserving_add_right volume c).lintegral_comp_emb
      (MeasurableEquiv.addRight c).measurableEmbedding F
  change (∫⁻ x, F (edgeDist x)) ≤ _
  calc
    _ ≤ ∫⁻ x, F (c - x) + F (x + c) := by
      apply lintegral_mono
      intro x
      change F (edgeDist x) ≤ F (c - x) + F (x + c)
      rcases le_total 0 x with h | h
      · rw [edgeDist, abs_of_nonneg h]
        exact le_self_add
      · rw [edgeDist, abs_of_nonpos h, sub_neg_eq_add, add_comm c x]
        exact le_add_self
    _ = 512 := by
      have hm₂ : Measurable (fun x ↦ F (x + c)) := hm.comp (by fun_prop)
      rw [lintegral_add_right _ hm₂, h₁, h₂, hi]
      norm_num

private def halfShell (ε : ℝ) : Set Plane :=
  {q ∈ mixedOpenCell | Real.cos q.2 ≤ Real.cos q.1 ∧
    ε < Real.cos q.1 * Real.cos q.2 ∧ Real.cos q.1 * Real.cos q.2 < 2 * ε}

private def halfMajorant (ε : ℝ) (q : Plane) : ℝ≥0∞ :=
  (Ioi (Real.sqrt ε)).indicator (fun x ↦ ENNReal.ofReal (32 / x ^ 2)) (edgeDist q.1) *
    {y : ℝ | 0 < edgeDist y ∧ edgeDist y < 8 * ε / edgeDist q.1}.indicator 1 q.2

private theorem measurable_halfMajorant (ε : ℝ) : Measurable (halfMajorant ε) := by
  have hd : Continuous edgeDist := continuous_const.sub continuous_abs
  unfold halfMajorant
  have h₁ : Measurable (fun q : Plane ↦
      (Ioi (Real.sqrt ε)).indicator (fun t ↦ ENNReal.ofReal (32 / t ^ 2)) (edgeDist q.1)) :=
    ((by fun_prop : Measurable (fun x : ℝ ↦ ENNReal.ofReal (32 / x ^ 2))).indicator
    (measurableSet_Ioi (a := Real.sqrt ε))).comp (hd.measurable.comp measurable_fst)
  let S : Set Plane := {q | 0 < edgeDist q.2 ∧ edgeDist q.2 < 8 * ε / edgeDist q.1}
  have hs : MeasurableSet S := (measurableSet_lt measurable_const (hd.measurable.comp
    measurable_snd)).inter (measurableSet_lt (hd.measurable.comp measurable_snd)
    (measurable_const.div (hd.measurable.comp measurable_fst)))
  exact h₁.mul (measurable_const.indicator hs)

private theorem halfMass {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ q, halfMajorant ε q) ≤ 512 := by
  have hd : Continuous edgeDist := continuous_const.sub continuous_abs
  have hm := measurable_halfMajorant ε
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  refine (lintegral_mono fun x ↦ ?_).trans (tail_mass hε)
  let F := (Ioi (Real.sqrt ε)).indicator (fun t ↦ ENNReal.ofReal (32 / t ^ 2))
  let S := {y : ℝ | 0 < edgeDist y ∧ edgeDist y < 8 * ε / edgeDist x}
  have hs : MeasurableSet S := (measurableSet_lt measurable_const hd.measurable).inter
    (measurableSet_lt hd.measurable measurable_const)
  change (∫⁻ y, F (edgeDist x) * S.indicator 1 y) ≤ _
  have hmS : Measurable (S.indicator (1 : ℝ → ℝ≥0∞)) := measurable_const.indicator hs
  rw [lintegral_const_mul _ hmS, lintegral_indicator_one hs]
  by_cases hx : Real.sqrt ε < edgeDist x
  · have hx' := (Real.sqrt_pos.2 hε).trans hx
    rw [show F (edgeDist x) = ENNReal.ofReal (32 / edgeDist x ^ 2) from indicator_of_mem hx _,
      indicator_of_mem (show edgeDist x ∈ Ioi (Real.sqrt ε) from hx)]
    refine (mul_le_mul_right (edgeDist_sublevel _ (by positivity)) _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 32 / edgeDist x ^ 2)]
    congr 1
    ring
  · rw [show F (edgeDist x) = 0 from indicator_of_notMem hx _, zero_mul]
    exact bot_le

private theorem half_majorizes {ε : ℝ} (hε : 0 < ε) {q : Plane} (hq : q ∈ halfShell ε) :
    ENNReal.ofReal (‖mixedTangentialCornerKernel q‖ / ε) ≤ halfMajorant ε q := by
  obtain ⟨hq, hkh, hl, hu⟩ := hq
  let h := Real.cos q.1
  let k := Real.cos q.2
  let x := edgeDist q.1
  let y := edgeDist q.2
  obtain ⟨hx, hx₂, hhx⟩ := edgeDist_cos (by simpa only [neg_div] using hq.1)
  obtain ⟨hy, hy₂, _⟩ := edgeDist_cos (by simpa only [neg_div] using hq.2)
  change 0 < x at hx
  change x / 2 ≤ h at hx₂
  change h ≤ x at hhx
  change 0 < y at hy
  change y / 2 ≤ k at hy₂
  have hh : 0 < h := by linarith
  have hk : 0 < k := by linarith
  have hxε : Real.sqrt ε < x := by
    have h1 : ε < x ^ 2 := calc
      ε < h * k := hl
      _ ≤ h * h := mul_le_mul_of_nonneg_left hkh hh.le
      _ ≤ x ^ 2 := by rw [← sq]; gcongr
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hyε : y < 8 * ε / x := by
    apply (lt_div_iff₀ hx).2
    have he : x * y ≤ (2 * h) * (2 * k) :=
      mul_le_mul (by linarith) (by linarith) hy.le (by positivity)
    nlinarith only [he, hu]
  have hp : 0 < h + k := add_pos hh hk
  have hbd : ‖mixedTangentialCornerKernel q‖ / ε ≤ 32 / x ^ 2 := calc
    _ ≤ (4 * (h * k) / (h + k) ^ 2) / ε :=
      div_le_div_of_nonneg_right (mixed_tangential_corner_kernel_bound hq) hε.le
    _ = (4 * ((h * k) / ε)) / (h + k) ^ 2 := by ring
    _ ≤ 8 / (h + k) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have h' := (div_lt_iff₀ hε).2 hu
      linarith only [h']
    _ ≤ 8 / (x / 2) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (by positivity))
      gcongr
      linarith
    _ = _ := by ring
  unfold halfMajorant
  rw [indicator_of_mem (show x ∈ Ioi (Real.sqrt ε) from hxε),
    indicator_of_mem (show q.2 ∈ {t : ℝ | 0 < edgeDist t ∧ edgeDist t < 8 * ε / x} from
      ⟨hy, hyε⟩), Pi.one_apply, mul_one]
  exact ENNReal.ofReal_le_ofReal hbd

/-- A level shell has uniformly bounded absolute mass for the model
kernel divided by the shell scale. Split according to the larger cosine
and integrate the smaller inward distance first. -/
theorem mixed_tangential_shell_mass {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ q in {q ∈ mixedOpenCell |
        ε < Real.cos q.1 * Real.cos q.2 ∧ Real.cos q.1 * Real.cos q.2 < 2 * ε},
      ENNReal.ofReal (‖mixedTangentialCornerKernel q‖ / ε)) ≤ 1024 := by
  let S := {q ∈ mixedOpenCell |
    ε < Real.cos q.1 * Real.cos q.2 ∧ Real.cos q.1 * Real.cos q.2 < 2 * ε}
  have hm : MeasurableSet S := by
    change MeasurableSet (mixedOpenCell ∩ {q : Plane |
      ε < Real.cos q.1 * Real.cos q.2 ∧ Real.cos q.1 * Real.cos q.2 < 2 * ε})
    apply (measurableSet_Ioo.prod measurableSet_Ioo).inter
    have hm' : Measurable (fun q : Plane ↦ Real.cos q.1 * Real.cos q.2) := by fun_prop
    exact (measurableSet_lt measurable_const hm').inter
      (measurableSet_lt hm' measurable_const)
  have hk (q : Plane) :
      mixedTangentialCornerKernel q.swap = -mixedTangentialCornerKernel q := by
    simp only [mixedTangentialCornerKernel, Prod.fst_swap, Prod.snd_swap, ← neg_div]
    congr 1 <;> ring
  have hMaj := measurable_halfMajorant ε
  let F := halfMajorant ε
  have hswap : (∫⁻ q : Plane, F q.swap) = ∫⁻ q, F q :=
    Measure.measurePreserving_swap.lintegral_comp_emb
      (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding F
  change (∫⁻ q in S, _) ≤ _
  rw [← lintegral_indicator hm]
  calc
    _ ≤ ∫⁻ q : Plane, F q + F q.swap := by
      apply lintegral_mono
      intro q
      by_cases hq : q ∈ S
      · rw [indicator_of_mem hq]
        obtain ⟨hc, hl, hu⟩ := hq
        rcases le_total (Real.cos q.2) (Real.cos q.1) with h | h
        · exact (half_majorizes hε ⟨hc, h, hl, hu⟩).trans le_self_add
        · have hq' : q.swap ∈ halfShell ε :=
            ⟨⟨hc.2, hc.1⟩, h, by simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm] using hl,
              by simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm] using hu⟩
          exact ((by simpa only [hk, norm_neg] using half_majorizes hε hq') :
            ENNReal.ofReal (‖mixedTangentialCornerKernel q‖ / ε) ≤ F q.swap).trans le_add_self
      · rw [indicator_of_notMem hq]
        exact bot_le
    _ ≤ 1024 := by
      have hms : Measurable (fun q : Plane ↦ F q.swap) := hMaj.comp measurable_swap
      rw [lintegral_add_right _ hms, hswap]
      calc
        _ ≤ (512 : ℝ≥0∞) + 512 := add_le_add (halfMass hε) (halfMass hε)
        _ = _ := by norm_num

private def shellHeight (q : Plane) : ℝ := Real.cos q.1 * Real.cos q.2
private def cornerRadius (q : Plane) : ℝ := Real.cos q.1 + Real.cos q.2

private theorem continuous_shellHeight : Continuous shellHeight := by unfold shellHeight; fun_prop
private theorem continuous_cornerRadius : Continuous cornerRadius := by
  unfold cornerRadius
  fun_prop

private theorem compact_closed_cell : IsCompact (closure mixedOpenCell) := by
  rw [mixedOpenCell, closure_prod_eq,
    closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)]
  exact isCompact_Icc.prod isCompact_Icc

private theorem cos_closed_cell {q : Plane} (hq : q ∈ closure mixedOpenCell) :
    0 ≤ Real.cos q.1 ∧ 0 ≤ Real.cos q.2 := by
  rw [mixedOpenCell, closure_prod_eq,
    closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)] at hq
  exact ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by simpa only [neg_div] using hq.1.1) hq.1.2,
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by simpa only [neg_div] using hq.2.1) hq.2.2⟩

private theorem small_near_corners {F : Plane → ℝ} (hc : ContinuousOn F (closure mixedOpenCell))
    (hz : ∀ q ∈ closure mixedOpenCell, Real.cos q.1 = 0 → Real.cos q.2 = 0 → F q = 0)
    {a : ℝ} (ha : 0 < a) :
    ∃ δ > 0, ∀ q ∈ mixedOpenCell, cornerRadius q < δ → ‖F q‖ ≤ a := by
  let S := closure mixedOpenCell ∩ {q : Plane | a ≤ ‖F q‖}
  have hSc : IsClosed S :=
    isClosed_closure.isClosed_le continuousOn_const hc.norm
  by_cases hn : S.Nonempty
  · have hScpt : IsCompact S := compact_closed_cell.of_isClosed_subset hSc inter_subset_left
    obtain ⟨q, hq, hmin⟩ := hScpt.exists_isMinOn hn continuous_cornerRadius.continuousOn
    obtain ⟨h₁, h₂⟩ := cos_closed_cell hq.1
    have hp : 0 < cornerRadius q := by
      by_contra! hn
      unfold cornerRadius at hn
      have he := hz q hq.1 (by linarith) (by linarith)
      exact ha.not_ge (by simpa [he] using hq.2)
    exact ⟨_, hp, fun r hr hlt ↦ le_of_not_ge fun hge ↦ hlt.not_ge
      (hmin (show r ∈ S from ⟨subset_closure hr, hge⟩))⟩
  · exact ⟨1, zero_lt_one, fun r hr _ ↦ le_of_not_ge fun hge ↦
      hn ⟨r, subset_closure hr, hge⟩⟩

/-- Uniform shell mass and the inverse-square bound away from the corners
make the kernel pairing tend to zero for any continuous corner defect. -/
theorem mixed_tangential_shell_defect_limit {F : Plane → ℝ}
    (hc : ContinuousOn F (closure mixedOpenCell))
    (hz : ∀ q ∈ closure mixedOpenCell, Real.cos q.1 = 0 → Real.cos q.2 = 0 → F q = 0)
    {ε : ℕ → ℝ} (he : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {w : ℕ → Plane → ℝ} (hm : ∀ n, Measurable (w n)) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ n q, ‖w n q‖ ≤ M / ε n)
    (hs : ∀ n q, w n q ≠ 0 →
      Real.cos q.1 * Real.cos q.2 ∈ Ioo (ε n) (2 * ε n)) :
    Tendsto (fun n ↦ ∫ q in mixedOpenCell, w n q * mixedTangentialCornerKernel q * F q)
      atTop (𝓝 0) := by
  let μ := volume.restrict mixedOpenCell
  have hS : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  have hmem := ae_restrict_mem (μ := volume) hS
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [show μ = volume.restrict mixedOpenCell from rfl, Measure.restrict_apply_univ]
    exact (compact_closed_cell.measure_lt_top (μ := volume)).trans_le' (measure_mono subset_closure)
  have hK : Measurable mixedTangentialCornerKernel := by
    unfold mixedTangentialCornerKernel
    fun_prop
  let P (n : ℕ) (q : Plane) := w n q * mixedTangentialCornerKernel q
  have hmP (n : ℕ) : Measurable (P n) := (hm n).mul hK
  have hmass (n : ℕ) : (∫⁻ q, ENNReal.ofReal ‖P n q‖ ∂μ) ≤ ENNReal.ofReal (1024 * M) := by
    let S := {q : Plane | shellHeight q ∈ Ioo (ε n) (2 * ε n)}
    have hms : MeasurableSet S := measurableSet_Ioo.preimage continuous_shellHeight.measurable
    let B := fun q ↦ ENNReal.ofReal (‖mixedTangentialCornerKernel q‖ / ε n)
    calc
      _ ≤ ∫⁻ q, S.indicator (fun q ↦ ENNReal.ofReal M * B q) q ∂μ := by
        apply lintegral_mono
        intro q
        by_cases hq : q ∈ S
        · rw [indicator_of_mem hq]
          change ENNReal.ofReal ‖w n q * mixedTangentialCornerKernel q‖ ≤ _
          rw [← ENNReal.ofReal_mul hM, norm_mul]
          apply ENNReal.ofReal_le_ofReal
          calc
            _ ≤ (M / ε n) * ‖mixedTangentialCornerKernel q‖ :=
              mul_le_mul_of_nonneg_right (hw n q) (norm_nonneg _)
            _ = _ := by ring
        · have hzero : w n q = 0 := not_not.mp (fun h ↦ hq (hs n q h))
          simp [hzero, P, indicator_of_notMem hq]
      _ = ENNReal.ofReal M * (∫⁻ q in S ∩ mixedOpenCell, B q) := by
        rw [lintegral_indicator hms, Measure.restrict_restrict hms,
          lintegral_const_mul _ ((hK.norm.div_const _).ennreal_ofReal)]
      _ ≤ ENNReal.ofReal (1024 * M) := by
        rw [mul_comm (1024 : ℝ), ENNReal.ofReal_mul hM, show ENNReal.ofReal 1024 = 1024 by norm_num]
        exact mul_le_mul_right (by
          rw [inter_comm]
          exact mixed_tangential_shell_mass (he n)) _
  have hiP (n : ℕ) : Integrable (P n) μ := by
    refine ⟨(hmP n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact (hmass n).trans_lt ENNReal.ofReal_lt_top
  have hrealMass (n : ℕ) : (∫ q, ‖P n q‖ ∂μ) ≤ 1024 * M := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hiP n).norm (.of_forall fun _ ↦ norm_nonneg _)]
    exact hmass n
  obtain ⟨L, hL⟩ := compact_closed_cell.exists_bound_of_continuousOn hc
  have hmF := (hc.mono subset_closure).aestronglyMeasurable (μ := volume) hS
  have hiFull (n : ℕ) : Integrable (fun q ↦ P n q * F q) μ :=
    ((hiP n).bdd_mul hmF (hmem.mono fun q hq ↦ hL q (subset_closure hq))).congr
      (.of_forall fun q ↦ mul_comm (F q) (P n q))
  apply Metric.tendsto_nhds.2
  intro η hη
  let a := η / (2 * (1024 * M + 1))
  have ha : 0 < a := by positivity
  obtain ⟨δ, hδ, hnear⟩ := small_near_corners hc hz ha
  let A := {q | cornerRadius q < δ}
  have hA : MeasurableSet A := measurableSet_lt continuous_cornerRadius.measurable measurable_const
  let V (n : ℕ) := Aᶜ.indicator (fun q ↦ P n q * F q)
  have hV : Tendsto (fun n ↦ ∫ q, V n q ∂μ) atTop (𝓝 0) := by
    conv_rhs => rw [← integral_zero Plane ℝ (μ := μ)]
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 8 * M / δ ^ 2 * max L 0)
    · exact fun n ↦ ((hiFull n).indicator hA.compl).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [hmem] with q hq
      by_cases h' : q ∈ Aᶜ
      · dsimp only [V]
        rw [indicator_of_mem h', norm_mul]
        have hle : δ ≤ cornerRadius q := le_of_not_gt h'
        have hp : 0 < cornerRadius q := hδ.trans_le hle
        have hside : ‖P n q‖ ≤ 8 * M / δ ^ 2 := by
          by_cases hw0 : w n q = 0
          · simp only [P, hw0, zero_mul, norm_zero]
            positivity
          have hsz := (hs n q hw0).2
          change shellHeight q < 2 * ε n at hsz
          calc
            ‖P n q‖ ≤ (M / ε n) * (4 * shellHeight q / cornerRadius q ^ 2) := by
              unfold P
              rw [norm_mul]
              exact mul_le_mul (hw n q) (mixed_tangential_corner_kernel_bound hq)
                (norm_nonneg _) (div_nonneg hM (he n).le)
            _ ≤ (M / ε n) * (4 * (2 * ε n) / δ ^ 2) := by
              have hen := he n
              gcongr
            _ = _ := by field_simp [(he n).ne']; ring
        exact mul_le_mul hside ((hL q (subset_closure hq)).trans (le_max_left _ _))
          (norm_nonneg _) (by positivity)
      · dsimp only [V]
        rw [indicator_of_notMem h', norm_zero]
        positivity
    · filter_upwards [hmem] with q hq
      have hpos : 0 < shellHeight q := mul_pos
        (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
        (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))
      have h2 : Tendsto (fun n ↦ 2 * ε n) atTop (𝓝 0) := by
        simpa using hlim.const_mul (2 : ℝ)
      apply tendsto_const_nhds.congr'
      filter_upwards [h2.eventually (gt_mem_nhds hpos)] with n hn
      have hzero : w n q = 0 := not_not.mp (fun h ↦ hn.not_gt (hs n q h).2)
      by_cases h : q ∈ Aᶜ <;> simp [V, P, hzero, h]
  filter_upwards [Metric.tendsto_nhds.1 hV (η / 2) (half_pos hη)] with n hn
  rw [dist_zero_right] at hn ⊢
  change ‖∫ q, P n q * F q ∂μ‖ < η
  have hnearInt : ‖∫ q in A, P n q * F q ∂μ‖ ≤ a * (1024 * M) := by
    have hi := (hiFull n).integrableOn (s := A)
    calc
      _ ≤ ∫ q in A, ‖P n q * F q‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ q in A, a * ‖P n q‖ ∂μ := by
        apply integral_mono_ae hi.norm ((hiP n).norm.const_mul a).integrableOn
        filter_upwards [ae_restrict_mem (μ := μ) hA, ae_restrict_of_ae hmem] with q hq hq'
        rw [norm_mul, mul_comm a]
        exact mul_le_mul_of_nonneg_left (hnear q hq' hq) (norm_nonneg _)
      _ ≤ _ := by
        rw [integral_const_mul]
        gcongr
        exact (setIntegral_le_integral (hiP n).norm (.of_forall fun _ ↦ norm_nonneg _)).trans
          (hrealMass n)
  have hsplit := integral_add_compl hA (hiFull n)
  have hvInt : (∫ q in Aᶜ, P n q * F q ∂μ) = ∫ q, V n q ∂μ :=
    (integral_indicator hA.compl).symm
  rw [← hsplit, hvInt]
  refine (norm_add_le _ _).trans_lt ((add_le_add hnearInt hn.le).trans_lt ?_)
  have haη : a * (1024 * M + 1) = η / 2 := by
    dsimp [a]
    field_simp
  linarith

/-- The full tangential current vanishes against symmetric shrinking-shell
weights of size at most the inverse shell scale. -/
theorem mixed_tangential_shell_limit {ω : L2} (d : MixedQuotientData ω)
    {ε : ℕ → ℝ} (he : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {w : ℕ → Plane → ℝ} (hm : ∀ n, Measurable (w n)) {M : ℝ} (hM : 0 ≤ M)
    (hws : ∀ n q, w n q.swap = w n q)
    (hw : ∀ n q, ‖w n q‖ ≤ M / ε n)
    (hs : ∀ n q, w n q ≠ 0 → Real.cos q.1 * Real.cos q.2 ∈ Ioo (ε n) (2 * ε n)) :
    Tendsto (fun n ↦ ∫ q in mixedOpenCell, w n q * mixedTangentialCurrent d q)
      atTop (𝓝 0) := by
  have hS : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  let μ := volume.restrict mixedOpenCell
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [show μ = volume.restrict mixedOpenCell from rfl, Measure.restrict_apply_univ]
    exact (compact_closed_cell.measure_lt_top (μ := volume)).trans_le' (measure_mono subset_closure)
  have hi (n : ℕ) : IntegrableOn (w n) mixedOpenCell := by
    have hLp : MemLp (w n) 1 μ :=
      MemLp.of_bound (hm n).aestronglyMeasurable _ (.of_forall (hw n))
    exact hLp.integrable le_rfl
  have h2 : Tendsto (fun n ↦ 2 * ε n) atTop (𝓝 0) := by simpa using hlim.const_mul (2 : ℝ)
  obtain ⟨hc, hz⟩ := mixed_tangential_model_defect d
  refine mixed_tangential_current_limit_of_model d hm hws hi (C := 2 * M) ?_ ?_
    (mixed_tangential_shell_defect_limit hc hz he hlim hm hM hw hs)
  · intro n
    filter_upwards with q
    change ‖w n q * shellHeight q‖ ≤ 2 * M
    by_cases h0 : w n q = 0
    · simp only [h0, zero_mul, norm_zero]
      positivity
    · obtain ⟨hl, hu⟩ := hs n q h0
      have hε := he n
      change ε n < shellHeight q at hl
      change shellHeight q < 2 * ε n at hu
      rw [norm_mul, Real.norm_of_nonneg (hε.trans hl).le]
      calc
        _ ≤ (M / ε n) * (2 * ε n) := by
          exact mul_le_mul (hw n q) hu.le (hε.trans hl).le (div_nonneg hM hε.le)
        _ = _ := by field_simp [hε.ne']
  · filter_upwards [ae_restrict_mem (μ := volume) hS] with q hq
    change Tendsto (fun n ↦ w n q * shellHeight q) atTop (𝓝 0)
    have hpos : 0 < shellHeight q := mul_pos
      (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
      (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))
    apply tendsto_const_nhds.congr'
    filter_upwards [h2.eventually (gt_mem_nhds hpos)] with n hn
    have h0 : w n q = 0 := not_not.mp (fun h ↦ hn.not_gt (hs n q h).2)
    rw [h0, zero_mul]

end NoEmbeddedEigenvalues
