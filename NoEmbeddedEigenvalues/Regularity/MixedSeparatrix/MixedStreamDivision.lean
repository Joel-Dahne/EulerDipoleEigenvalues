import NoEmbeddedEigenvalues.Analysis.LocalSobolev.DiagonalSobolev
import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix.MixedSeparatrix
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.QuotientLocal
import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedComparison

/-! # H² stream division at the odd sides of the mixed cell -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped ContDiff
local notation "Plane" => ℝ × ℝ
local notation "π" => Real.pi

/-- Sector parity on the continuous stream in a diagonal side chart. -/
theorem contStream_diagonalTraceChart_character {ζ : L2} {e₁ e₂ : Bool}
    (hs : InSector e₁ e₂ ζ) (j : Fin 2) (side : Bool) (q : Plane) :
    contStream ζ (diagonalTraceChart j (normalReflection (2 * cellEdgeNormal side) q)) =
      paritySign (if j = 0 then e₁ else e₂) * contStream ζ (diagonalTraceChart j q) := by
  let R := normalReflection (2 * cellEdgeNormal side)
  let C := diagonalTraceChart j
  have hc : (liftL2 (invLap ζ) ∘ C) =ᵐ[volume] (contStream ζ ∘ C) :=
    (quasiMeasurePreserving_diagonalTraceChart j).ae_eq_comp (streamLift_ae_eq_contStream ζ)
  have hr := (measurePreserving_normalReflection
    (2 * cellEdgeNormal side)).quasiMeasurePreserving.ae_eq_comp hc
  have he : (contStream ζ ∘ C ∘ R) =ᵐ[volume]
      (fun p ↦ paritySign (if j = 0 then e₁ else e₂) * contStream ζ (C p)) := by
    filter_upwards [hc, hr, liftL2_diagonalTraceChart_character_ae hs.invLap j side] with p h₁ h₂ h₃
    exact h₂.symm.trans (h₃.trans (congrArg (_ * ·) h₁))
  exact congrFun (Measure.eq_of_ae_eq he
    ((continuous_contStream ζ).comp ((continuous_diagonalTraceChart j).comp
      (by unfold R; fun_prop)))
    (continuous_const.mul ((continuous_contStream ζ).comp (continuous_diagonalTraceChart j)))) q

/-- Normal-centered coordinates for the line `a = t`: tangential coordinate
first, as in the one-variable division lemma. -/
private def normalCenter (t : ℝ) : Plane ≃ₜ Plane :=
  planeAffine (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) (t, 0)

private theorem normalCenter_apply (t : ℝ) (q : Plane) :
    normalCenter t q = (q.2 + t, q.1) := by
  ext <;> simp [normalCenter]

private theorem normalCenter_symm (t : ℝ) (q : Plane) :
    (normalCenter t).symm q = (q.2, q.1 - t) := by
  apply (normalCenter t).injective
  rw [Homeomorph.apply_symm_apply, normalCenter_apply, sub_add_cancel]

private theorem normalCenter_measurePreserving (t : ℝ) : MeasurePreserving (normalCenter t) := by
  have hm : MeasurePreserving (Prod.swap : Plane → Plane) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have ht : MeasurePreserving (fun q : Plane ↦ q + (t, 0)) volume volume :=
    measurePreserving_add_right volume _
  convert ht.comp hm using 1
  funext q
  ext <;> simp [normalCenter_apply]

private theorem MemSobolevLocOn.comp_normalCenter {k : ℕ} {U : Set Plane} {f : Plane → ℂ}
    (hf : MemSobolevLocOn k U f) (t : ℝ) :
    MemSobolevLocOn k (normalCenter t ⁻¹' U) (f ∘ normalCenter t) :=
  hf.comp_planeAffine _ _ (normalCenter_measurePreserving t)

private theorem MemSobolevLocOn.comp_normalCenter_symm {k : ℕ} {U : Set Plane} {f : Plane → ℂ}
    (hf : MemSobolevLocOn k U f) (t : ℝ) :
    MemSobolevLocOn k ((normalCenter t).symm ⁻¹' U) (f ∘ (normalCenter t).symm) := by
  let S := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have h : ((normalCenter t).symm : Plane → Plane) = planeAffine S (0, -t) := by
    funext p
    rw [normalCenter_symm]
    ext <;> simp [S, sub_eq_add_neg]
  have hm : MeasurePreserving (planeAffine S (0, -t)) := by
    rw [← h]
    exact MeasurePreserving.symm (normalCenter t).toMeasurableEquiv
      (normalCenter_measurePreserving t)
  rw [h]
  exact hf.comp_planeAffine S (0, -t) hm

private theorem mixedSide_factor (side : Bool) (y : ℝ) :
    Real.cos (y + cellEdgeNormal side) = y * ((if side then -1 else 1 : ℝ) * Real.sinc y) := by
  have hf : y * Real.sinc y = Real.sin y := by
    by_cases hy : y = 0
    · simp [hy]
    · rw [Real.sinc_of_ne_zero hy]
      field_simp
  cases side
  · change Real.cos (y + (-π) / 2) = y * (1 * Real.sinc y)
    rw [neg_div, ← sub_eq_add_neg, Real.cos_sub_pi_div_two, one_mul, hf]
  · simpa [cellEdgeNormal, Real.cos_add_pi_div_two, mul_neg] using congrArg Neg.neg hf.symm

private theorem mixed_odd_side_patch {ζ : L2} {e : Bool} (hs : InSector false e ζ)
    {ε : ℝ} (hε : 0 < ε)
    (hψ : MemSobolevLocOn 3 {p | |dipoleLift p| < ε} (contStream ζ))
    (side : Bool) (s : ℝ) :
    ∃ W : Set Plane, IsOpen W ∧ (cellEdgeNormal side, s) ∈ W ∧
      MemSobolevLocOn 2 W (fun q ↦ contStream ζ (diagInv q) / (Real.cos q.1 : ℂ)) := by
  let t := cellEdgeNormal side
  let C := normalCenter t
  let U := C ⁻¹' (diagInv ⁻¹' {p | |dipoleLift p| < ε})
  let F := (contStream ζ ∘ diagInv) ∘ C
  let Q := fun q : Plane ↦ contStream ζ (diagInv q) / (Real.cos q.1 : ℂ)
  let g := fun q : Plane ↦ (if side then -1 else 1 : ℝ) * Real.sinc q.2
  have ht : Real.cos t = 0 := by
    cases side <;> simp [t, cellEdgeNormal, neg_div]
  have hC : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  have hU : IsOpen U := (hC.preimage diagInv.continuous).preimage C.continuous
  have hU0 : (s, 0) ∈ U := by
    change |dipoleLift (diagInv (normalCenter t (s, 0)))| < ε
    rw [normalCenter_apply, zero_add, dipoleLift_eq_diag, diagCoord_diagInv]
    simpa only [ht, mul_zero, zero_mul, abs_zero]
  have hlocal : MemSobolevLocOn 3 U F := hψ.comp_diagInv.comp_normalCenter t
  have ho : ∀ᵐ q : Plane, F (axisReflect 1 q) = -F q := by
    exact Eventually.of_forall fun q ↦ by
      have h := contStream_diagonalTraceChart_character hs 0 side (q.1, q.2 + t)
      simp only [ite_true, paritySign, Bool.false_eq_true, ite_false, neg_one_mul,
        normalReflection_apply] at h
      simp only [F, C, Function.comp_apply, normalCenter_apply, axisReflect, one_ne_zero, ite_false]
      have he : 2 * cellEdgeNormal side - (q.2 + t) = -q.2 + t := by dsimp [t]; ring
      rwa [he] at h
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hU0)
  let V := axisRectangle 1 r (s - r) (s + r)
  have hV : V = Metric.ball (s, 0) r := by
    ext q
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero,
      abs_lt, abs_lt]
    change (s - r < q.1 ∧ q.1 < s + r) ∧ -r < q.2 ∧ q.2 < r ↔ _
    constructor <;> rintro ⟨⟨ha, hb⟩, hc, hd⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, hc, hd⟩
  have hVo : IsOpen V := hV ▸ Metric.isOpen_ball
  have hV0 : (s, 0) ∈ V := by rw [hV]; exact Metric.mem_ball_self hr
  have hcV : closure V = Metric.closedBall (s, 0) r := by
    rw [hV, closure_ball _ hr.ne']
  have hF := hlocal V hVo (hcV ▸ isCompact_closedBall _ _) (hcV ▸ hball)
  obtain ⟨D, hD, _⟩ := memSobolevOn_iff_exists_weakJet.mp hF
  obtain ⟨_, _, hdiv⟩ := odd_h3_division (show s - r < s + r by linarith) hr
  obtain ⟨L, _, hL, _, hid, _, _⟩ := hdiv F D hF hD (ae_restrict_of_ae ho)
  have hg : ContDiff ℝ ∞ g := by
    have hsinc : (fun q : Plane ↦ Real.sinc q.2) = fun q ↦ saddleFactor (0, Real.sqrt 2 * q.2) := by
      funext q
      simp only [saddleFactor, zero_div, Real.sinc_zero, one_mul]
      congr 1
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
    exact contDiff_const.mul (hsinc ▸ saddleFactor_regular.1.comp (by fun_prop))
  let O := V ∩ {q | g q ≠ 0}
  have hOo : IsOpen O := hVo.inter (isOpen_ne_fun hg.continuous continuous_const)
  have hO0 : (s, 0) ∈ O := ⟨hV0, by cases side <;> simp [g]⟩
  have hM := (hL.memSobolevLocOn.mono (inter_subset_left (t := {q | g q ≠ 0})))
    |>.div_smooth hOo hg (fun _ hp ↦ hp.2)
  have hn : ∀ᵐ q : Plane, q.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    have h : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by rw [ae_iff]; simp
    exact Measure.quasiMeasurePreserving_snd.ae h
  have hQc : MemSobolevLocOn 2 O (Q ∘ C) := by
    apply hM.congr_ae_on
    have hAE := (ae_restrict_iff' hVo.measurableSet).mp hid
    filter_upwards [hAE, hn] with q hq hn hqO
    change L q / (g q : ℂ) = F q / (Real.cos (q.2 + t) : ℂ)
    have he := hq hqO.1
    change F q = (q.2 : ℂ) * L q at he
    rw [he, mixedSide_factor]
    change L q / (g q : ℂ) = _ / ((q.2 * g q : ℝ) : ℂ)
    simpa only [Complex.ofReal_mul] using
      (mul_div_mul_left (L q) (g q : ℂ) (Complex.ofReal_ne_zero.mpr hn)).symm
  refine ⟨C.symm ⁻¹' O, hOo.preimage C.symm.continuous, ?_, ?_⟩
  · change (normalCenter t).symm (t, s) ∈ O
    rw [normalCenter_symm, sub_self]
    exact hO0
  · have h := hQc.comp_normalCenter_symm t
    apply h.congr_ae_on
    exact Eventually.of_forall fun q _ ↦ congrArg Q (C.apply_symm_apply q)

/-- The raw mixed stream quotient admits local H² on an open strip that
contains the closed cell, including the odd sides and both their corners. -/
theorem mixed_stream_quotient_local_h2 {ζ : L2} {e : Bool} (hs : InSector false e ζ)
    {ε : ℝ} (hε : 0 < ε)
    (hψ : MemSobolevLocOn 3 {p | |dipoleLift p| < ε} (contStream ζ)) :
    MemSobolevLocOn 2 {q | |q.1| < π}
      (fun q ↦ contStream ζ (diagInv q) / (Real.cos q.1 : ℂ)) := by
  apply memSobolevLocOn_of_locally
  intro q hq
  by_cases hn : Real.cos q.1 = 0
  · have h : |q.1| = π / 2 := by
      have he : Real.cos |q.1| = Real.cos (π / 2) := by rwa [Real.cos_abs, Real.cos_pi_div_two]
      apply le_antisymm
      · by_contra! hlt
        exact (Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (le_of_lt hq) hlt).ne he
      · by_contra! hlt
        exact (Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
          (by linarith [Real.pi_pos]) hlt).ne he.symm
    rcases (abs_eq (show 0 ≤ π / 2 by positivity)).mp h with h | h
    · simpa only [cellEdgeNormal, ite_true, Prod.mk.eta, ← h] using
        mixed_odd_side_patch hs hε hψ true q.2
    · simpa only [cellEdgeNormal, Bool.false_eq_true, ite_false, neg_div, Prod.mk.eta, ← h] using
        mixed_odd_side_patch hs hε hψ false q.2
  · have hu : MemSobolevLocOn 2 (univ : Set Plane) (contStream ζ) := by
      intro V _ hc _
      exact (memSobolevOn_liftL2 (memSobolev_two_invLap ζ)
        (hc.isBounded.subset subset_closure)).congr_ae (streamLift_ae_eq_contStream ζ)
    have huv : MemSobolevLocOn 2 (univ : Set Plane) (contStream ζ ∘ diagInv) := by
      simpa only [preimage_univ] using hu.comp_diagInv
    let W := {p : Plane | Real.cos p.1 ≠ 0}
    have hg : ContDiff ℝ ∞ (fun p : Plane ↦ Real.cos p.1) := by fun_prop
    have hW : IsOpen W := isOpen_ne_fun hg.continuous continuous_const
    exact ⟨W, hW, hn, (huv.mono (subset_univ _)).div_smooth hW hg (fun _ hp ↦ hp)⟩

end NoEmbeddedEigenvalues
