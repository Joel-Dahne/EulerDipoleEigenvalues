module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTraceFlux
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalParameterH2
public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals
public import Mathlib.Topology.Compactness.Lindelof

/-! # Endpoint traces from interval energy -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Restrict actual interval H1 data, retaining both functions. -/
theorem HasIntervalH1.restrict_interval {a b c d : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hac : a ≤ c) (hdb : d ≤ b) :
    HasIntervalH1 c d F D := by
  have hs : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono_set _ hs),
    h.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hs),
    fun x y hx hxy hy ↦ h.locally_absolutelyContinuous x y (hac.trans_lt hx) hxy
      (hy.trans_le hdb),
    h.hasDerivAt_ae.mono fun x hx hxI ↦ hx (hs hxI)⟩

/-- A uniform energy estimate using any closed window inside the original
interval, even when the evaluation point is an endpoint of the smaller window. -/
theorem HasIntervalH1.point_sq_le_subinterval {a b c d t : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (ht : t ∈ Icc c d) :
    ‖F t‖ ^ 2 ≤ (2 / (d - c)) * (∫ x in Ioo c d, ‖F x‖ ^ 2) +
      2 * (d - c) * ∫ x in Ioo c d, ‖D x‖ ^ 2 := by
  have hs := h.restrict_interval hac.le hdb.le
  have hc : ContinuousOn F (Icc c d) :=
    (h.continuousOn_Ioo (hac.trans (hcd.trans hdb))).mono (Icc_subset_Ioo hac hdb)
  have he := hs.extension_unique hcd hc (fun _ _ ↦ rfl)
  simpa only [← he ht] using hs.extension_sq_le hcd ht

/-- A canonical trace of a rescaled section is controlled on a physical-time
window of length one, not by the growing total period. -/
theorem clock_endpoint_trace_sq_le {S : ℝ} (hS : 4 ≤ S)
    {F H W : ℝ → ℂ}
    (hW : HasIntervalH1 (-1 / 4) (3 / 4) W (fun θ ↦ (S : ℂ) * H (θ * S)))
    (hWF : W =ᵐ[volume.restrict (Ioo (-1 / 4 : ℝ) (3 / 4))] (fun θ ↦ F (θ * S)))
    (side : Bool) :
    ‖interiorSectionTrace (fun s ↦ F (((if side then 1 else -1 : ℝ) / 8 + s) * S))‖ ^ 2 ≤
      2 * (∫ t in Ioo (-S / 8) (S / 8), ‖F t‖ ^ 2) +
      2 * (∫ t in Ioo (-S / 8) (S / 8), ‖H t‖ ^ 2) := by
  have hSp : 0 < S := by linarith
  have hi : 0 < 1 / S := one_div_pos.mpr hSp
  have hi4 : 1 / S ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hS
  let θ : ℝ := (if side then 1 else -1) / 8
  let c : ℝ := if side then θ - 1 / S else θ
  let d : ℝ := if side then θ else θ + 1 / S
  have hc : (-1 / 8 : ℝ) ≤ c := by cases side <;> dsimp [c, θ] <;> linarith
  have hd : d ≤ (1 / 8 : ℝ) := by cases side <;> dsimp [d, θ] <;> linarith
  have hlen : d - c = 1 / S := by cases side <;> dsimp [c, d] <;> ring
  have hcd : c < d := sub_pos.mp (hlen ▸ hi)
  have hθ : θ ∈ Icc c d := by
    cases side <;> dsimp [c, d, θ] <;> constructor <;> linarith
  have hθwide : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4) := by
    cases side <;> norm_num [θ]
  rw [interiorSectionTrace_eq_at hθwide (hW.continuousOn_Ioo (by norm_num)) hWF]
  have hpoint := hW.point_sq_le_subinterval (by linarith : (-1 / 4 : ℝ) < c)
    hcd (by linarith : d < (3 / 4 : ℝ)) hθ
  have hsub : Ioo c d ⊆ Ioo (-1 / 8 : ℝ) (1 / 8) := Ioo_subset_Ioo hc hd
  have hbase : Ioo (-1 / 8 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4 : ℝ) (3 / 4) :=
    Ioo_subset_Ioo (by norm_num) (by norm_num)
  have hWbase := hW.memLp_value.mono_measure (Measure.restrict_mono_set _ hbase)
  have hDbase := hW.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hbase)
  have hFWbase := (ae_restrict_of_ae_restrict_of_subset hbase hWF).symm
  have hFbase := hWbase.ae_eq hFWbase.symm
  have hHbase : MemLp (fun θ ↦ H (θ * S)) 2
      (volume.restrict (Ioo (-1 / 8 : ℝ) (1 / 8))) := by
    convert hDbase.const_smul ((S : ℂ)⁻¹) using 1
    ext θ
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hSp.ne'), one_mul]
  have hscale (K : ℝ → ℝ) :
      (∫ t in Ioo (-S / 8) (S / 8), K t) =
        S * ∫ θ in Ioo (-1 / 8 : ℝ) (1 / 8), K (θ * S) := by
    have hs := intervalIntegral.smul_integral_comp_mul_right K
      (a := (-1 / 8 : ℝ)) (b := 1 / 8) S
    rw [show (-1 / 8 : ℝ) * S = -S / 8 by ring,
      show (1 / 8 : ℝ) * S = S / 8 by ring] at hs
    rw [intervalIntegral.integral_of_le (by linarith : -S / 8 ≤ S / 8),
      ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo] at hs
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 / 8 : ℝ) ≤ 1 / 8),
      ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo] at hs
    exact hs.symm
  have hFWint : (∫ θ in Ioo (-1 / 8 : ℝ) (1 / 8), ‖W θ‖ ^ 2) =
      ∫ θ in Ioo (-1 / 8 : ℝ) (1 / 8), ‖F (θ * S)‖ ^ 2 :=
    integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset hbase hWF).mono
      fun _ he ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) he)
  have hDint : (∫ θ in Ioo (-1 / 8 : ℝ) (1 / 8), ‖(S : ℂ) * H (θ * S)‖ ^ 2) =
      S ^ 2 * ∫ θ in Ioo (-1 / 8 : ℝ) (1 / 8), ‖H (θ * S)‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSp, integral_const_mul]
  have hWle := setIntegral_mono_set (hWbase.integrable_norm_pow (by norm_num))
    (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall fun _ ht ↦ hsub ht)
  have hDle := setIntegral_mono_set (hDbase.integrable_norm_pow (by norm_num))
    (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall fun _ ht ↦ hsub ht)
  calc
    _ ≤ (2 / (d - c)) * (∫ x in Ioo c d, ‖W x‖ ^ 2) +
        2 * (d - c) * ∫ x in Ioo c d, ‖(S : ℂ) * H (x * S)‖ ^ 2 := hpoint
    _ ≤ (2 / (d - c)) * (∫ x in Ioo (-1 / 8 : ℝ) (1 / 8), ‖W x‖ ^ 2) +
        2 * (d - c) * ∫ x in Ioo (-1 / 8 : ℝ) (1 / 8), ‖(S : ℂ) * H (x * S)‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hWle (by positivity))
        (mul_le_mul_of_nonneg_left hDle (by positivity))
    _ = _ := by
      rw [hlen, hFWint, hDint, hscale (fun t ↦ ‖F t‖ ^ 2), hscale (fun t ↦ ‖H t‖ ^ 2)]
      field_simp



/-- Local square integrability and a common integrable square majorant imply
square integrability on the open level interval. -/
theorem memLp_two_of_local_sq_bound {r : ℝ} {T : ℝ → ℂ} {E : ℝ → ℝ}
    (hE : IntegrableOn E (Ioo 0 r))
    (hloc : ∀ a b : ℝ, 0 < a → a < b → b < r →
      MemLp T 2 (volume.restrict (Ioo a b)) ∧
        ∀ᵐ h ∂volume.restrict (Ioo a b), ‖T h‖ ^ 2 ≤ E h) :
    MemLp T 2 (volume.restrict (Ioo 0 r)) := by
  classical
  have hloc' (x : Ioo (0 : ℝ) r) : ∃ a b : ℝ,
      0 < a ∧ a < x ∧ x < b ∧ b < r := by
    obtain ⟨a, ha, hax⟩ := exists_between x.property.1
    obtain ⟨b, hxb, hb⟩ := exists_between x.property.2
    exact ⟨a, b, ha, hax, hxb, hb⟩
  choose a b ha hax hxb hb using hloc'
  let W (x : Ioo (0 : ℝ) r) := Ioo (a x) (b x)
  obtain ⟨s, hs, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (Ioo (0 : ℝ) r)).elim_countable_subcover
    W (fun _ ↦ isOpen_Ioo)
    (fun x hx ↦ mem_iUnion_of_mem ⟨x, hx⟩ ⟨hax ⟨x, hx⟩, hxb ⟨x, hx⟩⟩)
  let : Countable s := hs.to_subtype
  have hsub : Ioo (0 : ℝ) r ⊆ ⋃ i : s, W i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion_of_mem ⟨i, hi⟩ hxi
  have hM : AEStronglyMeasurable T (volume.restrict (⋃ i : s, W i.val)) :=
    AEStronglyMeasurable.iUnion fun i : s ↦
      (hloc _ _ (ha i.val) ((hax i.val).trans (hxb i.val)) (hb i.val)).1.aestronglyMeasurable
  have hB : ∀ᵐ h ∂volume.restrict (⋃ i : s, W i.val), ‖T h‖ ^ 2 ≤ E h := by
    apply (ae_restrict_iUnion_iff _ _).2
    intro i
    exact (hloc _ _ (ha i.val) ((hax i.val).trans (hxb i.val)) (hb i.val)).2
  have hm := hM.mono_measure (Measure.restrict_mono_set _ hsub)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply hE.mono' (hm.norm.pow 2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hB] with h hh
  change |‖T h‖ ^ 2| ≤ E h
  rwa [abs_of_nonneg (sq_nonneg _)]

end NoEmbeddedEigenvalues
