import NoEmbeddedEigenvalues.PhaseCellEstimates
import NoEmbeddedEigenvalues.QuarterPhaseCells
import NoEmbeddedEigenvalues.IntervalH1LocalToGlobal
import NoEmbeddedEigenvalues.WeightedCellEnergy
import NoEmbeddedEigenvalues.DescendingIntervalPartition

/-!
# Global quarter-divisor division

Blueprint: `lem:phase-cell-division`.

Disjoint complete cells provide the continuous quotient near resonances.
At their nonresonant boundaries the quotient is ordinary division. Countable
energy summation and local interval H¹ globalization give the whole collar;
reciprocal-distance integrability forces its canonical zero trace.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set MeasureTheory Filter
open scoped Topology ContDiff

/-- Global division with a measurable weight comparable to a constant on each
small complete cell. The same local quotient construction works without
differentiating the weight (`lem:comparable-weight-phase-division`). -/
theorem phase_cell_division_of_comparable_weight {lam : ℝ} (hlam : lam ≠ 0)
    {κ : ℂ} (hκ : κ ^ 4 = 1) {h₀ rW A : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1)
    (hrW : 0 < rW) (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hW : Measurable W) (hW1 : ∀ h ∈ Ioo 0 h₀, 1 ≤ W h)
    (hWcell : ∀ a z b : ℝ, 0 < a → a < z → z < b → b < rW →
      quarterDivisor lam κ z = 0 →
      |quarterPhase lam a - quarterPhase lam z| = Real.pi →
      |quarterPhase lam b - quarterPhase lam z| = Real.pi →
      ∃ w : ℝ, 0 ≤ w ∧ ∀ h ∈ Ioo a b, w ≤ W h ∧ W h ≤ A * w)
    {N N₁ N₂ : ℝ → ℂ} (hN : HasIntervalH2Loc 0 h₀ N N₁ N₂)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hWN₁ : MemLp (fun h ↦ (Real.sqrt (W h) : ℂ) * N₁ h) 2
      (volume.restrict (Ioo 0 h₀)))
    (hWN₂ : MemLp (fun h ↦ (Real.sqrt (W h) : ℂ) * ((h : ℂ) * N₂ h)) 2
      (volume.restrict (Ioo 0 h₀))) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam κ h₁ ∧
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
        (∀ h ∈ Ioo 0 h₁, quarterDivisor lam κ h * Q h = N h) ∧
        MemLp (fun h ↦ (Real.sqrt (W h) : ℂ) * (Q h / (h : ℂ))) 2
          (volume.restrict (Ioo 0 h₁)) ∧
        MemLp (fun h ↦ (Real.sqrt (W h) : ℂ) * Q₁ h) 2 (volume.restrict (Ioo 0 h₁)) ∧
        intervalH1Extension 0 h₁ Q Q₁ 0 = 0 := by
  classical
  obtain ⟨K, r, hK, hr, _, hest⟩ := phase_cell_estimates hlam
  obtain ⟨e, z, he, het, hep, hzp⟩ :=
    exists_complete_phase_cells hlam hκ (lt_min hh₀ (lt_min hr hrW))
  let s := fun n ↦ Ioo (e (n + 1)) (e n)
  have heh₀ (n : ℕ) : e n < h₀ := (hep n).2.1.trans_le (min_le_left _ _)
  have her (n : ℕ) : e n < r :=
    (hep n).2.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hNc (n : ℕ) : HasIntervalH2 (e (n + 1)) (e n) N N₁ N₂ :=
    hN _ _ (hep (n + 1)).1 (he (Nat.lt_succ_self n)) (heh₀ n)
  have hcell (n : ℕ) := hest κ hκ (e (n + 1)) (z n) (e n)
    (hep (n + 1)).1 (hzp n).1 (hzp n).2.1 (her n) (hzp n).2.2.1
    (hzp n).2.2.2.1 (hzp n).2.2.2.2 N N₁ N₂ (hNc n)
    (hzero (z n) ⟨(hep (n + 1)).1.trans (hzp n).1,
      (hzp n).2.1.trans (heh₀ n)⟩ (hzp n).2.2.1)
  choose q q₁ hq hqfac hql hqv hqd using hcell
  have hdis := descending_cells_disjoint he
  let Q := fun x ↦ if h : ∃ n, x ∈ s n then q (Nat.find h) x
    else N x / quarterDivisor lam κ x
  have hQon (n : ℕ) : EqOn Q (q n) (s n) := by
    intro x hx
    have hex : ∃ m, x ∈ s m := ⟨n, hx⟩
    have hi : Nat.find hex = n := by
      by_contra hne
      exact disjoint_left.1 (hdis hne) (Nat.find_spec hex) hx
    dsimp only [Q]
    rw [dite_eq_left hex, hi]
  have hQfac (x : ℝ) (hx : x ∈ Ioo 0 (e 0)) :
      quarterDivisor lam κ x * Q x = N x := by
    by_cases hc : ∃ n, x ∈ s n
    · obtain ⟨n, hn⟩ := hc
      rw [hQon n hn]
      exact hqfac n x hn
    · obtain ⟨n, rfl⟩ := (mem_descending_cell_or_endpoint het hx).resolve_left hc
      dsimp only [Q]
      rw [dite_eq_right hc]
      field_simp [(hep n).2.2.2]
  have hQc (n : ℕ) : HasIntervalH1 (e (n + 1)) (e n) Q (q₁ n) :=
    (hq n).congr_Ioo (hQon n).symm
  have hQdc (n : ℕ) : HasIntervalH1 (e (n + 1)) (e n) Q (deriv Q) :=
    (hQc n).with_deriv
  have hdeq (n : ℕ) : deriv Q =ᵐ[volume.restrict (s n)] q₁ n := by
    filter_upwards [ae_restrict_of_ae (hQc n).hasDerivAt_ae,
      ae_restrict_mem measurableSet_Ioo] with x hx hi
    exact (hx hi).deriv
  have hμ : volume.restrict (⋃ n, s n) = volume.restrict (Ioo 0 (e 0)) :=
    Measure.restrict_congr_set (descending_cells_ae_cover he (fun n ↦ (hep n).1) het)
  have hsub : (⋃ n, s n) ⊆ Ioo 0 h₀ := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact ⟨(hep (n + 1)).1.trans hn.1, hn.2.trans (heh₀ n)⟩
  have hW₀ : ∀ᵐ x ∂(volume.restrict (Ioo 0 h₀)), 1 ≤ W x :=
    (ae_restrict_mem measurableSet_Ioo).mono hW1
  have hN₁ := memLp_of_sqrt_weight_ge_one hW hW₀ hWN₁
  have hN₂ := memLp_of_sqrt_weight_ge_one hW hW₀ hWN₂
  let G := fun x ↦ ‖N₁ x‖ ^ 2 + x ^ 2 * ‖N₂ x‖ ^ 2
  have hN₁i := hN₁.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hWi : IntegrableOn (fun x ↦ x ^ 2 * ‖N₂ x‖ ^ 2) (Ioo 0 h₀) volume := by
    change Integrable (fun x ↦ x ^ 2 * ‖N₂ x‖ ^ 2) (volume.restrict (Ioo 0 h₀))
    convert! hN₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0) using 1
    funext x
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hGwhole : IntegrableOn G (Ioo 0 h₀) := hN₁i.add hWi
  have hGi : IntegrableOn G (⋃ n, s n) := hGwhole.mono_set hsub
  have hGpos (x : ℝ) : 0 ≤ G x :=
    add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hQhc (n : ℕ) : MemLp (fun x ↦ Q x / (x : ℂ)) 2 (volume.restrict (s n)) := by
    apply (hql n).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hQon n hx]
  have hGweighted : IntegrableOn (fun x ↦ W x * G x) (Ioo 0 h₀) := by
    apply ((hWN₁.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hWN₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (zero_le_one.trans (hW1 x hx)), G, Pi.add_apply]
    ring
  have hWcell' (n : ℕ) : ∃ w : ℝ, 0 ≤ w ∧
      ∀ᵐ x ∂(volume.restrict (s n)), w ≤ W x ∧ W x ≤ A * w := by
    have hen : e n < rW :=
      (hep n).2.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨w, hw, hcomp⟩ := hWcell _ _ _ (hep (n + 1)).1 (hzp n).1 (hzp n).2.1 hen
      (hzp n).2.2.1 (hzp n).2.2.2.1 (hzp n).2.2.2.2
    exact ⟨w, hw, (ae_restrict_mem measurableSet_Ioo).mono hcomp⟩
  have hweighted (F : ℝ → ℂ) (hF : ∀ n, MemLp F 2 (volume.restrict (s n)))
      (hE : ∀ n, (∫ x in s n, ‖F x‖ ^ 2) ≤ K * ∫ x in s n, G x) :
      MemLp (fun x ↦ (Real.sqrt (W x) : ℂ) * F x) 2 (volume.restrict (Ioo 0 (e 0))) := by
    rw [← hμ]
    have hWGi := hGweighted.mono_set hsub
    have hlocal (n : ℕ) :
        MemLp (fun x ↦ (Real.sqrt (W x) : ℂ) * F x) 2 (volume.restrict (s n)) ∧
          (∫ x in s n, ‖(Real.sqrt (W x) : ℂ) * F x‖ ^ 2) ≤
            A * K * ∫ x in s n, W x * G x := by
      obtain ⟨w, hw, hcomp⟩ := hWcell' n
      exact sqrt_weight_cell_energy hW hw hA hK.le hcomp
        (Filter.Eventually.of_forall hGpos) (hGi.mono_set (subset_iUnion s n))
        (hWGi.mono_set (subset_iUnion s n)) (hF n) (hE n)
    exact memLp_two_of_cell_energy (fun _ ↦ measurableSet_Ioo) hdis (mul_nonneg hA hK.le)
      hWGi (fun x hx ↦ mul_nonneg (zero_le_one.trans (hW1 x (hsub hx))) (hGpos x))
      (fun n ↦ (hlocal n).1) (fun n ↦ (hlocal n).2)
  have hQhW := hweighted _ hQhc (by
    intro n
    have hEq : (fun x ↦ ‖Q x / (x : ℂ)‖ ^ 2) =ᵐ[volume.restrict (s n)]
        (fun x ↦ ‖q n x / (x : ℂ)‖ ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [hQon n hx]
    rw [integral_congr_ae hEq]
    apply (hqv n).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply integral_mono ((hNc n).1.memLp_derivative.integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)) (hGi.mono_set (subset_iUnion s n))
    intro x
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hQdW := hweighted (deriv Q) (fun n ↦ (hQdc n).memLp_derivative) (by
    intro n
    calc
      (∫ x in s n, ‖deriv Q x‖ ^ 2) = ∫ x in s n, ‖q₁ n x‖ ^ 2 :=
        integral_congr_ae ((hdeq n).fun_comp (fun v : ℂ ↦ ‖v‖ ^ 2))
      _ ≤ _ := hqd n)
  have hWe : ∀ᵐ h ∂(volume.restrict (Ioo 0 (e 0))), 1 ≤ W h :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun h hh ↦ hW1 h ⟨hh.1, hh.2.trans (heh₀ 0)⟩)
  have hQhL := memLp_of_sqrt_weight_ge_one hW hWe hQhW
  have hQdL := memLp_of_sqrt_weight_ge_one hW hWe hQdW
  have hQm : AEStronglyMeasurable Q (volume.restrict (Ioo 0 (e 0))) := by
    rw [← hμ]
    exact AEStronglyMeasurable.iUnion fun n ↦ (hQc n).memLp_value.aestronglyMeasurable
  have hQL : MemLp Q 2 (volume.restrict (Ioo 0 (e 0))) := by
    apply hQhL.of_le_mul (c := e 0) hQm
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
    calc ‖Q x‖ = ‖(x : ℂ) * (Q x / (x : ℂ))‖ := by field_simp
         _ = x * ‖Q x / (x : ℂ)‖ := by
           rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
         _ ≤ e 0 * ‖Q x / (x : ℂ)‖ :=
           mul_le_mul_of_nonneg_right hx.2.le (norm_nonneg _)
  have hQinv (x : ℝ) (hx : x ∈ Ioo 0 (e 0)) (hne : quarterDivisor lam κ x ≠ 0) :
      Q x = (quarterDivisor lam κ x)⁻¹ * N x := by
    calc Q x = (quarterDivisor lam κ x)⁻¹ * (quarterDivisor lam κ x * Q x) := by
           rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
         _ = _ := by rw [hQfac x hx]
  have hQglobal : HasIntervalH1 0 (e 0) Q (deriv Q) := by
    apply hasIntervalH1_of_local (hep 0).1 hQL hQdL
    intro x hx
    obtain hc | hc := mem_descending_cell_or_endpoint het hx
    · obtain ⟨n, hn⟩ := hc
      exact ⟨e (n + 1), e n, (hep (n + 1)).1.le, he.antitone (Nat.zero_le n), hn, hQdc n⟩
    · obtain ⟨n, hn⟩ := hc
      have hne : quarterDivisor lam κ x ≠ 0 := hn ▸ (hep n).2.2.2
      have hd := (contDiffOn_quarterDivisor lam κ).contDiffAt
        (Ioo_mem_nhds hx.1 (hx.2.trans ((heh₀ 0).trans hh₀1)))
      have hev : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 (e 0) ∧ quarterDivisor lam κ y ≠ 0 :=
        by
          filter_upwards [Ioo_mem_nhds hx.1 hx.2, hd.continuousAt.eventually_ne hne]
            with y hy hyne
          exact ⟨hy, hyne⟩
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      let c := x - ε / 2
      let d := x + ε / 2
      have hcd : c < d := by dsimp [c, d]; linarith
      have hxc : x ∈ Ioo c d := by dsimp [c, d]; constructor <;> linarith
      have hnear (y : ℝ) (hy : y ∈ Icc c d) : dist y x < ε := by
        rw [Real.dist_eq, abs_lt]
        dsimp [c, d] at hy
        constructor <;> linarith [hy.1, hy.2]
      have hcp := hball (hnear c (left_mem_Icc.2 hcd.le))
      have hdp := hball (hnear d (right_mem_Icc.2 hcd.le))
      have hR : ContDiffOn ℝ ∞ (fun y ↦ (quarterDivisor lam κ y)⁻¹)
          (Metric.ball x ε) := by
        have hS : Metric.ball x ε ⊆ Ioo 0 1 := fun y hy ↦
          ⟨(hball hy).1.1, (hball hy).1.2.trans ((heh₀ 0).trans hh₀1)⟩
        exact ((contDiffOn_quarterDivisor lam κ).mono hS).inv fun y hy ↦ (hball hy).2
      have hcn := (hN c d hcp.1.1 hcd (hdp.1.2.trans (heh₀ 0))).1
      have hmul := hcn.mul_contDiffOn_open Metric.isOpen_ball hR
        (fun y hy ↦ hnear y hy)
      have hreg := hmul.congr_Ioo (fun y hy ↦
        (hQinv y (hball (hnear y (Ioo_subset_Icc_self hy))).1
          (hball (hnear y (Ioo_subset_Icc_self hy))).2).symm)
      exact ⟨c, d, hcp.1.1.le, hdp.1.2.le, hxc, hreg.with_deriv⟩
  exact ⟨e 0, (hep 0).1, heh₀ 0, (hep 0).2.2.1, Q, deriv Q, hQglobal,
    hQfac, hQhW, hQdW, hQglobal.trace_zero_of_div_memLp (hep 0).1 hQhL⟩

/-- Global division after decreasing the upper endpoint to a full-cell boundary
(`lem:phase-cell-division`). The quotient extends continuously through resonances,
and its zero-endpoint value is the canonical H¹ trace. -/
theorem phase_cell_division {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1) {N N₁ N₂ : ℝ → ℂ}
    (hN : HasIntervalH2Loc 0 h₀ N N₁ N₂)
    (hzero : ∀ h ∈ Ioo 0 h₀, quarterDivisor lam κ h = 0 → N h = 0)
    (hN₁ : MemLp N₁ 2 (volume.restrict (Ioo 0 h₀)))
    (hN₂ : MemLp (fun (h : ℝ) ↦ (h : ℂ) * N₂ h) 2 (volume.restrict (Ioo 0 h₀))) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ < h₀ ∧ IsPhaseCellEndpoint lam κ h₁ ∧
      ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 h₁ Q Q₁ ∧
        (∀ h ∈ Ioo 0 h₁, quarterDivisor lam κ h * Q h = N h) ∧
        MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 h₁)) ∧
        intervalH1Extension 0 h₁ Q Q₁ 0 = 0 := by
  obtain ⟨h₁, hh₁, hlt, hend, Q, Q₁, hQ, hfac, hmass, _, htrace⟩ :=
    phase_cell_division_of_comparable_weight hlam hκ (A := 1) hh₀ hh₀1 hh₀ zero_le_one
      (W := fun _ ↦ 1) measurable_const (fun _ _ ↦ le_rfl)
      (fun _ _ _ _ _ _ _ _ _ _ ↦ ⟨1, zero_le_one, fun _ _ ↦ by simp⟩) hN hzero
      (by simpa using hN₁) (by simpa using hN₂)
  exact ⟨h₁, hh₁, hlt, hend, Q, Q₁, hQ, hfac, by simpa using hmass, htrace⟩



end NoEmbeddedEigenvalues
