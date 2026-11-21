import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalZeroExtension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Local interval H¹ data and global finite energy

Blueprint: `lem:h1-local-finite-derivative`, `lem:h1-local-global`,
`lem:h1-div-zero-trace`.

Compatible local H¹ data globalize once the specified derivative has a global
L² norm. The value norm follows from the bounded integral primitive.
Subtracting that primitive gives a locally constant function on an interval,
so local increment identities globalize.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Filter MeasureTheory
open scoped Topology

/-- On a bounded connected interval, compatible local H¹ and a globally L²
specified derivative already force the value to be L² as well. -/
theorem hasIntervalH1_of_local_derivative {a b : ℝ} {F D : ℝ → ℂ} (hab : a < b)
    (hD : MemLp D 2 (volume.restrict (Ioo a b)))
    (hloc : ∀ x ∈ Ioo a b, ∃ c d : ℝ,
      a ≤ c ∧ d ≤ b ∧ x ∈ Ioo c d ∧ HasIntervalH1 c d F D) :
    HasIntervalH1 a b F D := by
  let m := (a + b) / 2
  have hm : m ∈ Icc a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hi : IntegrableOn D (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hD.integrable (by norm_num)
  have hint (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      IntervalIntegrable D volume x y :=
    (hi.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable
  let P := intervalH1Extension a b F D
  have hinc (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      P y - P x = ∫ t in x..y, D t := by
    dsimp only [P, intervalH1Extension]
    rw [add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hint m y hm hy) (hint m x hm hx)
  let L : Ioo a b → ℂ := fun x ↦ F x - P x
  have hL : IsLocallyConstant L := by
    apply (IsLocallyConstant.iff_eventually_eq L).2
    intro x
    obtain ⟨c, d, hac, hdb, hx, h⟩ := hloc x x.property
    have hn : ∀ᶠ y : Ioo a b in 𝓝 x, (y : ℝ) ∈ Ioo c d :=
      continuous_subtype_val.continuousAt.eventually (Ioo_mem_nhds hx.1 hx.2)
    filter_upwards [hn] with y hy
    dsimp only [L]
    have hf := h.integral_eq_sub hx hy
    have hp := hinc x y (Ioo_subset_Icc_self x.property) (Ioo_subset_Icc_self y.property)
    linear_combination -hf - hp
  have : PreconnectedSpace (Ioo a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hFTC (c : ℝ) (hc : c ∈ Ioo a b) (d : ℝ) (hd : d ∈ Ioo a b) :
      (∫ t in c..d, D t) = F d - F c := by
    have he := hL.apply_eq_of_preconnectedSpace ⟨c, hc⟩ ⟨d, hd⟩
    have hp := hinc c d (Ioo_subset_Icc_self hc) (Ioo_subset_Icc_self hd)
    dsimp only [L] at he
    linear_combination he - hp
  have hmI : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hPF : EqOn P F (Ioo a b) := by
    intro x hx
    have he := hL.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨m, hmI⟩
    have hmP : P m = F m := by simp [P, intervalH1Extension, m]
    dsimp only [L] at he
    rw [hmP, sub_self] at he
    exact (sub_eq_zero.mp he).symm
  have hPc : ContinuousOn P (Icc a b) := by
    have hu : IntervalIntegrable D volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 hi
    have hmU : m ∈ uIcc a b := by simpa only [uIcc_of_le hab.le] using hm
    have hc := intervalIntegral.continuousOn_primitive_interval' hu hmU
    exact continuousOn_const.add (by simpa only [uIcc_of_le hab.le] using hc)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc
  have hPL : MemLp P 2 (volume.restrict (Ioo a b)) :=
    MemLp.of_bound ((hPc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) M
      ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ hM x (Ioo_subset_Icc_self hx))
  have hF : MemLp F 2 (volume.restrict (Ioo a b)) :=
    hPL.ae_eq ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ hPF hx)
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq hab hD hFTC
  exact ⟨hF, hD, hac, (ae_restrict_iff' measurableSet_Ioo).1 hder⟩

/-- Local interval H¹ data with the same representative and derivative glue
without jumps, provided the two global L² norms are finite. -/
theorem hasIntervalH1_of_local {a b : ℝ} {F D : ℝ → ℂ} (hab : a < b)
    (hF : MemLp F 2 (volume.restrict (Ioo a b)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b)))
    (hloc : ∀ x ∈ Ioo a b, ∃ c d : ℝ,
      a ≤ c ∧ d ≤ b ∧ x ∈ Ioo c d ∧ HasIntervalH1 c d F D) :
    HasIntervalH1 a b F D := by
  have h := hasIntervalH1_of_local_derivative hab hD hloc
  exact ⟨hF, h.memLp_derivative, h.locally_absolutelyContinuous, h.hasDerivAt_ae⟩

/-- Finite reciprocal-distance L² energy forces the canonical left trace to vanish. -/
theorem HasIntervalH1.trace_zero_of_div_memLp {b : ℝ} {F D : ℝ → ℂ}
    (hb : 0 < b) (hF : HasIntervalH1 0 b F D)
    (hq : MemLp (fun x ↦ F x / (x : ℂ)) 2 (volume.restrict (Ioo 0 b))) :
    intervalH1Extension 0 b F D 0 = 0 := by
  let G := intervalH1Extension 0 b F D
  by_contra hne
  let m := ‖G 0‖ / 2
  have hm : 0 < m := half_pos (norm_pos_iff.2 hne)
  have hc := (hF.continuousOn_extension hb 0 ⟨le_rfl, hb.le⟩).norm
  have hn : ∀ᶠ x in 𝓝[Icc 0 b] 0, m < ‖G x‖ :=
    hc.eventually (lt_mem_nhds (by dsimp [m]; linarith [norm_pos_iff.2 hne]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hn
  let δ := min ε b / 2
  have hδ : 0 < δ := half_pos (lt_min hε hb)
  have hδε : δ < ε := by have := min_le_left ε b; dsimp [δ]; linarith
  have hδb : δ < b := by have := min_le_right ε b; dsimp [δ]; linarith
  have hsub : Ioc 0 δ ⊆ Ioo 0 b := fun x hx ↦ ⟨hx.1, hx.2.trans_lt hδb⟩
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc 0 δ)),
      ‖x⁻¹‖ ≤ m⁻¹ * ‖F x / (x : ℂ)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hdist : x ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
      exact hx.2.trans_lt hδε
    have hlow : m ≤ ‖F x‖ := by
      have := hball ⟨hdist, Ioo_subset_Icc_self (hsub hx)⟩
      change m < ‖intervalH1Extension 0 b F D x‖ at this
      rw [hF.extension_eq hb (hsub hx)] at this
      exact this.le
    have hdiv : m * x⁻¹ ≤ ‖F x / (x : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hlow (inv_nonneg.2 hx.1.le)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx.1]
    calc x⁻¹ = m⁻¹ * (m * x⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
         _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.2 hm.le)
  have hqi : IntegrableOn (fun x ↦ F x / (x : ℂ)) (Ioo 0 b) :=
    hq.integrable (by norm_num)
  have hi : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 0 δ) :=
    ((hqi.mono_set hsub).norm.const_mul m⁻¹).mono'
      (by fun_prop) hbound
  have hbad := intervalIntegrable_inv_iff.1
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).2 hi)
  exact hbad.elim (fun h ↦ hδ.ne' h.symm)
    (fun h ↦ h (by rw [uIcc_of_le hδ.le]; exact ⟨le_rfl, hδ.le⟩))

end NoEmbeddedEigenvalues
