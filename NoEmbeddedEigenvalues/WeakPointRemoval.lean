import NoEmbeddedEigenvalues.SobolevLocal
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Transverse cutoffs for specified weak partial identities

Blueprint: `lem:weak-transverse-line-removal`, `lem:weak-point-removal`.

A cutoff in the transverse coordinate has zero partial derivative in the tested
coordinate. Its exceptional limiting line is null. Thus local integrability of
the function and its specified derivative suffices; no radial tail estimate is
needed for this distributional extension. The same argument removes a line of
constant transverse coordinate from the tangential weak identity; it does not
remove a normal jump without a trace condition.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A line parallel to the tested coordinate direction cannot support a defect
in that specified partial derivative. No normal trace condition is needed. -/
theorem HasWeakPartialOn.remove_transverse_line {U : Set (ℝ × ℝ)} {t : ℝ} {j : Fin 2}
    {F D : ℝ × ℝ → ℂ}
    (h : HasWeakPartialOn (U \ {p | (if j = 0 then p.2 else p.1) = t}) j F D)
    (hF : LocallyIntegrableOn F U) (hD : LocallyIntegrableOn D U) :
    HasWeakPartialOn U j F D := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let y (p : ℝ × ℝ) : ℝ := if j = 0 then p.2 else p.1
  let θ (n : ℕ) (p : ℝ × ℝ) : ℂ :=
    1 - (b (((n : ℝ) + 1) * (y p - t)) : ℂ)
  have hθ (n : ℕ) : ContDiff ℝ ∞ (θ n) := by
    have hy : ContDiff ℝ ∞ y := by dsimp [y]; split_ifs <;> fun_prop
    exact contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
      (b.contDiff.comp (contDiff_const.mul (hy.sub contDiff_const))))
  have hθj (n : ℕ) : coordPartial j (θ n) = 0 := by
    funext p
    fin_cases j <;> simp [coordPartial, partialX, partialY, θ, y]
  have hθbound (n : ℕ) (p : ℝ × ℝ) : ‖θ n p‖ ≤ 1 := by
    dsimp only [θ]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr b.le_one)]
    linarith [b.nonneg (x := ((n : ℝ) + 1) * (y p - t))]
  have hyc : ∀ᵐ p : ℝ × ℝ, y p ≠ t := by
    have hx (a : ℝ) : ∀ᵐ x : ℝ, x ≠ a := by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton]
    fin_cases j
    · exact Measure.quasiMeasurePreserving_snd.ae (hx t)
    · exact Measure.quasiMeasurePreserving_fst.ae (hx t)
  have hθlim : ∀ᵐ p : ℝ × ℝ, Tendsto (fun n ↦ θ n p) atTop (𝓝 1) := by
    filter_upwards [hyc] with p hp
    have hd : 0 < |y p - t| := abs_pos.mpr (sub_ne_zero.mpr hp)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / |y p - t|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hz : b (((n : ℝ) + 1) * (y p - t)) = 0 := by
      apply b.zero_of_le_dist
      change 2 ≤ dist (((n : ℝ) + 1) * (y p - t)) 0
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (by positivity)]
      have hN' := (div_lt_iff₀ hd).1 hN
      nlinarith
    simp [θ, hz]
  refine ⟨hF, hD, fun φ hφ ↦ ?_⟩
  have hiF := integrable_mul_of_tsupport_subset hF (hφ.continuous_coordPartial j)
    (hφ.hasCompactSupport_coordPartial j)
    ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset)
  have hiD := integrable_mul_of_tsupport_subset hD hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have htest (n : ℕ) : IsTestFunctionOn (U \ {p | y p = t}) (fun p ↦ θ n p * φ p) := by
    refine ⟨(hθ n).mul hφ.contDiff, hφ.hasCompactSupport.mul_left, ?_⟩
    intro p hp
    refine ⟨hφ.tsupport_subset (tsupport_mul_subset_right (f := θ n) (g := φ) hp), ?_⟩
    intro he
    have hep : y p = t := he
    have hc : (fun p ↦ θ n p * φ p) =ᶠ[𝓝 p] 0 := by
      have hy : Continuous y := by dsimp [y]; split_ifs <;> fun_prop
      have ht : Tendsto (fun q ↦ ((n : ℝ) + 1) * (y q - t)) (𝓝 p) (𝓝 0) := by
        have hg : Continuous (fun q : ℝ × ℝ ↦ ((n : ℝ) + 1) * (y q - t)) := by
          fun_prop
        simpa only [ContinuousAt, hep, sub_self, mul_zero] using hg.continuousAt (x := p)
      filter_upwards [ht.eventually b.eventuallyEq_one] with p hp
      simp [θ, hp]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hc) hp
  have he (n : ℕ) :
      (∫ p, θ n p * (F p * coordPartial j φ p)) = -(∫ p, θ n p * (D p * φ p)) := by
    have hid := h.2.2 _ (htest n)
    have hder : coordPartial j (fun p ↦ θ n p * φ p) =
        fun p ↦ θ n p * coordPartial j φ p := by
      funext p
      rw [coordPartial_mul j ((hθ n).differentiable (by simp))
        (hφ.contDiff.differentiable (by simp)), hθj n]
      simp
    simpa only [hder, mul_assoc, mul_left_comm] using hid
  have hlim (A : ℝ × ℝ → ℂ) (hi : Integrable A) :
      Tendsto (fun n ↦ ∫ p, θ n p * A p) atTop (𝓝 (∫ p, A p)) := by
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖A p‖)
    · intro n
      exact (hθ n).continuous.aestronglyMeasurable.mul hi.aestronglyMeasurable
    · exact hi.norm
    · intro n
      exact Eventually.of_forall fun p ↦ by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hθbound n p)
    · filter_upwards [hθlim] with p hp
      simpa using hp.mul_const (A p)
  exact tendsto_nhds_unique (hlim _ hiF)
    (((hlim _ hiD).neg).congr (fun n ↦ (he n).symm))

/-- An isolated point cannot support a defect in a locally integrable coordinate
weak derivative on the plane. -/
theorem HasWeakPartialOn.remove_point {U : Set (ℝ × ℝ)} {c : ℝ × ℝ} {j : Fin 2}
    {F D : ℝ × ℝ → ℂ} (h : HasWeakPartialOn (U \ {c}) j F D)
    (hF : LocallyIntegrableOn F U) (hD : LocallyIntegrableOn D U) :
    HasWeakPartialOn U j F D := by
  apply HasWeakPartialOn.remove_transverse_line
    (t := if j = 0 then c.2 else c.1) ?_ hF hD
  apply h.mono
  rintro p ⟨hpU, hp⟩
  refine ⟨hpU, ?_⟩
  rintro rfl
  exact hp rfl

/-- Finite H¹ on a punctured plane domain extends through the isolated point.
This needs the full punctured-domain norms, not merely local H¹ away from it. -/
theorem MemSobolevOn.remove_point {U : Set (ℝ × ℝ)} {c : ℝ × ℝ}
    {F : ℝ × ℝ → ℂ} (h : MemSobolevOn 1 (U \ {c}) F) :
    MemSobolevOn 1 U F := by
  have hne : ∀ᵐ p : ℝ × ℝ, p ≠ c := by
    rw [ae_iff]
    simp [Measure.volume_eq_prod]
  have hμ : volume.restrict (U \ {c}) = volume.restrict U :=
    Measure.restrict_congr_set (hne.mono fun p hp ↦ by simp [hp])
  have hF : MemLp F 2 (volume.restrict U) := by
    simpa only [hμ] using h.1
  refine ⟨hF, fun j ↦ ?_⟩
  obtain ⟨D, hd, hD⟩ := h.2 j
  have hD' : MemLp D 2 (volume.restrict U) := by
    simpa only [hμ] using (show MemLp D 2 (volume.restrict (U \ {c})) from hD)
  exact ⟨D, hd.remove_point
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hD'.locallyIntegrable (by norm_num))), hD'⟩

end NoEmbeddedEigenvalues
