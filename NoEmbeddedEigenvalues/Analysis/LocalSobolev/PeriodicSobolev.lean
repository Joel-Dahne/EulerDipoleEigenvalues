module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalToGlobal
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.AnglePeriodization

/-!
# Sobolev reconstruction of periodic lifts

Blueprint: `lem:periodic-sobolev-reconstruction`.

A tensor product of the rescaled angular partition gives one compact cutoff whose
lattice translates sum to one. Cutoff localization followed by compact periodization
therefore reconstructs any periodic Hᵏ_loc function, without an injective torus chart.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff Real

/-- A compact smooth cutoff with periodized value one. -/
def torusPartition (p : ℝ × ℝ) : ℂ :=
  (anglePartition (0, p.1 / (2 * π)) : ℂ) *
    (anglePartition (0, p.2 / (2 * π)) : ℂ)

theorem contDiff_torusPartition : ContDiff ℝ ∞ torusPartition := by
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_anglePartition.comp
    (contDiff_const.prodMk (contDiff_fst.div_const _)))).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_anglePartition.comp
      (contDiff_const.prodMk (contDiff_snd.div_const _))))

theorem torusPartition_support_bound {p : ℝ × ℝ} (hp : torusPartition p ≠ 0) :
    ‖p‖ ≤ 2 * π := by
  have hx := anglePartition_support_le (0, p.1 / (2 * π))
    (Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul hp))
  have hy := anglePartition_support_le (0, p.2 / (2 * π))
    (Complex.ofReal_ne_zero.mp (right_ne_zero_of_mul hp))
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpi : 0 < 2 * π := by positivity
  simp only [abs_div, abs_of_pos hpi] at hx hy
  exact max_le (by simpa using (div_le_iff₀ hpi).mp hx)
    (by simpa using (div_le_iff₀ hpi).mp hy)

theorem hasCompactSupport_torusPartition : HasCompactSupport torusPartition := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (2 * π))
  intro p hp
  by_contra hn
  exact hp (by simpa using torusPartition_support_bound hn)

theorem liftPeriodize_torusPartition (p : ℝ × ℝ) : liftPeriodize torusPartition p = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (2 * π + ‖p‖) (1 + max |p.1 / (2 * π)| |p.2 / (2 * π)|))
  have hnorm : 2 * π + ‖p‖ ≤ N := (le_max_left _ _).trans hN.le
  have hmax := (le_max_right _ _).trans hN.le
  have hax : 1 + |p.1 / (2 * π)| ≤ N := by
    linarith [le_max_left |p.1 / (2 * π)| |p.2 / (2 * π)|]
  have hay : 1 + |p.2 / (2 * π)| ≤ N := by
    linarith [le_max_right |p.1 / (2 * π)| |p.2 / (2 * π)|]
  have hsum (x : ℝ) (hx : 1 + |x| ≤ N) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) N, (anglePartition (0, x + m) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum,
      ← periodizeSnd_eq_sum (q := (0, x)) anglePartition_support_le hx (le_refl |x|),
      periodize_anglePartition, Complex.ofReal_one]
  have hshift (x : ℝ) (m : ℤ) : (x + m * (2 * π)) / (2 * π) = x / (2 * π) + m := by
    have hpi : (2 * π) ≠ 0 := by positivity
    field_simp
  rw [liftPeriodize_eq_sum (fun q hq ↦ torusPartition_support_bound hq) hnorm le_rfl]
  simp only [shiftBox, Finset.sum_product, torusPartition, liftShift, hshift]
  simp_rw [← Finset.mul_sum, hsum _ hay, mul_one]
  exact hsum _ hax

/-- Any periodic Hᵏ_loc function on the plane is the lift of torus Hᵏ data. -/
theorem exists_memSobolev_of_periodic_lift {k : ℕ} {F : ℝ × ℝ → ℂ}
    (hper : IsPeriodicLift F) (hF : MemSobolevLocOn k univ F) :
    ∃ g : L2, MemSobolev k g ∧ liftL2 g =ᵐ[volume] F := by
  let G : ℝ × ℝ → ℂ := fun p ↦ torusPartition p * F p
  have hG : MemSobolevOn k univ G := hF.cutoff k isOpen_univ
    contDiff_torusPartition hasCompactSupport_torusPartition (subset_univ _)
  have hzero : ∀ p ∉ tsupport torusPartition, G p = 0 := fun p hp ↦ by
    simp [G, image_eq_zero_of_notMem_tsupport hp]
  refine ⟨compactPeriodize G,
    memSobolev_compactPeriodize k hasCompactSupport_torusPartition hzero hG, ?_⟩
  have hLp : MemLp G 2 volume := by simpa using hG.memLp
  filter_upwards [liftL2_compactPeriodize hasCompactSupport_torusPartition hzero hLp] with p hp
  rw [hp]
  have heq (n : ℤ × ℤ) : F (liftShift n p) = F p :=
    hper.eq_of_torusProj_eq (torusProj_liftShift n p)
  simp only [liftPeriodize, G, heq]
  rw [← finsum_mul, ← liftPeriodize, liftPeriodize_torusPartition, one_mul]

/-- Local integer-order Sobolev regularity of an L² lift implies torus regularity. -/
theorem memSobolev_of_liftL2_loc {k : ℕ} {g : L2}
    (hg : MemSobolevLocOn k univ (liftL2 g)) : MemSobolev k g := by
  obtain ⟨f, hf, heq⟩ := exists_memSobolev_of_periodic_lift (isPeriodicLift_liftL2 g) hg
  have hfg : f = g := by
    rw [← boxPeriodize_liftL2 f, ← boxPeriodize_liftL2 g]
    exact boxPeriodize_congr (ae_restrict_of_ae heq)
  simpa only [hfg] using hf

end NoEmbeddedEigenvalues
