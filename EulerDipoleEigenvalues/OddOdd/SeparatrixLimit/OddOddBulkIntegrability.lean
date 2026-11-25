module

public import EulerDipoleEigenvalues.OddOdd.Picone.OddOddForms

/-!
# Forcing and weighted mass integrability for the odd–odd bulk

The weighted forcing estimate is independent of the quotient, its parity and
the equation. The torus-vorticity interface is a specialization after restricting
the weighted L² hypothesis to the cell. Ordinary stream-level exhaustion
passes any integrable bulk density to the full cell integral. Diagonal coordinates
factor the squared dipole integral into two cosine-square moments.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology Real

private theorem saddleDist_le_edges {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    saddleDist p ≤ π - |(diagCoord p).1| - |(diagCoord p).2| := by
  set a := (diagCoord p).1
  set b := (diagCoord p).2
  have hx : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
  have hy : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
  obtain ⟨haL, haU⟩ := abs_lt.mp hp.1
  obtain ⟨hbL, hbU⟩ := abs_lt.mp hp.2
  change saddleDist p ≤ π - |a| - |b|
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · apply (Metric.infDist_le_dist_of_mem
      (show (π, 0) ∈ saddleSet from ⟨1, 0, by decide, by simp⟩)).trans
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hx, hy,
      abs_of_nonneg ha, abs_of_nonneg hb]
    apply max_le <;> rw [abs_le] <;> constructor <;> dsimp [a, b] at * <;> linarith
  · apply (Metric.infDist_le_dist_of_mem
      (show (0, π) ∈ saddleSet from ⟨0, 1, by decide, by simp⟩)).trans
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hx, hy,
      abs_of_nonneg ha, abs_of_nonpos hb]
    apply max_le <;> rw [abs_le] <;> constructor <;> dsimp [a, b] at * <;> linarith
  · apply (Metric.infDist_le_dist_of_mem
      (show (0, -π) ∈ saddleSet from ⟨0, -1, by decide, by simp⟩)).trans
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hx, hy,
      abs_of_nonpos ha, abs_of_nonneg hb]
    apply max_le <;> rw [abs_le] <;> constructor <;> dsimp [a, b] at * <;> linarith
  · apply (Metric.infDist_le_dist_of_mem
      (show (-π, 0) ∈ saddleSet from ⟨-1, 0, by decide, by simp⟩)).trans
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hx, hy,
      abs_of_nonpos ha, abs_of_nonpos hb]
    apply max_le <;> rw [abs_le] <;> constructor <;> dsimp [a, b] at * <;> linarith

/-- Distance to a cell corner is controlled by the two diagonal cosines. -/
theorem saddleDist_le_diag_cos {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    saddleDist p ≤ π / 2 * (cos (diagCoord p).1 + cos (diagCoord p).2) := by
  have hedge {t : ℝ} (ht : |t| < π / 2) : π / 2 - |t| ≤ π / 2 * cos t := by
    have h := one_sub_mul_le_cos (abs_nonneg t) ht.le
    rw [cos_abs] at h
    calc π / 2 - |t| = π / 2 * (1 - 2 / π * |t|) := by
           field_simp
         _ ≤ π / 2 * cos t := mul_le_mul_of_nonneg_left h pi_div_two_pos.le
  have h := saddleDist_le_edges hp
  linarith [hedge hp.1, hedge hp.2]

private theorem ddF_factor (p : ℝ × ℝ) :
    ddF p = (dipoleLift p ^ 2 + 2 * dipoleLift p + 4) / 3 * normalCoeff p := by
  unfold ddF normalCoeff
  ring

private theorem ddF_bounds {p : ℝ × ℝ} (h0 : 0 < dipoleLift p)
    (h2 : dipoleLift p < 2) :
    0 ≤ ddF p ∧ ddF p * gradSq dipoleLift p ≤ 16 ∧
      (1 ≤ dipoleLift p → ddF p ≤ 4) := by
  set s := dipoleLift p
  have hg := gradSq_dipoleLift_pos h0 h2
  have hn := normalCoeff_nonneg h0 h2
  have hβ0 : 0 ≤ (s ^ 2 + 2 * s + 4) / 3 := by positivity
  have hβ : (s ^ 2 + 2 * s + 4) / 3 ≤ 4 := by
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr h2.le)]
  have hδ : (cos p.1 - cos p.2) ^ 2 ≤ 4 := by
    have h := (abs_sub (cos p.1) (cos p.2)).trans
      (add_le_add (abs_cos_le_one _) (abs_cos_le_one _))
    simpa only [sq_abs, show (1 + 1 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) h 2
  refine ⟨?_, ?_, ?_⟩
  · rw [ddF_factor]
    exact mul_nonneg hβ0 hn
  · calc ddF p * gradSq dipoleLift p =
          (s ^ 2 + 2 * s + 4) / 3 * normalC p * (cos p.1 - cos p.2) ^ 2 := by
          unfold ddF normalC s
          field_simp
          ring
         _ ≤ 4 * 1 * 4 := by
           gcongr
           · exact (normalC_pos_le_one h0 h2).1.le
           · exact (normalC_pos_le_one h0 h2).2
         _ = 16 := by norm_num
  · intro hs
    have hn1 : normalCoeff p ≤ 1 := (normalCoeff_le h0 h2).trans
      ((div_le_one h0).mpr (by dsimp [s] at hs; linarith))
    rw [ddF_factor]
    calc (s ^ 2 + 2 * s + 4) / 3 * normalCoeff p ≤ 4 * 1 :=
          mul_le_mul hβ hn1 hn (by norm_num)
         _ = 4 := by norm_num

private theorem saddleDist_sq_le_gradSq {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hs : dipoleLift p ≤ 1) :
    saddleDist p ^ 2 ≤ π ^ 2 / 2 * gradSq dipoleLift p := by
  set a := (diagCoord p).1
  set b := (diagCoord p).2
  set u := cos a
  set v := cos b
  have hx : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
  have hy : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
  have hsr : dipoleLift p = 2 * u * v := dipoleLift_eq_diag p
  have hr : gradSq dipoleLift p = 2 * (u ^ 2 + v ^ 2) - (2 * u * v) ^ 2 := by
    dsimp only [u, v]
    simp only [gradSq_dipoleLift]
    rw [hx, hy, sin_add, sin_sub]
    linear_combination (2 * cos b ^ 2) * sin_sq_add_cos_sq a +
      (2 * cos a ^ 2) * sin_sq_add_cos_sq b
  have hs0 : 0 < dipoleLift p := by
    simpa only [positiveCell, Set.mem_ofPred_eq, Ψ_torusProj] using
      torusProj_mem_positiveCell hp
  have hsum : u ^ 2 + v ^ 2 ≤ gradSq dipoleLift p := by
    have hss := mul_le_mul_of_nonneg_left hs hs0.le
    rw [hsr] at hss
    nlinarith [sq_nonneg (u - v)]
  calc saddleDist p ^ 2 ≤ (π / 2 * (u + v)) ^ 2 :=
         pow_le_pow_left₀ Metric.infDist_nonneg (saddleDist_le_diag_cos hp) 2
       _ = π ^ 2 / 4 * (u + v) ^ 2 := by ring
       _ ≤ π ^ 2 / 4 * (2 * (u ^ 2 + v ^ 2)) :=
         mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (u - v)]) (by positivity)
       _ ≤ π ^ 2 / 4 * (2 * gradSq dipoleLift p) := by gcongr
       _ = π ^ 2 / 2 * gradSq dipoleLift p := by ring

/-- The inverse-square saddle singularity is removed by multiplying by d². -/
theorem ddF_mul_saddleDist_sq_bound {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    0 ≤ ddF p ∧ ddF p * saddleDist p ^ 2 ≤ 16 * π ^ 2 := by
  have hs0 : 0 < dipoleLift p := by
    simpa only [positiveCell, Set.mem_ofPred_eq, Ψ_torusProj] using
      torusProj_mem_positiveCell hp
  have hs2 : dipoleLift p ≤ 2 := by
    simpa only [Ψ_torusProj] using Ψ_le_two (torusProj p)
  obtain hs2 | hs2 := hs2.lt_or_eq
  · obtain ⟨hF0, hFr, hF⟩ := ddF_bounds hs0 hs2
    refine ⟨hF0, ?_⟩
    by_cases hs : dipoleLift p ≤ 1
    · calc ddF p * saddleDist p ^ 2 ≤
            ddF p * (π ^ 2 / 2 * gradSq dipoleLift p) :=
              mul_le_mul_of_nonneg_left (saddleDist_sq_le_gradSq hp hs) hF0
           _ = π ^ 2 / 2 * (ddF p * gradSq dipoleLift p) := by ring
           _ ≤ π ^ 2 / 2 * 16 := mul_le_mul_of_nonneg_left hFr (by positivity)
           _ ≤ 16 * π ^ 2 := by nlinarith [sq_nonneg π]
    · have hd : saddleDist p ≤ π := (saddleDist_le_edges hp).trans
        (by linarith [abs_nonneg (diagCoord p).1, abs_nonneg (diagCoord p).2])
      have hd2 := pow_le_pow_left₀ Metric.infDist_nonneg hd 2
      calc ddF p * saddleDist p ^ 2 ≤ 4 * π ^ 2 :=
             mul_le_mul (hF (le_of_not_ge hs)) hd2 (sq_nonneg _) (by norm_num)
           _ ≤ 16 * π ^ 2 := by nlinarith [sq_nonneg π]
  · have hz : ddF p = 0 := by norm_num [ddF, hs2]
    rw [hz]
    constructor
    · exact le_rfl
    · nlinarith [sq_nonneg π]

/-- A supplied forcing with e/d ∈ L² has absolutely integrable weighted density.
No equation, periodicity or separate unweighted L² hypothesis is required. -/
theorem dd_forcing_density_integrable {e : ℝ × ℝ → ℂ}
    (he : MemLp (fun p ↦ e p / (saddleDist p : ℂ)) 2
      (volume.restrict cellSquare)) :
    IntegrableOn (fun p ↦ ddF p * ‖e p‖ ^ 2) cellSquare := by
  have hcell : MeasurableSet cellSquare := by
    unfold cellSquare diagCoord
    measurability
  have mF : Measurable ddF := by
    change Measurable (fun p ↦ ddF p)
    simp only [ddF, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have md : Continuous saddleDist := Metric.continuous_infDist_pt saddleSet
  have hm : AEStronglyMeasurable (fun p ↦ ddF p * saddleDist p ^ 2)
      (volume.restrict cellSquare) := (mF.mul (md.measurable.pow_const 2)).aestronglyMeasurable
  have hb : ∀ᵐ p ∂volume.restrict cellSquare,
      ‖ddF p * saddleDist p ^ 2‖ ≤ 16 * π ^ 2 := by
    filter_upwards [ae_restrict_mem hcell] with p hp
    obtain ⟨hF, hbound⟩ := ddF_mul_saddleDist_sq_bound hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF (sq_nonneg _))] using hbound
  have hi := (he.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).bdd_mul hm hb
  apply hi.congr
  filter_upwards [ae_restrict_mem hcell] with p hp
  have hd : 0 < saddleDist p := (cos_pos_of_mem_Ioo (abs_lt.mp hp.1)).trans_le
    (cos_diag_fst_le_saddleDist p)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, div_pow]
  field_simp

/-- Absolute integrability from `ν/d ∈ L²`, independently of the eigenvalue equation. -/
theorem dd_vorticityDensity_integrable (ν : L2)
    (hν : MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood)) :
    IntegrableOn (ddVorticityDensity ν) cellSquare := by
  exact dd_forcing_density_integrable (hν.mono_measure
    (Measure.restrict_mono (fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)) le_rfl))

/-- The integral of the squared dipole over the lifted positive cell. -/
theorem integral_cellSquare_ddWeight :
    (∫ p in cellSquare, ddWeight p) = 2 * Real.pi ^ 2 := by
  have hcos : (∫ x in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos x ^ 2) = Real.pi / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_cos_sq]
    simp only [neg_div, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, sub_zero]
    ring
  rw [← integral_indicator isOpen_cellSquare.measurableSet,
    integral_eq_two_smul_integral_diagInv]
  have heq : (fun q ↦ cellSquare.indicator ddWeight (diagInv q)) =
      (Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2)).indicator
        (fun q ↦ 4 * (Real.cos q.1 ^ 2 * Real.cos q.2 ^ 2)) := by
    funext q
    have hq : diagInv q ∈ cellSquare ↔
        q ∈ Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2) := by
      simp only [cellSquare, mem_ofPred_eq, diagCoord_diagInv, abs_lt, mem_prod,
        mem_Ioo, neg_div]
    by_cases hp : diagInv q ∈ cellSquare
    · rw [indicator_of_mem hp, indicator_of_mem (hq.mp hp), ddWeight,
        dipoleLift_eq_diag, diagCoord_diagInv]
      ring
    · rw [indicator_of_notMem hp, indicator_of_notMem (mt hq.mpr hp)]
  rw [heq, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    integral_const_mul, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun x : ℝ ↦ Real.cos x ^ 2) (fun x : ℝ ↦ Real.cos x ^ 2), hcos]
  simp only [smul_eq_mul]
  ring

/-- Integrable functions converge under exhaustion by the actual stream levels. This is
    dominated convergence and does not assume any sign of the integrand. -/
theorem tendsto_ddTruncatedCell_integral {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f cellSquare) :
    Tendsto (fun ε ↦ ∫ p in ddTruncatedCell ε, f p) (𝓝[>] 0)
      (𝓝 (∫ p in cellSquare, f p)) := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hm (ε : ℝ) : MeasurableSet {p : ℝ × ℝ | ε < dipoleLift p} :=
    measurableSet_lt measurable_const (by unfold dipoleLift; fun_prop)
  have hrep (ε : ℝ) : (∫ p in ddTruncatedCell ε, f p) =
      ∫ p in cellSquare, {p | ε < dipoleLift p}.indicator f p := by
    rw [setIntegral_indicator (hm ε)]
    rfl
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict cellSquare)
    (F := fun ε ↦ {p | ε < dipoleLift p}.indicator f) (f := f) (fun p ↦ ‖f p‖)
    (Eventually.of_forall fun ε ↦ hf.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ {p | ε < dipoleLift p}
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp, norm_zero]
        exact norm_nonneg _)
    hf.norm (by
      filter_upwards [ae_restrict_mem hcell] with p hp
      have hs : 0 < dipoleLift p := by
        simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < dipoleLift p :=
        nhdsWithin_le_nhds (Iio_mem_nhds hs)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with ε hε
      rw [indicator_of_mem (show p ∈ {p | ε < dipoleLift p} from hε)])
  exact h.congr' (Eventually.of_forall fun ε ↦ (hrep ε).symm)

end EulerDipoleEigenvalues
