import NoEmbeddedEigenvalues.WeightedFrame
import NoEmbeddedEigenvalues.SaddleTransportWeights
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Weighted inverse-frame candidates on the base quarter

Blueprint: `def:quarter-inverse-frame`, `lem:quarter-inverse-frame-algebra`,
`lem:quarter-inverse-frame-estimate`.

The inverse rows of the orbit Jacobian (whose determinant is two) are
(-sin x/2, -sin y/2) and (-J₂/2, J₁/2), where J is the level variation.
These coefficients construct square-integrable weighted Cartesian candidates.
Identifying them as the specified spatial weak gradient is a separate step.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Level row of the inverse orbit Jacobian. -/
def quarterLevelDual (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  -(Real.sin (if j = 0 then (dipoleOrbit q.1 q.2).1 else (dipoleOrbit q.1 q.2).2) : ℂ) / 2

/-- Time row of the inverse orbit Jacobian, written through the level variation. -/
def quarterTimeDual (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  if j = 0 then -((deriv (fun h ↦ dipoleOrbit h q.2) q.1).2 : ℂ) / 2
  else ((deriv (fun h ↦ dipoleOrbit h q.2) q.1).1 : ℂ) / 2

/-- Cartesian candidate reconstructed from the two coordinate derivatives. -/
def quarterInverseGradient (H T : ℝ × ℝ → ℂ) (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  quarterLevelDual j q * H q + quarterTimeDual j q * T q

theorem measurable_quarterLevelDual (j : Fin 2) : Measurable (quarterLevelDual j) := by
  have hm := continuous_dipoleOrbit.measurable
  unfold quarterLevelDual
  split_ifs <;> fun_prop

theorem measurable_quarterTimeDual (j : Fin 2) : Measurable (quarterTimeDual j) := by
  have hm : Measurable (fun q : ℝ × ℝ ↦ deriv (fun h ↦ dipoleOrbit h q.2) q.1) := by
    have hc : Continuous (Function.uncurry (fun t h : ℝ ↦ dipoleOrbit h t)) := by
      change Continuous ((fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) ∘ Prod.swap)
      exact continuous_dipoleOrbit.comp continuous_swap
    have h := measurable_deriv_with_param (f := fun t h : ℝ ↦ dipoleOrbit h t) hc
    exact h.comp measurable_swap
  unfold quarterTimeDual
  split_ifs <;> fun_prop

/-- The normalized level-row coefficient is bounded even at totalized saddles. -/
theorem norm_quarterLevelDual_div_le (j : Fin 2) (q : ℝ × ℝ) :
    ‖quarterLevelDual j q / (saddleDist (dipoleOrbit q.1 q.2) : ℂ)‖ ≤ 1 := by
  let r := saddleDist (dipoleOrbit q.1 q.2)
  have hr : 0 ≤ r := Metric.infDist_nonneg
  have ha : ‖quarterLevelDual j q‖ ≤ r := by
    have hs := abs_sin_axis_le_saddleDist (dipoleOrbit q.1 q.2) j
    simp only [quarterLevelDual, norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_two]
    change |Real.sin (if j = 0 then (dipoleOrbit q.1 q.2).1
      else (dipoleOrbit q.1 q.2).2)| / 2 ≤ r
    linarith
  change ‖quarterLevelDual j q / (r : ℂ)‖ ≤ 1
  by_cases hz : r = 0
  · simp [hz]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (div_le_iff₀ (lt_of_le_of_ne hr (Ne.symm hz))).2 (by simpa using ha)

/-- The time row has at most the norm of the level variation. -/
theorem norm_quarterTimeDual_le (j : Fin 2) (q : ℝ × ℝ) :
    ‖quarterTimeDual j q‖ ≤ ‖deriv (fun h ↦ dipoleOrbit h q.2) q.1‖ := by
  have h₀ := norm_fst_le (deriv (fun h ↦ dipoleOrbit h q.2) q.1)
  have h₁ := norm_snd_le (deriv (fun h ↦ dipoleOrbit h q.2) q.1)
  unfold quarterTimeDual
  split_ifs <;>
    simp only [norm_div, norm_neg, Complex.norm_real, Complex.norm_two] <;>
    nlinarith [norm_nonneg (deriv (fun h ↦ dipoleOrbit h q.2) q.1)]

/-- The strong quarter weights give genuine L² bounds for the weighted inverse
frame candidates. This is an estimate, not yet a weak-derivative identification. -/
theorem quarterInverseGradient_memLp : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ b : ℝ, b ≤ δ → ∀ H T : ℝ × ℝ → ℂ,
      MemLp H 2 (volume.restrict (quarterOrbitStrip b)) →
      MemLp (fun q ↦ T q / (saddleDist (dipoleOrbit q.1 q.2) ^ 2 : ℂ)) 2
        (volume.restrict (quarterOrbitStrip b)) →
      ∀ j : Fin 2, MemLp (fun q ↦ quarterInverseGradient H T j q /
        (saddleDist (dipoleOrbit q.1 q.2) : ℂ)) 2
          (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨C, δ, hδ, hδ1, hJ⟩ := deriv_dipoleOrbit_level_le_saddleDist
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro b hb H T hH hT j
  have hd : Measurable (fun q : ℝ × ℝ ↦ saddleDist (dipoleOrbit q.1 q.2)) :=
    ((Metric.continuous_infDist_pt saddleSet).comp continuous_dipoleOrbit).measurable
  apply memLp_weighted_frame
    ((measurable_quarterLevelDual j).div hd.complex_ofReal).aestronglyMeasurable
    ((measurable_quarterTimeDual j).mul hd.complex_ofReal).aestronglyMeasurable
    (A := 1) (B := |C|) _ _ hH hT
  · exact Eventually.of_forall fun q ↦ norm_quarterLevelDual_div_le j q
  · filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    have hqδ : q.1 ∈ Ioo 0 δ := ⟨hq.1, hq.2.1.trans_le hb⟩
    have ht : |q.2| ≤ eighthPeriod q.1 := (abs_le.2 ⟨hq.2.2.1.le, hq.2.2.2.le⟩)
    let r := saddleDist (dipoleOrbit q.1 q.2)
    have hr : 0 ≤ r := Metric.infDist_nonneg
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    by_cases hz : r = 0
    · change ‖quarterTimeDual j q‖ * r ≤ |C|
      simp [hz]
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      calc
        _ ≤ ‖deriv (fun h ↦ dipoleOrbit h q.2) q.1‖ * r :=
          mul_le_mul_of_nonneg_right (norm_quarterTimeDual_le j q) hr
        _ ≤ (C / r) * r := mul_le_mul_of_nonneg_right (hJ q.1 hqδ q.2 ht).1 hr
        _ = C := div_mul_cancel₀ C hz
        _ ≤ |C| := le_abs_self C

/-- Conservation of the stream level fixes the normal component of the level
variation, with the factor two from Ψ = 2h. -/
theorem quarter_level_variation_normal {h t : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    Real.sin (dipoleOrbit h t).1 * (deriv (fun s ↦ dipoleOrbit s t) h).1 +
      Real.sin (dipoleOrbit h t).2 * (deriv (fun s ↦ dipoleOrbit s t) h).2 = -2 := by
  have hd := ((contDiffAt_orbitMap (t := t) hh).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h t))
  have hJ := hc.differentiableAt.hasDerivAt
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt h hJ
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt h hJ
  have hl := (hx.cos.add hy.cos).div_const 2
  have he : (fun s ↦ (Real.cos (dipoleOrbit s t).1 +
      Real.cos (dipoleOrbit s t).2) / 2) =ᶠ[nhds h] id := by
    filter_upwards [Ioo_mem_nhds hh.1 hh.2] with s hs
    exact levelCoord_dipoleOrbit hs.1 hs.2 t
  have hn := (hl.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id h)
  change (-Real.sin (dipoleOrbit h t).1 * (deriv (fun s ↦ dipoleOrbit s t) h).1 +
    -Real.sin (dipoleOrbit h t).2 * (deriv (fun s ↦ dipoleOrbit s t) h).2) / 2 = 1 at hn
  linarith only [hn]

/-- Exact inverse-frame algebra once both coordinate rows of a spatial gradient
have been identified. The row hypotheses are separate analytic obligations. -/
theorem quarterInverseGradient_of_coordinate_rows {H T X Y : ℝ × ℝ → ℂ}
    {q : ℝ × ℝ} (hq : q.1 ∈ Ioo (0 : ℝ) 1)
    (hH : H q = ((deriv (fun h ↦ dipoleOrbit h q.2) q.1).1 : ℂ) * X q +
      ((deriv (fun h ↦ dipoleOrbit h q.2) q.1).2 : ℂ) * Y q)
    (hT : T q = (Real.sin (dipoleOrbit q.1 q.2).2 : ℂ) * X q -
      (Real.sin (dipoleOrbit q.1 q.2).1 : ℂ) * Y q) (j : Fin 2) :
    quarterInverseGradient H T j q = if j = 0 then X q else Y q := by
  have hn : (Real.sin (dipoleOrbit q.1 q.2).1 : ℂ) *
        ((deriv (fun h ↦ dipoleOrbit h q.2) q.1).1 : ℂ) +
      (Real.sin (dipoleOrbit q.1 q.2).2 : ℂ) *
        ((deriv (fun h ↦ dipoleOrbit h q.2) q.1).2 : ℂ) = -2 := by
    exact_mod_cast quarter_level_variation_normal (t := q.2) hq
  unfold quarterInverseGradient quarterLevelDual quarterTimeDual
  rw [hH, hT]
  split_ifs with hj
  · linear_combination -(X q) / 2 * hn
  · linear_combination -(Y q) / 2 * hn

end NoEmbeddedEigenvalues
