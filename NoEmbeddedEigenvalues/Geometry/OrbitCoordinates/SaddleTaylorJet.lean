module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SmoothJetBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Cartesian jets of the saddle Taylor correction

The explicit dipole and its normalized quadratic differ by order four, including
all derivatives through order three. These geometric estimates have no
vorticity or eigenfunction hypotheses.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

private theorem classicalComplexJet_axis (w : List (Fin 2)) (j : Fin 2) (g : ℝ → ℂ) :
    classicalComplexJet w (fun q ↦ g (axisCoord j q)) =
      if w.all (· == j) then (fun q ↦ iteratedDeriv w.length g (axisCoord j q)) else 0 := by
  induction w with
  | nil => simp [classicalComplexJet, iteratedDeriv_zero]
  | cons i w ih =>
    rw [classicalComplexJet, ih]
    funext q
    by_cases hw : w.all (· == j)
    all_goals
      fin_cases i <;> fin_cases j <;>
        simp_all [coordPartial, axisCoord, partialX, partialY, iteratedDeriv_succ]

private def cosineRemainder (t : ℝ) : ℝ := 1 - t ^ 2 / 2 - Real.cos t

private theorem cosineRemainder_zero_jets (b : ℂ) (k : ℕ) (hk : k < 4) :
    iteratedDeriv k (fun t ↦ b * (cosineRemainder t : ℂ)) 0 = 0 := by
  have h₁ : deriv (fun t ↦ b * (cosineRemainder t : ℂ)) =
      fun t ↦ b * ((Real.sin t - t : ℝ) : ℂ) := by
    funext t
    have h := (((((hasDerivAt_id t).pow 2).div_const 2).const_sub 1).sub
      (Real.hasDerivAt_cos t)).ofReal_comp.const_mul b
    change deriv (fun t ↦ b * ((1 - t ^ 2 / 2 - Real.cos t : ℝ) : ℂ)) t = _
    have hd := h.deriv
    simp only [id_eq, Pi.pow_apply, Pi.sub_apply] at hd
    rw [hd]
    congr 2
    norm_num
    ring
  have h₂ : deriv (fun t ↦ b * ((Real.sin t - t : ℝ) : ℂ)) =
      fun t ↦ b * ((Real.cos t - 1 : ℝ) : ℂ) := by
    funext t
    exact (((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).ofReal_comp.const_mul b).deriv
  have h₃ : deriv (fun t ↦ b * ((Real.cos t - 1 : ℝ) : ℂ)) =
      fun t ↦ b * ((-Real.sin t : ℝ) : ℂ) := by
    funext t
    exact (((Real.hasDerivAt_cos t).sub_const 1).ofReal_comp.const_mul b).deriv
  interval_cases k
  · simp [cosineRemainder]
  · rw [iteratedDeriv_one, h₁]
    simp
  · rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, h₁, h₂]
    simp
  · rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, h₁, h₂, h₃]
    simp

private theorem saddle_correction_eq_cosineRemainder {c : ℝ × ℝ} (hc : c ∈ saddleSet) (a : ℂ) :
    (fun p ↦ saddleQuadratic c a p - a * (dipoleLift p : ℂ)) =
      fun p ↦ a * (Real.cos c.1 : ℂ) * (cosineRemainder (p.1 - c.1) : ℂ) -
        a * (Real.cos c.1 : ℂ) * (cosineRemainder (p.2 - c.2) : ℂ) := by
  have hx : Real.sin c.1 = 0 := by
    obtain ⟨m, n, _, rfl⟩ := hc
    exact Real.sin_int_mul_pi m
  have hy : Real.sin c.2 = 0 := by
    obtain ⟨m, n, _, rfl⟩ := hc
    exact Real.sin_int_mul_pi n
  have hzero : dipoleLift c = 0 := by
    simpa [saddleOrthoChart] using saddle_dipole_factorization hc (0, 0)
  have hcos : Real.cos c.2 = -Real.cos c.1 := by
    simpa [dipoleLift, eq_neg_iff_add_eq_zero, add_comm] using hzero
  have he (p : ℝ × ℝ) : dipoleLift p =
      Real.cos c.1 * (Real.cos (p.1 - c.1) - Real.cos (p.2 - c.2)) := by
    unfold dipoleLift
    rw [← sub_add_cancel p.1 c.1, ← sub_add_cancel p.2 c.2, Real.cos_add, Real.cos_add]
    simp only [hx, hy, hcos, mul_zero, sub_zero]
    rw [sub_add_cancel, sub_add_cancel]
    ring
  funext p
  rw [he, saddleQuadratic]
  unfold cosineRemainder
  push_cast
  ring

/-- The smooth Cartesian Taylor correction has finite radial jet norms
(`lem:saddle-taylor-correction`). -/
theorem saddle_taylor_correction {c : ℝ × ℝ} (hc : c ∈ saddleSet) (a : ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ E : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 3 (localDisk c ρ)
        (fun p ↦ saddleQuadratic c a p - a * (dipoleLift p : ℂ)) E ∧
      ∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c E := by
  rw [saddle_correction_eq_cosineRemainder hc a]
  let b := a * (Real.cos c.1 : ℂ)
  let g : ℝ → ℂ := fun t ↦ b * (cosineRemainder t : ℂ)
  let F : ℝ × ℝ → ℂ := fun p ↦ g (p.1 - c.1)
  let G : ℝ × ℝ → ℂ := fun p ↦ g (p.2 - c.2)
  change ∃ ρ : ℝ, 0 < ρ ∧ ∃ E, HasWeakJetOn 3 (localDisk c ρ) (fun p ↦ F p - G p) E ∧ _
  have hg : ContDiff ℝ ∞ g := by
    have hr : ContDiff ℝ ∞ cosineRemainder := by unfold cosineRemainder; fun_prop
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hr)
  have hF : ContDiff ℝ ∞ F := hg.comp (contDiff_fst.sub contDiff_const)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_snd.sub contDiff_const)
  have hz (w : List (Fin 2)) (hw : w.length < 4) (j : Fin 2) :
      classicalComplexJet w (fun p ↦ g (axisCoord j p - axisCoord j c)) c = 0 := by
    rw [classicalComplexJet_axis w j (fun t ↦ g (t - axisCoord j c))]
    split_ifs
    · simp only [iteratedDeriv_comp_sub_const, sub_self]
      exact cosineRemainder_zero_jets b w.length hw
    · rfl
  have hflat (w : List (Fin 2)) (hw : w.length < 4) :
      classicalComplexJet w (fun p ↦ F p - G p) c = 0 := by
    rw [classicalComplexJet_sub_on isOpen_univ hF.contDiffOn hG.contDiffOn w (mem_univ c)]
    change classicalComplexJet w F c - classicalComplexJet w G c = 0
    rw [show classicalComplexJet w F c = 0 from hz w hw 0,
      show classicalComplexJet w G c = 0 from hz w hw 1, sub_self]
  obtain ⟨ρ, hρ, _, hjet, hmass⟩ := exists_radial_classicalJet_flat_memLp isOpen_univ (mem_univ c)
    (hF.sub hG).contDiffOn 4 hflat
  exact ⟨ρ, hρ, _, ⟨hjet.1, fun w hw j ↦ hjet.2 w (by omega) j⟩,
    fun k hk ↦ hmass k (by omega)⟩

/-- The normalized quadratic is harmonic in Cartesian coordinates. -/
theorem saddleQuadratic_harmonic (c : ℝ × ℝ) (a : ℂ) (p : ℝ × ℝ) :
    classicalComplexJet [0, 0] (saddleQuadratic c a) p +
      classicalComplexJet [1, 1] (saddleQuadratic c a) p = 0 := by
  let b : ℂ := a * (Real.cos c.1 : ℂ) / 2
  have hx : partialX (saddleQuadratic c a) =
      fun q ↦ b * (-2 * ((q.1 - c.1 : ℝ) : ℂ)) := by
    funext q
    have hd := ((((hasDerivAt_id q.1).sub_const c.1).pow 2).const_sub
      ((q.2 - c.2) ^ 2)).ofReal_comp.const_mul b
    convert hd.deriv using 1 <;> simp [partialX, saddleQuadratic, b]
  have hy : partialY (saddleQuadratic c a) =
      fun q ↦ b * (2 * ((q.2 - c.2 : ℝ) : ℂ)) := by
    funext q
    have hd := ((((hasDerivAt_id q.2).sub_const c.2).pow 2).sub_const
      ((q.1 - c.1) ^ 2)).ofReal_comp.const_mul b
    convert hd.deriv using 1 <;> simp [partialY, saddleQuadratic, b]
  simp only [classicalComplexJet, coordPartial, Fin.reduceEq, ↓reduceIte]
  rw [hx, hy]
  have hxx : partialX (fun q : ℝ × ℝ ↦ b * (-2 * ((q.1 - c.1 : ℝ) : ℂ))) p = b * (-2) := by
    have hd := (((hasDerivAt_id p.1).sub_const c.1).ofReal_comp.const_mul (-2 : ℂ)).const_mul b
    simpa [partialX] using hd.deriv
  have hyy : partialY (fun q : ℝ × ℝ ↦ b * (2 * ((q.2 - c.2 : ℝ) : ℂ))) p = b * 2 := by
    have hd := (((hasDerivAt_id p.2).sub_const c.2).ofReal_comp.const_mul (2 : ℂ)).const_mul b
    simpa [partialY] using hd.deriv
  rw [hxx, hyy]
  ring

/-- Distance to the saddle lattice is at most distance to any fixed saddle. -/
theorem saddleDist_le_localRadius {c : ℝ × ℝ} (hc : c ∈ saddleSet) (p : ℝ × ℝ) :
    saddleDist p ≤ localRadius c p :=
  (Metric.infDist_le_dist_of_mem hc).trans (dist_le_localRadius c p)

/-- The zero-distance set is null, even though the infimum uses the product metric. -/
theorem ae_saddleDist_ne_zero : ∀ᵐ p : ℝ × ℝ, saddleDist p ≠ 0 := by
  let S : Set (ℝ × ℝ) := {p | p.1 / Real.pi ∈ Set.range ((↑) : ℤ → ℝ)}
  have hS : IsClosed S := Real.isClosed_range_intCast.preimage (by fun_prop)
  have hsub : saddleSet ⊆ S := by
    rintro p ⟨m, n, _, rfl⟩
    exact ⟨m, by simp [Real.pi_ne_zero]⟩
  have hnull : volume S = 0 := by
    have heq : S = (Set.range fun m : ℤ ↦ (m : ℝ) * Real.pi) ×ˢ (univ : Set ℝ) := by
      ext p
      simp only [S, mem_ofPred_eq, mem_range, mem_prod, mem_univ, and_true]
      constructor
      · rintro ⟨m, hm⟩; exact ⟨m, by rw [hm]; field_simp⟩
      · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hm]; simp [Real.pi_ne_zero]⟩
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod]
    simp [(Set.countable_range (fun m : ℤ ↦ (m : ℝ) * Real.pi)).measure_zero volume]
  have hne : saddleSet.Nonempty := ⟨(0, Real.pi), 0, 1, by decide, by simp⟩
  have ha : ∀ᵐ p, p ∉ S := by rw [ae_iff]; simpa using hnull
  filter_upwards [ha] with p hp hz
  have hp' : p ∈ closure saddleSet := by
    by_contra hn
    have hh := (Metric.infDist_pos_iff_notMem_closure hne).mp hn
    exact (ne_of_gt hh) hz
  exact hp ((closure_minimal hsub hS) hp')

/-- Changing the lattice weight to a fixed-saddle Euclidean weight costs no constant. -/
theorem memLp_div_localRadius {c : ℝ × ℝ} (hc : c ∈ saddleSet)
    {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : MemLp (fun p ↦ f p / (saddleDist p : ℂ)) 2 (volume.restrict U)) :
    MemLp (fun p ↦ f p / (localRadius c p : ℂ)) 2 (volume.restrict U) := by
  have hm : Measurable (fun p ↦ ((saddleDist p / localRadius c p : ℝ) : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    apply Measurable.div (Metric.continuous_infDist_pt saddleSet).measurable
    exact (show Continuous (localRadius c) by unfold localRadius; fun_prop).measurable
  have hb : MemLp (fun p ↦ ((saddleDist p / localRadius c p : ℝ) : ℂ)) ⊤
      (volume.restrict U) := by
    apply memLp_top_of_bound hm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (show 0 ≤ saddleDist p from Metric.infDist_nonneg)
          (show 0 ≤ localRadius c p from Real.sqrt_nonneg _))]
      exact div_le_one_of_le₀ (saddleDist_le_localRadius hc p)
        (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)
  apply (hb.mul hf).ae_eq
  filter_upwards [ae_restrict_of_ae ae_saddleDist_ne_zero] with p hp
  have hd : (saddleDist p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  push_cast
  simp only [Pi.mul_apply, div_eq_mul_inv]
  calc _ = (f p * (localRadius c p : ℂ)⁻¹) *
        ((saddleDist p : ℂ) * (saddleDist p : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd, mul_one]

end NoEmbeddedEigenvalues
