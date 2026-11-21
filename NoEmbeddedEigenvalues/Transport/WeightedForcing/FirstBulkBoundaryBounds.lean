import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterTraceComparison
import NoEmbeddedEigenvalues.Transport.WeightedForcing.OrbitBulkFlux

/-! # Pointwise first-bulk boundary energy -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

private theorem interiorSectionTrace_add {F G : ℝ → ℂ}
    (hF : HasContinuousSectionGerm F) (hG : HasContinuousSectionGerm G) :
    HasContinuousSectionGerm (fun s ↦ F s + G s) ∧
      interiorSectionTrace (fun s ↦ F s + G s) =
        interiorSectionTrace F + interiorSectionTrace G := by
  obtain ⟨f, a, b, ha, hb, hf, he⟩ := hF
  obtain ⟨g, c, d, hc, hd, hg, hg'⟩ := hG
  have hs := Ioo_subset_Ioo (le_max_left a c) (min_le_left b d)
  have ht := Ioo_subset_Ioo (le_max_right a c) (min_le_right b d)
  have hcont := (hf.mono hs).add (hg.mono ht)
  have hae : (fun s ↦ f s + g s) =ᵐ[volume.restrict (Ioo (max a c) (min b d))]
      (fun s ↦ F s + G s) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he,
      ae_restrict_of_ae_restrict_of_subset ht hg'] with s h₁ h₂
    rw [h₁, h₂]
  exact ⟨⟨_, _, _, max_lt ha hc, lt_min hb hd, hcont, hae⟩, by
    rw [interiorSectionTrace_eq (max_lt ha hc) (lt_min hb hd) hcont hae,
      interiorSectionTrace_eq ha hb hf he, interiorSectionTrace_eq hc hd hg hg']; rfl⟩

private theorem quarterFirstBulkTrace_eq_affine {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j : Fin 2, MemSobolevOn 1 U (D [j]))
    {b : ℝ} (hb : b < 1) (hρ : quarterEndpointRadius b < 1 / 2) (side : Bool) :
    ∀ᵐ h ∂volume.restrict (Ioo 0 b), ∀ μ : ℝ,
      let θ : ℝ := (if side then 1 else -1) / 8
      let t := θ * orbitPeriod h
      let V := deriv (fun x ↦ dipoleOrbit x t) h
      quarterFirstBulkTrace μ D θ h =
        (θ : ℂ) * Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ)) *
          ((V.1 : ℂ) * quarterGradientTrace (fun j ↦ D [j]) side 0 (quarterEndpointRadius h) +
           (V.2 : ℂ) * quarterGradientTrace (fun j ↦ D [j]) side 1 (quarterEndpointRadius h)) := by
  filter_upwards [quarterEndpointTrace_compare hU hcell (hD 0) hb hρ side,
    quarterEndpointTrace_compare hU hcell (hD 1) hb hρ side,
    ae_restrict_mem measurableSet_Ioo] with h h0 h1 hh μ
  let θ : ℝ := (if side then 1 else -1) / 8
  let V (s : ℝ) := deriv (fun x ↦ dipoleOrbit x ((θ + s) * orbitPeriod h)) h
  let A (j : Fin 2) (s : ℝ) := D [j] (actionAngleInv (h, θ + s))
  let C (j : Fin 2) (s : ℝ) : ℂ := (axisCoord j (V s) : ℂ)
  let P (s : ℝ) : ℂ := ((θ + s : ℝ) : ℂ) *
    Complex.exp (-Complex.I * ((μ * ((θ + s) * orbitPeriod h) : ℝ) : ℂ))
  have hv : Continuous V := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (contDiffAt_orbit_level_derivative (t := (θ + s) * orbitPeriod h)
      ⟨hh.1, hh.2.trans hb⟩).continuousAt.comp
        (f := fun y : ℝ ↦ (h, (θ + y) * orbitPeriod h)) (by fun_prop)
  have hc (j : Fin 2) : Continuous (C j) := by
    fin_cases j
    · exact Complex.continuous_ofReal.comp hv.fst
    · exact Complex.continuous_ofReal.comp hv.snd
  have hp : Continuous P := by dsimp [P]; fun_prop
  have hs := interiorSectionTrace_add (h0.1.mul_continuous (hc 0)) (h1.1.mul_continuous (hc 1))
  change interiorSectionTrace (fun s ↦ P s * (C 0 s * A 0 s + C 1 s * A 1 s)) = _
  rw [interiorSectionTrace_mul_continuous hs.1 hp, hs.2,
    interiorSectionTrace_mul_continuous h0.1 (hc 0),
    interiorSectionTrace_mul_continuous h1.1 (hc 1), h0.2, h1.2]
  simp only [P, C, V, axisCoord, add_zero]
  rfl

/-- The distinct first-bulk endpoint term in the second moving-endpoint
formula is controlled level by level by the canonical affine gradient
energy, with one collar and one bound for all real frequencies. -/
theorem quarter_first_bulk_boundary_sq_le {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j : Fin 2, MemSobolevOn 1 U (D [j])) :
    ∃ d K : ℝ, 0 < d ∧ 0 ≤ K ∧
      ∀ᵐ (h : ℝ) ∂volume.restrict (Ioo 0 d), ∀ μ : ℝ,
        ‖(h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ) *
          (quarterFirstBulkTrace μ D (1 / 8) h - quarterFirstBulkTrace μ D (-1 / 8) h)‖ ^ 2 ≤
            K * quarterEndpointGradientEnergy (quarterGradientTrace (fun j ↦ D [j])) h := by
  obtain ⟨A, a, ha, ha1, hA⟩ := deriv_dipoleOrbit_level_le_saddleDist
  obtain ⟨b, hb, hb1, hB⟩ := quarterEndpointCoefficient_weighted_bounds
  obtain ⟨B, hBpos, hB⟩ := hB 0
  let d := min (1 / 256) (min a b)
  let K := 4 * (8 * B) ^ 2 * |A| ^ 2
  have hd : 0 < d := lt_min (by norm_num) (lt_min ha hb)
  have hda : d ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hdb : d ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hds : d ≤ 1 / 256 := min_le_left _ _
  have hd1 : d < 1 := hda.trans_lt ha1
  have hρ : quarterEndpointRadius d < 1 / 2 := by
    have hs : Real.sqrt d ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hd hd1]
  refine ⟨d, K, hd, by dsimp [K]; positivity, ?_⟩
  filter_upwards [quarterFirstBulkTrace_eq_affine hU hcell hD hd1 hρ true,
    quarterFirstBulkTrace_eq_affine hU hcell hD hd1 hρ false,
    ae_restrict_mem measurableSet_Ioo] with h hp hm hh μ
  let T := quarterGradientTrace (fun j ↦ D [j])
  let E (side : Bool) := ∑ j : Fin 2, ‖T side j (quarterEndpointRadius h)‖ ^ 2
  have h0 : 0 < h := hh.1
  have h1 : h < 1 := hh.2.trans hd1
  have hS : ‖(h : ℂ) * ((deriv orbitPeriod h : ℝ) : ℂ)‖ ≤ 8 * B := by
    have hh' : h ∈ Ioo 0 b := ⟨hh.1, hh.2.trans_le hdb⟩
    have hbnd := (hB 1 (Or.inr rfl) h hh').1
    have hs : HasDerivAt orbitPeriod (8 * deriv eighthPeriod h) h :=
      (((contDiffOn_eighthPeriod.contDiffAt (Ioo_mem_nhds h0 h1)).differentiableAt
        (by simp)).hasDerivAt).const_mul 8
    rw [hs.deriv, Complex.ofReal_mul, show ((8 : ℝ) : ℂ) = 8 by norm_num,
      show (h : ℂ) * (8 * (↑(deriv eighthPeriod h) : ℂ)) =
        8 * ((h : ℂ) * (↑(deriv eighthPeriod h) : ℂ)) by ring,
      norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa [quarterEndpointCoefficient] using hbnd
  have hTrace (side : Bool) :
      ‖quarterFirstBulkTrace μ D ((if side then 1 else -1 : ℝ) / 8) h‖ ^ 2 ≤
        2 * |A| ^ 2 * (E side / h) := by
    let θ : ℝ := (if side then 1 else -1) / 8
    let t := θ * orbitPeriod h
    let V := deriv (fun x ↦ dipoleOrbit x t) h
    have he : quarterFirstBulkTrace μ D θ h =
        (θ : ℂ) * Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ)) *
          ((V.1 : ℂ) * T side 0 (quarterEndpointRadius h) +
           (V.2 : ℂ) * T side 1 (quarterEndpointRadius h)) := by
      cases side
      · exact hm μ
      · exact hp μ
    have ht : |t| = eighthPeriod h := by
      have hs := eighthPeriod_pos h0 h1
      have he : t = (if side then 1 else -1 : ℝ) * eighthPeriod h := by
        dsimp [t, θ, orbitPeriod]; ring
      rw [he]
      cases side <;> simp [abs_of_pos hs]
    have hd0 := (saddleDist_dipoleOrbit_endpoints h0 h1 ht).1
    have hV : ‖V‖ ≤ |A| / Real.sqrt h := by
      have h := (hA h ⟨h0, hh.2.trans_le hda⟩ t ht.le).1
      exact h.trans ((div_le_div_of_nonneg_right (le_abs_self A)
        ((Real.sqrt_pos.mpr h0).le.trans hd0)).trans
        (div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr h0) hd0))
    have hmul (j : Fin 2) :
        ‖(axisCoord j V : ℂ) * T side j (quarterEndpointRadius h)‖ ^ 2 ≤
          |A| ^ 2 / h * ‖T side j (quarterEndpointRadius h)‖ ^ 2 := by
      have hc : ‖(axisCoord j V : ℂ)‖ ≤ ‖V‖ := by
        fin_cases j
        · simpa [axisCoord] using (norm_fst_le V)
        · simpa [axisCoord] using (norm_snd_le V)
      rw [norm_mul, mul_pow, ← Real.sq_sqrt h0.le, ← div_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).2
        (hc.trans hV)
    have hθ : ‖(θ : ℂ)‖ ≤ 1 := by cases side <;> norm_num [θ, Complex.norm_real]
    have hexp : ‖Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
    rw [he, norm_mul, norm_mul, hexp, mul_one, mul_pow]
    let X := (V.1 : ℂ) * T side 0 (quarterEndpointRadius h)
    let Y := (V.2 : ℂ) * T side 1 (quarterEndpointRadius h)
    change ‖(θ : ℂ)‖ ^ 2 * ‖X + Y‖ ^ 2 ≤ _
    have hnorm := (sq_le_sq₀ (norm_nonneg (θ : ℂ)) zero_le_one).2 hθ
    have hm₀ : ‖X‖ ^ 2 ≤ |A| ^ 2 / h * ‖T side 0 (quarterEndpointRadius h)‖ ^ 2 := hmul 0
    have hm₁ : ‖Y‖ ^ 2 ≤ |A| ^ 2 / h * ‖T side 1 (quarterEndpointRadius h)‖ ^ 2 := hmul 1
    calc
      _ ≤ 1 * ‖X + Y‖ ^ 2 := mul_le_mul_of_nonneg_right (by simpa using hnorm) (sq_nonneg _)
      _ ≤ 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) := by simpa only [one_mul] using norm_add_sq_le X Y
      _ ≤ 2 * (|A| ^ 2 / h * ‖T side 0 (quarterEndpointRadius h)‖ ^ 2 +
          |A| ^ 2 / h * ‖T side 1 (quarterEndpointRadius h)‖ ^ 2) := by gcongr
      _ = _ := by simp only [E, Fin.sum_univ_two]; ring
  have hbndP : ‖quarterFirstBulkTrace μ D (1 / 8) h‖ ^ 2 ≤ 2 * |A| ^ 2 * (E true / h) := by
    simpa only [ite_true] using hTrace true
  have hbndM : ‖quarterFirstBulkTrace μ D (-1 / 8) h‖ ^ 2 ≤ 2 * |A| ^ 2 * (E false / h) := by
    simpa only [Bool.false_eq_true, ite_false] using hTrace false
  let X := quarterFirstBulkTrace μ D (1 / 8) h
  let Y := quarterFirstBulkTrace μ D (-1 / 8) h
  have hXY : ‖X - Y‖ ^ 2 ≤ 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) := by
    simpa only [sub_eq_add_neg, norm_neg] using norm_add_sq_le X (-Y)
  rw [norm_mul, mul_pow]
  calc
    _ ≤ (8 * B) ^ 2 * (2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2)) := by
      exact mul_le_mul ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hS) hXY
        (sq_nonneg _) (sq_nonneg _)
    _ ≤ (8 * B) ^ 2 * (2 * (2 * |A| ^ 2 * (E true / h) +
      2 * |A| ^ 2 * (E false / h))) := by
      gcongr
    _ = _ := by simp only [quarterEndpointGradientEnergy, K, E, Fintype.sum_bool]; ring

end NoEmbeddedEigenvalues
