module

public import NoEmbeddedEigenvalues.Virial.OriginalDomain.CellPeriodization
public import NoEmbeddedEigenvalues.Symmetry.Sectors

/-!
# Dipole orthogonality and cell pairings

Blueprint: `lem:dipole-fourier-pairing`, `lem:dipole-transport-orthogonality`,
`lem:dipole-invlap-pairing`, `lem:cell-lift-integral`, `lem:odd-dipole-cell-pairing`.

The dipole has four unit Fourier frequencies. Summing the weak transport equations at
those frequencies cancels every term, so an L² transport derivative is orthogonal to
`Ψ`. Nonzero-parameter eigenfunctions inherit this orthogonality, and inverse-Laplacian
pairing changes its sign. No self-adjointness or Sobolev regularity is needed.

The cell identities transfer a torus integral to the lifted positive square. For data odd
under the first reflection, `Ψg` is reflection-invariant and its torus integral is twice
its cell integral. The product vanishes on the separatrix, so no boundary trace or
separatrix null-set assertion is needed for that decomposition.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- The dipole is a four-mode trigonometric polynomial. -/
theorem dipole_eq_char_sum (t : Torus) :
    (Ψ t : ℂ) = (char (1, 0) t + char (-1, 0) t + char (0, 1) t + char (0, -1) t) / 2 := by
  obtain ⟨⟨x, y⟩, rfl⟩ := torusProj_surjective t
  simp only [torusProj, Ψ, Real.Angle.cos_coe, char_coe, Int.cast_one, Int.cast_neg,
    Int.cast_zero, one_mul, neg_one_mul, zero_mul, add_zero, zero_add]
  simp only [mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  push_cast
  ring

/-- Pairing with the dipole uses only the four unit Fourier frequencies. -/
theorem integral_dipole_mul_eq_fourier (g : L2) :
    (∫ t, (Ψ t : ℂ) * g t) = (2 * Real.pi : ℂ) ^ 2 / 2 *
      (fourierCoeff g (1, 0) + fourierCoeff g (-1, 0) +
        fourierCoeff g (0, 1) + fourierCoeff g (0, -1)) := by
  have hi (k : ℤ × ℤ) : Integrable (fun t ↦ char k t * g t) := by
    simpa only [← char_neg, neg_neg] using integrable_char_pairing g (-k)
  have hk (k : ℤ × ℤ) : (∫ t, char k t * g t) =
      (2 * Real.pi : ℂ) ^ 2 * fourierCoeff g (-k) := by
    rw [fourierCoeff_eq_integral_char_neg]
    simp only [neg_neg]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  calc
    (∫ t, (Ψ t : ℂ) * g t) = (1 / 2 : ℂ) *
        ∫ t, char (1, 0) t * g t + char (-1, 0) t * g t +
          char (0, 1) t * g t + char (0, -1) t * g t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun t ↦ by dsimp only; rw [dipole_eq_char_sum]; ring
    _ = _ := by
      have h12 := integral_add (hi (1, 0)) (hi (-1, 0))
      have h123 := integral_add ((hi (1, 0)).add (hi (-1, 0))) (hi (0, 1))
      have h1234 := integral_add (((hi (1, 0)).add (hi (-1, 0))).add (hi (0, 1))) (hi (0, -1))
      simp only [Pi.add_apply] at h12 h123 h1234
      rw [h1234, h123, h12]
      simp only [hk]
      norm_num
      ring

/-- A weak transport derivative is orthogonal to the dipole. No self-adjointness
    theorem or regularity of the transported function is required. -/
theorem HasL0.integral_dipole_mul_eq_zero {g h : L2} (hgh : HasL0 g h) :
    (∫ t, (Ψ t : ℂ) * h t) = 0 := by
  rw [integral_dipole_mul_eq_fourier]
  have hc := (hasL0_iff_fourierCoeff g h).mp hgh
  rw [hc (1, 0), hc (-1, 0), hc (0, 1), hc (0, -1)]
  norm_num [transportCoeff]
  ring

/-- A nonzero-parameter eigenfunction is orthogonal to the dipole, in any sector. -/
theorem IsEigenSolution.integral_dipole_mul_eq_zero {lam : ℝ} (hlam : lam ≠ 0)
    {ω : L2} (hω : IsEigenSolution lam ω) : (∫ t, (Ψ t : ℂ) * ω t) = 0 := by
  have heq : (∫ t, (Ψ t : ℂ) * ((Complex.I * lam) • ω : L2) t) =
      (Complex.I * lam) * ∫ t, (Ψ t : ℂ) * ω t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (Complex.I * lam) ω] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring
  have hz := heq.symm.trans hω.2.integral_dipole_mul_eq_zero
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hlam))

/-- The inverse Laplacian acts by `-1` on the frequencies seen by dipole pairing. -/
theorem integral_dipole_mul_invLap (g : L2) :
    (∫ t, (Ψ t : ℂ) * invLap g t) = -(∫ t, (Ψ t : ℂ) * g t) := by
  simp only [integral_dipole_mul_eq_fourier, fourierCoeff_invLap]
  norm_num [normSq]
  ring

/-- Integrating a torus function on the positive cell is the same as integrating its
    lift on the diagonal square. This is a measure identity, not a Sobolev assertion. -/
theorem setIntegral_lift_cellSquare {F : Torus → ℂ} (hF : AEStronglyMeasurable F) :
    (∫ p in cellSquare, F (torusProj p)) = ∫ t in positiveCell, F t := by
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  have hpos : MeasurableSet positiveCell := (isOpen_lt continuous_const hΨ).measurableSet
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hm := integral_map measurePreserving_torusProj_box.measurable.aemeasurable
    (f := positiveCell.indicator F) (by
      rw [measurePreserving_torusProj_box.map_eq]
      exact hF.indicator hpos)
  have hmap : (∫ p in periodBox, positiveCell.indicator F (torusProj p)) =
      ∫ t, positiveCell.indicator F t := by
    simpa only [measurePreserving_torusProj_box.map_eq] using hm.symm
  calc
    (∫ p in cellSquare, F (torusProj p)) =
        ∫ p in periodBox, cellSquare.indicator (fun p ↦ F (torusProj p)) p := by
      rw [setIntegral_indicator hcell, inter_eq_right.mpr cellSquare_subset_periodBox]
    _ = ∫ p in periodBox, positiveCell.indicator F (torusProj p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_periodBox] with p hp
      by_cases hc : p ∈ cellSquare
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (torusProj_mem_positiveCell hc)]
      · have hn : torusProj p ∉ positiveCell := by
          intro hn
          apply hc
          apply mem_cellSquare_of_mem_periodBox hp
          simpa only [positiveCell, mem_ofPred_eq, Ψ_torusProj] using hn
        rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hn]
    _ = ∫ t in positiveCell, F t := by rw [hmap, integral_indicator hpos]

/-- For an odd function, `Ψg` is reflection-invariant. Its torus integral is twice
    its lifted positive-cell integral; the product vanishes on the separatrix. -/
theorem integral_dipole_mul_eq_two_cell (g : L2) (hg : reflect₁ g = -g) :
    (∫ t, (Ψ t : ℂ) * g t) =
      (2 : ℂ) * ∫ p in cellSquare, (dipoleLift p : ℂ) * liftL2 g p := by
  classical
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  let Φ : C(Torus, ℂ) := ⟨fun t ↦ (Ψ t : ℂ), Complex.continuous_ofReal.comp hΨ⟩
  let F : Torus → ℂ := fun t ↦ (Ψ t : ℂ) * g t
  have hi : Integrable F := by
    simpa only [F, Φ, ContinuousMap.coe_mk, mul_comm] using integrable_mul_continuous g Φ
  have hpos : MeasurableSet positiveCell := (isOpen_lt continuous_const hΨ).measurableSet
  let P : Torus → ℂ := positiveCell.indicator F
  have hiP : Integrable P := hi.indicator hpos
  have hiPS : Integrable (fun t ↦ P (S₁ t)) :=
    (measurePreserving_S₁.integrable_comp hiP.aestronglyMeasurable).2 hiP
  have hraw := ae_comp_of_pullback_eq (T := S₁) (hT := measurePreserving_S₁) hg
  have hsym : ∀ᵐ t, F (S₁ t) = F t := by
    filter_upwards [hraw, Lp.coeFn_neg g] with t ht hn
    have hΨS : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    simp only [F, ht, hn, Pi.neg_apply, hΨS, Complex.ofReal_neg, neg_mul_neg]
  have hsum : (fun t ↦ P t + P (S₁ t)) =ᵐ[volume] F := by
    filter_upwards [hsym] with t ht
    have hΨS : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    change positiveCell.indicator F t + positiveCell.indicator F (S₁ t) = F t
    by_cases h0 : 0 < Ψ t
    · have hn : S₁ t ∉ positiveCell := by change ¬0 < Ψ (S₁ t); rw [hΨS]; linarith
      rw [Set.indicator_of_mem (show t ∈ positiveCell from h0),
        Set.indicator_of_notMem hn, add_zero]
    · by_cases hn : Ψ t < 0
      · have hp : S₁ t ∈ positiveCell := by change 0 < Ψ (S₁ t); rw [hΨS]; linarith
        rw [Set.indicator_of_notMem (show t ∉ positiveCell from h0),
          Set.indicator_of_mem hp, zero_add, ht]
      · have hz : Ψ t = 0 := by linarith
        have hp : S₁ t ∉ positiveCell := by change ¬0 < Ψ (S₁ t); rw [hΨS, hz]; norm_num
        rw [Set.indicator_of_notMem (show t ∉ positiveCell from h0),
          Set.indicator_of_notMem hp]
        simp only [F, hz, Complex.ofReal_zero, zero_mul, add_zero]
  have hchange : (∫ t, P (S₁ t)) = ∫ t, P t := by
    have hm := integral_map measurePreserving_S₁.measurable.aemeasurable (f := P) (by
      rw [measurePreserving_S₁.map_eq]
      exact hiP.aestronglyMeasurable)
    simpa only [measurePreserving_S₁.map_eq] using hm.symm
  calc
    (∫ t, F t) = ∫ t, P t + P (S₁ t) := (integral_congr_ae hsum).symm
    _ = (∫ t, P t) + ∫ t, P (S₁ t) := integral_add hiP hiPS
    _ = (2 : ℂ) * ∫ t in positiveCell, F t := by
      rw [hchange]
      dsimp only [P]
      rw [integral_indicator hpos]
      ring
    _ = _ := by
      rw [← setIntegral_lift_cellSquare hi.aestronglyMeasurable]
      simp only [F, Ψ_torusProj, liftL2]

end NoEmbeddedEigenvalues
