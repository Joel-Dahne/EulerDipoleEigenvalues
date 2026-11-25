module

public import EulerDipoleEigenvalues.OddOdd.Picone.ZonalWeakPairing
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The weighted zonal spectral gap

Blueprint: `lem:zonal-gradient-modes`, `lem:zonal-coefficient-parity`,
`lem:zonal-poincare`.

The weak mode pairing identifies the Gram matrix of the mode gradients.
Normalize the nonconstant gradients in the Hilbert product of two weighted
L² spaces and apply Bessel. Only the value expansion is complete; no gradient
energy expansion or weighted Sobolev approximation is used.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped InnerProductSpace

private theorem continuous_memLp_zonal {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 zonalMeasure := by
  let F : C(ZonalCompactSquare, ℂ) := ⟨fun p ↦ f (p.1, p.2), by fun_prop⟩
  have hr : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have heq : zonalToLp F =ᵐ[zonalMeasure] f := by
    filter_upwards [coeFn_zonalToLp F, ae_mem_zonalSquare] with p hp hm
    rw [hp]
    change f ((projIcc _ _ hr p.1 : ZonalInterval), (projIcc _ _ hr p.2 : ZonalInterval)) = f p
    rw [projIcc_of_mem _ ⟨hm.1.1.le, hm.1.2.le⟩,
      projIcc_of_mem _ ⟨hm.2.1.le, hm.2.2.le⟩]
  exact (memLp_congr_ae heq).mp (Lp.memLp (zonalToLp F))

theorem memLp_zonalProduct (k : ℕ × ℕ) :
    MemLp (fun p ↦ (zonalProduct k p : ℂ)) 2 zonalMeasure :=
  (memLp_congr_ae (coeFn_zonalModeLp k)).mp (Lp.memLp (zonalModeLp k))

theorem memLp_zonalProductPartial (k : ℕ × ℕ) (j : Fin 2) :
    MemLp (fun p ↦ (zonalProductPartial k j p : ℂ)) 2 zonalMeasure :=
  continuous_memLp_zonal
    (Complex.continuous_ofReal.comp (contDiff_zonalProductPartial k j).continuous)

private theorem weak_zonalProduct (k : ℕ × ℕ) (j : Fin 2) :
    HasWeakPartialOn zonalSquare j (fun p ↦ (zonalProduct k p : ℂ))
      (fun p ↦ (zonalProductPartial k j p : ℂ)) := by
  have hQ : ContDiff ℝ 1 (zonalProduct k) :=
    ((contDiff_zonalMode k.1).of_le (by simp) |>.comp contDiff_fst).mul
      ((contDiff_zonalMode k.2).of_le (by simp) |>.comp contDiff_snd)
  have heq : coordPartial j (fun p ↦ (zonalProduct k p : ℂ)) =
      fun p ↦ (zonalProductPartial k j p : ℂ) := by
    have hr := coordPartial_zonalProduct k j
    fin_cases j
    · simpa [coordPartial] using
        (partialX_ofReal (hQ.differentiable (by simp))).trans (congrArg (fun f p ↦ (f p : ℂ)) hr)
    · simpa [coordPartial] using
        (partialY_ofReal (hQ.differentiable (by simp))).trans (congrArg (fun f p ↦ (f p : ℂ)) hr)
  rw [← heq]
  exact hasWeakPartialOn_of_contDiff (Complex.ofRealCLM.contDiff.comp hQ) zonalSquare j

/-- Hilbert product of the two weighted scalar gradient components. -/
abbrev ZonalGradientSpace := WithLp 2 (Lp ℂ 2 zonalMeasure × Lp ℂ 2 zonalMeasure)

def zonalGradientLp (k : ℕ × ℕ) : ZonalGradientSpace :=
  WithLp.toLp 2 ((memLp_zonalProductPartial k 0).toLp _,
    (memLp_zonalProductPartial k 1).toLp _)

private theorem inner_partial_toLp (k : ℕ × ℕ) (j : Fin 2)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 zonalMeasure) :
    ⟪(memLp_zonalProductPartial k j).toLp _, hf.toLp f⟫_ℂ =
      ∫ p, f p * (zonalProductPartial k j p : ℂ) ∂zonalMeasure := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_zonalProductPartial k j).coeFn_toLp, hf.coeFn_toLp] with p hp hq
  simp [hp, hq, RCLike.inner_apply]

/-- The gradient pairing on the supplied maximal diagonal weak domain. -/
theorem inner_zonalGradientLp {z za zb : ℝ × ℝ → ℂ}
    (ha : HasWeakPartialOn zonalSquare 0 z za) (hb : HasWeakPartialOn zonalSquare 1 z zb)
    (hz : MemLp z 2 zonalMeasure) (hza : MemLp za 2 zonalMeasure)
    (hzb : MemLp zb 2 zonalMeasure) (k : ℕ × ℕ) :
    ⟪zonalGradientLp k, WithLp.toLp 2 (hza.toLp za, hzb.toLp zb)⟫_ℂ =
      (2 * zonalEigenvalue k.1 k.2 : ℝ) *
        (∫ p, z p * (zonalProduct k p : ℂ) ∂zonalMeasure) := by
  obtain ⟨ia, ib, _, heq⟩ := zonal_weak_pairing_square ha hb hz hza hzb k
  rw [zonalGradientLp, WithLp.prod_inner_apply, inner_partial_toLp, inner_partial_toLp,
    ← integral_add ia ib]
  exact heq

/-- The gradient Gram matrix is diagonal with entries twice the eigenvalues. -/
theorem inner_zonalGradientLp_modes (k l : ℕ × ℕ) :
    ⟪zonalGradientLp k, zonalGradientLp l⟫_ℂ =
      if k = l then (2 * zonalEigenvalue k.1 k.2 : ℝ) else 0 := by
  rw [show zonalGradientLp l = WithLp.toLp 2
    ((memLp_zonalProductPartial l 0).toLp _, (memLp_zonalProductPartial l 1).toLp _) from rfl,
    inner_zonalGradientLp (weak_zonalProduct l 0) (weak_zonalProduct l 1)
      (memLp_zonalProduct l)]
  have heq : (∫ p, (zonalProduct l p : ℂ) * (zonalProduct k p : ℂ) ∂zonalMeasure) =
      if k = l then 1 else 0 := by
    simp_rw [← Complex.ofReal_mul]
    rw [integral_complex_ofReal, integral_zonalProduct_mul]
    by_cases h : k = l <;> simp [h, eq_comm]
  rw [heq]
  split_ifs <;> simp

theorem zonalEigenvalue_pos {k : ℕ × ℕ} (hk : k ≠ (0, 0)) :
    0 < 2 * zonalEigenvalue k.1 k.2 := by
  have hs : 1 ≤ k.1 + k.2 := by
    by_contra hn
    have : k.1 = 0 ∧ k.2 = 0 := by omega
    exact hk (Prod.ext this.1 this.2)
  have hs' : (1 : ℝ) ≤ (k.1 : ℝ) + k.2 := by exact_mod_cast hs
  unfold zonalEigenvalue
  nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]

/-- Indices for all nonconstant modes, before imposing central parity. -/
abbrev ZonalNonconstant := {k : ℕ × ℕ // k ≠ (0, 0)}

/-- Unit gradient modes; no completeness assertion is made for this family. -/
def zonalUnitGradient (k : ZonalNonconstant) : ZonalGradientSpace :=
  ((Real.sqrt (2 * zonalEigenvalue k.val.1 k.val.2) : ℂ)⁻¹) • zonalGradientLp k.val

theorem orthonormal_zonalUnitGradient : Orthonormal ℂ zonalUnitGradient := by
  apply orthonormal_iff_ite.mpr
  intro k l
  simp only [zonalUnitGradient, inner_smul_left, inner_smul_right, map_inv₀,
    Complex.conj_ofReal, inner_zonalGradientLp_modes]
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    norm_cast
    have hp := zonalEigenvalue_pos k.property
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.mpr hp).ne'
    field_simp
    nlinarith
  · have hval : k.val ≠ l.val := fun h ↦ hkl (Subtype.ext h)
    simp [hval, hkl]

/-- Explicit complex coefficients of the product-mode expansion. -/
def zonalCoeff (z : ℝ × ℝ → ℂ) (k : ℕ × ℕ) : ℂ :=
  ∫ p, z p * (zonalProduct k p : ℂ) ∂zonalMeasure

private theorem norm_sq_toLp {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 zonalMeasure) :
    ‖hf.toLp f‖ ^ 2 = ∫ p, ‖f p‖ ^ 2 ∂zonalMeasure := by
  have heq : (‖hf.toLp f‖ ^ 2 : ℂ) = ((∫ p, ‖f p‖ ^ 2 ∂zonalMeasure : ℝ) : ℂ) := by
    calc
      _ = inner ℂ (hf.toLp f) (hf.toLp f) := by
        simp [inner_self_eq_norm_sq_to_K]
      _ = _ := by
        rw [MeasureTheory.L2.inner_def]
        have hraw : (fun p ↦ inner ℂ (hf.toLp f p) (hf.toLp f p)) =ᵐ[zonalMeasure]
            fun p ↦ ((‖f p‖ ^ 2 : ℝ) : ℂ) := by
          filter_upwards [hf.coeFn_toLp] with p hp
          simp [hp, inner_self_eq_norm_sq_to_K]
        rw [integral_congr_ae hraw, integral_complex_ofReal]
  exact_mod_cast heq

private theorem hasSum_zonalCoeff {z : ℝ × ℝ → ℂ} (hz : MemLp z 2 zonalMeasure) :
    HasSum (fun k ↦ ‖zonalCoeff z k‖ ^ 2) (‖hz.toLp z‖ ^ 2) := by
  have heq (k : ℕ × ℕ) : (∫ p, (zonalProduct k p : ℂ) * hz.toLp z p ∂zonalMeasure) =
      zonalCoeff z k := by
    apply integral_congr_ae
    filter_upwards [hz.coeFn_toLp] with p hp
    rw [hp]; ring
  simpa only [heq] using hasSum_sq_zonalCoeff (hz.toLp z)

/-- Normalized gradient pairings with the explicit raw coefficients. -/
theorem inner_zonalUnitGradient {z za zb : ℝ × ℝ → ℂ}
    (ha : HasWeakPartialOn zonalSquare 0 z za) (hb : HasWeakPartialOn zonalSquare 1 z zb)
    (hz : MemLp z 2 zonalMeasure) (hza : MemLp za 2 zonalMeasure)
    (hzb : MemLp zb 2 zonalMeasure) (k : ZonalNonconstant) :
    ⟪zonalUnitGradient k, WithLp.toLp 2 (hza.toLp za, hzb.toLp zb)⟫_ℂ =
      (Real.sqrt (2 * zonalEigenvalue k.val.1 k.val.2) : ℂ) * zonalCoeff z k.val := by
  rw [zonalUnitGradient, inner_smul_left,
    inner_zonalGradientLp ha hb hz hza hzb]
  simp only [map_inv₀, Complex.conj_ofReal]
  have hp := zonalEigenvalue_pos k.property
  have hs : (Real.sqrt (2 * zonalEigenvalue k.val.1 k.val.2) : ℂ) ^ 2 =
      ((2 * zonalEigenvalue k.val.1 k.val.2 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  have hn : (Real.sqrt (2 * zonalEigenvalue k.val.1 k.val.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  change _ = _ * zonalCoeff z k.val
  rw [← mul_assoc, ← hs]
  field_simp
  rfl

/-- The spectral estimate once the constant coefficient vanishes and every
nonzero coefficient has even total degree. -/
theorem zonal_gap_of_even_coefficients {z za zb : ℝ × ℝ → ℂ}
    (ha : HasWeakPartialOn zonalSquare 0 z za) (hb : HasWeakPartialOn zonalSquare 1 z zb)
    (hz : MemLp z 2 zonalMeasure) (hza : MemLp za 2 zonalMeasure)
    (hzb : MemLp zb 2 zonalMeasure) (hmean : ∫ p, z p ∂zonalMeasure = 0)
    (heven : ∀ k, zonalCoeff z k ≠ 0 → Even (k.1 + k.2)) :
    6 * (∫ p, ‖z p‖ ^ 2 ∂zonalMeasure) ≤
      (∫ p, ‖za p‖ ^ 2 ∂zonalMeasure) + (∫ p, ‖zb p‖ ^ 2 ∂zonalMeasure) := by
  have hc0 : zonalCoeff z (0, 0) = 0 := by
    simpa [zonalCoeff, zonalProduct] using hmean
  have hsupp : Function.support (fun k ↦ ‖zonalCoeff z k‖ ^ 2) ⊆
      {k : ℕ × ℕ | k ≠ (0, 0)} := by
    intro k hk heq
    subst k
    simp [Function.mem_support, hc0] at hk
  have hparseval : HasSum (fun k : ZonalNonconstant ↦ ‖zonalCoeff z k.val‖ ^ 2)
      (‖hz.toLp z‖ ^ 2) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mpr (hasSum_zonalCoeff hz)
  have hpair (k : ZonalNonconstant) :
      ‖inner ℂ (zonalUnitGradient k) (WithLp.toLp 2 (hza.toLp za, hzb.toLp zb))‖ ^ 2 =
        (2 * zonalEigenvalue k.val.1 k.val.2) * ‖zonalCoeff z k.val‖ ^ 2 := by
    rw [inner_zonalUnitGradient ha hb hz hza hzb, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (zonalEigenvalue_pos k.property).le]
  have hgap (k : ZonalNonconstant) (hc : zonalCoeff z k.val ≠ 0) :
      6 ≤ 2 * zonalEigenvalue k.val.1 k.val.2 := by
    have := zonalEigenvalue_gap k.property (heven k.val hc)
    linarith
  have h := poincare_of_weak_modes orthonormal_zonalUnitGradient hparseval hpair hgap
  simpa only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
    norm_sq_toLp] using h

theorem zonalProduct_neg (k : ℕ × ℕ) (p : ℝ × ℝ) :
    zonalProduct k (-p) = (-1 : ℝ) ^ (k.1 + k.2) * zonalProduct k p := by
  change zonalMode k.1 (-p.1) * zonalMode k.2 (-p.2) = _
  simp only [zonalProduct, zonalMode_neg, pow_add]
  ring

private theorem neg_preimage_zonalSquare : (fun p : ℝ × ℝ ↦ -p) ⁻¹' zonalSquare =
    zonalSquare := by
  have heq : zonalSquare = {p : ℝ × ℝ | |p.1| < Real.pi / 2 ∧ |p.2| < Real.pi / 2} := by
    ext p; simp [zonalSquare, abs_lt, neg_div]
  ext p
  simp [heq]

/-- The diagonal probability measure is invariant under simultaneous negation. -/
theorem integral_neg_zonalMeasure (f : ℝ × ℝ → ℂ) :
    (∫ p, f (-p) ∂zonalMeasure) = ∫ p, f p ∂zonalMeasure := by
  have hnv : MeasurePreserving (fun p : ℝ × ℝ ↦ -p) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hn := hnv.restrict_preimage_emb
    (Homeomorph.neg (ℝ × ℝ)).measurableEmbedding zonalSquare
  rw [neg_preimage_zonalSquare] at hn
  have hi := hn.integral_comp (Homeomorph.neg (ℝ × ℝ)).measurableEmbedding
    (fun p ↦ (zonalDensity p : ℂ) * f p)
  have hd (p : ℝ × ℝ) : zonalDensity (-p) = zonalDensity p := by
    change 4 / Real.pi ^ 2 * (Real.cos (-p.1) ^ 2 * Real.cos (-p.2) ^ 2) = _
    simp [zonalDensity]
  simpa only [integral_zonalMeasure_complex, hd] using hi

/-- Changing variables by central negation gives the coefficient parity identity. -/
theorem zonalCoeff_central_parity {z : ℝ × ℝ → ℂ}
    (hc : ∀ᵐ p ∂zonalMeasure, z (-p) = z p) (k : ℕ × ℕ) :
    zonalCoeff z k = (-1 : ℂ) ^ (k.1 + k.2) * zonalCoeff z k := by
  calc
    _ = ∫ p, z (-p) * (zonalProduct k (-p) : ℂ) ∂zonalMeasure :=
      (integral_neg_zonalMeasure (fun p ↦ z p * (zonalProduct k p : ℂ))).symm
    _ = ∫ p, (-1 : ℂ) ^ (k.1 + k.2) * (z p * (zonalProduct k p : ℂ)) ∂zonalMeasure := by
      apply integral_congr_ae
      filter_upwards [hc] with p hp
      rw [hp, zonalProduct_neg]
      push_cast
      ring
    _ = _ := integral_const_mul _ _

/-- Central evenness removes every coefficient of odd total degree. -/
theorem zonalCoeff_even {z : ℝ × ℝ → ℂ}
    (hc : ∀ᵐ p ∂zonalMeasure, z (-p) = z p) (k : ℕ × ℕ)
    (hk : zonalCoeff z k ≠ 0) : Even (k.1 + k.2) := by
  have heq := zonalCoeff_central_parity hc k
  rcases Nat.even_or_odd (k.1 + k.2) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at heq
    have hz : zonalCoeff z k = 0 := by linear_combination (1 / 2 : ℂ) * heq
    exact (hk hz).elim

/-- Weighted Poincaré on the entire diagonal weak domain, in Cartesian-energy
normalization. There is no trace or mean-zero hypothesis. -/
theorem zonal_poincare_square {z za zb : ℝ × ℝ → ℂ}
    (ha : HasWeakPartialOn zonalSquare 0 z za) (hb : HasWeakPartialOn zonalSquare 1 z zb)
    (hz : MemLp z 2 zonalMeasure) (hza : MemLp za 2 zonalMeasure)
    (hzb : MemLp zb 2 zonalMeasure) (hc : ∀ᵐ p ∂zonalMeasure, z (-p) = z p) :
    6 * (∫ p, ‖z p - ∫ q, z q ∂zonalMeasure‖ ^ 2 ∂zonalMeasure) ≤
      (∫ p, ‖za p‖ ^ 2 ∂zonalMeasure) + (∫ p, ‖zb p‖ ^ 2 ∂zonalMeasure) := by
  let m := ∫ q, z q ∂zonalMeasure
  have hconst (j : Fin 2) : HasWeakPartialOn zonalSquare j (fun _ ↦ -m) (fun _ ↦ 0) := by
    have hd : coordPartial j (fun _ : ℝ × ℝ ↦ -m) = fun _ ↦ 0 := by
      funext p
      unfold coordPartial
      split_ifs <;> simp [partialX, partialY]
    simpa only [hd] using hasWeakPartialOn_of_contDiff
      (show ContDiff ℝ 1 (fun _ : ℝ × ℝ ↦ -m) from contDiff_const) zonalSquare j
  have ha' : HasWeakPartialOn zonalSquare 0 (fun p ↦ z p - m) za := by
    simpa [sub_eq_add_neg] using ha.add (hconst 0)
  have hb' : HasWeakPartialOn zonalSquare 1 (fun p ↦ z p - m) zb := by
    simpa [sub_eq_add_neg] using hb.add (hconst 1)
  have hm : (∫ p, z p - m ∂zonalMeasure) = 0 := by
    rw [integral_sub (hz.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have hc' : ∀ᵐ p ∂zonalMeasure, (z (-p) - m) = z p - m := hc.mono fun p hp ↦ by rw [hp]
  exact zonal_gap_of_even_coefficients ha' hb' (hz.sub (memLp_const m)) hza hzb hm
    (zonalCoeff_even hc')

end EulerDipoleEigenvalues
