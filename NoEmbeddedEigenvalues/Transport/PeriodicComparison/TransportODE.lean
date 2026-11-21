module

public import NoEmbeddedEigenvalues.Transport.CanonicalProfile.CanonicalProfile

/-!
# Finite-interval transport estimates

Blueprint: `lem:transport-boundary-estimate`, `lem:periodic-transport-character`,
`lem:transport-pairing-error`.

The integrating factor for `W' = i(λW + F)` has derivative `i e^{-iλt} F`.
Its endpoint identity controls the solution on an interval from the forcing
and the defect in the boundary condition `W(b) = κ W(a)`, provided the
phase divisor stays away from zero. This is the ODE input to `lem:pairing-limit`;
it requires neither differentiability of the forcing nor orbitwise Sobolev traces.
Periodic uniqueness then transfers translation characters from the forcing to the
solution. In the pairing-limit argument this avoids transferring the planar a.e.
rotation character of the vorticity to orbit representatives. A final elementary
estimate bounds the integral pairing error from supremum bounds.

The monotone and antitone Lipschitz change-of-variable lemmas for absolute continuity
(previously in `Melnikov.lean`) are shared by translation of transport solutions and
parametrization of the separatrix trace.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Set Filter
open scoped Interval Topology ComplexConjugate

/-! ### Changes of variable in absolutely continuous functions -/

/-- Absolute continuity is preserved by an antitone Lipschitz change of variable: disjoint
    intervals are mapped to disjoint intervals of at most `K` times the length. -/
theorem AbsolutelyContinuousOnInterval.comp_antitoneOn {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {φ : ℝ → ℝ} {α β c d : ℝ} (hf : AbsolutelyContinuousOnInterval f α β)
    {K : NNReal} (hφL : LipschitzOnWith K φ (uIcc c d)) (hφa : AntitoneOn φ (uIcc c d))
    (hφm : MapsTo φ (uIcc c d) (uIcc α β)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) c d := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  have hK : (0 : ℝ) ≤ K := K.2
  refine ⟨δ / (K + 1), by positivity, fun E hE hlen ↦ ?_⟩
  obtain ⟨n, I⟩ := E
  set S := uIcc c d
  have hminS {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : min x y ∈ S := by
    rcases le_total x y with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hmaxS {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : max x y ∈ S := by
    rcases le_total x y with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hmax {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : max (φ x) (φ y) = φ (min x y) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_left (hφa hx hy h)]
    · rw [min_eq_right h, max_eq_right (hφa hy hx h)]
  have hmin {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : min (φ x) (φ y) = φ (max x y) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_right (hφa hx hy h)]
    · rw [max_eq_left h, min_eq_left (hφa hy hx h)]
  have hE' : (n, fun i ↦ (φ (I i).1, φ (I i).2)) ∈
      AbsolutelyContinuousOnInterval.disjWithin α β := by
    refine ⟨fun i hi ↦ ⟨hφm (hE.1 i hi).1, hφm (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    have hd := hE.2 hi hj hij
    obtain ⟨hi1, hi2⟩ := hE.1 i hi
    obtain ⟨hj1, hj2⟩ := hE.1 j hj
    simp only [Function.onFun, uIoc, Set.Ioc_disjoint_Ioc] at hd ⊢
    rw [hmax hi1 hi2, hmax hj1 hj2, hmin hi1 hi2, hmin hj1 hj2,
      hmin (hminS hi1 hi2) (hminS hj1 hj2), hmax (hmaxS hi1 hi2) (hmaxS hj1 hj2)]
    exact hφa (hminS (hmaxS hi1 hi2) (hmaxS hj1 hj2)) (hmaxS (hminS hi1 hi2) (hminS hj1 hj2)) hd
  refine hfδ _ hE' ?_
  calc ∑ i ∈ Finset.range n, dist (φ (I i).1) (φ (I i).2)
      ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 :=
        Finset.sum_le_sum fun i hi ↦ hφL.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (δ / (K + 1)) := by gcongr
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- Absolute continuity is preserved by a monotone Lipschitz change of variable. -/
theorem AbsolutelyContinuousOnInterval.comp_monotoneOn {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {φ : ℝ → ℝ} {α β c d : ℝ} (hf : AbsolutelyContinuousOnInterval f α β)
    {K : NNReal} (hφL : LipschitzOnWith K φ (uIcc c d)) (hφm : MonotoneOn φ (uIcc c d))
    (hφs : MapsTo φ (uIcc c d) (uIcc α β)) :
    AbsolutelyContinuousOnInterval (f ∘ φ) c d := by
  have hnm {a b x : ℝ} (h : x ∈ uIcc a b) : -x ∈ uIcc (-a) (-b) := by
    rw [mem_uIcc] at h ⊢
    rcases h with h | h
    · exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
  have hneg : AbsolutelyContinuousOnInterval (f ∘ Neg.neg) (-α) (-β) :=
    AbsolutelyContinuousOnInterval.comp_antitoneOn hf (K := 1) LipschitzWith.id.neg.lipschitzOnWith
      (fun x _ y _ h ↦ neg_le_neg h) fun x hx ↦ by
        simpa using hnm hx
  have h := AbsolutelyContinuousOnInterval.comp_antitoneOn hneg (φ := fun x ↦ -φ x) (K := K) hφL.neg
    (fun x hx y hy h ↦ neg_le_neg (hφm hx hy h)) fun x hx ↦ by
      exact hnm (hφs hx)
  convert h using 1
  funext x
  simp

/-- The integrating-factor identity for an absolutely continuous transport solution. -/
theorem transport_integratingFactor {lam a b : ℝ} {W F : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval W a b) (hF : IntervalIntegrable F volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt W (I * (lam * W t + F t)) t) :
    exp (-(I * lam * b)) * W b - exp (-(I * lam * a)) * W a =
      I * ∫ t in a..b, exp (-(I * lam * t)) * F t := by
  let e : ℝ → ℂ := fun t ↦ exp (-(I * lam * t))
  have hecd : ContDiff ℝ 1 e := (contDiff_const.mul ofRealCLM.contDiff).neg.cexp
  have he (t : ℝ) : HasDerivAt e (e t * -(I * lam)) t := by
    simpa [e] using (((hasDerivAt_id (t : ℂ)).const_mul (I * lam)).neg.cexp).comp_ofReal
  have hDi : IntervalIntegrable (fun t ↦ I * (e t * F t)) volume a b :=
    (hF.continuousOn_mul hecd.continuous.continuousOn).const_mul I
  have hder : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t ↦ e t * W t) (I * (e t * F t)) t := by
    filter_upwards [hd] with t ht htab
    convert (he t).mul (ht htab) using 1
    ring
  have hFTC := complex_integral_eq_sub_of_ac
    (hecd.contDiffOn.absolutelyContinuousOnInterval.fun_smul hac) hDi hder
  rw [intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

/-- On a nonresonant interval, the forcing and the boundary defect bound the solution. -/
theorem norm_transport_le_of_boundary {lam a b ε δ : ℝ} {κ : ℂ} {W F : ℝ → ℂ}
    (hab : a ≤ b) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hac : AbsolutelyContinuousOnInterval W a b) (hF : IntervalIntegrable F volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt W (I * (lam * W t + F t)) t)
    (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ ε)
    (hdiv : δ ≤ ‖exp (I * lam * (b - a)) - κ‖) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖W x‖ ≤ (‖W b - κ * W a‖ + ε * (b - a)) / δ + ε * (b - a) := by
  let e : ℝ → ℂ := fun t ↦ exp (-(I * lam * t))
  have hen (t : ℝ) : ‖e t‖ = 1 := norm_exp_neg_I_mul lam t
  have hinc {y : ℝ} (hy : y ∈ Icc a b) :
      ‖e y * W y - e a * W a‖ ≤ ε * (y - a) := by
    have hsub : uIcc a y ⊆ uIcc a b := by
      rw [uIcc_of_le hy.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hy.2
    have hi := transport_integratingFactor (hac.mono hsub) (hF.mono_set hsub)
      (hd.mono fun t ht hty ↦ ht (hsub hty))
    change ‖exp (-(I * lam * y)) * W y - exp (-(I * lam * a)) * W a‖ ≤ _
    rw [hi, norm_mul, norm_I, one_mul]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := y) (f := fun t ↦ e t * F t) (C := ε) (fun t ht ↦ by
        rw [uIoc_of_le hy.1] at ht
        rw [norm_mul, hen, one_mul]
        exact hFb t ⟨ht.1.le, ht.2.trans hy.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.2 hy.1)] using hbnd
  have hea : e a = e b * exp (I * lam * (b - a)) := by
    dsimp only [e]
    rw [← exp_add]
    congr 1
    ring
  have hcoef : ‖e a - κ * e b‖ = ‖exp (I * lam * (b - a)) - κ‖ := by
    rw [hea, show e b * exp (I * lam * (b - a)) - κ * e b =
      e b * (exp (I * lam * (b - a)) - κ) by ring, norm_mul, hen, one_mul]
  have hstart : ‖W a‖ ≤ (‖W b - κ * W a‖ + ε * (b - a)) / δ := by
    apply (le_div_iff₀ hδ).2
    calc
      ‖W a‖ * δ ≤ ‖W a‖ * ‖e a - κ * e b‖ := by rw [hcoef]; gcongr
      _ = ‖(e a - κ * e b) * W a‖ := by rw [norm_mul, mul_comm]
      _ = ‖e b * (W b - κ * W a) - (e b * W b - e a * W a)‖ := by congr 1; ring
      _ ≤ ‖e b * (W b - κ * W a)‖ + ‖e b * W b - e a * W a‖ := norm_sub_le _ _
      _ ≤ ‖W b - κ * W a‖ + ε * (b - a) := by
        rw [norm_mul, hen, one_mul]
        exact add_le_add le_rfl (hinc ⟨hab, le_rfl⟩)
  calc
    ‖W x‖ = ‖e x * W x‖ := by rw [norm_mul, hen, one_mul]
    _ = ‖e a * W a + (e x * W x - e a * W a)‖ := by congr 1; ring
    _ ≤ ‖e a * W a‖ + ‖e x * W x - e a * W a‖ := norm_add_le _ _
    _ ≤ ‖W a‖ + ε * (x - a) := by
      rw [norm_mul, hen, one_mul]
      exact add_le_add le_rfl (hinc hx)
    _ ≤ (‖W b - κ * W a‖ + ε * (b - a)) / δ + ε * (b - a) :=
      add_le_add hstart (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hε)

/-- A nonresonant periodic transport equation has at most one locally absolutely
    continuous solution. No regularity of the forcing is needed for uniqueness. -/
theorem eq_of_periodic_transport {lam S : ℝ} {Z W F : ℝ → ℂ}
    (hS : 0 < S) (hnr : exp (I * lam * S) ≠ 1)
    (hZp : Function.Periodic Z S) (hWp : Function.Periodic W S)
    (hZac : ∀ a b, AbsolutelyContinuousOnInterval Z a b)
    (hWac : ∀ a b, AbsolutelyContinuousOnInterval W a b)
    (hZd : ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + F t)) t)
    (hWd : ∀ᵐ t, HasDerivAt W (I * (lam * W t + F t)) t) : Z = W := by
  have hD : ∀ᵐ t, HasDerivAt (fun t ↦ Z t - W t)
      (I * (lam * (Z t - W t) + (0 : ℂ))) t := by
    filter_upwards [hZd, hWd] with t htZ htW
    convert htZ.sub htW using 1
    ring
  have hδ : 0 < ‖exp (I * lam * S) - 1‖ := norm_pos_iff.2 (sub_ne_zero.mpr hnr)
  funext t
  have hb := norm_transport_le_of_boundary (lam := lam) (a := t) (b := t + S)
    (ε := 0) (δ := ‖exp (I * lam * S) - 1‖) (κ := 1)
    (W := fun t ↦ Z t - W t) (F := fun _ ↦ 0)
    (by linarith) le_rfl hδ ((hZac _ _).sub (hWac _ _)) intervalIntegrable_const
    (hD.mono fun _ ht _ ↦ ht) (by simp)
    (by simp) (x := t) ⟨le_rfl, by linarith⟩
  have hz : ‖Z t - W t‖ ≤ 0 := by simpa [hZp t, hWp t] using hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- A nonresonant periodic solution inherits every translation character of its forcing.
    In particular, a quarter-period character follows without choosing pointwise
    representatives of the vorticity's planar rotation character. -/
theorem transport_character_of_periodic {lam S T : ℝ} {κ : ℂ} {Z F : ℝ → ℂ}
    (hS : 0 < S) (hnr : exp (I * lam * S) ≠ 1) (hZp : Function.Periodic Z S)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval Z a b)
    (hd : ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + F t)) t)
    (hF : ∀ t, F (t + T) = κ * F t) : ∀ t, Z (t + T) = κ * Z t := by
  have hshift (a b : ℝ) : AbsolutelyContinuousOnInterval (fun t ↦ Z (t + T)) a b := by
    change AbsolutelyContinuousOnInterval (Z ∘ fun t ↦ t + T) a b
    have hL : LipschitzWith 1 (fun t : ℝ ↦ t + T) :=
      LipschitzWith.of_dist_le_mul fun x y ↦ by simp
    refine AbsolutelyContinuousOnInterval.comp_monotoneOn (hac (a + T) (b + T))
      hL.lipschitzOnWith (fun x _ y _ hxy ↦ by linarith) ?_
    intro t ht
    rw [mem_uIcc] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ⟨by dsimp; linarith [ht.1], by dsimp; linarith [ht.2]⟩
    · exact Or.inr ⟨by dsimp; linarith [ht.1], by dsimp; linarith [ht.2]⟩
  have hdshift : ∀ᵐ t, HasDerivAt (fun t ↦ Z (t + T))
      (I * (lam * Z (t + T) + κ * F t)) t := by
    filter_upwards [(measurePreserving_add_right volume T).quasiMeasurePreserving.ae hd] with t ht
    simpa only [Function.comp_def, id_eq, one_smul, hF t] using!
      ht.scomp t ((hasDerivAt_id t).add_const T)
  have hdmul : ∀ᵐ t, HasDerivAt (fun t ↦ κ * Z t)
      (I * (lam * (κ * Z t) + κ * F t)) t := by
    filter_upwards [hd] with t ht
    convert ht.const_mul κ using 1
    ring
  have heq := eq_of_periodic_transport hS hnr
    (Z := fun t ↦ Z (t + T)) (W := fun t ↦ κ * Z t) (F := fun t ↦ κ * F t)
    (fun t ↦ by simpa only [add_right_comm] using hZp (t + T))
    (fun t ↦ congrArg (κ * ·) (hZp t)) hshift
    (fun a b ↦ (hac a b).const_smul κ) hdshift hdmul
  exact fun t ↦ congrFun heq t

/-- Supremum bounds for two complex pairings give their finite-interval integral error.
    The vorticities need not be differentiable. -/
theorem abs_integral_pairing_sub_le {a b A B M ε : ℝ} {V Ω G H : ℝ → ℂ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVG : IntervalIntegrable (fun t ↦ (V t * conj (G t)).re) volume a b)
    (hΩH : IntervalIntegrable (fun t ↦ (Ω t * conj (H t)).re) volume a b)
    (hV : ∀ t ∈ Icc a b, ‖V t - Ω t‖ ≤ A)
    (hΩ : ∀ t ∈ Icc a b, ‖Ω t‖ ≤ B)
    (hG : ∀ t ∈ Icc a b, ‖G t‖ ≤ M)
    (hGH : ∀ t ∈ Icc a b, ‖G t - H t‖ ≤ ε) :
    |(∫ t in a..b, (V t * conj (G t)).re) -
      ∫ t in a..b, (Ω t * conj (H t)).re| ≤ (A * M + B * ε) * (b - a) := by
  rw [← intervalIntegral.integral_sub hVG hΩH]
  have hpt (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(V t * conj (G t)).re - (Ω t * conj (H t)).re‖ ≤ A * M + B * ε := by
    rw [Real.norm_eq_abs, ← sub_re]
    calc
      |(V t * conj (G t) - Ω t * conj (H t)).re|
          ≤ ‖V t * conj (G t) - Ω t * conj (H t)‖ := abs_re_le_norm _
      _ = ‖(V t - Ω t) * conj (G t) + Ω t * conj (G t - H t)‖ := by
        rw [map_sub]; congr 1; ring
      _ ≤ ‖(V t - Ω t) * conj (G t)‖ + ‖Ω t * conj (G t - H t)‖ := norm_add_le _ _
      _ = ‖V t - Ω t‖ * ‖G t‖ + ‖Ω t‖ * ‖G t - H t‖ := by simp only [norm_mul, norm_conj]
      _ ≤ A * M + B * ε := add_le_add
        (mul_le_mul (hV t ht) (hG t ht) (norm_nonneg _) hA)
        (mul_le_mul (hΩ t ht) (hGH t ht) (norm_nonneg _) hB)
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun t ht ↦ hpt t (by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] using hbnd

end NoEmbeddedEigenvalues
