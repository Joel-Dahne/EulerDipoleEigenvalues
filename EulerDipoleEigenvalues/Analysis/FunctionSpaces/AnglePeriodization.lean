module

public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.LineMollifier

/-!
# Periodization of compactly supported angular test functions

Finite angular support makes the integer periodization locally a finite sum.
Blueprint: `def:angular-periodization`, `lem:angular-periodization` (proved).
This supplies the periodic tests used by the weak action-angle transport and full forward
chain rules. Periodization commutes with both coordinate derivatives.
The periodization, integral unfolding, and normalized angular partition have no
admitted dependencies.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A uniform bound on the second coordinate of the support. -/
def HasBoundedSndSupport {E : Type*} [Zero E] (f : ℝ × ℝ → E) : Prop :=
  ∃ R : ℝ, ∀ q, f q ≠ 0 → |q.2| ≤ R

/-- Integer periodization in the second variable. -/
def periodizeSnd {E : Type*} [AddCommMonoid E] (f : ℝ × ℝ → E) (q : ℝ × ℝ) : E :=
  ∑ᶠ n : ℤ, f (q.1, q.2 + n)

section Basic

variable {E : Type*} [NormedAddCommGroup E]
variable {f : ℝ × ℝ → E}

private theorem angle_support_subset {R r : ℝ} {N : ℕ}
    (hR : ∀ q, f q ≠ 0 → |q.2| ≤ R) (hN : R + r ≤ N) {q : ℝ × ℝ} (hq : |q.2| ≤ r) :
    Function.support (fun n : ℤ ↦ f (q.1, q.2 + n)) ⊆
      (Finset.Icc (-(N : ℤ)) N : Set ℤ) := by
  intro n hn
  have hb := abs_le.mp (hR (q.1, q.2 + n) hn)
  have hq' := abs_le.mp hq
  have hlo : -(N : ℝ) ≤ n := by linarith
  have hhi : (n : ℝ) ≤ N := by linarith
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem periodizeSnd_eq_sum {R r : ℝ} {N : ℕ}
    (hR : ∀ q, f q ≠ 0 → |q.2| ≤ R) (hN : R + r ≤ N) {q : ℝ × ℝ} (hq : |q.2| ≤ r) :
    periodizeSnd f q = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f (q.1, q.2 + n) :=
  finsum_eq_sum_of_support_subset _ (angle_support_subset hR hN hq)

theorem periodizeSnd_periodic (q : ℝ × ℝ) :
    periodizeSnd f (q.1, q.2 + 1) = periodizeSnd f q := by
  have he := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    (f := fun n : ℤ ↦ f (q.1, q.2 + n))
  change (∑ᶠ n : ℤ, f (q.1, q.2 + 1 + n)) = ∑ᶠ n : ℤ, f (q.1, q.2 + n)
  convert he using 1
  congr 1
  funext n
  congr 1
  simp [Equiv.addRight, add_comm, add_left_comm]

theorem HasCompactSupport.hasBoundedSndSupport (hf : HasCompactSupport f) :
    HasBoundedSndSupport f := by
  obtain ⟨R, hR⟩ := hf.exists_bound_of_continuousOn
    (f := fun q : ℝ × ℝ ↦ |q.2|) (continuous_abs.comp continuous_snd).continuousOn
  exact ⟨R, fun q hq ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hR q (subset_closure hq)⟩

variable [NormedSpace ℝ E]

theorem HasBoundedSndSupport.partialY (hf : HasBoundedSndSupport f) :
    HasBoundedSndSupport (partialY f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun q hq ↦ ?_⟩
  have hs : Function.support (fun θ ↦ f (q.1, θ)) ⊆ Icc (-R) R :=
    fun θ hθ ↦ abs_le.mp (hR (q.1, θ) hθ)
  have hd : q.2 ∈ tsupport (fun θ ↦ f (q.1, θ)) := support_deriv_subset hq
  exact abs_le.mpr (closure_minimal hs isClosed_Icc hd)

theorem HasBoundedSndSupport.partialX (hf : HasBoundedSndSupport f) :
    HasBoundedSndSupport (partialX f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun q hq ↦ ?_⟩
  by_contra hn
  have hz : (fun x ↦ f (x, q.2)) = 0 := by
    funext x
    by_contra hx
    exact hn (hR (x, q.2) hx)
  apply hq
  change deriv (fun x ↦ f (x, q.2)) q.1 = 0
  rw [hz]
  exact (hasDerivAt_const q.1 (0 : E)).deriv

theorem contDiff_periodizeSnd {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hs : HasBoundedSndSupport f) : ContDiff ℝ n (periodizeSnd f) := by
  obtain ⟨R, hR⟩ := hs
  rw [contDiff_iff_contDiffAt]
  intro q
  let r := |q.2| + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (R + r)
  have hsum : ContDiff ℝ n (fun z : ℝ × ℝ ↦
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, f (z.1, z.2 + m)) :=
    ContDiff.sum (fun m _ ↦ hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)))
  apply hsum.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(continuous_abs.comp continuous_snd).continuousAt.eventually
    (eventually_lt_nhds (show |q.2| < r by dsimp [r]; linarith))] with z hz
  exact periodizeSnd_eq_sum hR hN.le hz.le

theorem partialX_periodizeSnd (hf : ContDiff ℝ 1 f) (hs : HasBoundedSndSupport f)
    (q : ℝ × ℝ) : partialX (periodizeSnd f) q = periodizeSnd (partialX f) q := by
  obtain ⟨R, hR⟩ := hs
  obtain ⟨D, hD⟩ := (show HasBoundedSndSupport f from ⟨R, hR⟩).partialX
  obtain ⟨N, hN⟩ := exists_nat_gt (max R D + |q.2|)
  have hNR : R + |q.2| ≤ N := by linarith [le_max_left R D]
  have hND : D + |q.2| ≤ N := by linarith [le_max_right R D]
  have hd : HasDerivAt (fun x ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      f (x, q.2 + m)) (∑ m ∈ Finset.Icc (-(N : ℤ)) N, partialX f (q.1, q.2 + m)) q.1 := by
    apply HasDerivAt.fun_sum
    intro m _
    exact hasDerivAt_partialX (hf.differentiable one_ne_zero (q.1, q.2 + m))
  have he : (fun x ↦ periodizeSnd f (x, q.2)) =
      (fun x ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) N, f (x, q.2 + m)) :=
    funext fun x ↦ periodizeSnd_eq_sum hR hNR le_rfl
  change deriv (fun x ↦ periodizeSnd f (x, q.2)) q.1 = _
  rw [he, hd.deriv]
  exact (periodizeSnd_eq_sum hD hND le_rfl).symm

theorem partialY_periodizeSnd (hf : ContDiff ℝ 1 f) (hs : HasBoundedSndSupport f)
    (q : ℝ × ℝ) : partialY (periodizeSnd f) q = periodizeSnd (partialY f) q := by
  obtain ⟨R, hR⟩ := hs
  obtain ⟨D, hD⟩ := (show HasBoundedSndSupport f from ⟨R, hR⟩).partialY
  let r := |q.2| + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (max R D + r)
  have hNR : R + r ≤ N := le_of_lt (by linarith [le_max_left R D])
  have hND : D + r ≤ N := le_of_lt (by linarith [le_max_right R D])
  have hd : HasDerivAt (fun θ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      f (q.1, θ + m)) (∑ m ∈ Finset.Icc (-(N : ℤ)) N, partialY f (q.1, q.2 + m)) q.2 := by
    apply HasDerivAt.fun_sum
    intro m _
    simpa only [Function.comp_def, one_smul, id_eq] using
      (hasDerivAt_partialY (hf.differentiable one_ne_zero (q.1, q.2 + m))).scomp
        q.2 ((hasDerivAt_id q.2).add_const (m : ℝ))
  have he : (fun θ ↦ periodizeSnd f (q.1, θ)) =ᶠ[𝓝 q.2]
      (fun θ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) N, f (q.1, θ + m)) := by
    filter_upwards [continuous_abs.continuousAt.eventually
      (eventually_lt_nhds (show |q.2| < r by dsimp [r]; linarith))] with θ hθ
    exact periodizeSnd_eq_sum hR hNR hθ.le
  change deriv (fun θ ↦ periodizeSnd f (q.1, θ)) q.2 = _
  rw [(hd.congr_of_eventuallyEq he).deriv]
  exact (periodizeSnd_eq_sum hD hND (by dsimp [r]; linarith)).symm

omit [NormedSpace ℝ E] in
theorem periodizeSnd_eq_zero {a b : ℝ} (hs : ∀ q, q.1 ∉ Icc a b → f q = 0)
    {q : ℝ × ℝ} (hq : q.1 ∉ Icc a b) : periodizeSnd f q = 0 := by
  have hz : ∀ m : ℤ, f (q.1, q.2 + m) = 0 := fun m ↦ hs (q.1, q.2 + m) hq
  simp only [periodizeSnd, hz, finsum_zero]

end Basic

/-- A translate of the fundamental angular window, with no restriction on the first variable. -/
def angleWindow (n : ℤ) : Set (ℝ × ℝ) :=
  univ ×ˢ Ico ((n : ℝ) - 1 / 4) ((n : ℝ) + 3 / 4)

private theorem measurableSet_angleWindow (n : ℤ) : MeasurableSet (angleWindow n) :=
  MeasurableSet.univ.prod measurableSet_Ico

private theorem measurePreserving_angleShift (n : ℤ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, q.2 + n)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id volume).prod (measurePreserving_add_right volume (n : ℝ))

private theorem iUnion_angleWindow : (⋃ n : ℤ, angleWindow n) = univ := by
  apply eq_univ_of_forall
  intro q
  apply mem_iUnion.mpr
  refine ⟨⌊q.2 + 1 / 4⌋, mem_univ _, ?_, ?_⟩
  · linarith [Int.floor_le (q.2 + 1 / 4)]
  · linarith [Int.lt_floor_add_one (q.2 + 1 / 4)]

private theorem pairwiseDisjoint_angleWindow :
    Pairwise (fun m n ↦ Disjoint (angleWindow m) (angleWindow n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro q hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hgap : (m : ℝ) + 1 ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [hm.2.2, hn.2.1]
  · have hgap : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [hn.2.2, hm.2.1]

private theorem integral_angleWindow_shift (f : ℝ × ℝ → ℂ) (n : ℤ) :
    (∫ q in angleWindow n, f q) = ∫ q in angleWindow 0, f (q.1, q.2 + n) := by
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight (n : ℝ))
  have hmp : MeasurePreserving e volume volume := measurePreserving_angleShift n
  have hpre : e ⁻¹' angleWindow n = angleWindow 0 := by
    ext q
    change (q.1 ∈ univ ∧ q.2 + n ∈ Ico ((n : ℝ) - 1 / 4) ((n : ℝ) + 3 / 4)) ↔
      (q.1 ∈ univ ∧ q.2 ∈ Ico ((0 : ℤ) - 1 / 4 : ℝ) ((0 : ℤ) + 3 / 4 : ℝ))
    simp only [mem_univ, true_and, mem_Ico, Int.cast_zero, zero_sub, zero_add]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hi := hmp.setIntegral_preimage_emb e.measurableEmbedding f (angleWindow n)
  rw [hpre] at hi
  exact hi.symm

private theorem angleWindow_zero_bound {q : ℝ × ℝ} (hq : q ∈ angleWindow 0) : |q.2| ≤ 1 := by
  have hh : -(1 / 4 : ℝ) ≤ q.2 ∧ q.2 < 3 / 4 := by
    simpa only [angleWindow, mem_prod, mem_univ, true_and, mem_Ico,
      Int.cast_zero, zero_sub, zero_add] using hq
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-- Unfolding a finite-angular-support function from one period gives its full integral. -/
theorem integral_periodizeSnd {f : ℝ × ℝ → ℂ} (hf : Integrable f)
    (hs : HasBoundedSndSupport f) :
    (∫ q, f q) = ∫ q in angleWindow 0, periodizeSnd f q := by
  obtain ⟨R, hR⟩ := hs
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
  have hz : ∀ n ∉ Finset.Icc (-(N : ℤ)) N,
      (∫ q in angleWindow 0, f (q.1, q.2 + n)) = 0 := by
    intro n hn
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_angleWindow 0)] with q hq
    change f (q.1, q.2 + n) = 0
    by_contra hne
    exact hn (angle_support_subset hR hN.le (angleWindow_zero_bound hq) hne)
  have hshift : ∀ n : ℤ, Integrable (fun q : ℝ × ℝ ↦ f (q.1, q.2 + n)) := fun n ↦
    ((measurePreserving_angleShift n).integrable_comp hf.aestronglyMeasurable).mpr hf
  calc
    _ = ∫ q in ⋃ n : ℤ, angleWindow n, f q := by rw [iUnion_angleWindow, setIntegral_univ]
    _ = ∑' n : ℤ, ∫ q in angleWindow n, f q :=
      integral_iUnion measurableSet_angleWindow pairwiseDisjoint_angleWindow hf.integrableOn
    _ = ∑' n : ℤ, ∫ q in angleWindow 0, f (q.1, q.2 + n) := by
      congr 1
      funext n
      exact integral_angleWindow_shift f n
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ∫ q in angleWindow 0, f (q.1, q.2 + n) := tsum_eq_sum hz
    _ = ∫ q in angleWindow 0, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f (q.1, q.2 + n) :=
      (integral_finsetSum _ (fun n _ ↦ (hshift n).integrableOn)).symm
    _ = _ := by
      apply setIntegral_congr_fun (measurableSet_angleWindow 0)
      intro q hq
      exact (periodizeSnd_eq_sum hR hN.le (angleWindow_zero_bound hq)).symm

theorem periodizeSnd_mul_periodic {A φ : ℝ × ℝ → ℂ}
    (hA : ∀ q : ℝ × ℝ, A (q.1, q.2 + 1) = A q) (q : ℝ × ℝ) :
    periodizeSnd (fun z ↦ A z * φ z) q = A q * periodizeSnd φ q := by
  have hp : Function.Periodic (fun θ ↦ A (q.1, θ)) 1 := fun θ ↦ hA (q.1, θ)
  have he (m : ℤ) : A (q.1, q.2 + m) = A q := by
    simpa only [mul_one] using (hp.int_mul m) q.2
  unfold periodizeSnd
  simp_rw [he]
  simpa only [mul_comm] using (finsum_mul (fun m : ℤ ↦ φ (q.1, q.2 + m)) (A q)).symm

/-- Periodic multipliers may be carried through the unfolding identity. -/
theorem integral_mul_periodizeSnd {A φ : ℝ × ℝ → ℂ}
    (hA : ∀ q : ℝ × ℝ, A (q.1, q.2 + 1) = A q)
    (hs : HasBoundedSndSupport φ) (hi : Integrable (fun q ↦ A q * φ q)) :
    (∫ q, A q * φ q) = ∫ q in angleWindow 0, A q * periodizeSnd φ q := by
  have hprod : HasBoundedSndSupport (fun q ↦ A q * φ q) := by
    obtain ⟨R, hR⟩ := hs
    refine ⟨R, fun q hq ↦ hR q ?_⟩
    intro hz
    exact hq (by simp [hz])
  rw [integral_periodizeSnd hi hprod]
  apply setIntegral_congr_fun (measurableSet_angleWindow 0)
  intro q _
  exact periodizeSnd_mul_periodic hA q

/-- Unfolding on a horizontal strip only needs periodicity on that strip. -/
theorem integral_mul_periodizeSnd_strip {U : Set ℝ} (hU : MeasurableSet U)
    {A φ : ℝ × ℝ → ℂ}
    (hA : ∀ q : ℝ × ℝ, q.1 ∈ U → A (q.1, q.2 + 1) = A q)
    (hs : HasBoundedSndSupport φ) (hsub : tsupport φ ⊆ U ×ˢ univ)
    (hi : Integrable (fun q ↦ A q * φ q)) :
    (∫ q, A q * φ q) =
      ∫ q in U ×ˢ Ico (-1 / 4 : ℝ) (3 / 4), A q * periodizeSnd φ q := by
  classical
  let V := U ×ˢ (univ : Set ℝ)
  let B := V.indicator A
  have hV : MeasurableSet V := hU.prod MeasurableSet.univ
  have heq : (fun q ↦ B q * φ q) = (fun q ↦ A q * φ q) := by
    funext q
    by_cases hq : q ∈ V
    · simp [B, hq]
    · have hz : φ q = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ hq (hsub ht))
      simp [hz]
  have hB : ∀ q : ℝ × ℝ, B (q.1, q.2 + 1) = B q := by
    intro q
    by_cases hq : q.1 ∈ U
    · simp [B, V, hq, hA q hq]
    · simp [B, V, hq]
  have him : Integrable (fun q ↦ B q * φ q) := by rwa [heq]
  rw [← heq, integral_mul_periodizeSnd hB hs him]
  have hind : (fun q ↦ B q * periodizeSnd φ q) =
      V.indicator (fun q ↦ A q * periodizeSnd φ q) := by
    funext q
    by_cases hq : q ∈ V <;> simp [B, hq]
  rw [hind, integral_indicator hV, Measure.restrict_restrict hV]
  have hset : V ∩ angleWindow 0 = U ×ˢ Ico (-1 / 4 : ℝ) (3 / 4) := by
    ext q
    norm_num [V, angleWindow]
  rw [hset]

/-- A smooth angular bump used to build a periodic partition of unity. -/
private def angleBump (q : ℝ × ℝ) : ℝ := stdBump q.2

private theorem contDiff_angleBump : ContDiff ℝ ∞ angleBump :=
  contDiff_stdBump.comp contDiff_snd

private theorem angleBump_support_le (q : ℝ × ℝ) (hq : angleBump q ≠ 0) : |q.2| ≤ 1 := by
  have h : q.2 ∈ Function.support stdBump := hq
  rw [support_stdBump] at h
  exact (abs_lt.mpr h).le

private theorem bounded_angleBump : HasBoundedSndSupport angleBump :=
  ⟨1, angleBump_support_le⟩

private theorem periodize_angleBump_pos (q : ℝ × ℝ) : 0 < periodizeSnd angleBump q := by
  let n : ℤ := -⌊q.2 + 1 / 4⌋
  have hlo := Int.floor_le (q.2 + 1 / 4)
  have hhi := Int.lt_floor_add_one (q.2 + 1 / 4)
  have hθ : q.2 + (n : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
    dsimp [n]
    push_cast
    constructor <;> linarith
  have hnz : angleBump (q.1, q.2 + n) ≠ 0 := by
    change q.2 + (n : ℝ) ∈ Function.support stdBump
    rwa [support_stdBump]
  have hp : 0 < angleBump (q.1, q.2 + n) :=
    lt_of_le_of_ne (stdBump_nonneg _) (Ne.symm hnz)
  obtain ⟨R, hR⟩ := bounded_angleBump
  obtain ⟨N, hN⟩ := exists_nat_gt (R + |q.2|)
  have hn := angle_support_subset hR hN.le (le_refl |q.2|) hnz
  rw [periodizeSnd_eq_sum hR hN.le (le_refl |q.2|)]
  exact hp.trans_le (Finset.single_le_sum
    (f := fun m : ℤ ↦ angleBump (q.1, q.2 + m))
    (fun m _ ↦ stdBump_nonneg (q.2 + m)) hn)

/-- A smooth angular cutoff whose integer translates sum to one. -/
@[no_expose] def anglePartition (q : ℝ × ℝ) : ℝ := angleBump q / periodizeSnd angleBump q

theorem contDiff_anglePartition : ContDiff ℝ ∞ anglePartition :=
  contDiff_angleBump.div (contDiff_periodizeSnd contDiff_angleBump bounded_angleBump)
    (fun q ↦ (periodize_angleBump_pos q).ne')

theorem anglePartition_support_le (q : ℝ × ℝ)
    (hq : anglePartition q ≠ 0) : |q.2| ≤ 1 := by
  apply angleBump_support_le q
  intro hz
  exact hq (by simp [anglePartition, hz])

theorem bounded_anglePartition : HasBoundedSndSupport anglePartition :=
  ⟨1, anglePartition_support_le⟩

theorem periodize_anglePartition (q : ℝ × ℝ) : periodizeSnd anglePartition q = 1 := by
  have hR : ∀ q, angleBump q ≠ 0 → |q.2| ≤ 1 := angleBump_support_le
  have hρ : ∀ q, anglePartition q ≠ 0 → |q.2| ≤ 1 := anglePartition_support_le
  obtain ⟨N, hN⟩ := exists_nat_gt (1 + |q.2|)
  have hp : Function.Periodic (fun θ ↦ periodizeSnd angleBump (q.1, θ)) 1 :=
    fun θ ↦ periodizeSnd_periodic (q.1, θ)
  have he (m : ℤ) : periodizeSnd angleBump (q.1, q.2 + m) = periodizeSnd angleBump q := by
    simpa only [mul_one] using (hp.int_mul m) q.2
  rw [periodizeSnd_eq_sum hρ hN.le (le_refl |q.2|)]
  simp_rw [anglePartition, he]
  rw [← Finset.sum_div, ← periodizeSnd_eq_sum hR hN.le (le_refl |q.2|)]
  exact div_self (periodize_angleBump_pos q).ne'

/-- Multiplication by the angular partition turns periodic data into a compact angular test. -/
def cutoffPeriodicSnd (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ := (anglePartition q : ℂ) * F q

private theorem cutoffPeriodicSnd_support_le (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ)
    (hq : cutoffPeriodicSnd F q ≠ 0) : |q.2| ≤ 1 := by
  apply anglePartition_support_le q
  intro hz
  exact hq (by simp [cutoffPeriodicSnd, hz])

theorem bounded_cutoffPeriodicSnd (F : ℝ × ℝ → ℂ) :
    HasBoundedSndSupport (cutoffPeriodicSnd F) := ⟨1, cutoffPeriodicSnd_support_le F⟩

theorem periodize_cutoffPeriodicSnd {F : ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q) (q : ℝ × ℝ) :
    periodizeSnd (cutoffPeriodicSnd F) q = F q := by
  have hρ : ∀ q, anglePartition q ≠ 0 → |q.2| ≤ 1 := anglePartition_support_le
  have hσ : ∀ q, cutoffPeriodicSnd F q ≠ 0 → |q.2| ≤ 1 := cutoffPeriodicSnd_support_le F
  obtain ⟨N, hN⟩ := exists_nat_gt (1 + |q.2|)
  have hp : Function.Periodic (fun θ ↦ F (q.1, θ)) 1 := fun θ ↦ hper (q.1, θ)
  have he (m : ℤ) : F (q.1, q.2 + m) = F q := by
    simpa only [mul_one] using (hp.int_mul m) q.2
  rw [periodizeSnd_eq_sum hσ hN.le (le_refl |q.2|)]
  simp_rw [cutoffPeriodicSnd, he]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum,
    ← periodizeSnd_eq_sum hρ hN.le (le_refl |q.2|), periodize_anglePartition]
  simp

theorem isTestFunctionOn_cutoffPeriodicSnd {F : ℝ × ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hF : ContDiff ℝ ∞ F)
    (hs : ∀ q, q.1 ∉ Icc a b → F q = 0) :
    IsTestFunctionOn (Ioo 0 1 ×ˢ (univ : Set ℝ)) (cutoffPeriodicSnd F) := by
  have hc : ContDiff ℝ ∞ (cutoffPeriodicSnd F) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_anglePartition).mul hF
  have hz : ∀ q ∉ Icc a b ×ˢ Icc (-1 : ℝ) 1, cutoffPeriodicSnd F q = 0 := by
    intro q hq
    by_cases hlev : q.1 ∈ Icc a b
    · have hθ : q.2 ∉ Icc (-1 : ℝ) 1 := fun h ↦ hq ⟨hlev, h⟩
      have hp : anglePartition q = 0 := by
        by_contra hn
        exact hθ (abs_le.mp (anglePartition_support_le q hn))
      simp [cutoffPeriodicSnd, hp]
    · simp [cutoffPeriodicSnd, hs q hlev]
  have ht : tsupport (cutoffPeriodicSnd F) ⊆ Icc a b ×ˢ Icc (-1 : ℝ) 1 :=
    closure_minimal (fun q hq ↦ by_contra fun hn ↦ hq (hz q hn)) (isClosed_Icc.prod isClosed_Icc)
  exact ⟨hc, HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) hz,
    fun q hq ↦ ⟨⟨lt_of_lt_of_le ha (ht hq).1.1, lt_of_le_of_lt (ht hq).1.2 hb⟩, mem_univ _⟩⟩

theorem periodize_partialY_cutoffPeriodicSnd {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (q : ℝ × ℝ) : periodizeSnd (partialY (cutoffPeriodicSnd F)) q = partialY F q := by
  have hc : ContDiff ℝ 1 (cutoffPeriodicSnd F) :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_anglePartition).mul hF).of_le (by simp)
  rw [← partialY_periodizeSnd hc (bounded_cutoffPeriodicSnd F)]
  rw [show periodizeSnd (cutoffPeriodicSnd F) = F from funext (periodize_cutoffPeriodicSnd hper)]

end EulerDipoleEigenvalues
