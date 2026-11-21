import NoEmbeddedEigenvalues.Setup.TorusTransportTests

/-! # Periodization, weak transport, and Sobolev regularity of lifts -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex ComplexConjugate
open scoped Topology ContDiff InnerProductSpace Real

/-! ### Periodization of compactly supported functions -/

section Periodize

/-- The translate `p + 2πn`. -/
def liftShift (n : ℤ × ℤ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + n.1 * (2 * π), p.2 + n.2 * (2 * π))

/-- The `2π`-periodization `∑ₙ φ(p + 2πn)`. -/
def liftPeriodize (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := ∑ᶠ n : ℤ × ℤ, φ (liftShift n p)

/-- The frequencies `|n₁|, |n₂| ≤ N`. -/
def shiftBox (N : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N

theorem contDiff_liftShift {k : ℕ∞ω} (n : ℤ × ℤ) : ContDiff ℝ k (liftShift n) :=
  (contDiff_fst.add contDiff_const).prodMk (contDiff_snd.add contDiff_const)

private theorem int_bound {m : ℤ} {N : ℕ} {B : ℝ} (h : |(m : ℝ) * (2 * π)| ≤ B)
    (hN : B ≤ N) : -(N : ℤ) ≤ m ∧ m ≤ N := by
  have hpi : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have h1 : |(m : ℝ)| ≤ N := by
    rw [abs_mul, abs_of_pos Real.two_pi_pos] at h
    nlinarith [abs_nonneg (m : ℝ)]
  rw [abs_le] at h1
  exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩

private theorem shift_support_subset {φ : ℝ × ℝ → ℂ} {R r : ℝ} {N : ℕ}
    (hR : ∀ q, φ q ≠ 0 → ‖q‖ ≤ R) (hN : R + r ≤ N) {p : ℝ × ℝ} (hp : ‖p‖ ≤ r) :
    Function.support (fun n ↦ φ (liftShift n p)) ⊆ (shiftBox N : Set (ℤ × ℤ)) := by
  intro n hn
  have hq := hR _ hn
  have key (a : ℝ) (m : ℤ) (ha : |a| ≤ r) (hm : |a + m * (2 * π)| ≤ R) :
      -(N : ℤ) ≤ m ∧ m ≤ N := by
    refine int_bound (B := R + r) ?_ hN
    calc |(m : ℝ) * (2 * π)| = |(a + m * (2 * π)) - a| := by ring_nf
      _ ≤ |a + m * (2 * π)| + |a| := abs_sub _ _
      _ ≤ R + r := add_le_add hm ha
  have h1 := key p.1 n.1 ((norm_fst_le p).trans hp) ((norm_fst_le _).trans hq)
  have h2 := key p.2 n.2 ((norm_snd_le p).trans hp) ((norm_snd_le _).trans hq)
  simp only [shiftBox, Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
  exact ⟨h1, h2⟩

theorem liftPeriodize_eq_sum {φ : ℝ × ℝ → ℂ} {R r : ℝ} {N : ℕ}
    (hR : ∀ q, φ q ≠ 0 → ‖q‖ ≤ R) (hN : R + r ≤ N) {p : ℝ × ℝ} (hp : ‖p‖ ≤ r) :
    liftPeriodize φ p = ∑ n ∈ shiftBox N, φ (liftShift n p) :=
  finsum_eq_sum_of_support_subset _ (shift_support_subset hR hN hp)

theorem exists_norm_bound_tsupport {φ : ℝ × ℝ → ℂ} (hs : HasCompactSupport φ) :
    ∃ R, ∀ q ∈ tsupport φ, ‖q‖ ≤ R := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  exact ⟨R, fun q hq ↦ mem_closedBall_zero_iff.1 (hR hq)⟩

theorem isPeriodicLift_liftPeriodize (φ : ℝ × ℝ → ℂ) : IsPeriodicLift (liftPeriodize φ) := by
  intro p
  constructor
  · have he := finsum_comp_equiv (Equiv.addRight ((1, 0) : ℤ × ℤ))
      (f := fun n : ℤ × ℤ ↦ φ (liftShift n p))
    refine Eq.trans ?_ he
    unfold liftPeriodize
    congr 1
    funext n
    congr 1
    simp only [liftShift, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add, Int.cast_add,
      Int.cast_one, add_zero]
    ext
    · simp only
      ring
    · rfl
  · have he := finsum_comp_equiv (Equiv.addRight ((0, 1) : ℤ × ℤ))
      (f := fun n : ℤ × ℤ ↦ φ (liftShift n p))
    refine Eq.trans ?_ he
    unfold liftPeriodize
    congr 1
    funext n
    congr 1
    simp only [liftShift, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add, Int.cast_add,
      Int.cast_one, add_zero]
    ext
    · rfl
    · simp only
      ring

theorem contDiff_liftPeriodize {k : ℕ∞ω} {φ : ℝ × ℝ → ℂ} (hf : ContDiff ℝ k φ)
    (hs : HasCompactSupport φ) : ContDiff ℝ k (liftPeriodize φ) := by
  obtain ⟨R, hR⟩ := exists_norm_bound_tsupport hs
  have hR' : ∀ q, φ q ≠ 0 → ‖q‖ ≤ R := fun q hq ↦ hR q (subset_tsupport _ hq)
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨N, hN⟩ := exists_nat_gt (R + (‖p‖ + 1))
  have hsum : ContDiff ℝ k (fun z ↦ ∑ m ∈ shiftBox N, φ (liftShift m z)) :=
    ContDiff.sum fun m _ ↦ hf.comp (contDiff_liftShift m)
  apply hsum.contDiffAt.congr_of_eventuallyEq
  filter_upwards [continuous_norm.continuousAt.eventually
    (eventually_lt_nhds (show ‖p‖ < ‖p‖ + 1 by linarith))] with z hz
  exact liftPeriodize_eq_sum hR' hN.le hz.le

theorem continuous_liftPeriodize {φ : ℝ × ℝ → ℂ} (hf : Continuous φ)
    (hs : HasCompactSupport φ) : Continuous (liftPeriodize φ) :=
  (contDiff_liftPeriodize (k := 0) (contDiff_zero.2 hf) hs).continuous

theorem partialX_liftPeriodize {φ : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) : partialX (liftPeriodize φ) = liftPeriodize (partialX φ) := by
  funext p
  obtain ⟨R, hR⟩ := exists_norm_bound_tsupport hs
  have hR0 : ∀ q, φ q ≠ 0 → ‖q‖ ≤ R := fun q hq ↦ hR q (subset_tsupport _ hq)
  have hR1 : ∀ q, partialX φ q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (tsupport_partialX_subset φ (subset_tsupport _ hq))
  obtain ⟨N, hN⟩ := exists_nat_gt (R + (‖p‖ + 1))
  have hd : HasDerivAt (fun s ↦ ∑ m ∈ shiftBox N, φ (liftShift m (s, p.2)))
      (∑ m ∈ shiftBox N, partialX φ (liftShift m p)) p.1 := by
    apply HasDerivAt.fun_sum
    intro m _
    exact (hasDerivAt_partialX (hf.differentiable one_ne_zero (liftShift m p))).comp_add_const
      _ _
  have he : (fun s ↦ liftPeriodize φ (s, p.2)) =ᶠ[𝓝 p.1]
      fun s ↦ ∑ m ∈ shiftBox N, φ (liftShift m (s, p.2)) := by
    have hc : Continuous fun s : ℝ ↦ ‖((s, p.2) : ℝ × ℝ)‖ := by fun_prop
    filter_upwards [hc.continuousAt.eventually
      (eventually_lt_nhds (show ‖((p.1, p.2) : ℝ × ℝ)‖ < ‖p‖ + 1 by simp))] with s hs
    exact liftPeriodize_eq_sum hR0 hN.le hs.le
  rw [partialX, (hd.congr_of_eventuallyEq he).deriv]
  exact (liftPeriodize_eq_sum hR1 hN.le (by linarith)).symm

theorem partialY_liftPeriodize {φ : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) : partialY (liftPeriodize φ) = liftPeriodize (partialY φ) := by
  funext p
  obtain ⟨R, hR⟩ := exists_norm_bound_tsupport hs
  have hR0 : ∀ q, φ q ≠ 0 → ‖q‖ ≤ R := fun q hq ↦ hR q (subset_tsupport _ hq)
  have hR1 : ∀ q, partialY φ q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (tsupport_partialY_subset φ (subset_tsupport _ hq))
  obtain ⟨N, hN⟩ := exists_nat_gt (R + (‖p‖ + 1))
  have hd : HasDerivAt (fun s ↦ ∑ m ∈ shiftBox N, φ (liftShift m (p.1, s)))
      (∑ m ∈ shiftBox N, partialY φ (liftShift m p)) p.2 := by
    apply HasDerivAt.fun_sum
    intro m _
    exact (hasDerivAt_partialY (hf.differentiable one_ne_zero (liftShift m p))).comp_add_const
      _ _
  have he : (fun s ↦ liftPeriodize φ (p.1, s)) =ᶠ[𝓝 p.2]
      fun s ↦ ∑ m ∈ shiftBox N, φ (liftShift m (p.1, s)) := by
    have hc : Continuous fun s : ℝ ↦ ‖((p.1, s) : ℝ × ℝ)‖ := by fun_prop
    filter_upwards [hc.continuousAt.eventually
      (eventually_lt_nhds (show ‖((p.1, p.2) : ℝ × ℝ)‖ < ‖p‖ + 1 by simp))] with s hs
    exact liftPeriodize_eq_sum hR0 hN.le hs.le
  rw [partialY, (hd.congr_of_eventuallyEq he).deriv]
  exact (liftPeriodize_eq_sum hR1 hN.le (by linarith)).symm

/-- Periodization commutes with `L₀`, whose coefficients are periodic. -/
theorem liftPeriodize_classicalL0 {φ : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) :
    liftPeriodize (classicalL0 φ) = classicalL0 (liftPeriodize φ) := by
  funext p
  obtain ⟨R, hR⟩ := exists_norm_bound_tsupport hs
  have hRx : ∀ q, partialX φ q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (tsupport_partialX_subset φ (subset_tsupport _ hq))
  have hRy : ∀ q, partialY φ q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (tsupport_partialY_subset φ (subset_tsupport _ hq))
  have hRL : ∀ q, classicalL0 φ q ≠ 0 → ‖q‖ ≤ R := by
    intro q hq
    by_contra hn
    have hx : partialX φ q = 0 := by_contra fun h ↦ hn (hRx q h)
    have hy : partialY φ q = 0 := by_contra fun h ↦ hn (hRy q h)
    exact hq (by simp [classicalL0, hx, hy])
  obtain ⟨N, hN⟩ := exists_nat_gt (R + ‖p‖)
  rw [classicalL0, partialX_liftPeriodize hf hs, partialY_liftPeriodize hf hs,
    liftPeriodize_eq_sum hRL hN.le le_rfl, liftPeriodize_eq_sum hRx hN.le le_rfl,
    liftPeriodize_eq_sum hRy hN.le le_rfl, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [classicalL0, liftShift, Real.sin_add_int_mul_two_pi]

end Periodize

/-! ### Unfolding integrals -/

section Unfold

/-- The square `(2πn₁, 2πn₁ + 2π] × (2πn₂, 2πn₂ + 2π]`. -/
def liftSquare (n : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Ioc (n.1 * (2 * π)) (n.1 * (2 * π) + 2 * π) ×ˢ Ioc (n.2 * (2 * π)) (n.2 * (2 * π) + 2 * π)

theorem measurableSet_liftSquare (n : ℤ × ℤ) : MeasurableSet (liftSquare n) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem liftSquare_zero : liftSquare 0 = Ioc 0 (0 + 2 * π) ×ˢ Ioc 0 (0 + 2 * π) := by
  simp [liftSquare]

theorem iUnion_liftSquare : ⋃ n, liftSquare n = univ := by
  have hcover : ⋃ n : ℤ, Ioc (n * (2 * π)) (n * (2 * π) + 2 * π) = univ := by
    convert iUnion_Ioc_zsmul (show 0 < 2 * π by positivity) using 1
    ext x
    simp only [mem_iUnion, mem_Ioc, zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, one_mul]
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p.1 : p.1 ∈ _)
  obtain ⟨m, hm⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p.2 : p.2 ∈ _)
  exact ⟨(n, m), hn, hm⟩

private theorem int_eq_of_mem_Ioc {a b : ℤ} {x : ℝ}
    (ha : x ∈ Ioc (a * (2 * π)) (a * (2 * π) + 2 * π))
    (hb : x ∈ Ioc (b * (2 * π)) (b * (2 * π) + 2 * π)) : a = b := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast Int.add_one_le_iff.mpr h
    have h2 : ((a : ℝ) + 1) * (2 * π) ≤ b * (2 * π) :=
      mul_le_mul_of_nonneg_right h1 Real.two_pi_pos.le
    linarith [ha.2, hb.1]
  · have h1 : (b : ℝ) + 1 ≤ a := by exact_mod_cast Int.add_one_le_iff.mpr h
    have h2 : ((b : ℝ) + 1) * (2 * π) ≤ a * (2 * π) :=
      mul_le_mul_of_nonneg_right h1 Real.two_pi_pos.le
    linarith [ha.1, hb.2]

theorem pairwise_disjoint_liftSquare :
    Pairwise (fun m n ↦ Disjoint (liftSquare m) (liftSquare n)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun p hm hn ↦ hmn ?_
  exact Prod.ext (int_eq_of_mem_Ioc hm.1 hn.1) (int_eq_of_mem_Ioc hm.2 hn.2)

private theorem mem_shiftBox_of_mem_liftSquare {n : ℤ × ℤ} {p : ℝ × ℝ} {R : ℝ} {N : ℕ}
    (hp : p ∈ liftSquare n) (hR : ‖p‖ ≤ R) (hN : R + 2 * π ≤ N) : n ∈ shiftBox N := by
  have key (a : ℝ) (m : ℤ) (ha : |a| ≤ R)
      (hm : a ∈ Ioc (m * (2 * π)) (m * (2 * π) + 2 * π)) : -(N : ℤ) ≤ m ∧ m ≤ N := by
    refine int_bound (B := R + 2 * π) ?_ hN
    rw [abs_le] at ha ⊢
    constructor <;> linarith [hm.1, hm.2, Real.two_pi_pos]
  have h1 := key p.1 n.1 ((norm_fst_le p).trans hR) hp.1
  have h2 := key p.2 n.2 ((norm_snd_le p).trans hR) hp.2
  simp only [shiftBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1, h2⟩

theorem norm_le_of_mem_liftSquare_zero {p : ℝ × ℝ} (hp : p ∈ liftSquare 0) : ‖p‖ ≤ 2 * π := by
  rw [liftSquare_zero] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h1, abs_of_pos h3]
  exact max_le (by linarith) (by linarith)

theorem measurePreserving_liftShift (n : ℤ × ℤ) :
    MeasurePreserving (liftShift n) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume _).prod (measurePreserving_add_right volume _)

private theorem integral_liftSquare_shift (f : ℝ × ℝ → ℂ) (n : ℤ × ℤ) :
    (∫ q in liftSquare n, f q) = ∫ q in liftSquare 0, f (liftShift n q) := by
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.addRight (n.1 * (2 * π))).prodCongr (MeasurableEquiv.addRight (n.2 * (2 * π)))
  have hmp : MeasurePreserving e volume volume := measurePreserving_liftShift n
  have hpre : e ⁻¹' liftSquare n = liftSquare 0 := by
    ext q
    change (q.1 + n.1 * (2 * π) ∈ Ioc _ _ ∧ q.2 + n.2 * (2 * π) ∈ Ioc _ _) ↔ q ∈ liftSquare 0
    rw [liftSquare_zero]
    simp only [mem_Ioc, mem_prod, zero_add]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hi := hmp.setIntegral_preimage_emb e.measurableEmbedding f (liftSquare n)
  rw [hpre] at hi
  exact hi.symm

/-- Unfolding: the integral of a function of bounded support is the integral of its
periodization over one period square. -/
theorem integral_liftPeriodize {f : ℝ × ℝ → ℂ} (hf : Integrable f) {R : ℝ}
    (hR : ∀ q, f q ≠ 0 → ‖q‖ ≤ R) :
    ∫ q, f q = ∫ q in liftSquare 0, liftPeriodize f q := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 2 * π)
  have hz : ∀ n ∉ shiftBox N, (∫ q in liftSquare 0, f (liftShift n q)) = 0 := by
    intro n hn
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_liftSquare 0)] with q hq
    change f (liftShift n q) = 0
    by_contra hne
    exact hn (shift_support_subset hR hN.le (norm_le_of_mem_liftSquare_zero hq) hne)
  have hshift (n : ℤ × ℤ) : Integrable (fun q ↦ f (liftShift n q)) :=
    ((measurePreserving_liftShift n).integrable_comp hf.aestronglyMeasurable).mpr hf
  calc
    _ = ∫ q in ⋃ n, liftSquare n, f q := by rw [iUnion_liftSquare, setIntegral_univ]
    _ = ∑' n, ∫ q in liftSquare n, f q :=
      integral_iUnion measurableSet_liftSquare pairwise_disjoint_liftSquare hf.integrableOn
    _ = ∑' n, ∫ q in liftSquare 0, f (liftShift n q) := by
      congr 1
      funext n
      exact integral_liftSquare_shift f n
    _ = ∑ n ∈ shiftBox N, ∫ q in liftSquare 0, f (liftShift n q) := tsum_eq_sum hz
    _ = ∫ q in liftSquare 0, ∑ n ∈ shiftBox N, f (liftShift n q) :=
      (integral_finsetSum _ (fun n _ ↦ (hshift n).integrableOn)).symm
    _ = _ := by
      apply setIntegral_congr_fun (measurableSet_liftSquare 0)
      intro q hq
      exact (liftPeriodize_eq_sum hR hN.le (norm_le_of_mem_liftSquare_zero hq)).symm

theorem liftL2_liftShift (g : L2) (n : ℤ × ℤ) (p : ℝ × ℝ) :
    liftL2 g (liftShift n p) = liftL2 g p := by
  have h (x : ℝ) (m : ℤ) : ((x + m * (2 * π) : ℝ) : Real.Angle) = x :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨m, by ring⟩
  simp only [liftL2, torusProj, liftShift, h]

/-- Lifts of integrable torus functions are locally integrable. -/
theorem locallyIntegrable_comp_torusProj {E : Type*} [NormedAddCommGroup E] {G : Torus → E}
    (hG : Integrable G) : LocallyIntegrable (fun p ↦ G (torusProj p)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hsq (n : ℤ × ℤ) : IntegrableOn (fun p ↦ G (torusProj p)) (liftSquare n) :=
    ((measurePreserving_torusProj_square _ _).integrable_comp hG.aestronglyMeasurable).2 hG
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 2 * π)
  refine (integrableOn_finset_iUnion (s := shiftBox N).2 fun n _ ↦ hsq n).mono_set
    fun p hp ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.mp (iUnion_liftSquare.symm ▸ mem_univ p : p ∈ ⋃ n, liftSquare n)
  exact mem_iUnion₂.2 ⟨n, mem_shiftBox_of_mem_liftSquare hn
    (mem_closedBall_zero_iff.1 (hR hp)) hN.le, hn⟩

/-- Lifts of `L²` functions are locally integrable. -/
theorem locallyIntegrable_liftL2 (g : L2) : LocallyIntegrable (liftL2 g) :=
  locallyIntegrable_comp_torusProj (integrable_L2 g)

/-- Lifts of `L²` functions are square integrable on bounded sets. -/
theorem memLp_liftL2 (g : L2) {U : Set (ℝ × ℝ)} (hb : Bornology.IsBounded U) :
    MemLp (liftL2 g) 2 (volume.restrict U) := by
  have hm : AEStronglyMeasurable (liftL2 g) (volume.restrict U) :=
    (locallyIntegrable_liftL2 g).aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hG : Integrable (fun t ↦ ‖g t‖ ^ 2) := (Lp.memLp g).integrable_norm_pow (by norm_num)
  exact ((locallyIntegrable_comp_torusProj hG).integrableOn_isCompact
    hb.isCompact_closure).mono_set subset_closure

/-- Unfolding against a lift: `∫_{ℝ²} (g ∘ π) φ = ∫_{𝕋²} g Pφ`. -/
theorem integral_liftL2_mul_eq (g : L2) {φ : ℝ × ℝ → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) :
    ∫ p, liftL2 g p * φ p = ∫ t, g t *
      torusFun (continuous_liftPeriodize hφ hs) (isPeriodicLift_liftPeriodize φ) t := by
  obtain ⟨R, hR⟩ := exists_norm_bound_tsupport hs
  have hi : Integrable (fun p ↦ liftL2 g p * φ p) :=
    integrable_mul_of_tsupport_subset ((locallyIntegrable_liftL2 g).locallyIntegrableOn univ)
      hφ hs (subset_univ _)
  have hR' : ∀ q, liftL2 g q * φ q ≠ 0 → ‖q‖ ≤ R :=
    fun q hq ↦ hR q (subset_tsupport _ (right_ne_zero_of_mul hq))
  rw [integral_liftPeriodize hi hR']
  set Φ := torusFun (continuous_liftPeriodize hφ hs) (isPeriodicLift_liftPeriodize φ)
  have hP (q : ℝ × ℝ) : liftPeriodize (fun p ↦ liftL2 g p * φ p) q =
      g (torusProj q) * Φ (torusProj q) := by
    rw [torusFun_torusProj]
    unfold liftPeriodize
    simp_rw [liftL2_liftShift]
    exact (mul_finsum _ _).symm
  simp_rw [hP]
  have hmp := measurePreserving_torusProj_square 0 0
  have h := integral_map (μ := volume.restrict (Ioc 0 (0 + 2 * π) ×ˢ Ioc 0 (0 + 2 * π)))
    hmp.measurable.aemeasurable (f := fun t ↦ g t * Φ t)
    (by rw [hmp.map_eq]; exact (Lp.aestronglyMeasurable g).mul Φ.continuous.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  rw [liftSquare_zero, ← h]

end Unfold

/-! ### Almost-everywhere identities of lifts -/

/-- Almost-everywhere statements on the torus lift to the real plane. -/
theorem ae_torusProj {P : Torus → Prop} (hP : ∀ᵐ t, P t) : ∀ᵐ p : ℝ × ℝ, P (torusProj p) := by
  let I : ℤ → Set ℝ := fun n ↦ Ioc (n * (2 * Real.pi)) (n * (2 * Real.pi) + 2 * Real.pi)
  have hcover : ⋃ n, I n = univ := by
    convert iUnion_Ioc_zsmul (show 0 < 2 * Real.pi by positivity) using 1
    ext x
    simp only [I, mem_iUnion, mem_Ioc, zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, one_mul]
  have hcover2 : ⋃ n : ℤ × ℤ, I n.1 ×ˢ I n.2 = univ := by
    ext p
    simp only [mem_iUnion, mem_prod, mem_univ, iff_true]
    have hx : p.1 ∈ ⋃ n, I n := hcover.symm ▸ mem_univ _
    have hy : p.2 ∈ ⋃ n, I n := hcover.symm ▸ mem_univ _
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact ⟨(n, m), hn, hm⟩
  have hall : ∀ n : ℤ × ℤ, ∀ᵐ p ∂(volume.restrict (I n.1 ×ˢ I n.2)), P (torusProj p) := by
    intro n
    exact (measurePreserving_torusProj_square _ _).quasiMeasurePreserving.ae hP
  have hh := (ae_restrict_iUnion_iff (fun n : ℤ × ℤ ↦ I n.1 ×ˢ I n.2)
    (fun p ↦ P (torusProj p))).2 hall
  simpa only [hcover2, Measure.restrict_univ] using hh

theorem liftL2_ae_eq {u : L2} {G : Torus → ℂ} (h : u =ᵐ[volume] G) :
    liftL2 u =ᵐ[volume] fun p ↦ G (torusProj p) :=
  ae_torusProj h

theorem liftL2_mulL2_ae (c : C(Torus, ℂ)) (u : L2) :
    liftL2 (mulL2 c u) =ᵐ[volume] fun p ↦ c (torusProj p) * liftL2 u p :=
  liftL2_ae_eq (mulL2_ae c u)

theorem liftL2_add_ae (u v : L2) :
    liftL2 (u + v) =ᵐ[volume] fun p ↦ liftL2 u p + liftL2 v p :=
  liftL2_ae_eq (Lp.coeFn_add u v)

theorem liftL2_sub_ae (u v : L2) :
    liftL2 (u - v) =ᵐ[volume] fun p ↦ liftL2 u p - liftL2 v p :=
  liftL2_ae_eq (Lp.coeFn_sub u v)

theorem liftL2_smul_ae (r : ℂ) (u : L2) :
    liftL2 (r • u) =ᵐ[volume] fun p ↦ r * liftL2 u p :=
  liftL2_ae_eq (Lp.coeFn_smul r u)

/-! ### Weak transport of lifts -/

theorem isTestFunctionOn_classicalL0 {U : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) : IsTestFunctionOn U (classicalL0 φ) := by
  have hx : ContDiff ℝ ∞ (partialX φ) := by
    simpa [coordPartial] using contDiff_coordPartial_top 0 hφ.contDiff
  have hy : ContDiff ℝ ∞ (partialY φ) := by
    simpa [coordPartial] using contDiff_coordPartial_top 1 hφ.contDiff
  have hc : ContDiff ℝ ∞ (classicalL0 φ) := by unfold classicalL0; fun_prop
  have hz : ∀ p ∉ tsupport φ, classicalL0 φ p = 0 := by
    intro p hp
    have hpx : partialX φ p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hp (tsupport_partialX_subset φ h))
    have hpy : partialY φ p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hp (tsupport_partialY_subset φ h))
    simp [classicalL0, hpx, hpy]
  have hs : tsupport (classicalL0 φ) ⊆ tsupport φ :=
    closure_minimal (fun p hp ↦ by_contra fun hn ↦ hp (hz p hn)) (isClosed_tsupport φ)
  exact ⟨hc, hφ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hφ.tsupport_subset⟩

/-- If `L₀g = h` on the torus, then the lifts satisfy `∫ (g ∘ π) L₀φ = -∫ (h ∘ π) φ` for every
compactly supported smooth `φ` on the plane. -/
theorem integral_liftL2_mul_classicalL0 {g h : L2} (hgh : HasL0 g h) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn univ φ) :
    ∫ p, liftL2 g p * classicalL0 φ p = -∫ p, liftL2 h p * φ p := by
  have hφc := hφ.contDiff
  have hP1 : ContDiff ℝ 1 (liftPeriodize φ) :=
    (contDiff_liftPeriodize hφc hφ.hasCompactSupport).of_le (by simp)
  have hpP := isPeriodicLift_liftPeriodize φ
  have H := hgh.integral_mul_eq (hasClassicalPartial_torusFun_x hP1 hpP)
    (hasClassicalPartial_torusFun_y hP1 hpP)
  have hL := isTestFunctionOn_classicalL0 hφ
  rw [integral_liftL2_mul_eq h hφc.continuous hφ.hasCompactSupport,
    integral_liftL2_mul_eq g hL.contDiff.continuous hL.hasCompactSupport, H, neg_neg]
  congr 1
  funext t
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  congr 1
  rw [torusFun_torusProj, torusFun_torusProj, torusFun_torusProj, sinYTorus_torusProj,
    sinXTorus_torusProj, liftPeriodize_classicalL0 (hφc.of_le (by simp)) hφ.hasCompactSupport]
  simp [classicalL0]

/-! ### Sobolev regularity of lifts (`lem:local-to-global`) -/

/-- Fourier partial derivatives on the torus are weak partial derivatives of the lifts, tested
against compactly supported smooth functions on the plane. -/
theorem integral_liftL2_mul_coordPartial {j : Fin 2} {g h : L2}
    (hgh : HasFourierPartial j g h) {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn univ φ) :
    ∫ p, liftL2 g p * coordPartial j φ p = -∫ p, liftL2 h p * φ p := by
  have hφc := hφ.contDiff
  have hφ1 : ContDiff ℝ 1 φ := hφc.of_le (by simp)
  have hP1 : ContDiff ℝ 1 (liftPeriodize φ) :=
    (contDiff_liftPeriodize hφc hφ.hasCompactSupport).of_le (by simp)
  have hpP := isPeriodicLift_liftPeriodize φ
  rw [integral_liftL2_mul_eq h hφc.continuous hφ.hasCompactSupport,
    integral_liftL2_mul_eq g (hφ.continuous_coordPartial j) (hφ.hasCompactSupport_coordPartial j)]
  by_cases hj : j = 0
  · subst j
    rw [hgh.hasWeakPartial _ _ (hasClassicalPartial_torusFun_x hP1 hpP), neg_neg]
    congr 1
    funext t
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    congr 1
    rw [torusFun_torusProj, torusFun_torusProj, partialX_liftPeriodize hφ1 hφ.hasCompactSupport]
    simp [coordPartial]
  · have hj1 : j = 1 := by omega
    subst j
    rw [hgh.hasWeakPartial _ _ (hasClassicalPartial_torusFun_y hP1 hpP), neg_neg]
    congr 1
    funext t
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    congr 1
    rw [torusFun_torusProj, torusFun_torusProj, partialY_liftPeriodize hφ1 hφ.hasCompactSupport]
    simp [coordPartial]

/-- The weak derivatives of the lift are the lifts of the Fourier derivatives. -/
theorem hasWeakPartialOn_liftL2 {j : Fin 2} {g h : L2} (hgh : HasFourierPartial j g h)
    (U : Set (ℝ × ℝ)) : HasWeakPartialOn U j (liftL2 g) (liftL2 h) :=
  ⟨(locallyIntegrable_liftL2 g).locallyIntegrableOn U,
    (locallyIntegrable_liftL2 h).locallyIntegrableOn U,
    fun _ hφ ↦ integral_liftL2_mul_coordPartial hgh (hφ.mono (subset_univ U))⟩

/-- Lifts of torus Sobolev functions: on a bounded set the lift of `g ∈ Hᵏ(𝕋²)` lies in
    `Hᵏ(U)`. -/
theorem memSobolevOn_liftL2 {k : ℕ} {g : L2} (hg : MemSobolev k g) {U : Set (ℝ × ℝ)}
    (hb : Bornology.IsBounded U) : MemSobolevOn k U (liftL2 g) := by
  induction k generalizing g with
  | zero => exact memLp_liftL2 g hb
  | succ k ih =>
    refine ⟨memLp_liftL2 g hb, fun j ↦ ?_⟩
    have hg' : MemSobolev ((k : ℝ) + 1) g := by exact_mod_cast hg
    obtain ⟨h, hd⟩ :=
      (hg'.mono (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).exists_hasFourierPartial j
    exact ⟨liftL2 h, hasWeakPartialOn_liftL2 hd U, ih (hg'.of_hasFourierPartial hd)⟩

end NoEmbeddedEigenvalues
