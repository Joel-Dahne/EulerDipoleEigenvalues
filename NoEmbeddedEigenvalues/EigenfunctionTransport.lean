import NoEmbeddedEigenvalues.Transport
import NoEmbeddedEigenvalues.Sectors

/-!
# Transport traces of eigenfunctions

Blueprint: `lem:ee-transport-traces` (with the Melnikov identity `ee_melnikov`);
also `lem:level-integral-congr` (changing
representatives on levels, a.e. statements on a.e. level, level integrals over `[-2L, 6L)`).

Specialize the abstract Melnikov and pairing statements to eigenfunctions, replacing the
raw stream lift with its continuous representative. The neighbourhood is the diagonal
square `|a|, |b| < 3π/2`, whose boundary lines are invariant under the dipole flow.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A bounded open invariant neighbourhood of the closed positive cell. -/
def cellNeighbourhood : Set (ℝ × ℝ) :=
  {p | |(diagCoord p).1| < 3 * Real.pi / 2 ∧ |(diagCoord p).2| < 3 * Real.pi / 2}

private theorem scalar_barrier_ne {a b : ℝ → ℝ} {c t₀ : ℝ}
    (ha : ∀ t, HasDerivAt a (-cos (a t) * sin (b t)) t)
    (hc : cos c = 0) (h0 : a 0 ≠ c) : a t₀ ≠ c := by
  intro ht
  have hl (t : ℝ) : LipschitzWith 1 (fun y : ℝ ↦ -cos y * sin (b t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    calc |(-cos x * sin (b t)) - (-cos y * sin (b t))| =
        |-(cos x - cos y) * sin (b t)| := by congr 1; ring
      _ = |cos x - cos y| * |sin (b t)| := by rw [abs_mul, abs_neg]
      _ ≤ |x - y| * 1 :=
        mul_le_mul (abs_cos_sub_cos_le x y) (abs_sin_le_one _) (abs_nonneg _) (abs_nonneg _)
      _ = |x - y| := mul_one _
  have heq : a = fun _ ↦ c := ODE_solution_unique_univ
    (v := fun t y ↦ -cos y * sin (b t)) (s := fun _ ↦ univ) (t₀ := t₀)
    (fun t ↦ (hl t).lipschitzOnWith) (fun t ↦ ⟨ha t, trivial⟩)
    (fun t ↦ ⟨by simpa [hc] using hasDerivAt_const t c, trivial⟩) ht
  exact h0 (congrFun heq 0)

private theorem cos_three_pi_div_two : cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, cos_add_pi, cos_pi_div_two, neg_zero]

/-- The larger diagonal square is an open union of complete dipole orbits. -/
theorem isOrbitUnion_cellNeighbourhood : IsOrbitUnion cellNeighbourhood := by
  constructor
  · unfold cellNeighbourhood diagCoord
    exact (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 + p.2) / 2|)
      continuous_const).inter (isOpen_lt
        (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 - p.2) / 2|) continuous_const)
  · intro p hp t
    have hac (s : ℝ) := (hasDerivAt_diag_fst p s).continuousAt
    have hbc (s : ℝ) := (hasDerivAt_diag_snd p s).continuousAt
    have ha : Continuous (fun s ↦ (diagCoord (dipoleFlow p s)).1) :=
      continuous_iff_continuousAt.2 hac
    have hb : Continuous (fun s ↦ (diagCoord (dipoleFlow p s)).2) :=
      continuous_iff_continuousAt.2 hbc
    have hane (c : ℝ) (hc : cos c = 0) (hp0 : (diagCoord p).1 ≠ c) :
        ∀ s, (diagCoord (dipoleFlow p s)).1 ≠ c := by
      intro s
      exact scalar_barrier_ne (a := fun t ↦ (diagCoord (dipoleFlow p t)).1)
        (b := fun t ↦ (diagCoord (dipoleFlow p t)).2) (t₀ := s)
        (hasDerivAt_diag_fst p) hc (by simpa [dipoleFlow_zero] using hp0)
    have hbne (c : ℝ) (hc : cos c = 0) (hp0 : (diagCoord p).2 ≠ c) :
        ∀ s, (diagCoord (dipoleFlow p s)).2 ≠ c := by
      intro s
      apply scalar_barrier_ne (a := fun s ↦ (diagCoord (dipoleFlow p s)).2)
        (b := fun s ↦ -(diagCoord (dipoleFlow p s)).1) _ hc
        (by simpa [dipoleFlow_zero] using hp0)
      intro s
      convert hasDerivAt_diag_snd p s using 1
      simp [sin_neg]
      ring
    obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
    obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
    have hcn : cos (-(3 * Real.pi / 2)) = 0 := by rw [cos_neg, cos_three_pi_div_two]
    constructor
    · rw [abs_lt]
      constructor
      · have hn := hane (-(3 * Real.pi / 2)) hcn ha0.ne'
        have hh := lt_of_forall_ne (v := 3 * Real.pi / 2) ha.neg
          (fun s h ↦ hn s (by change -(diagCoord (dipoleFlow p s)).1 = _ at h; linarith))
          (by simpa [dipoleFlow_zero] using neg_lt_neg ha0) t
        change -(diagCoord (dipoleFlow p t)).1 < 3 * Real.pi / 2 at hh
        linarith
      · exact lt_of_forall_ne ha (hane _ cos_three_pi_div_two ha1.ne)
          (by simpa [dipoleFlow_zero] using ha1) t
    · rw [abs_lt]
      constructor
      · have hn := hbne (-(3 * Real.pi / 2)) hcn hb0.ne'
        have hh := lt_of_forall_ne (v := 3 * Real.pi / 2) hb.neg
          (fun s h ↦ hn s (by change -(diagCoord (dipoleFlow p s)).2 = _ at h; linarith))
          (by simpa [dipoleFlow_zero] using neg_lt_neg hb0) t
        change -(diagCoord (dipoleFlow p t)).2 < 3 * Real.pi / 2 at hh
        linarith
      · exact lt_of_forall_ne hb (hbne _ cos_three_pi_div_two hb1.ne)
          (by simpa [dipoleFlow_zero] using hb1) t

/-- The neighbourhood is bounded in the real lift. -/
theorem isBounded_cellNeighbourhood : Bornology.IsBounded cellNeighbourhood := by
  apply Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ) |>.2
  refine ⟨3 * Real.pi, fun p hp ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
  obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
  simp only [diagCoord] at ha0 ha1 hb0 hb1
  simp only [Real.norm_eq_abs, abs_le]
  constructor <;> constructor <;> linarith

/-- It contains the closed positive-cell square. -/
theorem closure_cellSquare_subset_cellNeighbourhood : closure cellSquare ⊆ cellNeighbourhood := by
  have hc : IsClosed {p : ℝ × ℝ | |(diagCoord p).1| ≤ Real.pi / 2 ∧
      |(diagCoord p).2| ≤ Real.pi / 2} := by
    unfold diagCoord
    exact (isClosed_le (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 + p.2) / 2|)
      continuous_const).inter (isClosed_le
        (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 - p.2) / 2|) continuous_const)
  have hs : closure cellSquare ⊆ {p | |(diagCoord p).1| ≤ Real.pi / 2 ∧
      |(diagCoord p).2| ≤ Real.pi / 2} :=
    closure_minimal (fun p (hp : p ∈ cellSquare) ↦ ⟨hp.1.le, hp.2.le⟩) hc
  intro p hp
  obtain ⟨ha, hb⟩ := hs hp
  constructor <;> linarith [Real.pi_pos]

/-- Rotation preserves the neighbourhood. -/
theorem rotLift_mem_cellNeighbourhood {p : ℝ × ℝ} (hp : p ∈ cellNeighbourhood) :
    rotLift p ∈ cellNeighbourhood := by
  change |(p.2 + -p.1) / 2| < 3 * Real.pi / 2 ∧
    |(p.2 - -p.1) / 2| < 3 * Real.pi / 2
  convert hp.symm using 2
  · rw [show (p.2 + -p.1) / 2 = -((p.1 - p.2) / 2) by ring, abs_neg]
    rfl
  · congr 1
    dsimp [diagCoord]
    ring

/-- `|g|²` of an `L²` function on the torus is integrable on the square `(-2π, 2π]²` of the
    lift, which contains the closed cell. -/
theorem integrableOn_norm_liftL2_sq (g : L2) :
    IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2)
      (Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi)) := by
  have hg : Integrable (fun t ↦ ‖g t‖ ^ 2) := (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hsq (a b : ℝ) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2)
      (Ioc a (a + 2 * Real.pi) ×ˢ Ioc b (b + 2 * Real.pi)) :=
    ((measurePreserving_torusProj_square a b).integrable_comp
      hg.aestronglyMeasurable).2 hg
  have hI : Ioc (-2 * Real.pi) (2 * Real.pi) =
      Ioc (-2 * Real.pi) (-2 * Real.pi + 2 * Real.pi) ∪ Ioc 0 (0 + 2 * Real.pi) := by
    rw [show -2 * Real.pi + 2 * Real.pi = 0 by ring, zero_add,
      Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  rw [hI, prod_union, union_prod, union_prod]
  exact ((hsq _ _).union (hsq _ _)).union ((hsq _ _).union (hsq _ _))

/-- Weak partial derivatives are unchanged by a global a.e. change of representative. -/
theorem HasWeakPartialOn.congr_value {U : Set (ℝ × ℝ)} {j : Fin 2}
    {f g d : ℝ × ℝ → ℂ} (h : HasWeakPartialOn U j f d) (hfg : f =ᵐ[volume] g) :
    HasWeakPartialOn U j g d := by
  refine ⟨h.1.congr hfg.restrict, h.2.1, fun φ hφ ↦ ?_⟩
  rw [← h.2.2 φ hφ]
  exact integral_congr_ae (hfg.mono fun p hp ↦ congrArg (· * coordPartial j φ p) hp.symm)

/-- Local Sobolev membership is unchanged by a global a.e. change of representative. -/
theorem MemSobolevOn.congr_value {k : ℕ} {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ}
    (h : MemSobolevOn k U f) (hfg : f =ᵐ[volume] g) : MemSobolevOn k U g := by
  cases k with
  | zero => exact MemLp.ae_eq hfg.restrict h
  | succ k =>
    refine ⟨MemLp.ae_eq hfg.restrict h.1, fun j ↦ ?_⟩
    obtain ⟨d, hd, hk⟩ := h.2 j
    exact ⟨d, hd.congr_value hfg, hk⟩

private theorem dist_dipoleFlow_le (p q : ℝ × ℝ) (t : ℝ) :
    dist (dipoleFlow p t) (dipoleFlow q t) ≤ dist p q * Real.exp |t| := by
  have hc (p : ℝ × ℝ) : Continuous (dipoleFlow p) :=
    continuous_iff_continuousAt.2 (fun s ↦ (hasDerivAt_dipoleFlow p s).continuousAt)
  by_cases ht : 0 ≤ t
  · have hh := dist_le_of_trajectories_ODE (v := fun _ ↦ dipoleVelocity)
      (a := 0) (b := t) (K := 1) (δ := dist p q)
      (fun _ ↦ lipschitzWith_dipoleVelocity) (hc p).continuousOn
      (fun s _ ↦ (hasDerivAt_dipoleFlow p s).hasDerivWithinAt) (hc q).continuousOn
      (fun s _ ↦ (hasDerivAt_dipoleFlow q s).hasDerivWithinAt)
      (by simp [dipoleFlow_zero]) t ⟨ht, le_rfl⟩
    simpa only [NNReal.coe_one, one_mul, sub_zero, abs_of_nonneg ht] using hh
  · have hneg := lt_of_not_ge ht
    have hh := dist_le_of_trajectories_ODE (v := fun _ x ↦ -dipoleVelocity x)
      (f := fun s ↦ dipoleFlow p (-s)) (g := fun s ↦ dipoleFlow q (-s))
      (a := 0) (b := -t) (K := 1) (δ := dist p q)
      (fun _ ↦ lipschitzWith_dipoleVelocity.neg) ((hc p).comp continuous_neg).continuousOn
      (fun s _ ↦ by simpa only [Function.comp_def, neg_one_smul] using
        ((hasDerivAt_dipoleFlow p (-s)).scomp s (hasDerivAt_neg s)).hasDerivWithinAt)
      ((hc q).comp continuous_neg).continuousOn
      (fun s _ ↦ by simpa only [Function.comp_def, neg_one_smul] using
        ((hasDerivAt_dipoleFlow q (-s)).scomp s (hasDerivAt_neg s)).hasDerivWithinAt)
      (by simp [dipoleFlow_zero]) (-t) ⟨by linarith, le_rfl⟩
    simpa only [neg_neg, NNReal.coe_one, one_mul, sub_zero, abs_of_neg hneg] using hh

private theorem lipschitzWith_dipoleFlow_time (p : ℝ × ℝ) : LipschitzWith 1 (dipoleFlow p) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s ↦ (hasDerivAt_dipoleFlow p s).differentiableAt)
  intro s
  rw [(hasDerivAt_dipoleFlow p s).deriv]
  exact_mod_cast norm_dipoleVelocity_le (dipoleFlow p s)

/-- Joint continuity needs only Lipschitz dependence on the initial data, not differentiable
    dependence of ODE solutions. -/
theorem continuous_dipoleFlow : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ dipoleFlow q.1 q.2) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨p, t⟩
  apply tendsto_iff_dist_tendsto_zero.2
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ ↦
      dist q.1 p * Real.exp |q.2| + dist q.2 t) := by fun_prop
  have hl : Tendsto (fun q : (ℝ × ℝ) × ℝ ↦
      dist q.1 p * Real.exp |q.2| + dist q.2 t) (𝓝 (p, t)) (𝓝 0) := by
    simpa using hc.tendsto (p, t)
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hl
  intro q
  calc dist (dipoleFlow q.1 q.2) (dipoleFlow p t) ≤
      dist (dipoleFlow q.1 q.2) (dipoleFlow p q.2) +
        dist (dipoleFlow p q.2) (dipoleFlow p t) := dist_triangle _ _ _
    _ ≤ dist q.1 p * Real.exp |q.2| + dist q.2 t := by
      exact add_le_add (dist_dipoleFlow_le q.1 p q.2)
        (by simpa using (lipschitzWith_dipoleFlow_time p).dist_le_mul q.2 t)

/-- The orbit parametrization is jointly continuous in level and time. -/
theorem continuous_dipoleOrbit : Continuous (fun q : ℝ × ℝ ↦ dipoleOrbit q.1 q.2) := by
  exact continuous_dipoleFlow.comp
    (by fun_prop : Continuous fun q : ℝ × ℝ ↦ ((Real.arccos q.1, -Real.arccos q.1), q.2))

/-- Measurability of the period, including the total integral values outside `(0,1)`. -/
theorem measurable_eighthPeriod : Measurable eighthPeriod := by
  let A : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ Real.arccos (√q.1)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  have hm : Measurable (fun q : ℝ × ℝ ↦ 1 / √(cos q.2 ^ 2 - q.1 ^ 2)) := by fun_prop
  have hh := (hm.indicator hA).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hh.measurable using 1
  funext h
  rw [eighthPeriod, intervalIntegral.integral_of_le (Real.arccos_nonneg _)]
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- Changing a measurable representative on a planar null set changes its level integral
    only on a null set of levels. The proof uses the nonnegative orbit-coordinate formula,
    not a possibly undefined Bochner integral. -/
theorem ae_levelIntegral_congr {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[volume] g) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), levelIntegral h f = levelIntegral h g := by
  let d : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal |f p - g p|
  have hd : Measurable d :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hf.sub hg))
  have hd0 : d =ᵐ[volume] 0 := hfg.mono fun p hp ↦ by simp [d, hp]
  have hc0 : (∫⁻ p in cellSquare, d p) = 0 := by
    rw [lintegral_congr_ae hd0.restrict]
    simp
  have hc := lintegral_cellSquare_eq hd
  rw [hc0] at hc
  have hz : (∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      d (dipoleOrbit h t)) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_left (by norm_num)
  let A : Set (ℝ × ℝ) := {q | -2 * eighthPeriod q.1 ≤ q.2 ∧ q.2 < 6 * eighthPeriod q.1}
  have hA : MeasurableSet A :=
    (measurableSet_le (measurable_eighthPeriod.comp measurable_fst |>.const_mul (-2))
      measurable_snd).inter (measurableSet_lt measurable_snd
        (measurable_eighthPeriod.comp measurable_fst |>.const_mul 6))
  have hm : Measurable (fun h ↦ ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      d (dipoleOrbit h t)) := by
    have hh := ((hd.comp continuous_dipoleOrbit.measurable).indicator hA).lintegral_prod_right'
      (ν := (volume : Measure ℝ))
    convert hh using 1
    funext h
    rw [← lintegral_indicator measurableSet_Ico]
    rfl
  have hae := (lintegral_eq_zero_iff hm).1 hz
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with h hh h01
  have hS := orbitPeriod_pos h01.1 h01.2
  have hL := eighthPeriod_pos h01.1 h01.2
  have htime : Measurable (fun t ↦ d (dipoleOrbit h t)) :=
    hd.comp (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have ha := (lintegral_eq_zero_iff htime).1 hh
  have hn : (fun t ↦ |f (dipoleOrbit h t) - g (dipoleOrbit h t)|) =ᵐ[
      volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))] 0 := by
    filter_upwards [ha] with t ht
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (abs_nonneg _)
  have hint : IntervalIntegrable (fun t ↦ |f (dipoleOrbit h t) - g (dipoleOrbit h t)|)
      volume (-2 * eighthPeriod h) (6 * eighthPeriod h) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le (by linarith)).2
      ((integrable_zero ℝ ℝ _).congr hn.symm)
  have hp : Function.Periodic (fun t ↦ |f (dipoleOrbit h t) - g (dipoleOrbit h t)|)
      (orbitPeriod h) := by
    intro t
    exact congrArg (fun p : ℝ × ℝ ↦ |f p - g p|) (dipoleOrbit_periodic h01.1 h01.2 t)
  have hsum : -2 * eighthPeriod h + orbitPeriod h = 6 * eighthPeriod h := by
    unfold orbitPeriod
    ring
  have hint' := hint
  rw [← hsum] at hint'
  have hint0 := hp.intervalIntegrable hS.ne' hint' 0 (orbitPeriod h)
  have hbase : (∫ t in (-2 * eighthPeriod h)..(-2 * eighthPeriod h + orbitPeriod h),
      |f (dipoleOrbit h t) - g (dipoleOrbit h t)|) = 0 := by
    rw [hsum, intervalIntegral.integral_of_le (by linarith), ← integral_Ico_eq_integral_Ioc,
      integral_congr_ae hn]
    simp
  have hzero : (∫ t in Ioc 0 (orbitPeriod h), |f (dipoleOrbit h t) - g (dipoleOrbit h t)|) = 0 := by
    rw [← intervalIntegral.integral_of_le hS.le]
    simpa only [zero_add] using (hp.intervalIntegral_add_eq 0 (-2 * eighthPeriod h)).trans hbase
  have hn0 := (integral_eq_zero_iff_of_nonneg (fun t ↦ abs_nonneg _) hint0.1).1 hzero
  have hn0' := (ae_restrict_iff' measurableSet_Ioc).1 hn0
  unfold levelIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hn0'] with t ht htI
  rw [uIoc_of_le hS.le] at htI
  exact sub_eq_zero.mp (abs_eq_zero.mp (ht htI))

/-- Level integrals over one period are integrals over `[-2L(h), 6L(h))`, the range of the
    flow-time coordinate, by periodicity of the orbit. -/
theorem levelIntegral_eq_setIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (f : ℝ × ℝ → E) :
    levelIntegral h f =
      ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), f (dipoleOrbit h t) := by
  have hL := eighthPeriod_pos h0 h1
  have hp : Function.Periodic (fun t ↦ f (dipoleOrbit h t)) (orbitPeriod h) := fun t ↦
    congrArg f (dipoleOrbit_periodic h0 h1 t)
  have hsum : -2 * eighthPeriod h + orbitPeriod h = 6 * eighthPeriod h := by
    unfold orbitPeriod
    ring
  rw [levelIntegral, ← zero_add (orbitPeriod h), hp.intervalIntegral_add_eq 0 (-2 * eighthPeriod h),
    hsum, intervalIntegral.integral_of_le (by linarith), integral_Ico_eq_integral_Ioc]

/-- Almost-everywhere statements on the cell hold almost everywhere on almost every level. -/
theorem ae_level_of_ae_cellSquare {P : ℝ × ℝ → Prop} (hP : MeasurableSet {p | P p})
    (hae : ∀ᵐ p ∂(volume.restrict cellSquare), P p) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), ∀ᵐ t ∂(volume.restrict
      (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))), P (dipoleOrbit h t) := by
  let d : ℝ × ℝ → ℝ≥0∞ := {p | P p}ᶜ.indicator 1
  have hd : Measurable d := measurable_one.indicator hP.compl
  have hc0 : (∫⁻ p in cellSquare, d p) = 0 := by
    rw [lintegral_indicator_one hP.compl]
    exact ae_iff.1 hae
  have hc := lintegral_cellSquare_eq hd
  rw [hc0] at hc
  have hz : (∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      d (dipoleOrbit h t)) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_left (by norm_num)
  let A : Set (ℝ × ℝ) := {q | -2 * eighthPeriod q.1 ≤ q.2 ∧ q.2 < 6 * eighthPeriod q.1}
  have hA : MeasurableSet A :=
    (measurableSet_le (measurable_eighthPeriod.comp measurable_fst |>.const_mul (-2))
      measurable_snd).inter (measurableSet_lt measurable_snd
        (measurable_eighthPeriod.comp measurable_fst |>.const_mul 6))
  have hm : Measurable (fun h ↦ ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      d (dipoleOrbit h t)) := by
    have hh := ((hd.comp continuous_dipoleOrbit.measurable).indicator hA).lintegral_prod_right'
      (ν := (volume : Measure ℝ))
    convert hh using 1
    funext h
    rw [← lintegral_indicator measurableSet_Ico]
    rfl
  filter_upwards [(lintegral_eq_zero_iff hm).1 hz] with h hh
  have htime : Measurable (fun t ↦ d (dipoleOrbit h t)) :=
    hd.comp (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  filter_upwards [(lintegral_eq_zero_iff htime).1 hh] with t ht
  by_contra hne
  have : d (dipoleOrbit h t) = 1 := indicator_of_mem (show dipoleOrbit h t ∈ {p | P p}ᶜ from hne) _
  simp [this] at ht

/-- The raw stream lift and its continuous representative agree almost everywhere globally. -/
theorem streamLift_ae_eq_contStream (ω : L2) : streamLift ω =ᵐ[volume] contStream ω :=
  ae_torusProj (coeFn_invLap_eq_continuousRep ω)

/-- The continuous stream representative is continuous on the real lift. -/
theorem continuous_contStream (ω : L2) : Continuous (contStream ω) :=
  (continuousRep (invLap ω)).continuous.comp isOpenQuotientMap_torusProj.continuous

private theorem torusProj_rotLift (p : ℝ × ℝ) : torusProj (rotLift p) = R (torusProj p) := by
  ext <;> simp [torusProj, rotLift, R, Real.Angle.coe_neg]

/-- The continuous representative inherits the rotation character pointwise. -/
theorem contStream_rotLift {ω : L2} {κ : Bool} (hκ : InRotationCharacter κ ω) (p : ℝ × ℝ) :
    contStream ω (rotLift p) = paritySign κ * contStream ω p := by
  change rotate ω = paritySign κ • ω at hκ
  have hrot : rotate (invLap ω) = paritySign κ • invLap ω := by
    change rotationSymmetry.action (invLap ω) = _
    rw [rotationSymmetry.invLap_commute]
    change invLap (rotate ω) = _
    rw [hκ, map_smul]
  have hi := coeFn_invLap_eq_continuousRep ω
  have hc := measurePreserving_R.quasiMeasurePreserving.ae_eq_comp hi
  have hr := Lp.coeFn_compMeasurePreserving (invLap ω) measurePreserving_R
  change (rotate (invLap ω) : Torus → ℂ) =ᵐ[volume] (fun t ↦ invLap ω (R t)) at hr
  rw [hrot] at hr
  have ha : (fun t ↦ continuousRep (invLap ω) (R t)) =ᵐ[volume]
      (fun t ↦ paritySign κ * continuousRep (invLap ω) t) := by
    filter_upwards [hr, hc, hi, Lp.coeFn_smul (paritySign κ) (invLap ω)] with t ht hct hit hst
    simp only [Function.comp_apply] at hct
    rw [← hct, ← ht, hst]
    change paritySign κ * invLap ω t = _
    rw [hit]
  have : (volume : Measure Torus).IsOpenPosMeasure := by
    change (volume : Measure (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi))).IsOpenPosMeasure
    infer_instance
  have heq := Measure.eq_of_ae_eq ha
    ((continuousRep (invLap ω)).continuous.comp (by unfold R; fun_prop))
    (continuous_const.mul (continuousRep (invLap ω)).continuous)
  change continuousRep (invLap ω) (torusProj (rotLift p)) = _
  rw [torusProj_rotLift]
  exact congrFun heq (torusProj p)

/-- Rotation of the raw vorticity lift holds almost everywhere, as it should for `L²` data. -/
theorem liftL2_rotLift_ae {ω : L2} {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∀ᵐ p, liftL2 ω (rotLift p) = paritySign κ * liftL2 ω p := by
  change rotate ω = paritySign κ • ω at hκ
  have hr := Lp.coeFn_compMeasurePreserving ω measurePreserving_R
  change (rotate ω : Torus → ℂ) =ᵐ[volume] (fun t ↦ ω (R t)) at hr
  rw [hκ] at hr
  have ha : ∀ᵐ t : Torus, ω (R t) = paritySign κ * ω t := by
    filter_upwards [hr, Lp.coeFn_smul (paritySign κ) ω] with t ht hst
    rw [← ht, hst]
    rfl
  filter_upwards [ae_torusProj ha] with p hp
  simpa only [liftL2, torusProj_rotLift] using hp

/-- Eigenfunctions form transport pairs with the continuous, rather than raw, stream lift. -/
theorem isTransportPair_contStream {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U)
    (hb : Bornology.IsBounded U) : IsTransportPair lam U (liftL2 ω) (contStream ω) := by
  have hp := isTransportPair_of_isEigenSolution hlam hω hU hb
  have heq := streamLift_ae_eq_contStream ω
  refine ⟨hlam, hU, hp.memLp, hp.memSobolevOn.congr_value heq,
    hp.hasWeakL0On.congr_value ?_⟩
  filter_upwards [heq] with p hp
  exact congrArg (fun z ↦ liftL2 ω p + z) hp

/-- Iterating the rotation character: `ψ̃(Rᵏ p) = κᵏ ψ̃(p)`. -/
theorem contStream_iterate_rotLift {ω : L2} {κ : Bool} (hκ : InRotationCharacter κ ω) (k : ℕ)
    (p : ℝ × ℝ) : contStream ω (rotLift^[k] p) = paritySign κ ^ k * contStream ω p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply, ih, contStream_rotLift hκ, pow_succ]
    ring

/-- The Melnikov identity on the arcs (`lem:ee-transport-traces`): for an eigenfunction with
    rotation character `κ`, the arc trace `g = ψ̃ ∘ γ_k` has integrable derivative and
    `∫ g' e^{-iλt} dt = 0`. From `melnikov` on `γ₀` and `g = κᵏ (ψ̃ ∘ γ₀)`. -/
theorem ee_melnikov {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (k : ℕ) :
    Integrable (deriv (contStream ω ∘ cellArc k)) ∧
      ∫ t, profileIntegrand lam (contStream ω ∘ cellArc k) t = 0 := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hU := isOrbitUnion_cellNeighbourhood
  have hp := isTransportPair_contStream hlam hω hU isBounded_cellNeighbourhood
  have hfR : ∀ p ∈ cellNeighbourhood, contStream ω (p.2, -p.1) = c * contStream ω p := by
    intro p _
    rw [hcc]
    exact contStream_rotLift hκ p
  have hvR : ∀ᵐ p ∂(volume.restrict cellNeighbourhood),
      liftL2 ω (p.2, -p.1) = c * liftL2 ω p := by
    simpa only [hcc, rotLift] using ae_restrict_of_ae (liftL2_rotLift_ae hκ)
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  obtain ⟨hg, hM⟩ := melnikov hp closure_cellSquare_subset_cellNeighbourhood hc hUR hfR hvR
    (continuous_contStream ω).continuousOn
  have hArc : (contStream ω ∘ cellArc k) =
      fun s ↦ paritySign κ ^ k * (contStream ω ∘ separatrixArc) s := by
    funext s
    exact contStream_iterate_rotLift hκ k (separatrixArc s)
  rw [hArc]
  refine ⟨by simpa only [deriv_const_mul_field'] using hg.const_mul (paritySign κ ^ k), ?_⟩
  simp only [profileIntegrand, deriv_const_mul_field', mul_assoc, integral_const_mul]
  simp only [profileIntegrand, mul_assoc] at hM
  rw [hM, mul_zero]

/-- Melnikov and pairing traces specialized to raw eigenfunction lifts and continuous arc
    traces. The only analytic admissions used are the existing transport-pair, Melnikov,
    pairing-limit and orbit-coordinate statements. -/
theorem ee_transport_traces {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (_hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) :
    (∀ k < 4, Integrable (deriv (contStream ω ∘ cellArc k))) ∧
    ∀ N : Set ℝ, volume N = 0 → ∃ hs : ℕ → ℝ,
      (∀ j, hs j ∈ Ioo 0 1 ∧ hs j ∉ N) ∧ Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun j ↦ levelIntegral (hs j) fun p ↦
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ s,
          (canonicalProfile lam (contStream ω ∘ cellArc k) s *
            (starRingEnd ℂ) (contStream ω (cellArc k s))).re)) := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hU := isOrbitUnion_cellNeighbourhood
  have hp := isTransportPair_contStream hlam hω hU isBounded_cellNeighbourhood
  have hfR : ∀ p ∈ cellNeighbourhood, contStream ω (p.2, -p.1) = c * contStream ω p := by
    intro p _
    rw [hcc]
    exact contStream_rotLift hκ p
  have hvR : ∀ᵐ p ∂(volume.restrict cellNeighbourhood),
      liftL2 ω (p.2, -p.1) = c * liftL2 ω p := by
    simpa only [hcc, rotLift] using ae_restrict_of_ae (liftL2_rotLift_ae hκ)
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  refine ⟨fun k _ ↦ (ee_melnikov hlam hω hκ k).1, ?_⟩
  · intro N hN
    have hvm : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    have hfm : Measurable (streamLift ω) := (Lp.stronglyMeasurable (invLap ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    have hcm := (continuous_contStream ω).measurable
    have hraw : Measurable (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) := by
      fun_prop
    have hcont : Measurable (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      fun_prop
    have hrep : (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) =ᵐ[volume]
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      filter_upwards [streamLift_ae_eq_contStream ω] with p hp
      rw [hp]
    have hlevels := ae_levelIntegral_congr hraw hcont hrep
    let Nr : Set ℝ := {h | h ∈ Ioo 0 1 ∧ levelIntegral h
      (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) ≠ levelIntegral h
      (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re)}
    have hNr : volume Nr = 0 := by
      have hh := (ae_restrict_iff' measurableSet_Ioo).1 hlevels
      simpa only [ae_iff, not_imp] using hh
    obtain ⟨seq, hseq, hlim, hpair⟩ := pairing_limit hp
      closure_cellSquare_subset_cellNeighbourhood hc hUR hfR hvR
      (continuous_contStream ω).continuousOn (hN := measure_union_null hN hNr)
    refine ⟨seq, fun j ↦ ⟨(hseq j).1, fun hj ↦ (hseq j).2.1 (Or.inl hj)⟩, hlim, ?_⟩
    apply hpair.congr
    intro j
    have heq : levelIntegral (seq j)
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) = levelIntegral (seq j)
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      by_contra hj
      exact (hseq j).2.1 (Or.inr ⟨(hseq j).1, hj⟩)
    exact heq.symm

end NoEmbeddedEigenvalues
