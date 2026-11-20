import NoEmbeddedEigenvalues.Certificates.Mixed
import NoEmbeddedEigenvalues.MixedRobinCutoff
import NoEmbeddedEigenvalues.Analysis.BoundaryConeTrace
import NoEmbeddedEigenvalues.RectangleH1Approximation

/-!
# Mixed second-order comparison forms

Everything in this file uses diagonal coordinates and Lebesgue measure `da db`.
The boundary inputs are transverse Sobolev traces, not evaluations of an
arbitrary almost-everywhere representative.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Set MeasureTheory ComplexConjugate Filter
open scoped Topology
open scoped ContDiff

/-- The Robin side of the quarter form uses tangential coordinate `a`. -/
def mixedQuarterForm (z za zb : ℝ × ℝ → ℂ) (top : ℝ → ℂ) : ℝ :=
  (∫ q in mixedQuarterCell, mixedComparisonDiagonal q * (‖za q‖ ^ 2 + ‖zb q‖ ^ 2) +
    2 * mixedComparisonOffDiagonal q * (za q * conj (zb q)).re +
    mixedComparisonPotential q * ‖z q‖ ^ 2) +
  ∫ a in Ioo (0 : ℝ) (Real.pi / 2), Real.cos a * ‖top a‖ ^ 2

/-- Finite H¹ data on the quarter, including the canonical trace on its Robin side. -/
structure MixedQuarterFormDomain (z za zb : ℝ × ℝ → ℂ) (top : ℝ → ℂ) : Prop where
  h1 : MemSobolevOn 1 mixedQuarterCell z
  weakA : HasWeakPartialOn mixedQuarterCell 0 z za
  weakB : HasWeakPartialOn mixedQuarterCell 1 z zb
  topTrace : HasTransverseH1Trace 0 (Real.pi / 2) 0 (Real.pi / 2) (Real.pi / 2) id z top

/-- The vanishing trace is on `a=0` for odd-in-a and on `b=0` for odd-in-b. -/
def MixedQuarterZeroTrace (oddA : Bool) (z : ℝ × ℝ → ℂ) : Prop :=
  HasTransverseH1Trace 0 (Real.pi / 2) 0 (Real.pi / 2) 0
    (axisTraceChart (if oddA then 0 else 1)) z (fun _ ↦ 0)

local notation "L" => (Real.pi / 2)
local notation "Q" => mixedQuarterCell
local notation "S" => (Ioo (0 : ℝ) L)

/-- Smooth approximation in the form norm, on the fixed open quarter and
its canonical top trace. The approximants vanish pointwise on the odd axis. -/
def MixedQuarterSmoothApproximation (oddA : Bool)
    (z za zb : ℝ × ℝ → ℂ) (top : ℝ → ℂ) : Prop :=
  ∃ v : ℕ → ℝ × ℝ → ℂ, (∀ n, ContDiff ℝ 2 (v n)) ∧
    (∀ n t, t ∈ Icc 0 L → (if oddA then v n (0, t) else v n (t, 0)) = 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun q ↦ v n q - z q) 2 (volume.restrict Q)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun q ↦ partialX (v n) q - za q) 2 (volume.restrict Q))
      atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun q ↦ partialY (v n) q - zb q) 2 (volume.restrict Q))
      atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun x ↦ v n (x, L) - top x) 2 (volume.restrict S)) atTop (𝓝 0)

private theorem mixed_quarter_weak_memLp {z d : ℝ × ℝ → ℂ} {j : Fin 2}
    (h : MemSobolevOn 1 Q z) (hd : HasWeakPartialOn Q j z d) :
    MemLp d 2 (volume.restrict Q) := by
  obtain ⟨D, hD, hLp⟩ := h.2 j
  have ho : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  exact hLp.ae_eq ((ae_restrict_iff' ho.measurableSet).mpr (hD.ae_eq ho hd))

/-- Density in the quarter H¹ space with a specified zero odd-axis trace. -/
theorem mixed_quarter_smooth_approximation (oddA : Bool)
    {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ} (hz : MixedQuarterFormDomain z za zb top)
    (hzero : MixedQuarterZeroTrace oddA z) : MixedQuarterSmoothApproximation oddA z za zb top := by
  have hL : 0 < L := half_pos Real.pi_pos
  have hzB := mixed_quarter_weak_memLp hz.h1 hz.weakB
  cases oddA
  · obtain ⟨v, hv, hzero', tv, tx, ty⟩ :=
      square_smooth_approximation_odd_snd hL hz.h1 hz.weakA hz.weakB hzero
    exact ⟨v, hv, fun n t _ ↦ hzero' n t, tv, tx, ty,
      hz.topTrace.tendsto_smooth_top hz.weakB hz.h1.1 hzB
        (fun n ↦ (hv n).of_le (by norm_num)) tv ty⟩
  · obtain ⟨v, hv, hzero', tv, tx, ty⟩ :=
      square_smooth_approximation_odd_fst hL hz.h1 hz.weakA hz.weakB hzero
    exact ⟨v, hv, fun n t _ ↦ hzero' n t, tv, tx, ty,
      hz.topTrace.tendsto_smooth_top hz.weakB hz.h1.1 hzB
        (fun n ↦ (hv n).of_le (by norm_num)) tv ty⟩

private theorem mixed_quarter_weight_memLp :
    MemLp mixedComparisonDiagonal ⊤ (volume.restrict Q) ∧
      MemLp (fun q ↦ 2 * mixedComparisonOffDiagonal q) ⊤ (volume.restrict Q) ∧
      MemLp mixedComparisonPotential ⊤ (volume.restrict Q) ∧
      MemLp (fun q : ℝ × ℝ ↦ Real.cos q.1 ^ 2) ⊤ (volume.restrict Q) ∧
      MemLp Real.cos ⊤ (volume.restrict S) := by
  have hm : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  have hM (q : ℝ × ℝ) (hq : q ∈ Q) :
      q ∈ Ico 0 L ×ˢ Icc 0 L :=
    ⟨⟨hq.1.1.le, hq.1.2⟩, Ioo_subset_Icc_self hq.2⟩
  have hc (q : ℝ × ℝ) (hq : q ∈ Q) :=
    mixed_robin_coefficients_contDiffAt (n := 0) (hM q hq)
  have hD : ContinuousOn mixedComparisonDiagonal Q :=
    fun q hq ↦ (hc q hq).1.continuousAt.continuousWithinAt
  have hE : ContinuousOn (fun q ↦ 2 * mixedComparisonOffDiagonal q) Q :=
    fun q hq ↦ ((hc q hq).2.continuousAt.const_mul 2).continuousWithinAt
  have hV : ContinuousOn mixedComparisonPotential Q := fun q hq ↦
    (mixed_robin_potential_continuousAt (hM q hq) (Or.inl hq.1.1)).continuousWithinAt
  have hb (q : ℝ × ℝ) (hq : q ∈ Q) := mixed_comparison_coefficient_bounds
    (p := q) (show q ∈ mixedOpenCell from
      ⟨⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩,
        ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩⟩)
  refine ⟨memLp_top_of_bound (hD.aestronglyMeasurable hm) 3 ?_,
    memLp_top_of_bound (hE.aestronglyMeasurable hm) 4 ?_,
    memLp_top_of_bound (hV.aestronglyMeasurable hm) 4 ?_,
    memLp_top_of_bound (by fun_prop) 1 ?_,
    memLp_top_of_bound Real.continuous_cos.aestronglyMeasurable 1 ?_⟩
  · filter_upwards [ae_restrict_mem hm] with q hq
    have hq' : q ∈ mixedOpenCell := ⟨⟨by linarith [hq.1.1, Real.pi_pos], hq.1.2⟩,
      ⟨by linarith [hq.2.1, Real.pi_pos], hq.2.2⟩⟩
    have hpos := (mixed_comparison_matrix_positive hq').1
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (hb q hq).2.2.1
  · filter_upwards [ae_restrict_mem hm] with q hq
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [(hb q hq).2.2.2]
  · filter_upwards [ae_restrict_mem hm] with q hq
    have h := hb q hq
    rw [Real.norm_eq_abs, abs_of_nonpos (neg_nonneg.mp h.1)]
    exact h.2.1
  · exact Eventually.of_forall fun q ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  · exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- The smooth Robin inequality passes to the given strong approximants. -/
theorem mixed_robin_comparison_of_approximation (oddA : Bool) {ρ : ℝ × ℝ → ℝ}
    (hρ : MixedRobinMultiplier ρ) {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    (hrobin : ∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ mixedRobinNumerator oddA ρ h)
    {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ}
    (hz : MixedQuarterFormDomain z za zb top)
    (hv : MixedQuarterSmoothApproximation oddA z za zb top) :
    c * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      mixedQuarterForm z za zb top := by
  obtain ⟨v, hv, hvzero, tv, tx, ty, tt⟩ := hv
  have hza := mixed_quarter_weak_memLp hz.h1 hz.weakA
  have hzb := mixed_quarter_weak_memLp hz.h1 hz.weakB
  have hzt : MemLp top 2 (volume.restrict S) :=
    (hz.topTrace.l2_estimate_of_weak_snd hz.weakB hzb).1
  have hZ : MemLp z 2 (volume.restrict Q) := hz.h1.1
  have hL (u : ℝ × ℝ → ℂ) (hu : Continuous u) : MemLp u 2 (volume.restrict Q) :=
    memLp_two_restrict_of_continuous hu (isOpen_Ioo.prod isOpen_Ioo) (by
      change IsCompact (closure (Ioo (0 : ℝ) L ×ˢ Ioo (0 : ℝ) L))
      rw [closure_prod_eq, closure_Ioo (half_pos Real.pi_pos).ne]
      exact isCompact_Icc.prod isCompact_Icc)
  have h0 (n : ℕ) := hL (v n) (hv n).continuous
  have h1 (n : ℕ) := hL (partialX (v n)) (contDiff_partialX (n := 1) (hv n)).continuous
  have h2 (n : ℕ) := hL (partialY (v n)) (contDiff_partialY (n := 1) (hv n)).continuous
  have ht (n : ℕ) : MemLp (fun x ↦ v n (x, L)) 2 (volume.restrict S) := by
    have hc : Continuous (fun x ↦ v n (x, L)) :=
      (hv n).continuous.comp (continuous_id.prodMk continuous_const)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
      (s := Icc (0 : ℝ) L)
    have hb := memLp_top_of_bound hc.aestronglyMeasurable C
      ((ae_restrict_mem (μ := volume) measurableSet_Ioo).mono
        fun x hx ↦ hC x (Ioo_subset_Icc_self hx))
    let : IsFiniteMeasure (volume.restrict S) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact measure_Ioo_lt_top⟩
    exact hb.mono_exponent (by simp)
  obtain ⟨hD, hE, hV, hW, hCos⟩ := mixed_quarter_weight_memLp
  have hr (a : ℂ) : (a * conj a).re = ‖a‖ ^ 2 := by
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  have hm := bounded_real_pair_limit_of_L2 hW h0 h0 hZ hZ tv tv
  have ha := bounded_real_pair_limit_of_L2 hD h1 h1 hza hza tx tx
  have hb := bounded_real_pair_limit_of_L2 hD h2 h2 hzb hzb ty ty
  have he := bounded_real_pair_limit_of_L2 hE h1 h2 hza hzb tx ty
  have hp := bounded_real_pair_limit_of_L2 hV h0 h0 hZ hZ tv tv
  have htop := bounded_real_pair_limit_of_L2 hCos ht ht hzt hzt tt tt
  simp only [hr] at hm ha hb hp htop
  have hbulk {u a b : ℝ × ℝ → ℂ}
      (h₁ : IntegrableOn (fun q ↦ mixedComparisonDiagonal q * ‖a q‖ ^ 2) Q)
      (h₂ : IntegrableOn (fun q ↦ mixedComparisonDiagonal q * ‖b q‖ ^ 2) Q)
      (h₃ : IntegrableOn (fun q ↦ (2 * mixedComparisonOffDiagonal q) * (a q * conj (b q)).re) Q)
      (h₄ : IntegrableOn (fun q ↦ mixedComparisonPotential q * ‖u q‖ ^ 2) Q) :
      (∫ q in Q, mixedRobinBulk u a b q) =
        (∫ q in Q, mixedComparisonDiagonal q * ‖a q‖ ^ 2) +
        (∫ q in Q, mixedComparisonDiagonal q * ‖b q‖ ^ 2) +
        (∫ q in Q, (2 * mixedComparisonOffDiagonal q) * (a q * conj (b q)).re) +
        ∫ q in Q, mixedComparisonPotential q * ‖u q‖ ^ 2 := by
    simp only [mixedRobinBulk, mul_add]
    have h := integral_add ((h₁.add h₂).add h₃) h₄
    have h' := integral_add (h₁.add h₂) h₃
    have h'' := integral_add h₁ h₂
    simp only [Pi.add_apply] at h h' h''
    rw [h, h', h'']
  have hbLim : Tendsto (fun n ↦ ∫ q in Q, mixedRobinBulk (v n)
      (partialX (v n)) (partialY (v n)) q) atTop (𝓝 (∫ q in Q, mixedRobinBulk z za zb q)) := by
    rw [hbulk ha.2.1 hb.2.1 he.2.1 hp.2.1]
    exact (((ha.2.2.add hb.2.2).add he.2.2).add hp.2.2).congr' (Eventually.of_forall fun n ↦
      (hbulk (ha.1 n) (hb.1 n) (he.1 n) (hp.1 n)).symm)
  exact le_of_tendsto_of_tendsto (hm.2.2.const_mul c) (hbLim.add htop.2.2)
    (Eventually.of_forall fun n ↦
      mixed_robin_comparison_smooth oddA hρ hinterior hrobin (hv n) (hvzero n))

/-- The logarithmic Robin comparison lemma for either odd axis. -/
theorem mixed_robin_comparison (oddA : Bool) {ρ : ℝ × ℝ → ℝ} (hρ : MixedRobinMultiplier ρ)
    {c : ℝ}
    (hinterior : ∀ q ∈ mixedQuarterCell,
      c * Real.cos q.1 ^ 2 * mixedRobinComparison oddA ρ q ≤
        mixedComparisonOperator (mixedRobinComparison oddA ρ) q)
    (hrobin : ∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ mixedRobinNumerator oddA ρ h)
    {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ}
    (hz : MixedQuarterFormDomain z za zb top) (hzero : MixedQuarterZeroTrace oddA z) :
    c * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      mixedQuarterForm z za zb top :=
  mixed_robin_comparison_of_approximation oddA hρ hinterior hrobin hz
    (mixed_quarter_smooth_approximation oddA hz hzero)

private theorem mixed_exp_partials {q : ℝ × ℝ} (hs : 0 < q.1 + q.2) :
    partialX (fun p ↦ Real.exp (mixedOddAExponent p)) q =
      Real.exp (mixedOddAExponent q) * partialX mixedOddAExponent q ∧
    partialY (fun p ↦ Real.exp (mixedOddAExponent p)) q =
      Real.exp (mixedOddAExponent q) * partialY mixedOddAExponent q := by
  have h := (mixedOddAExponent_contDiffAt (n := 1) hs).differentiableAt (by norm_num)
  have hx := h.comp q.1 (show DifferentiableAt ℝ (fun x : ℝ ↦ (x, q.2)) q.1 by fun_prop)
  have hy := h.comp q.2 (show DifferentiableAt ℝ (fun y : ℝ ↦ (q.1, y)) q.2 by fun_prop)
  exact ⟨hx.hasDerivAt.exp.deriv, hy.hasDerivAt.exp.deriv⟩

/-- The two explicit multipliers meet the regularity and boundedness
hypotheses for logarithmic Robin comparison. -/
theorem mixed_explicit_robin_multipliers :
    MixedRobinMultiplier (fun q ↦ Real.exp (mixedOddAExponent q)) ∧
    MixedRobinMultiplier mixedOddBMultiplier := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn mixedOddAExponent K := mixedOddAExponent_continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hM' (q : ℝ × ℝ) (hq : q ∈ K) :
      Real.exp (-M) ≤ Real.exp (mixedOddAExponent q) ∧
        Real.exp (mixedOddAExponent q) ≤ Real.exp M := by
    have hb : |mixedOddAExponent q| ≤ M := by simpa only [Real.norm_eq_abs] using hM q hq
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp hb).1, Real.exp_le_exp.mpr (abs_le.mp hb).2⟩
  constructor
  · refine ⟨?_, Real.continuous_exp.comp_continuousOn hcont,
      ⟨Real.exp (-M), Real.exp M, Real.exp_pos _, hM'⟩, ?_⟩
    · refine ⟨{q | 0 < q.1 + q.2}, isOpen_lt continuous_const
        (continuous_fst.add continuous_snd), fun q hq ↦ ?_, fun q hq ↦ ?_⟩
      · exact add_pos_of_pos_of_nonneg hq.1.1 hq.2.1
      · exact (Real.contDiff_exp.contDiffAt.comp q
          (mixedOddAExponent_contDiffAt hq)).contDiffWithinAt
    · obtain ⟨C, hC, hb⟩ := mixed_odd_a_exponent_bounds_regular
      refine ⟨2 * Real.exp M * C, by positivity, fun q hq ↦ ?_⟩
      obtain ⟨hx, hy⟩ := mixed_exp_partials (add_pos_of_pos_of_nonneg hq.1.1 hq.2.1)
      obtain ⟨_, hbx, hby⟩ := hb q hq
      have hE := (hM' q ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩).2
      rw [hx, hy, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ Real.exp M * C + Real.exp M * C :=
          add_le_add (mul_le_mul hE hbx (abs_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul hE hby (abs_nonneg _) (Real.exp_pos _).le)
        _ = 2 * Real.exp M * C := by ring
        _ ≤ _ := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (abs_nonneg _))
  · refine ⟨?_, mixedOddBMultiplier_continuous.continuousOn,
      ⟨3 / 4, 5 / 3, by norm_num, fun _ hq ↦ mixed_odd_b_multiplier_closed_bounds hq⟩,
      mixed_odd_b_multiplier_derivative_bound⟩
    exact ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst, fun _ hq ↦ hq.1.1,
      fun _ hq ↦ (mixedOddBMultiplier_contDiffAt hq).contDiffWithinAt⟩

/-- The Robin numerator of the exponential multiplier, with its positive
exponential factored out. -/
private theorem mixed_odd_a_robin_exp {h : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) :
    0 ≤ mixedRobinNumerator true (fun q ↦ Real.exp (mixedOddAExponent q)) h := by
  obtain ⟨hx', hy'⟩ := mixed_exp_partials (q := (h, 0)) (by simpa using hh.1)
  unfold mixedRobinNumerator
  simp only [ite_true, hx', hy']
  have hsign : 0 ≤ 3 * h - 2 * (1 - h ^ 2) * partialX mixedOddAExponent (h, 0) -
      (2 - h ^ 2) * partialY mixedOddAExponent (h, 0) :=
    (div_nonneg hh.1.le (by norm_num) : 0 ≤ h / 250).trans (mixed_odd_a_robin h hh)
  convert mul_nonneg (Real.exp_pos (mixedOddAExponent (h, 0))).le hsign using 1; ring

/-- Both certified quarter comparisons give the common lower bound 1/200. -/
theorem mixed_quarter_coercivity (oddA : Bool) {z za zb : ℝ × ℝ → ℂ} {top : ℝ → ℂ}
    (hz : MixedQuarterFormDomain z za zb top) (hzero : MixedQuarterZeroTrace oddA z) :
    (1 / 200 : ℝ) * (∫ q in mixedQuarterCell, Real.cos q.1 ^ 2 * ‖z q‖ ^ 2) ≤
      mixedQuarterForm z za zb top := by
  cases oddA
  · have h := mixed_robin_comparison false mixed_explicit_robin_multipliers.2
      (c := 1 / 100) (fun _ hq ↦ mixed_odd_b_interior hq)
      (fun h hh ↦ (mul_nonneg (by norm_num) hh.1.le : 0 ≤ 1789 / 2500 * h).trans
        (mixed_odd_b_multiplier_robin.2 h hh)) hz hzero
    exact (mul_le_mul_of_nonneg_right (by norm_num)
      (integral_nonneg fun _ ↦ by positivity)).trans h
  · exact mixed_robin_comparison true mixed_explicit_robin_multipliers.1
      (fun _ hq ↦ mixed_odd_a_interior hq) (fun _ hh ↦ mixed_odd_a_robin_exp hh) hz hzero

end NoEmbeddedEigenvalues
