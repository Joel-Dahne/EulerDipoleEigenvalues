module

public import EulerDipoleEigenvalues.Geometry.OrbitCoordinates.SaddleNormalForm
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TransversalMollifier
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier

/-!
# Finite-order bounds from vanishing classical jets

Bounds for each derivative are obtained by repeated mean-value inequalities,
not by differentiating a value-only big-O estimate. The intermediate balls use
the product norm; Euclidean radius is used only after the norm comparison.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped ContDiff Topology

/-- Concatenation preserves the order of the specified classical derivatives. -/
theorem classicalComplexJet_append (v w : List (Fin 2)) (f : ℝ × ℝ → ℂ) :
    classicalComplexJet (v ++ w) f = classicalComplexJet v (classicalComplexJet w f) := by
  induction v with
  | nil => rfl
  | cons j v ih => simp only [List.cons_append, classicalComplexJet, ih]

/-- Smoothness of every ordered coordinate jet on the same open domain. -/
theorem contDiffOn_classicalComplexJet {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin 2)) :
    ContDiffOn ℝ ∞ (classicalComplexJet w f) U := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact contDiffOn_coordPartial hU ih j

private theorem norm_fderiv_le_coordPartial {f : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f q) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖coordPartial j f q‖ ≤ B) : ‖fderiv ℝ f q‖ ≤ 2 * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have he := congrArg (fderiv ℝ f q) hv
  simp only [map_add, map_smul] at he
  rw [he]
  have h0 : ‖fderiv ℝ f q (1, 0)‖ ≤ B := by
    simpa only [coordPartial, ite_true, partialX_eq_fderiv hf] using hb 0
  have h1 : ‖fderiv ℝ f q (0, 1)‖ ≤ B := by
    simpa [coordPartial, partialY_eq_fderiv hf] using hb 1
  calc
    _ ≤ ‖v.1‖ * ‖fderiv ℝ f q (1, 0)‖ + ‖v.2‖ * ‖fderiv ℝ f q (0, 1)‖ := by
      simpa only [norm_smul] using norm_add_le
        (v.1 • fderiv ℝ f q (1, 0)) (v.2 • fderiv ℝ f q (0, 1))
    _ ≤ ‖v.1‖ * B + ‖v.2‖ * B := add_le_add
      (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ ≤ (2 * B) * ‖v‖ := by
      nlinarith [mul_le_mul_of_nonneg_right (norm_fst_le v) hB,
        mul_le_mul_of_nonneg_right (norm_snd_le v) hB]

/-- A bounded top jet and vanishing lower jets give a quantitative Taylor bound.
The constant and radius are uniform in the point. -/
theorem norm_le_pow_of_flat_jet {c : ℝ × ℝ} {R B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Metric.ball c R))
    (hz : ∀ w : List (Fin 2), w.length < n → classicalComplexJet w f c = 0)
    (hb : ∀ w : List (Fin 2), w.length = n → ∀ p ∈ Metric.ball c R,
      ‖classicalComplexJet w f p‖ ≤ B) :
    ∀ p ∈ Metric.ball c R, ‖f p‖ ≤ (2 ^ n * B) * dist p c ^ n := by
  induction n generalizing f with
  | zero =>
    intro p hp
    simpa only [classicalComplexJet, pow_zero, one_mul, mul_one] using hb [] rfl p hp
  | succ n ih =>
    intro p hp
    have hpR : dist p c < R := hp
    have hf0 : f c = 0 := hz [] (by simp)
    have hd (j : Fin 2) (q : ℝ × ℝ) (hq : q ∈ Metric.ball c R) :
        ‖coordPartial j f q‖ ≤ (2 ^ n * B) * dist q c ^ n := by
      apply ih (contDiffOn_coordPartial Metric.isOpen_ball hf j) _ _ q hq
      · intro w hw
        simpa only [classicalComplexJet_append, classicalComplexJet] using
          hz (w ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
      · intro w hw x hx
        simpa only [classicalComplexJet_append, classicalComplexJet] using
          hb (w ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega) x hx
    have hsub : Metric.closedBall c (dist p c) ⊆ Metric.ball c R := by
      intro q hq
      exact lt_of_le_of_lt hq hpR
    have hdiff (q : ℝ × ℝ) (hq : q ∈ Metric.closedBall c (dist p c)) :
        DifferentiableAt ℝ f q :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hsub hq))).differentiableAt (by simp)
    have hder (q : ℝ × ℝ) (hq : q ∈ Metric.closedBall c (dist p c)) :
        ‖fderiv ℝ f q‖ ≤ 2 * ((2 ^ n * B) * dist p c ^ n) := by
      apply norm_fderiv_le_coordPartial (hdiff q hq) (by positivity)
      intro j
      exact (hd j q (hsub hq)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ dist_nonneg hq n) (by positivity))
    have he := (convex_closedBall c (dist p c)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hder (Metric.mem_closedBall_self dist_nonneg)
      (Metric.mem_closedBall.mpr (le_refl (dist p c)))
    simpa only [hf0, sub_zero, ← dist_eq_norm, pow_succ, mul_assoc, mul_left_comm, mul_comm]
      using he

/-- One bounded top jet on one precompact neighbourhood, uniformly over words. -/
theorem exists_bound_top_classicalJet {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} (hc : c ∈ U) {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧ Metric.ball c R ⊆ U ∧
      ∀ w : List (Fin 2), w.length = n → ∀ p ∈ Metric.ball c R,
        ‖classicalComplexJet w f p‖ ≤ B := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  have hs : Metric.closedBall c (r / 2) ⊆ U := by
    intro p hp
    exact hsub (lt_of_le_of_lt hp (half_lt_self hr))
  let G (p : ℝ × ℝ) : (Fin n → Fin 2) → ℂ :=
    fun v ↦ classicalComplexJet (List.ofFn v) f p
  have hg : ContinuousOn G (Metric.closedBall c (r / 2)) :=
    continuousOn_pi.mpr fun v ↦
      ((contDiffOn_classicalComplexJet hU hf (List.ofFn v)).continuousOn).mono hs
  obtain ⟨B, hb⟩ := (isCompact_closedBall c (r / 2)).exists_bound_of_continuousOn hg
  refine ⟨r / 2, max B 1, by linarith, by positivity,
    fun p hp ↦ hs (Metric.ball_subset_closedBall hp), ?_⟩
  intro w hw p hp
  obtain ⟨v, hv⟩ : ∃ v : Fin n → Fin 2, List.ofFn v = w := by
    subst n
    exact ⟨w.get, List.ofFn_get w⟩
  calc
    ‖classicalComplexJet w f p‖ = ‖G p v‖ := by rw [← hv]
    _ ≤ ‖G p‖ := norm_le_pi_norm _ _
    _ ≤ B := hb p (Metric.ball_subset_closedBall hp)
    _ ≤ max B 1 := le_max_left _ _

/-- All differentiated Taylor bounds share one constant and one neighbourhood. -/
theorem exists_classicalJet_flat_bounds {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} (hc : c ∈ U) {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (hz : ∀ w : List (Fin 2), w.length < n → classicalComplexJet w f c = 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ Metric.ball c R ⊆ U ∧
      ∀ w : List (Fin 2), w.length ≤ n → ∀ p ∈ Metric.ball c R,
        ‖classicalComplexJet w f p‖ ≤ C * dist p c ^ (n - w.length) := by
  obtain ⟨R, B, hR, hB, hsub, hb⟩ := exists_bound_top_classicalJet hU hc hf n
  refine ⟨R, 2 ^ n * B, hR, by positivity, hsub, ?_⟩
  intro w hw p hp
  have hf' := contDiffOn_classicalComplexJet Metric.isOpen_ball (hf.mono hsub) w
  have he := norm_le_pow_of_flat_jet hB.le (n - w.length) hf'
    (fun v hv ↦ by
      rw [← classicalComplexJet_append]
      exact hz (v ++ w) (by simp only [List.length_append]; omega))
    (fun v hv q hq ↦ by
      rw [← classicalComplexJet_append]
      exact hb (v ++ w) (by simp only [List.length_append]; omega) q hq) p hp
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg dist_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le n w.length)) hB.le

/-- Euclidean-radius form of the finite Taylor bounds, on a genuine disk. -/
theorem exists_radial_classicalJet_flat_bounds {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} (hc : c ∈ U) {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (hz : ∀ w : List (Fin 2), w.length < n → classicalComplexJet w f c = 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ localDisk c R ⊆ U ∧
      ∀ w : List (Fin 2), w.length ≤ n → ∀ p ∈ localDisk c R,
        ‖classicalComplexJet w f p‖ ≤ C * localRadius c p ^ (n - w.length) := by
  obtain ⟨R, C, hR, hC, hsub, hb⟩ := exists_classicalJet_flat_bounds hU hc hf n hz
  have hs : localDisk c R ⊆ Metric.ball c R :=
    fun p hp ↦ (dist_le_localRadius c p).trans_lt hp
  refine ⟨R, C, hR, hC, hs.trans hsub, fun w hw p hp ↦ ?_⟩
  exact (hb w hw p (hs hp)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ dist_nonneg (dist_le_localRadius c p) _) hC.le)

/-- Local smoothness suffices for the actual classical weak derivative. -/
theorem hasWeakPartialOn_of_contDiffOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : Fin 2) :
    HasWeakPartialOn U j f (coordPartial j f) := by
  have h1 : HasWeakPartialOn U j (fun _ ↦ (1 : ℂ)) (fun _ ↦ (0 : ℂ)) := by
    have he : coordPartial j (fun _ : ℝ × ℝ ↦ (1 : ℂ)) = (fun _ ↦ (0 : ℂ)) := by
      funext p
      unfold coordPartial
      split_ifs <;> simp [partialX, partialY]
    simpa only [he] using
      hasWeakPartialOn_of_contDiff (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ ↦ (1 : ℂ))) U j
  simpa only [mul_one, mul_zero, add_zero] using h1.mul_contDiffOn hU hf

/-- Every local smooth jet is a specified weak jet on the full open domain. -/
theorem classicalComplexJet_weakOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    HasWeakJetOn n U f (fun w ↦ classicalComplexJet w f) :=
  ⟨rfl, fun w _ j ↦ hasWeakPartialOn_of_contDiffOn hU
    (contDiffOn_classicalComplexJet hU hf w) j⟩

/-- A smooth flat jet has genuine finite radial L² mass, not merely totalized
energies. All entries use the same positive-radius disk. -/
theorem exists_radial_classicalJet_flat_memLp {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} (hc : c ∈ U) {f : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (hz : ∀ w : List (Fin 2), w.length < n → classicalComplexJet w f c = 0) :
    ∃ R : ℝ, 0 < R ∧ localDisk c R ⊆ U ∧
      HasWeakJetOn n (localDisk c R) f (fun w ↦ classicalComplexJet w f) ∧
      ∀ k ≤ n, RadialJetLp k (n - k) (localDisk c R) c
        (fun w ↦ classicalComplexJet w f) := by
  obtain ⟨R, C, hR, hC, hsub, hb⟩ := exists_radial_classicalJet_flat_bounds hU hc hf n hz
  have hV : IsOpen (localDisk c R) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have : IsFiniteMeasure (volume.restrict (localDisk c R)) := by
    apply isFiniteMeasure_restrict.mpr
    exact (Metric.isBounded_ball.subset (show localDisk c R ⊆ Metric.ball c R from
      fun p hp ↦ (dist_le_localRadius c p).trans_lt hp)).measure_lt_top.ne
  refine ⟨R, hR, hsub, classicalComplexJet_weakOn hV (hf.mono hsub) n, ?_⟩
  intro k hk w hw
  have hcont := (contDiffOn_classicalComplexJet hU hf w).continuousOn.mono hsub
  have hm := hcont.aestronglyMeasurable (μ := volume) hV.measurableSet
  have hden : Measurable (fun p ↦ (localRadius c p ^ (n - k) : ℂ)) := by
    unfold localRadius
    fun_prop
  have hconst : MemLp (fun _ : ℝ × ℝ ↦ C) 2 (volume.restrict (localDisk c R)) :=
    memLp_const _
  apply hconst.mono' (hm.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
  dsimp only [Pi.div_apply]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _)]
  by_cases hr : localRadius c p ^ (n - k) = 0
  · simp only [hr, div_zero]
    exact hC.le
  · have hrpos : 0 < localRadius c p ^ (n - k) :=
      lt_of_le_of_ne (pow_nonneg (show 0 ≤ localRadius c p from Real.sqrt_nonneg _) _)
        (Ne.symm hr)
    apply (div_le_iff₀ hrpos).mpr
    simpa only [hw] using hb w (by omega) p hp

/-- Subtraction commutes with every ordered classical jet on an open set. -/
theorem classicalComplexJet_sub_on {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f g : ℝ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (w : List (Fin 2)) :
    EqOn (classicalComplexJet w (fun p ↦ f p - g p))
      (fun p ↦ classicalComplexJet w f p - classicalComplexJet w g p) U := by
  induction w with
  | nil => intro p hp; rfl
  | cons j w ih =>
    intro p hp
    have he : classicalComplexJet w (fun p ↦ f p - g p) =ᶠ[𝓝 p]
        (fun p ↦ classicalComplexJet w f p - classicalComplexJet w g p) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hp, ih⟩
    change coordPartial j _ p = _
    rw [coordPartial_congr_nhds he]
    have hdF := ((contDiffOn_classicalComplexJet hU hf w).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
    have hdG := ((contDiffOn_classicalComplexJet hU hg w).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
    change coordPartial j (fun p ↦ classicalComplexJet w f p - classicalComplexJet w g p) p =
      coordPartial j (classicalComplexJet w f) p - coordPartial j (classicalComplexJet w g) p
    unfold coordPartial
    split_ifs
    · exact partialX_sub hdF hdG
    · exact partialY_sub hdF hdG

end EulerDipoleEigenvalues
