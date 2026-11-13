import NoEmbeddedEigenvalues.SmoothJetBounds
import NoEmbeddedEigenvalues.Regularity.CylinderInverse
import NoEmbeddedEigenvalues.SaddleForcingMass

/-!
# Finite quadratic remainders of odd--odd cylinder data

Axis parity is first identified pointwise for the continuous representative.
The coefficient is the mixed second derivative at the origin. Finite Taylor
bounds then control the value and each derivative on the same disk; no infinite
harmonic expansion or evaluation of raw L² representatives on axes is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff Topology

/-- Euclidean disks centered at the origin are invariant under axis reflection. -/
theorem localRadius_axisReflect (j : Fin 2) (p : ℝ × ℝ) :
    localRadius 0 (axisReflect j p) = localRadius 0 p := by
  unfold axisReflect
  split_ifs <;> simp [localRadius]

/-- Continuous representatives inherit the axis identities everywhere on a disk. -/
theorem HasAxisParityOn.eqOn_disk {ρ : ℝ} {ε : Fin 2 → Bool} {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) f) (hf : ContinuousOn f (localDisk 0 ρ))
    (j : Fin 2) :
    EqOn (fun p ↦ f (axisReflect j p)) (fun p ↦ paritySign (ε j) * f p) (localDisk 0 ρ) := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hc : Continuous (axisReflect j) := by
    unfold axisReflect
    split_ifs <;> fun_prop
  apply Measure.eqOn_open_of_ae_eq (hp j) hU
  · exact hf.comp hc.continuousOn fun p hp ↦ by
      change localRadius 0 (axisReflect j p) < ρ
      rwa [localRadius_axisReflect]
  · exact continuousOn_const.mul hf

/-- Pure second jets vanish at the center for continuous odd--odd data. -/
theorem oddOdd_pure_second_zero {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn (fun _ ↦ false) (localDisk 0 ρ) f)
    (hf : ContinuousOn f (localDisk 0 ρ)) :
    ∀ j : Fin 2, classicalComplexJet [j, j] f 0 = 0 := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hx : (fun t : ℝ ↦ f (t, 0)) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    have ht := (continuous_id.prodMk (continuous_const (y := (0 : ℝ)))).continuousAt
      |>.preimage_mem_nhds (hU.mem_nhds h0)
    filter_upwards [ht] with t ht
    have he := hp.eqOn_disk hf 1 ht
    simp only [axisReflect, show (1 : Fin 2) ≠ 0 by decide, ite_false, neg_zero,
      paritySign, Bool.false_eq_true, neg_one_mul] at he
    exact CharZero.eq_neg_self_iff.mp he
  have hy : (fun t : ℝ ↦ f (0, t)) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    have ht := ((continuous_const (y := (0 : ℝ))).prodMk continuous_id).continuousAt
      |>.preimage_mem_nhds (hU.mem_nhds h0)
    filter_upwards [ht] with t ht
    have he := hp.eqOn_disk hf 0 ht
    simp only [axisReflect, ite_true, neg_zero, paritySign, Bool.false_eq_true,
      ite_false, neg_one_mul] at he
    exact CharZero.eq_neg_self_iff.mp he
  intro j
  fin_cases j
  · change deriv (deriv (fun t : ℝ ↦ f (t, 0))) 0 = 0
    simpa using hx.deriv.deriv_eq
  · change deriv (deriv (fun t : ℝ ↦ f (0, t))) 0 = 0
    simpa using hy.deriv.deriv_eq

/-- The quadratic in normalized saddle coordinates. -/
def saddleAxisQuadratic (a : ℂ) (p : ℝ × ℝ) : ℂ := a * ((p.1 * p.2 : ℝ) : ℂ)

/-- The normalized chart quadratic is globally smooth. -/
theorem contDiff_saddleAxisQuadratic (a : ℂ) : ContDiff ℝ ∞ (saddleAxisQuadratic a) := by
  unfold saddleAxisQuadratic
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul contDiff_snd))

private theorem axisQuadratic_first (a : ℂ) (j : Fin 2) :
    coordPartial j (saddleAxisQuadratic a) =
      fun p ↦ a * ((if j = 0 then p.2 else p.1 : ℝ) : ℂ) := by
  funext p
  fin_cases j
  · have hd := ((hasDerivAt_id p.1).mul_const p.2).ofReal_comp.const_mul a
    simpa [coordPartial, partialX, saddleAxisQuadratic] using hd.deriv
  · have hd := ((hasDerivAt_id p.2).const_mul p.1).ofReal_comp.const_mul a
    simpa [coordPartial, partialY, saddleAxisQuadratic] using hd.deriv

private theorem axisQuadratic_second (a : ℂ) (i j : Fin 2) :
    classicalComplexJet [i, j] (saddleAxisQuadratic a) = fun _ ↦ if i = j then 0 else a := by
  change coordPartial i (coordPartial j (saddleAxisQuadratic a)) = _
  rw [axisQuadratic_first]
  funext p
  fin_cases i <;> fin_cases j
  · simp [coordPartial, partialX]
  · simpa [coordPartial, partialX] using
      (((hasDerivAt_id p.1).ofReal_comp).const_mul a).deriv
  · simpa [coordPartial, partialY] using
      (((hasDerivAt_id p.2).ofReal_comp).const_mul a).deriv
  · simp [coordPartial, partialY]

private theorem axisQuadratic_third (a : ℂ) (i j k : Fin 2) :
    classicalComplexJet [i, j, k] (saddleAxisQuadratic a) = 0 := by
  change coordPartial i (classicalComplexJet [j, k] (saddleAxisQuadratic a)) = 0
  rw [axisQuadratic_second]
  funext p
  unfold coordPartial
  split_ifs <;> simp [partialX, partialY]

/-- The cylinder's parity and forbidden finite jets determine one quadratic
with a remainder whose jets vanish through order three. -/
theorem oddOdd_quadratic_flat_jet {ρ : ℝ} (hρ : 0 < ρ) {h : ℝ × ℝ → ℂ}
    (hs : ContDiffOn ℝ ∞ h (localDisk 0 ρ))
    (hp : HasAxisParityOn (fun _ ↦ false) (localDisk 0 ρ) h)
    (hz : ∀ w : List (Fin 2), ¬AllowedSaddleDegree (fun _ ↦ false) w.length →
      classicalComplexJet w h 0 = 0) :
    ∃ a : ℂ, ∀ w : List (Fin 2), w.length < 4 →
      classicalComplexJet w (fun p ↦ h p - saddleAxisQuadratic a p) 0 = 0 := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have h1 (j : Fin 2) : classicalComplexJet [j] h 0 = 0 := by
    apply hz
    intro hm
    have he : Even (1 : ℕ) := hm.1.mpr rfl
    obtain ⟨k, hk⟩ := he
    omega
  have h3 (i j k : Fin 2) : classicalComplexJet [i, j, k] h 0 = 0 := by
    apply hz
    intro hm
    exact oddOdd_cylinder_gap_three 3 hm rfl
  have h2 := oddOdd_pure_second_zero hρ hp hs.continuousOn
  have hxy : classicalComplexJet [1, 0] h 0 = classicalComplexJet [0, 1] h 0 := by
    simpa [classicalComplexJet, coordPartial] using
      partialY_partialX_at (hs.contDiffAt (hU.mem_nhds h0))
  refine ⟨classicalComplexJet [0, 1] h 0, fun w hw ↦ ?_⟩
  rw [classicalComplexJet_sub_on hU hs (contDiff_saddleAxisQuadratic _).contDiffOn w h0]
  change classicalComplexJet w h 0 -
    classicalComplexJet w (saddleAxisQuadratic (classicalComplexJet [0, 1] h 0)) 0 = 0
  rcases w with _ | ⟨i, w⟩
  · have he := hz [] (by simp [AllowedSaddleDegree])
    simpa [classicalComplexJet, saddleAxisQuadratic] using he
  rcases w with _ | ⟨j, w⟩
  · rw [h1]
    change 0 - coordPartial i (saddleAxisQuadratic _) 0 = 0
    rw [axisQuadratic_first]
    simp
  rcases w with _ | ⟨k, w⟩
  · rw [axisQuadratic_second]
    fin_cases i <;> fin_cases j <;> simp [h2, hxy]
  rcases w with _ | ⟨l, w⟩
  · rw [h3, axisQuadratic_third]
    simp
  · simp only [List.length_cons] at hw
    omega

/-- Finite Taylor estimates give the actual critical weighted remainder jet. -/
theorem oddOdd_quadratic_remainder_mass {ρ : ℝ} (hρ : 0 < ρ) {h : ℝ × ℝ → ℂ}
    (hs : ContDiffOn ℝ ∞ h (localDisk 0 ρ))
    (hp : HasAxisParityOn (fun _ ↦ false) (localDisk 0 ρ) h)
    (hz : ∀ w : List (Fin 2), ¬AllowedSaddleDegree (fun _ ↦ false) w.length →
      classicalComplexJet w h 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ r < ρ ∧ ∃ a : ℂ,
      HasWeakJetOn 2 (localDisk 0 r) (fun p ↦ h p - saddleAxisQuadratic a p)
        (fun w ↦ classicalComplexJet w (fun p ↦ h p - saddleAxisQuadratic a p)) ∧
      ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk 0 r) 0
        (fun w ↦ classicalComplexJet w (fun p ↦ h p - saddleAxisQuadratic a p)) := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  obtain ⟨a, ha⟩ := oddOdd_quadratic_flat_jet hρ hs hp hz
  obtain ⟨R, hR, hsub, hD, hm⟩ := exists_radial_classicalJet_flat_memLp hU h0
    (hs.sub (contDiff_saddleAxisQuadratic a).contDiffOn) 4 ha
  let r := min R (ρ / 2)
  have hr : 0 < r := lt_min hR (by linarith)
  have hrρ : r < ρ := (min_le_right R (ρ / 2)).trans_lt (half_lt_self hρ)
  have hsmall : localDisk 0 r ⊆ localDisk 0 R :=
    fun p hp ↦ show localRadius 0 p < R from lt_of_lt_of_le hp (min_le_left R (ρ / 2))
  refine ⟨r, hr, hrρ, a, ?_, fun k hk ↦ (hm k (by omega)).mono hsmall⟩
  have hd := hD.mono hsmall
  exact ⟨hd.1, fun w hw j ↦ hd.2 w (by omega) j⟩

/-- The smooth subcritical summand has quadratic growth and finite
three-halves weighted gradient mass on one disk. -/
theorem oddOdd_subcritical_smooth_mass {ρ : ℝ} (hρ : 0 < ρ) {h : ℝ × ℝ → ℂ}
    (hs : ContDiffOn ℝ ∞ h (localDisk 0 ρ))
    (hz : ∀ w : List (Fin 2), ¬AllowedSaddleDegree (fun _ ↦ false) w.length →
      classicalComplexJet w h 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ r < ρ ∧ 0 < C ∧
      (∀ p ∈ localDisk 0 r, ‖h p‖ ≤ C * Real.rpow (localRadius 0 p) (3 / 2)) ∧
      ∀ j : Fin 2, MemLp (fun p ↦ coordPartial j h p /
        (Real.rpow (localRadius 0 p) (3 / 2) : ℂ)) 2 (volume.restrict (localDisk 0 r)) := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hflat : ∀ w : List (Fin 2), w.length < 2 → classicalComplexJet w h 0 = 0 := by
    intro w hw
    apply hz
    intro hm
    have hn : w.length ≠ 0 := by
      intro he
      simpa using (hm.2 he).1
    obtain ⟨k, hk⟩ := hm.1.mpr rfl
    omega
  obtain ⟨R, C, hR, hC, hsub, hb⟩ :=
    exists_radial_classicalJet_flat_bounds hU h0 hs 2 hflat
  let r := min R (min (ρ / 2) 1)
  have hr : 0 < r := lt_min hR (lt_min (by linarith) zero_lt_one)
  have hrρ : r < ρ := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (half_lt_self hρ))
  have hsmall : localDisk 0 r ⊆ localDisk 0 R := fun p hp ↦
    show localRadius 0 p < R from lt_of_lt_of_le hp (min_le_left _ _)
  have hsmallU : localDisk 0 r ⊆ localDisk 0 ρ := hsmall.trans hsub
  have hV : IsOpen (localDisk 0 r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hrad : Measurable (localRadius (0 : ℝ × ℝ)) := by unfold localRadius; fun_prop
  refine ⟨r, C, hr, hrρ, hC, ?_, fun j ↦ ?_⟩
  · intro p hp
    have hx0 : 0 ≤ localRadius 0 p := Real.sqrt_nonneg _
    have hx1 : localRadius 0 p ≤ 1 :=
      (show localRadius 0 p < r from hp).le.trans
        ((min_le_right _ _).trans (min_le_right _ _))
    have he : localRadius 0 p ^ 2 ≤ Real.rpow (localRadius 0 p) (3 / 2) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
        Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
          (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
    exact (hb [] (by simp) p (hsmall hp)).trans (mul_le_mul_of_nonneg_left he hC.le)
  · have hc := (contDiffOn_coordPartial hU hs j).continuousOn.mono hsmallU
    have hm := hc.aestronglyMeasurable (μ := volume) hV.measurableSet
    have htop : MemLp (fun p ↦ coordPartial j h p / (localRadius 0 p : ℂ)) ⊤
        (volume.restrict (localDisk 0 r)) := by
      apply memLp_top_of_bound
        (hm.aemeasurable.div
          (Complex.measurable_ofReal.comp hrad).aemeasurable).aestronglyMeasurable C
      filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
      dsimp only [Pi.div_apply, Function.comp_apply]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ localRadius 0 p from Real.sqrt_nonneg _)]
      by_cases hx : localRadius 0 p = 0
      · simp [hx, hC.le]
      · have hxpos : 0 < localRadius 0 p :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
        apply (div_le_iff₀ hxpos).mpr
        simpa only [classicalComplexJet, List.length_singleton, Nat.reduceSub,
          pow_one] using hb [j] (by simp) p (hsmall hp)
    apply (htop.mul (memLp_inv_sqrt_localRadius 0 r)).ae_eq
    apply Filter.Eventually.of_forall
    intro p
    have he : Real.rpow (localRadius 0 p) (3 / 2) =
        localRadius 0 p * Real.sqrt (localRadius 0 p) := by
      by_cases hx : localRadius 0 p = 0
      · simp [hx, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      · have hxpos : 0 < localRadius 0 p :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
        rw [Real.sqrt_eq_rpow]
        simp only [Real.rpow_eq_pow]
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hxpos,
          Real.rpow_one]
    dsimp only [Pi.mul_apply]
    rw [he]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end NoEmbeddedEigenvalues
