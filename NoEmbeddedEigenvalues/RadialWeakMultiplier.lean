import NoEmbeddedEigenvalues.WeakPointRemoval
import NoEmbeddedEigenvalues.WeakJetOperations
import NoEmbeddedEigenvalues.TransversalMollifier

/-!
# Weak multiplication by radial powers

Blueprint: `lem:weak-derivative-product`, `lem:radial-weak-multiplier`,
`lem:radial-gradient-h1`, `lem:radial-ray-quotients-h1`.

Local smooth multiplication fixes the derivative representative. An isolated
singularity is then removed using local integrability, rather than by selecting
new Sobolev derivatives on quadrants.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology

/-- The weak product rule for a multiplier smooth only on the given open set. -/
theorem HasWeakPartialOn.mul_contDiffOn {U : Set (ℝ × ℝ)} {j : Fin 2}
    {F D χ : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn U j F D) (hU : IsOpen U)
    (hχ : ContDiffOn ℝ ∞ χ U) :
    HasWeakPartialOn U j (fun p ↦ χ p * F p)
      (fun p ↦ coordPartial j χ p * F p + χ p * D p) := by
  have hχj := contDiffOn_coordPartial hU hχ j
  refine ⟨hd.1.continuousOn_mul hχ.continuousOn hU.isLocallyClosed,
    (hd.1.continuousOn_mul hχj.continuousOn hU.isLocallyClosed).add
      (hd.2.1.continuousOn_mul hχ.continuousOn hU.isLocallyClosed), fun φ hφ ↦ ?_⟩
  have hψ := hφ.mul_contDiffOn hU hχ
  have hφj : IsTestFunctionOn U (coordPartial j φ) :=
    ⟨contDiff_coordPartial_top j hφ.contDiff, hφ.hasCompactSupport_coordPartial j,
      (tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset⟩
  have ha := hφ.mul_contDiffOn hU hχj
  have hb := hφj.mul_contDiffOn hU hχ
  have hi (G : ℝ × ℝ → ℂ) (hg : LocallyIntegrableOn G U)
      (ψ : ℝ × ℝ → ℂ) (ht : IsTestFunctionOn U ψ) : Integrable (fun p ↦ G p * ψ p) :=
    integrable_mul_of_tsupport_subset hg ht.contDiff.continuous ht.hasCompactSupport
      ht.tsupport_subset
  have ia := hi F hd.1 _ ha
  have ib := hi F hd.1 _ hb
  have ic := hi D hd.2.1 _ hψ
  have hprod : coordPartial j (fun p ↦ χ p * φ p) =
      fun p ↦ coordPartial j χ p * φ p + χ p * coordPartial j φ p := by
    funext p
    by_cases hp : p ∈ U
    · exact coordPartial_mul_at
        ((hχ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
        (hφ.contDiff.differentiable (by simp) p) j
    · have hpφ : p ∉ tsupport φ := fun ht ↦ hp (hφ.tsupport_subset ht)
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht ↦ hp (hψ.tsupport_subset (tsupport_coordPartial_subset j _ ht))),
        image_eq_zero_of_notMem_tsupport hpφ,
        image_eq_zero_of_notMem_tsupport (fun ht ↦ hpφ (tsupport_coordPartial_subset j φ ht))]
      simp
  have hw := hd.2.2 _ hψ
  rw [hprod] at hw
  simp only [mul_add] at hw
  rw [integral_add ia ib] at hw
  have e1 : (∫ p, χ p * F p * coordPartial j φ p) =
      ∫ p, F p * (χ p * coordPartial j φ p) := by congr 1; funext p; ring
  have e2 : (∫ p, (coordPartial j χ p * F p + χ p * D p) * φ p) =
      (∫ p, F p * (coordPartial j χ p * φ p)) + ∫ p, D p * (χ p * φ p) := by
    rw [← integral_add ia ic]
    congr 1; funext p; ring
  rw [e1, e2]
  linear_combination hw

/-- Euclidean radius vanishes at exactly its center. -/
theorem localRadius_eq_zero_iff (c p : ℝ × ℝ) : localRadius c p = 0 ↔ p = c := by
  constructor
  · intro hz
    have hh := (Real.sqrt_eq_zero (by positivity :
      0 ≤ (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)).1 hz
    apply Prod.ext
    · nlinarith [sq_nonneg (p.2 - c.2)]
    · nlinarith [sq_nonneg (p.1 - c.1)]
  · rintro rfl
    simp [localRadius]

/-- A globally measurable radial multiplier, smooth off the center. -/
def radialMultiplier (c : ℝ × ℝ) (s : ℝ) (p : ℝ × ℝ) : ℂ :=
  (Real.rpow ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) (-s / 2) : ℂ)

theorem radialMultiplier_eq (c : ℝ × ℝ) (s : ℝ) (p : ℝ × ℝ) :
    radialMultiplier c s p = (Real.rpow (localRadius c p) s : ℂ)⁻¹ := by
  have hq : 0 ≤ (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 := by positivity
  rw [radialMultiplier, ← Complex.ofReal_inv]
  congr 1
  simp only [localRadius, Real.sqrt_eq_rpow, Real.rpow_eq_pow]
  rw [← Real.rpow_mul hq, ← Real.rpow_neg hq]
  congr 1
  ring

theorem contDiffOn_radialMultiplier (c : ℝ × ℝ) (s : ℝ) :
    ContDiffOn ℝ ∞ (radialMultiplier c s) ({c}ᶜ : Set (ℝ × ℝ)) := by
  apply Complex.ofRealCLM.contDiff.comp_contDiffOn
  apply ContDiffOn.rpow_const_of_ne (by fun_prop)
  intro p hp hz
  have hr : localRadius c p = 0 := by simp [localRadius, hz]
  exact hp ((localRadius_eq_zero_iff c p).1 hr)

/-- Specified ordinary partials of the radial multiplier off its center. -/
theorem coordPartial_radialMultiplier {c p : ℝ × ℝ} (hp : p ≠ c)
    (s : ℝ) (j : Fin 2) :
    coordPartial j (radialMultiplier c s) p =
      (-s : ℂ) * ((axisCoord j p - axisCoord j c : ℝ) : ℂ) *
        (Real.rpow (localRadius c p) (-s - 2) : ℂ) := by
  have hr : 0 < localRadius c p := lt_of_le_of_ne (Real.sqrt_nonneg _) (by
    exact Ne.symm (mt (localRadius_eq_zero_iff c p).1 hp))
  have hs : 0 < (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 := by
    exact (Real.sqrt_pos).1 hr
  have hsq : localRadius c p ^ (2 : ℝ) = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 := by
    rw [Real.rpow_two]
    exact Real.sq_sqrt hs.le
  have hex : ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) ^ (-s / 2 - 1) =
      (localRadius c p) ^ (-s - 2) := by
    rw [← hsq, ← Real.rpow_mul (le_of_lt hr)]
    congr 1
    ring
  fin_cases j
  · have hbase : HasDerivAt (fun t : ℝ ↦ (t - c.1) ^ 2 + (p.2 - c.2) ^ 2)
        (2 * (p.1 - c.1)) p.1 := by
      convert (((hasDerivAt_id p.1).sub_const c.1).pow 2).add_const
        ((p.2 - c.2) ^ 2) using 1
      · funext t; rfl
      · dsimp; ring
    have hd := (hbase.rpow_const (p := -s / 2) (Or.inl hs.ne')).ofReal_comp.deriv
    dsimp [coordPartial, partialX, radialMultiplier, axisCoord]
    rw [hd, hex]
    push_cast
    ring
  · have hbase : HasDerivAt (fun t : ℝ ↦ (p.1 - c.1) ^ 2 + (t - c.2) ^ 2)
        (2 * (p.2 - c.2)) p.2 := by
      convert (((hasDerivAt_id p.2).sub_const c.2).pow 2).const_add
        ((p.1 - c.1) ^ 2) using 1
      · funext t; rfl
      · dsimp; ring
    have hd := (hbase.rpow_const (p := -s / 2) (Or.inl hs.ne')).ofReal_comp.deriv
    dsimp [coordPartial, partialY, radialMultiplier, axisCoord]
    rw [hd, hex]
    push_cast
    ring

/-- Each coordinate displacement divided by Euclidean radius is bounded by one,
including the totalized value at the center. -/
theorem norm_radial_coordinate_le (c p : ℝ × ℝ) (j : Fin 2) :
    ‖(((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ)‖ ≤ 1 := by
  have hr : 0 ≤ localRadius c p := Real.sqrt_nonneg _
  by_cases hz : localRadius c p = 0
  · simp [hz]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hr,
    div_le_one (lt_of_le_of_ne hr (Ne.symm hz))]
  have hs : localRadius c p ^ 2 = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  change |axisCoord j p - axisCoord j c| ≤ localRadius c p
  rw [abs_le]
  fin_cases j <;> dsimp [axisCoord] <;> constructor <;>
    nlinarith [sq_nonneg (p.1 - c.1), sq_nonneg (p.2 - c.2)]

/-- The explicit weak derivative of a radial quotient, together with its genuine
L² membership. The extra inverse radius controls differentiation of the weight. -/
theorem HasWeakPartialOn.radial_div {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} {s : ℝ} {j : Fin 2} {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U j F D)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ)) 2 (volume.restrict U))
    (hFw : MemLp (fun p ↦ F p / (Real.rpow (localRadius c p) (s + 1) : ℂ)) 2
      (volume.restrict U))
    (hDw : MemLp (fun p ↦ D p / (Real.rpow (localRadius c p) s : ℂ)) 2 (volume.restrict U)) :
    let E := fun p ↦ (-s : ℂ) *
      (((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ) *
        (F p / (Real.rpow (localRadius c p) (s + 1) : ℂ)) +
      D p / (Real.rpow (localRadius c p) s : ℂ)
    HasWeakPartialOn U j (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ)) E ∧
      MemLp E 2 (volume.restrict U) := by
  dsimp only
  let E := fun p ↦ (-s : ℂ) *
      (((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ) *
        (F p / (Real.rpow (localRadius c p) (s + 1) : ℂ)) +
      D p / (Real.rpow (localRadius c p) s : ℂ)
  have hm : Measurable (fun p ↦
      (((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ)) := by
    have ha : Continuous (axisCoord j) := by unfold axisCoord; split_ifs <;> fun_prop
    have hr : Continuous (localRadius c) := by unfold localRadius; fun_prop
    fun_prop
  have hb : MemLp (fun p ↦
      (((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall (fun p ↦ norm_radial_coordinate_le c p j))
  have hE : MemLp E 2 (volume.restrict U) := by
    apply MemLp.add (f := fun p ↦ (-s : ℂ) *
      (((axisCoord j p - axisCoord j c) / localRadius c p : ℝ) : ℂ) *
        (F p / (Real.rpow (localRadius c p) (s + 1) : ℂ)))
      (g := fun p ↦ D p / (Real.rpow (localRadius c p) s : ℂ))
    · simpa only [Pi.mul_apply, mul_assoc] using (hb.mul hFw).const_mul (-s : ℂ)
    · exact hDw
  refine ⟨?_, hE⟩
  have hU' : IsOpen (U \ {c}) := hU.sdiff isClosed_singleton
  have hd' := (hd.mono (sdiff_subset : U \ {c} ⊆ U)).mul_contDiffOn hU'
    ((contDiffOn_radialMultiplier c s).mono (by intro p hp; exact hp.2))
  have hpartial : HasWeakPartialOn (U \ {c}) j
      (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ)) E := by
    apply hd'.congr_ae_on hU'.measurableSet
    · exact Eventually.of_forall fun p _ ↦ by
        rw [radialMultiplier_eq]
        simp [div_eq_mul_inv, mul_comm]
    · exact Eventually.of_forall fun p hp ↦ by
        have hpc : p ≠ c := hp.2
        have hr : 0 < localRadius c p := lt_of_le_of_ne (Real.sqrt_nonneg _)
          (Ne.symm (mt (localRadius_eq_zero_iff c p).1 hpc))
        have hpow : Real.rpow (localRadius c p) (s + 1) =
            Real.rpow (localRadius c p) s * localRadius c p := by
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_add hr, Real.rpow_one]
        have hneg : Real.rpow (localRadius c p) (-s - 2) =
            (Real.rpow (localRadius c p) s * localRadius c p ^ 2)⁻¹ := by
          simp only [Real.rpow_eq_pow]
          rw [show -s - 2 = -(s + 2) by ring, Real.rpow_neg hr.le,
            Real.rpow_add hr, Real.rpow_two]
        dsimp only [E]
        rw [coordPartial_radialMultiplier hpc, radialMultiplier_eq, hneg, hpow]
        push_cast
        field_simp
  exact hpartial.remove_point
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hE.locallyIntegrable (by norm_num)))

/-- The same specified derivatives produce a full H¹ radial quotient. -/
theorem memSobolevOn_radial_div {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ × ℝ} {s : ℝ} {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hd : ∀ j, HasWeakPartialOn U j F (D j))
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ)) 2 (volume.restrict U))
    (hFw : MemLp (fun p ↦ F p / (Real.rpow (localRadius c p) (s + 1) : ℂ)) 2
      (volume.restrict U))
    (hDw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (localRadius c p) s : ℂ)) 2
      (volume.restrict U)) :
    MemSobolevOn 1 U (fun p ↦ F p / (Real.rpow (localRadius c p) s : ℂ)) := by
  refine ⟨hF, fun j ↦ ?_⟩
  exact ⟨_, (hd j).radial_div hU hF hFw (hDw j)⟩

/-- On a bounded disk a stronger integer radial weight controls every weaker
real exponent. The center is discarded only by a.e. equality. -/
theorem memLp_div_localRadius_rpow {c : ℝ × ℝ} {ρ : ℝ} {m : ℕ} {t : ℝ}
    {F : ℝ × ℝ → ℂ} (ht : t ≤ m)
    (hF : MemLp (fun p ↦ F p / (localRadius c p ^ m : ℂ)) 2
      (volume.restrict (localDisk c ρ))) :
    MemLp (fun p ↦ F p / (Real.rpow (localRadius c p) t : ℂ)) 2
      (volume.restrict (localDisk c ρ)) := by
  have hR : Continuous (localRadius c) := by unfold localRadius; fun_prop
  have hc : Continuous (fun p ↦ (Real.rpow (localRadius c p) (m - t) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (hR.rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr ht)))
  have hU : IsOpen (localDisk c ρ) := isOpen_lt hR continuous_const
  have hb : MemLp (fun p ↦ (Real.rpow (localRadius c p) (m - t) : ℂ)) ⊤
      (volume.restrict (localDisk c ρ)) := by
    apply memLp_top_of_bound hc.aestronglyMeasurable (Real.rpow ρ (m - t))
    filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ Real.rpow (localRadius c p) (m - t) from
        Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (le_of_lt hp) (sub_nonneg.mpr ht)
  have hn : ∀ᵐ p ∂(volume.restrict (localDisk c ρ)), p ≠ c :=
    ae_restrict_of_ae (by rw [ae_iff]; simp [Measure.volume_eq_prod])
  apply (hb.mul hF).ae_eq
  filter_upwards [hn] with p hp
  have hr : 0 < localRadius c p := lt_of_le_of_ne (Real.sqrt_nonneg _)
    (Ne.symm (mt (localRadius_eq_zero_iff c p).1 hp))
  have hex : Real.rpow (localRadius c p) (m - t) =
      localRadius c p ^ m / Real.rpow (localRadius c p) t := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_natCast]
  dsimp only [Pi.mul_apply]
  rw [hex]
  push_cast
  have hrC : (localRadius c p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have htC : (Real.rpow (localRadius c p) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hr t).ne'
  field_simp

/-- The two stronger saddle-jet weights give H¹ of the divided gradient through
its center, with no quadrant trace or crossing-gluing input. -/
theorem HasWeakJetOn.radial_gradient_h1 {c : ℝ × ℝ} {ρ : ℝ}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) F D)
    (h₁ : RadialJetLp 1 3 (localDisk c ρ) c D)
    (h₂ : RadialJetLp 2 2 (localDisk c ρ) c D) (j : Fin 2) :
    MemSobolevOn 1 (localDisk c ρ)
      (fun p ↦ D [j] p / (Real.rpow (localRadius c p) (3 / 2) : ℂ)) := by
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  exact memSobolevOn_radial_div hU (fun i ↦ hD.2 [j] (by simp) i)
    (memLp_div_localRadius_rpow (by norm_num) (h₁ [j] rfl))
    (memLp_div_localRadius_rpow (by norm_num) (h₁ [j] rfl))
    (fun i ↦ memLp_div_localRadius_rpow (by norm_num) (h₂ [i, j] rfl))

/-- Stronger divided remainders are H¹ through the center too. Ordinary
Cartesian L² traces of these quotients suffice for subcritical logarithmic rays. -/
theorem HasWeakJetOn.radial_ray_quotients_h1 {c : ℝ × ℝ} {ρ : ℝ}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) F D)
    (h₀ : RadialJetLp 0 4 (localDisk c ρ) c D)
    (h₁ : RadialJetLp 1 3 (localDisk c ρ) c D)
    (h₂ : RadialJetLp 2 2 (localDisk c ρ) c D) :
    MemSobolevOn 1 (localDisk c ρ)
      (fun p ↦ F p / (Real.rpow (localRadius c p) 3 : ℂ)) ∧
      ∀ j : Fin 2, MemSobolevOn 1 (localDisk c ρ)
        (fun p ↦ D [j] p / (Real.rpow (localRadius c p) 2 : ℂ)) := by
  have hU : IsOpen (localDisk c ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hF : MemLp (fun p ↦ F p / (localRadius c p ^ 4 : ℂ)) 2
      (volume.restrict (localDisk c ρ)) := by
    simpa only [hD.1] using h₀ [] rfl
  refine ⟨memSobolevOn_radial_div hU (fun i ↦ ?_)
    (memLp_div_localRadius_rpow (by norm_num) hF)
    (memLp_div_localRadius_rpow (by norm_num) hF)
    (fun i ↦ memLp_div_localRadius_rpow (by norm_num) (h₁ [i] rfl)), fun j ↦ ?_⟩
  · simpa only [hD.1] using hD.2 [] (by simp) i
  · exact memSobolevOn_radial_div hU (fun i ↦ hD.2 [j] (by simp) i)
      (memLp_div_localRadius_rpow (by norm_num) (h₁ [j] rfl))
      (memLp_div_localRadius_rpow (by norm_num) (h₁ [j] rfl))
      (fun i ↦ memLp_div_localRadius_rpow (by norm_num) (h₂ [i, j] rfl))

end NoEmbeddedEigenvalues
