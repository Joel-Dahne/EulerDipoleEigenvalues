import NoEmbeddedEigenvalues.TransversalMollifier
import NoEmbeddedEigenvalues.VirialFourier
import NoEmbeddedEigenvalues.EigenfunctionTransport

/-!
# Periodizing cell functions to the torus

Used by the proof of `lem:virial-l2`: the transversal mollifier produces functions on `ℝ²`
supported in a fixed compact subset of the cell square, while the `H¹` virial identities are
on the torus.

* Uniqueness of weak derivatives on open sets, and the weak transport derivative of a function
  with weak partial derivatives.
* `boxPeriodize F`: the element of `L²(𝕋²)` with values `F` on the fundamental box
  `(-π, π]²`, which contains the cell square. It is linear, does not increase `L²` norms, turns
  multiplication by periodic functions into `mulL2`, and maps weak derivatives of functions
  supported in a compact subset of the cell square to Fourier derivatives
  (`hasFourierPartial_boxPeriodize`). The last is tested against the characters, cut off
  near the support, so no density argument is needed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex ComplexConjugate
open scoped Topology ContDiff InnerProductSpace Real

/-! ### Uniqueness of weak derivatives -/

section Unique

variable {U : Set (ℝ × ℝ)}

/-- A locally integrable function on an open set with zero integral against every test
function vanishes almost everywhere there. -/
theorem ae_eq_zero_of_forall_test (hU : IsOpen U) {h : ℝ × ℝ → ℂ}
    (hh : LocallyIntegrableOn h U) (h0 : ∀ φ, IsTestFunctionOn U φ → ∫ p, h p * φ p = 0) :
    ∀ᵐ p, p ∈ U → h p = 0 := by
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hh fun g hg hgc hgU ↦ ?_
  have ht : IsTestFunctionOn U (fun p ↦ (g p : ℂ)) :=
    ⟨ofRealCLM.contDiff.comp hg, hgc.comp_left ofReal_zero,
      (tsupport_comp_subset ofReal_zero g).trans hgU⟩
  rw [← h0 _ ht]
  congr 1
  funext p
  rw [real_smul, mul_comm]

/-- Weak partial derivatives are unique almost everywhere. -/
theorem HasWeakPartialOn.ae_eq (hU : IsOpen U) {j : Fin 2} {F d d' : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U j F d) (hd' : HasWeakPartialOn U j F d') :
    ∀ᵐ p, p ∈ U → d p = d' p := by
  have h := ae_eq_zero_of_forall_test hU (hd.2.1.sub hd'.2.1) fun φ hφ ↦ by
    have i := integrable_mul_of_tsupport_subset hd.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    have i' := integrable_mul_of_tsupport_subset hd'.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub i i', ← neg_neg (∫ p, d p * φ p), ← neg_neg (∫ p, d' p * φ p),
      ← hd.2.2 φ hφ, ← hd'.2.2 φ hφ, sub_self]
  filter_upwards [h] with p hp hpU
  exact sub_eq_zero.1 (hp hpU)

/-- Weak transport derivatives are unique almost everywhere. -/
theorem HasWeakL0On.ae_eq (hU : IsOpen U) {F k k' : ℝ × ℝ → ℂ}
    (hk : HasWeakL0On U F k) (hk' : HasWeakL0On U F k') :
    ∀ᵐ p, p ∈ U → k p = k' p := by
  have h := ae_eq_zero_of_forall_test hU (hk.2.1.sub hk'.2.1) fun φ hφ ↦ by
    have i := integrable_mul_of_tsupport_subset hk.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    have i' := integrable_mul_of_tsupport_subset hk'.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub i i', ← neg_neg (∫ p, k p * φ p), ← neg_neg (∫ p, k' p * φ p),
      ← hk.2.2 φ hφ, ← hk'.2.2 φ hφ, sub_self]
  filter_upwards [h] with p hp hpU
  exact sub_eq_zero.1 (hp hpU)

/-- The weak derivative of a function vanishing on an open set vanishes there. -/
theorem HasWeakPartialOn.ae_eq_zero (hU : IsOpen U) {j : Fin 2} {F d : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U j F d) (hF : ∀ p ∈ U, F p = 0) : ∀ᵐ p, p ∈ U → d p = 0 :=
  ae_eq_zero_of_forall_test hU hd.2.1 fun φ hφ ↦ by
    have h := hd.2.2 φ hφ
    have h0 : ∫ p, F p * coordPartial j φ p = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun p ↦ ?_)
      by_cases hp : p ∈ U
      · simp [hF p hp]
      · have : coordPartial j φ p = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs ↦ hp (hφ.tsupport_subset (tsupport_coordPartial_subset j φ hs)))
        simp [this]
    rw [h0] at h
    exact neg_eq_zero.1 h.symm

theorem HasWeakL0On.mono {V : Set (ℝ × ℝ)} {F k : ℝ × ℝ → ℂ} (hk : HasWeakL0On U F k)
    (hVU : V ⊆ U) : HasWeakL0On V F k :=
  ⟨hk.1.mono_set hVU, hk.2.1.mono_set hVU, fun φ hφ ↦ hk.2.2 φ (hφ.mono hVU)⟩

theorem HasWeakL0On.sub {F G k l : ℝ × ℝ → ℂ} (hk : HasWeakL0On U F k)
    (hl : HasWeakL0On U G l) :
    HasWeakL0On U (fun p ↦ F p - G p) (fun p ↦ k p - l p) := by
  refine ⟨hk.1.sub hl.1, hk.2.1.sub hl.2.1, fun φ hφ ↦ ?_⟩
  have hL : Continuous (classicalL0 φ) := by
    have h0 : Continuous (partialX φ) := by simpa [coordPartial] using hφ.continuous_coordPartial 0
    have h1 : Continuous (partialY φ) := by simpa [coordPartial] using hφ.continuous_coordPartial 1
    exact ((Real.continuous_sin.comp continuous_snd).smul h0).sub
      ((Real.continuous_sin.comp continuous_fst).smul h1)
  have hLs : HasCompactSupport (classicalL0 φ) := by
    refine hφ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) ?_
    refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_smul_subset_right _ _).trans (tsupport_partialX_subset φ)
    · exact (tsupport_smul_subset_right _ _).trans (tsupport_partialY_subset φ)
  have hLsub : tsupport (classicalL0 φ) ⊆ U := by
    refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
    · exact ((tsupport_smul_subset_right _ _).trans (tsupport_partialX_subset φ)).trans
        hφ.tsupport_subset
    · exact ((tsupport_smul_subset_right _ _).trans (tsupport_partialY_subset φ)).trans
        hφ.tsupport_subset
  have i1 := integrable_mul_of_tsupport_subset hk.1 hL hLs hLsub
  have i2 := integrable_mul_of_tsupport_subset hl.1 hL hLs hLsub
  have i3 := integrable_mul_of_tsupport_subset hk.2.1 hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have i4 := integrable_mul_of_tsupport_subset hl.2.1 hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  simp only [sub_mul]
  rw [integral_sub i1 i2, integral_sub i3 i4, hk.2.2 φ hφ, hl.2.2 φ hφ]
  ring

/-- A function with weak partial derivatives has the weak transport derivative
`L₀F = sin y ∂ₓF - sin x ∂_yF`. -/
theorem HasWeakPartialOn.hasWeakL0On (hU : IsOpen U) {F d₀ d₁ : ℝ × ℝ → ℂ}
    (h₀ : HasWeakPartialOn U 0 F d₀) (h₁ : HasWeakPartialOn U 1 F d₁) :
    HasWeakL0On U F (fun p ↦ (Real.sin p.2 : ℂ) * d₀ p - (Real.sin p.1 : ℂ) * d₁ p) := by
  have hsy : Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have hsx : Continuous (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  refine ⟨h₀.1, (h₀.2.1.continuousOn_mul hsy.continuousOn hU.isLocallyClosed).sub
    (h₁.2.1.continuousOn_mul hsx.continuousOn hU.isLocallyClosed), fun φ hφ ↦ ?_⟩
  have hsyd : Differentiable ℝ (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have hsxd : Differentiable ℝ (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have hφd : Differentiable ℝ φ := hφ.contDiff.differentiable (by simp)
  have ty : IsTestFunctionOn U (fun p ↦ (Real.sin p.2 : ℂ) * φ p) :=
    ⟨(ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)).mul hφ.contDiff,
      hφ.hasCompactSupport.mul_left, (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩
  have tx : IsTestFunctionOn U (fun p ↦ (Real.sin p.1 : ℂ) * φ p) :=
    ⟨(ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_fst)).mul hφ.contDiff,
      hφ.hasCompactSupport.mul_left, (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩
  have ey : coordPartial 0 (fun p ↦ (Real.sin p.2 : ℂ) * φ p) =
      fun p ↦ (Real.sin p.2 : ℂ) * partialX φ p := by
    rw [coordPartial_mul 0 hsyd hφd]
    funext p
    simp [coordPartial, partialX]
  have ex : coordPartial 1 (fun p ↦ (Real.sin p.1 : ℂ) * φ p) =
      fun p ↦ (Real.sin p.1 : ℂ) * partialY φ p := by
    rw [coordPartial_mul 1 hsxd hφd]
    funext p
    simp [coordPartial, partialY]
  have wy := h₀.2.2 _ ty
  have wx := h₁.2.2 _ tx
  rw [ey] at wy
  rw [ex] at wx
  have i1 := integrable_mul_of_tsupport_subset h₀.1 (ty.continuous_coordPartial 0)
    (ty.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 _).trans ty.tsupport_subset)
  have i2 := integrable_mul_of_tsupport_subset h₁.1 (tx.continuous_coordPartial 1)
    (tx.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 _).trans tx.tsupport_subset)
  have i3 := integrable_mul_of_tsupport_subset h₀.2.1 ty.contDiff.continuous
    ty.hasCompactSupport ty.tsupport_subset
  have i4 := integrable_mul_of_tsupport_subset h₁.2.1 tx.contDiff.continuous
    tx.hasCompactSupport tx.tsupport_subset
  rw [ey] at i1
  rw [ex] at i2
  have e1 : (fun p ↦ F p * classicalL0 φ p) = fun p ↦
      F p * ((Real.sin p.2 : ℂ) * partialX φ p) - F p * ((Real.sin p.1 : ℂ) * partialY φ p) := by
    funext p
    simp only [classicalL0, real_smul]
    ring
  have e2 : (fun p ↦ ((Real.sin p.2 : ℂ) * d₀ p - (Real.sin p.1 : ℂ) * d₁ p) * φ p) = fun p ↦
      d₀ p * ((Real.sin p.2 : ℂ) * φ p) - d₁ p * ((Real.sin p.1 : ℂ) * φ p) := by
    funext p
    ring
  rw [e1, e2, integral_sub i1 i2, integral_sub i3 i4, wy, wx]
  ring

end Unique

/-! ### The fundamental box `(-π, π]²` -/

/-- The box `(-π, π]²`, a fundamental domain of the torus containing the cell square. -/
def periodBox : Set (ℝ × ℝ) := Ioc (-π) (-π + 2 * π) ×ˢ Ioc (-π) (-π + 2 * π)

theorem measurableSet_periodBox : MeasurableSet periodBox :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem cellSquare_subset_periodBox : cellSquare ⊆ periodBox := by
  intro p hp
  change |(p.1 + p.2) / 2| < π / 2 ∧ |(p.1 - p.2) / 2| < π / 2 at hp
  obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
  obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The representative of an angle in `(-π, π]`. -/
def angleRep (θ : Real.Angle) : ℝ :=
  ((AddCircle.equivIoc (2 * π) (-π) (θ : AddCircle (2 * π)) : Ioc (-π) (-π + 2 * π)) : ℝ)

theorem measurable_angleRep : Measurable angleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2 * π) (-π)).measurable

theorem angleRep_mem (θ : Real.Angle) : angleRep θ ∈ Ioc (-π) (-π + 2 * π) :=
  (AddCircle.equivIoc (2 * π) (-π) (θ : AddCircle (2 * π))).2

theorem coe_angleRep (θ : Real.Angle) : ((angleRep θ : ℝ) : Real.Angle) = θ := by
  have h := (AddCircle.equivIoc (2 * π) (-π)).symm_apply_apply (θ : AddCircle (2 * π))
  rwa [AddCircle.equivIoc, QuotientAddGroup.equivIocMod_symm_apply] at h

theorem angleRep_coe {x : ℝ} (hx : x ∈ Ioc (-π) (-π + 2 * π)) : angleRep x = x :=
  (AddCircle.coe_eq_coe_iff_of_mem_Ioc (angleRep_mem _) hx).1 (coe_angleRep _)

/-- The representative of a point of the torus in `(-π, π]²`. -/
def torusRep (t : Torus) : ℝ × ℝ := (angleRep t.1, angleRep t.2)

theorem measurable_torusRep : Measurable torusRep :=
  (measurable_angleRep.comp measurable_fst).prodMk (measurable_angleRep.comp measurable_snd)

theorem torusProj_torusRep (t : Torus) : torusProj (torusRep t) = t := by
  simp only [torusProj, torusRep, coe_angleRep]

theorem torusRep_torusProj {p : ℝ × ℝ} (hp : p ∈ periodBox) : torusRep (torusProj p) = p :=
  Prod.ext (angleRep_coe hp.1) (angleRep_coe hp.2)

theorem torusRep_mem (t : Torus) : torusRep t ∈ periodBox :=
  ⟨angleRep_mem _, angleRep_mem _⟩

theorem measurePreserving_torusProj_box :
    MeasurePreserving torusProj (volume.restrict periodBox) volume :=
  measurePreserving_torusProj_square (-π) (-π)

theorem measurePreserving_torusRep :
    MeasurePreserving torusRep volume (volume.restrict periodBox) := by
  refine ⟨measurable_torusRep, ?_⟩
  conv_lhs => rw [← measurePreserving_torusProj_box.map_eq]
  rw [Measure.map_map measurable_torusRep measurePreserving_torusProj_box.measurable]
  conv_rhs => rw [← Measure.map_id (μ := volume.restrict periodBox)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_periodBox] with p hp
  exact torusRep_torusProj hp

/-- Points of the box with `Ψ > 0` lie in the cell square. -/
theorem mem_cellSquare_of_mem_periodBox {p : ℝ × ℝ} (hp : p ∈ periodBox)
    (hpos : 0 < dipoleLift p) : p ∈ cellSquare := by
  have ht : torusProj p ∈ positiveCell := by
    change 0 < Ψ (torusProj p)
    rwa [Ψ_torusProj]
  obtain ⟨q, hq, hqp⟩ := exists_mem_cellSquare ht
  have : q = p := by
    rw [← torusRep_torusProj (cellSquare_subset_periodBox hq), ← torusRep_torusProj hp, hqp]
  exact this ▸ hq

theorem memLp_liftL2_periodBox (u : L2) : MemLp (liftL2 u) 2 (volume.restrict periodBox) :=
  (Lp.memLp u).comp_measurePreserving measurePreserving_torusProj_box

/-! ### Periodization through the box -/

open scoped Classical in
/-- The element of `L²(𝕋²)` with the values of `F` on the box `(-π, π]²` (zero if these are not
square integrable). -/
def boxPeriodize (F : ℝ × ℝ → ℂ) : L2 :=
  if h : MemLp (fun t ↦ F (torusRep t)) 2 volume then h.toLp else 0

section Periodize

variable {F G : ℝ × ℝ → ℂ}

theorem memLp_comp_torusRep (hF : MemLp F 2 (volume.restrict periodBox)) :
    MemLp (fun t ↦ F (torusRep t)) 2 volume :=
  hF.comp_measurePreserving measurePreserving_torusRep

theorem coeFn_boxPeriodize (hF : MemLp F 2 (volume.restrict periodBox)) :
    boxPeriodize F =ᵐ[volume] fun t ↦ F (torusRep t) := by
  rw [boxPeriodize, dite_eq_left (memLp_comp_torusRep hF)]
  exact MemLp.coeFn_toLp _

theorem norm_boxPeriodize (hF : MemLp F 2 (volume.restrict periodBox)) :
    ‖boxPeriodize F‖ = (eLpNorm F 2 (volume.restrict periodBox)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_boxPeriodize hF)]
  congr 1
  exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable measurePreserving_torusRep

theorem norm_boxPeriodize_le (hF : MemLp F 2 volume) :
    ‖boxPeriodize F‖ ≤ (eLpNorm F 2 volume).toReal := by
  rw [norm_boxPeriodize (hF.restrict _)]
  exact ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem boxPeriodize_congr (h : F =ᵐ[volume.restrict periodBox] G) :
    boxPeriodize F = boxPeriodize G := by
  have h' : (fun t ↦ F (torusRep t)) =ᵐ[volume] fun t ↦ G (torusRep t) :=
    measurePreserving_torusRep.quasiMeasurePreserving.ae_eq_comp h
  unfold boxPeriodize
  by_cases hF : MemLp (fun t ↦ F (torusRep t)) 2 volume
  · rw [dite_eq_left hF, dite_eq_left (hF.ae_eq h')]
    exact MemLp.toLp_congr _ _ h'
  · rw [dite_eq_right hF, dite_eq_right (fun hG ↦ hF (hG.ae_eq h'.symm))]

theorem boxPeriodize_congr_box (h : ∀ p ∈ periodBox, F p = G p) :
    boxPeriodize F = boxPeriodize G :=
  boxPeriodize_congr ((ae_restrict_iff' measurableSet_periodBox).2 (Eventually.of_forall h))

theorem boxPeriodize_add (hF : MemLp F 2 (volume.restrict periodBox))
    (hG : MemLp G 2 (volume.restrict periodBox)) :
    boxPeriodize (F + G) = boxPeriodize F + boxPeriodize G := by
  apply Lp.ext
  filter_upwards [coeFn_boxPeriodize (hF.add hG), coeFn_boxPeriodize hF, coeFn_boxPeriodize hG,
    Lp.coeFn_add (boxPeriodize F) (boxPeriodize G)] with t h h₁ h₂ h₃
  rw [h, h₃]
  simp only [Pi.add_apply]
  rw [h₁, h₂]

theorem boxPeriodize_sub (hF : MemLp F 2 (volume.restrict periodBox))
    (hG : MemLp G 2 (volume.restrict periodBox)) :
    boxPeriodize (F - G) = boxPeriodize F - boxPeriodize G := by
  apply Lp.ext
  filter_upwards [coeFn_boxPeriodize (hF.sub hG), coeFn_boxPeriodize hF, coeFn_boxPeriodize hG,
    Lp.coeFn_sub (boxPeriodize F) (boxPeriodize G)] with t h h₁ h₂ h₃
  rw [h, h₃]
  simp only [Pi.sub_apply]
  rw [h₁, h₂]

theorem boxPeriodize_const_mul (hF : MemLp F 2 (volume.restrict periodBox)) (c : ℂ) :
    boxPeriodize (fun p ↦ c * F p) = c • boxPeriodize F := by
  apply Lp.ext
  filter_upwards [coeFn_boxPeriodize (hF.const_mul c), coeFn_boxPeriodize hF,
    Lp.coeFn_smul c (boxPeriodize F)] with t h h₁ h₂
  rw [h, h₂, Pi.smul_apply, h₁, smul_eq_mul]

/-- Multiplication by a continuous periodic function. -/
theorem boxPeriodize_mul {g : ℝ × ℝ → ℂ} (hc : Continuous g) (hp : IsPeriodicLift g)
    (hF : MemLp F 2 (volume.restrict periodBox)) :
    boxPeriodize (fun p ↦ g p * F p) = mulL2 (torusFun hc hp) (boxPeriodize F) := by
  have hg (p : ℝ × ℝ) : g p = torusFun hc hp (torusProj p) := (torusFun_torusProj hc hp p).symm
  have hgF : MemLp (fun p ↦ g p * F p) 2 (volume.restrict periodBox) := by
    refine hF.of_le_mul (c := ‖torusFun hc hp‖)
      (hc.aestronglyMeasurable.mul hF.aestronglyMeasurable) (Eventually.of_forall fun p ↦ ?_)
    rw [norm_mul, hg]
    exact mul_le_mul_of_nonneg_right ((torusFun hc hp).norm_coe_le_norm _) (norm_nonneg _)
  apply Lp.ext
  filter_upwards [coeFn_boxPeriodize hgF, coeFn_boxPeriodize hF,
    mulL2_ae (torusFun hc hp) (boxPeriodize F)] with t h h₁ h₂
  rw [h, h₂, h₁, hg, torusProj_torusRep]

theorem boxPeriodize_liftL2 (u : L2) : boxPeriodize (liftL2 u) = u := by
  have he : (fun t ↦ liftL2 u (torusRep t)) = fun t ↦ u t := by
    funext t
    simp only [liftL2, torusProj_torusRep]
  have hm : MemLp (fun t ↦ liftL2 u (torusRep t)) 2 volume := he ▸ Lp.memLp u
  apply Lp.ext
  rw [boxPeriodize, dite_eq_left hm]
  filter_upwards [hm.coeFn_toLp] with t ht
  rw [ht]
  simp only [liftL2, torusProj_torusRep]

end Periodize

/-! ### Weak derivatives become Fourier derivatives -/

theorem isOpen_cellSquare : IsOpen cellSquare := by
  unfold cellSquare diagCoord
  exact (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 + p.2) / 2|)
    continuous_const).inter (isOpen_lt
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 - p.2) / 2|) continuous_const)

/-- A function constant near `p` has zero partial derivatives at `p`. -/
theorem coordPartial_eq_zero_of_eventuallyEq {u : ℝ × ℝ → ℂ} {p : ℝ × ℝ} {c : ℂ}
    (h : u =ᶠ[𝓝 p] fun _ ↦ c) (j : Fin 2) : coordPartial j u p = 0 := by
  unfold coordPartial
  split_ifs
  · have hl : (fun t ↦ u (t, p.2)) =ᶠ[𝓝 p.1] fun _ ↦ c :=
      (Continuous.tendsto (by fun_prop : Continuous fun t : ℝ ↦ (t, p.2)) p.1).eventually h
    rw [partialX, hl.deriv_eq, deriv_const]
  · have hl : (fun t ↦ u (p.1, t)) =ᶠ[𝓝 p.2] fun _ ↦ c :=
      (Continuous.tendsto (by fun_prop : Continuous fun t : ℝ ↦ (p.1, t)) p.2).eventually h
    rw [partialY, hl.deriv_eq, deriv_const]

/-- The Fourier coefficients of a periodized function vanishing off the box are integrals
over the plane against the conjugate characters. -/
theorem fourierCoeff_boxPeriodize {G : ℝ × ℝ → ℂ} (hG : MemLp G 2 (volume.restrict periodBox))
    (hG0 : ∀ᵐ p, p ∉ periodBox → G p = 0) (k : ℤ × ℤ) :
    fourierCoeff (boxPeriodize G) k =
      ((2 * π : ℂ) ^ 2)⁻¹ * ∫ p, char (-k) (torusProj p) * G p := by
  rw [fourierCoeff_eq_integral_char_neg]
  congr 1
  have hc : Continuous torusProj := isOpenQuotientMap_torusProj.continuous
  have e1 : ∫ t, char (-k) t * boxPeriodize G t =
      ∫ t, (fun p ↦ char (-k) (torusProj p) * G p) (torusRep t) := by
    apply integral_congr_ae
    filter_upwards [coeFn_boxPeriodize hG] with t ht
    simp only [ht, torusProj_torusRep]
  have hm : AEStronglyMeasurable (fun p ↦ char (-k) (torusProj p) * G p)
      (Measure.map torusRep volume) := by
    rw [measurePreserving_torusRep.map_eq]
    exact ((char (-k)).continuous.comp hc).aestronglyMeasurable.mul hG.aestronglyMeasurable
  rw [e1, ← integral_map measurable_torusRep.aemeasurable hm, measurePreserving_torusRep.map_eq,
    setIntegral_eq_integral_of_ae_compl_eq_zero]
  filter_upwards [hG0] with p hp hpB
  simp [hp hpB]

/-- The periodization of a function with compact support in the cell square turns its weak
partial derivatives into Fourier partial derivatives. -/
theorem hasFourierPartial_boxPeriodize {j : Fin 2} {F d : ℝ × ℝ → ℂ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKc : K ⊆ cellSquare) (hF0 : ∀ p ∉ K, F p = 0)
    (hF : MemLp F 2 volume) (hd2 : MemLp d 2 volume) (hd : HasWeakPartialOn univ j F d) :
    HasFourierPartial j (boxPeriodize F) (boxPeriodize d) := by
  -- `d` vanishes off `K`.
  have hd0 : ∀ᵐ p, p ∉ K → d p = 0 :=
    (hd.mono (subset_univ Kᶜ)).ae_eq_zero hK.isClosed.isOpen_compl fun p hp ↦ hF0 p hp
  -- A cutoff `θ` equal to `1` near `K` with compact support in the cell square.
  obtain ⟨V₂, hV₂o, hKV₂, hV₂c, hV₂k⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_cellSquare hKc
  obtain ⟨V₁, hV₁o, hKV₁, hV₁c, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₂o isClosed_closure hV₁c
  have hθc : HasCompactSupport θ := by
    rw [HasCompactSupport, tsupport, hθs]
    exact hV₂k
  have hθ1' (p : ℝ × ℝ) (hp : p ∈ V₁) : θ p = 1 := (hθ1 p).1 (subset_closure hp)
  intro k
  -- The conjugate character on the plane.
  set a : ℂ := ((-k).1 : ℂ)
  set b : ℂ := ((-k).2 : ℂ)
  let e : ℝ × ℝ → ℂ := fun p ↦ exp (I * (a * p.1 + b * p.2))
  have he (p : ℝ × ℝ) : char (-k) (torusProj p) = e p := char_coe (-k) p.1 p.2
  have hes : ContDiff ℝ ∞ e := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.1 : ℝ) : ℂ)) := ofRealCLM.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ ((p.2 : ℝ) : ℂ)) := ofRealCLM.contDiff.comp contDiff_snd
    exact Complex.contDiff_exp.comp (contDiff_const.mul ((contDiff_const.mul h1).add
      (contDiff_const.mul h2)))
  have hed : coordPartial j e = fun p ↦ -(I * frequencyComponent k j) * e p := by
    funext p
    unfold coordPartial
    split_ifs with hj
    · have hd : HasDerivAt (fun t : ℝ ↦ e (t, p.2)) (e p * (I * a)) p.1 := by
        have := (((hasDerivAt_id p.1).ofReal_comp.const_mul a).add_const (b * p.2)).const_mul I
        simpa [e] using this.cexp
      rw [partialX, hd.deriv]
      simp [frequencyComponent, hj, a]
      ring
    · have hd : HasDerivAt (fun t : ℝ ↦ e (p.1, t)) (e p * (I * b)) p.2 := by
        have := (((hasDerivAt_id p.2).ofReal_comp.const_mul b).const_add (a * p.1)).const_mul I
        simpa [e] using this.cexp
      rw [partialY, hd.deriv]
      simp [frequencyComponent, hj, b]
      ring
  -- The test function `θ e`.
  let θc : ℝ × ℝ → ℂ := fun p ↦ (θ p : ℂ)
  have hθcs : ContDiff ℝ ∞ θc := ofRealCLM.contDiff.comp hθ
  have hφ : IsTestFunctionOn univ (fun p ↦ θc p * e p) :=
    ⟨hθcs.mul hes, (hθc.comp_left ofReal_zero).mul_right, subset_univ _⟩
  have hw := hd.2.2 _ hφ
  rw [coordPartial_mul j (hθcs.differentiable (by simp)) (hes.differentiable (by simp)), hed]
    at hw
  have hl : (fun p ↦ F p * (coordPartial j θc p * e p + θc p * (-(I * frequencyComponent k j) *
      e p))) = fun p ↦ -(I * frequencyComponent k j) * (e p * F p) := by
    funext p
    by_cases hp : p ∈ K
    · have h1 : θc =ᶠ[𝓝 p] fun _ ↦ 1 := by
        filter_upwards [hV₁o.mem_nhds (hKV₁ hp)] with q hq
        simp [θc, hθ1' q hq]
      rw [coordPartial_eq_zero_of_eventuallyEq h1, h1.eq_of_nhds]
      ring
    · simp [hF0 p hp]
  have hr : (fun p ↦ d p * (θc p * e p)) =ᵐ[volume] fun p ↦ e p * d p := by
    filter_upwards [hd0] with p hp
    by_cases hpK : p ∈ K
    · simp [θc, hθ1' p (hKV₁ hpK), mul_comm]
    · simp [hp hpK]
  rw [hl, integral_congr_ae hr, integral_const_mul] at hw
  -- Both coefficients as plane integrals.
  have hB : ∀ {G : ℝ × ℝ → ℂ}, (∀ᵐ p, p ∉ K → G p = 0) → ∀ᵐ p, p ∉ periodBox → G p = 0 :=
    fun hG ↦ hG.mono fun p hp hpB ↦ hp fun hpK ↦ hpB (cellSquare_subset_periodBox (hKc hpK))
  rw [fourierCoeff_boxPeriodize (hd2.restrict _) (hB hd0),
    fourierCoeff_boxPeriodize (hF.restrict _) (hB (Eventually.of_forall hF0))]
  simp only [he]
  linear_combination (((2 * π : ℂ) ^ 2)⁻¹) * hw

/-! ### Lifts, multiplication operators and pairings -/

section Lifts

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

theorem squarePairing_congr_ae {A A' B B' : ℝ × ℝ → ℂ} (hA : A =ᵐ[volume] A')
    (hB : B =ᵐ[volume] B') : squarePairing A B = squarePairing A' B' := by
  unfold squarePairing squareIntegral
  apply integral_congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [hA, hB] with p h1 h2
  rw [h1, h2]

theorem mulL2_add_right (c : C(Torus, ℂ)) (u v : L2) :
    mulL2 c (u + v) = mulL2 c u + mulL2 c v := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (u + v), mulL2_ae c u, mulL2_ae c v, Lp.coeFn_add u v,
    Lp.coeFn_add (mulL2 c u) (mulL2 c v)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄, Pi.add_apply, h₁, h₂, h₃, Pi.add_apply, mul_add]

theorem mulL2_sub_right (c : C(Torus, ℂ)) (u v : L2) :
    mulL2 c (u - v) = mulL2 c u - mulL2 c v := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (u - v), mulL2_ae c u, mulL2_ae c v, Lp.coeFn_sub u v,
    Lp.coeFn_sub (mulL2 c u) (mulL2 c v)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄, Pi.sub_apply, h₁, h₂, h₃, Pi.sub_apply, mul_sub]

theorem mulL2_smul_right (c : C(Torus, ℂ)) (r : ℂ) (u : L2) :
    mulL2 c (r • u) = r • mulL2 c u := by
  apply Lp.ext
  filter_upwards [mulL2_ae c (r • u), mulL2_ae c u, Lp.coeFn_smul r u,
    Lp.coeFn_smul r (mulL2 c u)] with t h h₁ h₂ h₃
  rw [h, h₃, Pi.smul_apply, h₁, h₂, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem mulL2_mulL2 (a b : C(Torus, ℂ)) (u : L2) :
    mulL2 a (mulL2 b u) = mulL2 (a * b) u := by
  apply Lp.ext
  filter_upwards [mulL2_ae a (mulL2 b u), mulL2_ae b u, mulL2_ae (a * b) u] with t h h₁ h₂
  rw [h, h₁, h₂, ContinuousMap.mul_apply, mul_assoc]

theorem mulL2_zero_left (u : L2) : mulL2 0 u = 0 := by
  apply Lp.ext
  filter_upwards [mulL2_ae 0 u, Lp.coeFn_zero ℂ 2 (volume : Measure Torus)] with t h h₁
  rw [h, h₁, ContinuousMap.zero_apply, zero_mul, Pi.zero_apply]

theorem norm_mulL2_le (c : C(Torus, ℂ)) (u : L2) : ‖mulL2 c u‖ ≤ ‖c‖ * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [mulL2_ae c u] with t h
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_right (c.norm_coe_le_norm t) (norm_nonneg _)

end Lifts

/-! ### Cutoffs in the level variable -/

theorem coordPartial_congr_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u w : ℝ × ℝ → E} {p : ℝ × ℝ} (h : u =ᶠ[𝓝 p] w) (j : Fin 2) :
    coordPartial j u p = coordPartial j w p := by
  unfold coordPartial
  split_ifs
  · have hl : (fun t ↦ u (t, p.2)) =ᶠ[𝓝 p.1] fun t ↦ w (t, p.2) :=
      (Continuous.tendsto (by fun_prop : Continuous fun t : ℝ ↦ (t, p.2)) p.1).eventually h
    rw [partialX, partialX, hl.deriv_eq]
  · have hl : (fun t ↦ u (p.1, t)) =ᶠ[𝓝 p.2] fun t ↦ w (p.1, t) :=
      (Continuous.tendsto (by fun_prop : Continuous fun t : ℝ ↦ (p.1, t)) p.2).eventually h
    rw [partialY, partialY, hl.deriv_eq]

/-- A smooth cutoff in the level variable, supported in `(0, 1)`, vanishing on `(-∞, h₁/2]` and
equal to `1` near `[h₁, h₂]`. -/
theorem exists_levelCutoff {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₂1 : h₂ < 1) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Ioo 0 1 ∧ (∀ s ≤ h₁ / 2, χ s = 0) ∧
      ∃ δ > 0, ∀ s ∈ Ioo (h₁ - δ) (h₂ + δ), χ s = 1 := by
  set δ := min h₁ (1 - h₂) / 4
  have hδ : 0 < δ := by positivity
  have hδ₁ : δ ≤ h₁ / 4 := by have := min_le_left h₁ (1 - h₂); simp only [δ]; linarith
  have hδ₂ : δ ≤ (1 - h₂) / 4 := by have := min_le_right h₁ (1 - h₂); simp only [δ]; linarith
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (s := Ioo (h₁ / 2) ((1 + h₂) / 2)) (t := Icc (h₁ - δ) (h₂ + δ)) isOpen_Ioo isClosed_Icc
    (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨χ, hχ, ?_, fun s hs ↦ ?_, δ, hδ, fun s hs ↦ (hχ1 s).1 ⟨hs.1.le, hs.2.le⟩⟩
  · rw [tsupport, hχs]
    refine (closure_mono Ioo_subset_Icc_self).trans ?_
    rw [isClosed_Icc.closure_eq]
    exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · by_contra h
    have : s ∈ Function.support χ := h
    rw [hχs] at this
    linarith [this.1]

/-- On the box, the cell cutoff agrees near each point with the periodic cutoff `χ(Ψ/2)`. -/
theorem cellCutoff_eventuallyEq {χ : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hχ0 : ∀ s ≤ a, χ s = 0)
    {p : ℝ × ℝ} (hp : p ∈ periodBox) :
    cellCutoff χ =ᶠ[𝓝 p] fun q ↦ χ (dipoleLift q / 2) := by
  have hO : IsOpen (cellSquare ∪ {q | dipoleLift q < 2 * a}) :=
    isOpen_cellSquare.union (isOpen_lt (by unfold dipoleLift; fun_prop) continuous_const)
  have hpO : p ∈ cellSquare ∪ {q | dipoleLift q < 2 * a} := by
    by_cases hpos : 0 < dipoleLift p
    · exact Or.inl (mem_cellSquare_of_mem_periodBox hp hpos)
    · exact Or.inr (show dipoleLift p < 2 * a by linarith)
  filter_upwards [hO.mem_nhds hpO] with q hq
  rcases hq with hq | hq
  · simp [cellCutoff, hq, levelCoord]
  · have h0 : χ (dipoleLift q / 2) = 0 := hχ0 _ (by change dipoleLift q < 2 * a at hq; linarith)
    by_cases hc : q ∈ cellSquare
    · simp [cellCutoff, hc, levelCoord, h0]
    · simp [cellCutoff, hc, h0]

/-! ### Limits -/

section Limits

variable {ι : Type*} {l : Filter ι}

/-- `L²(ℝ²)` convergence of the inputs gives convergence of the periodizations. -/
theorem tendsto_boxPeriodize {F : ι → ℝ × ℝ → ℂ} {G : ℝ × ℝ → ℂ}
    (hF : ∀ᶠ i in l, MemLp (F i) 2 (volume.restrict periodBox))
    (hG : MemLp G 2 (volume.restrict periodBox))
    (h : Tendsto (fun i ↦ eLpNorm (fun p ↦ F i p - G p) 2 volume) l (𝓝 0)) :
    Tendsto (fun i ↦ boxPeriodize (F i)) l (𝓝 (boxPeriodize G)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hB : Tendsto (fun i ↦ eLpNorm (fun p ↦ F i p - G p) 2 (volume.restrict periodBox)) l
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
      (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hT := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB
  refine hT.congr' ?_
  filter_upwards [hF] with i hi
  simp only [Function.comp_apply]
  rw [← boxPeriodize_sub hi hG, norm_boxPeriodize (hi.sub hG)]
  rfl

theorem tendsto_mulL2 (c : C(Torus, ℂ)) {x : ι → L2} {y : L2} (h : Tendsto x l (𝓝 y)) :
    Tendsto (fun i ↦ mulL2 c (x i)) l (𝓝 (mulL2 c y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using h.const_mul ‖c‖)
  rw [← mulL2_sub_right]
  exact norm_mulL2_le c _

end Limits

end NoEmbeddedEigenvalues
