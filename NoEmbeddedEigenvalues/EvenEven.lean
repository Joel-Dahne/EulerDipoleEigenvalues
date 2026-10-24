import NoEmbeddedEigenvalues.NormalVirial
import NoEmbeddedEigenvalues.EvenEvenBoundary
import NoEmbeddedEigenvalues.PairingLimit

/-!
# Even–even exclusion

Blueprint: `lem:ee-cell-vanishing`, `lem:ee-vorticity-from-density`,
`lem:nonnegative-exhaustion`, `lem:ee-character-exclusion` and `thm:ee-exclusion`.

Combine the truncated virial from `NormalVirial.lean`, the gradient traces and
canonical arc positivity from `EvenEvenBoundary.lean`, and the transport pairing
limit from `PairingLimit.lean` on one sequence avoiding all exceptional levels.
Nonnegative exhaustion gives zero bulk density. Since its vorticity coefficient
is positive almost everywhere in the cell, the vorticity vanishes there; reflection
extends this to the torus. Only truncated integrability is needed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A symmetry/measure bridge: vanishing on a positive-cell lift forces an even vorticity
    to vanish on both torus cells. It needs no eigenvalue or stream-function hypothesis. -/
theorem InSector.eq_zero_of_lift_ae_zero_on_cellSquare {ω : L2}
    (hs : InSector true true ω)
    (hz : ∀ᵐ p ∂(volume.restrict cellSquare), liftL2 ω p = 0) : ω = 0 := by
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  let I : Set ℝ := Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)
  let F : Set (ℝ × ℝ) := I ×ˢ I
  have hI : MeasurableSet I := measurableSet_Ioc
  have hF : MeasurableSet F := hI.prod hI
  have hproj : MeasurePreserving torusProj (volume.restrict F) volume := by
    change MeasurePreserving (Prod.map (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi)))
      (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi)))) (volume.restrict F)
      (volume : Measure (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)))
    have hm := AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)
    refine ⟨by fun_prop, ?_⟩
    have hp := (hm.prod hm).map_eq
    simpa only [F, I, Measure.prod_restrict, ← Measure.volume_eq_prod,
      torusProj, Real.Angle.coe, Prod.map] using hp
  have hsub : cellSquare ⊆ F := by
    intro p hp
    change |(p.1 + p.2) / 2| < Real.pi / 2 ∧
      |(p.1 - p.2) / 2| < Real.pi / 2 at hp
    obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
    obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hinj : InjOn torusProj F := by
    intro p hp q hq heq
    apply Prod.ext
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hp.1 hq.1).1 (congrArg Prod.fst heq)
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hp.2 hq.2).1 (congrArg Prod.snd heq)
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hz' := (ae_restrict_iff' hcell).1 hz
  have hpos : ∀ᵐ t : Torus, 0 < Ψ t → ω t = 0 := by
    have hequiv := ae_map_iff (μ := volume.restrict F) hproj.measurable.aemeasurable
      (p := fun t : Torus ↦ 0 < Ψ t → ω t = 0)
      (by
        simp only [imp_iff_not_or]
        exact (measurableSet_lt measurable_const hΨ.measurable).compl.union
          ((Lp.stronglyMeasurable ω).measurable (measurableSet_singleton 0)))
    simp only [hproj.map_eq] at hequiv
    apply hequiv.2
    filter_upwards [ae_restrict_of_ae hz', ae_restrict_mem hF] with p hp hpF hpt
    obtain ⟨q, hq, hqp⟩ := exists_mem_cellSquare hpt
    have hqp' : q = p := hinj (hsub hq) hpF hqp
    subst q
    exact hp hq
  have hsingle (x : Real.Angle) : volume ({x} : Set Real.Angle) = 0 := by
    change (volume : Measure (AddCircle (2 * Real.pi))) {x} = 0
    have hx := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
    have hx0 : (volume : Measure (AddCircle (2 * Real.pi))) (Metric.closedBall x 0) = 0 := by
      simpa only [mul_zero, min_eq_right (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        ENNReal.ofReal_zero] using hx
    exact measure_mono_null
      (singleton_subset_iff.mpr (Metric.mem_closedBall_self (by norm_num))) hx0
  have hnull : ∀ᵐ t : Torus, Ψ t ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq hΨ continuous_const).isOpen_compl.measurableSet).2
    exact Eventually.of_forall fun x ↦ by
      rw [ae_iff]
      simp only [not_not]
      have hsub' : {y : Real.Angle | Ψ (x, y) = 0} ⊆
          {((Real.pi : ℝ) : Real.Angle) - x, x - ((Real.pi : ℝ) : Real.Angle)} := by
        intro y hy
        rcases Ψ_eq_zero_iff (x, y) |>.mp hy with hy | hy
        · exact Or.inl (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hy))
        · exact Or.inr (eq_sub_iff_add_eq.mpr
            (by simpa [add_comm] using (sub_eq_iff_eq_add.mp hy).symm))
      have hpair := measure_union_null (hsingle (((Real.pi : ℝ) : Real.Angle) - x))
        (hsingle (x - ((Real.pi : ℝ) : Real.Angle)))
      exact measure_mono_null hsub' (by simpa only [singleton_union] using hpair)
  have href : reflect₁ ω = ω := by simpa [paritySign] using hs.1
  have hraw := Lp.coeFn_compMeasurePreserving ω measurePreserving_S₁
  change (reflect₁ ω : Torus → ℂ) =ᵐ[volume] (fun t ↦ ω (S₁ t)) at hraw
  rw [href] at hraw
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hpos, measurePreserving_S₁.quasiMeasurePreserving.ae hpos, hraw, hnull]
    with t hp hpn ht hn
  by_cases hpt : 0 < Ψ t
  · exact hp hpt
  · have hsneg : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    rw [ht]
    apply hpn
    rw [hsneg]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpt) hn)

/-- Unlike the gradient argument, exclusion only needs strict positivity of the vorticity
    coefficient away from a null set. -/
theorem normalCoeff_pos_of_cos_ne {p : ℝ × ℝ} (h0 : 0 < dipoleLift p)
    (hne : Real.cos p.1 ≠ Real.cos p.2) : 0 < normalCoeff p := by
  have hx := Real.cos_le_one p.1
  have hy := Real.cos_le_one p.2
  have h2 : dipoleLift p < 2 := by
    unfold dipoleLift
    by_contra hn
    exact hne (by linarith)
  have hρ := gradSq_dipoleLift_pos h0 h2
  unfold normalCoeff
  exact div_pos (mul_pos (mul_pos h0 (by linarith)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)))
    (sq_pos_of_pos hρ)

/-- Zero bulk density forces the vorticity itself to vanish on the cell. -/
theorem lift_ae_zero_of_eeBulkDensity_ae_zero {ω : L2}
    (hz : ∀ᵐ p ∂(volume.restrict cellSquare), eeBulkDensity ω p = 0) :
    ∀ᵐ p ∂(volume.restrict cellSquare), liftL2 ω p = 0 := by
  filter_upwards [hz, ae_restrict_of_ae ae_cos_fst_ne_cos_snd,
    ae_restrict_mem (show MeasurableSet cellSquare by unfold cellSquare diagCoord; measurability)]
    with p hp hne hcell
  have h0 : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hcell
  have hf := normalCoeff_pos_of_cos_ne h0 hne
  have h2 : dipoleLift p < 2 := by
    have hx := Real.cos_le_one p.1
    have hy := Real.cos_le_one p.2
    unfold dipoleLift
    by_contra hn
    exact hne (by linarith)
  obtain ⟨hc0, hc1⟩ := normalC_pos_le_one h0 h2
  have hnc : 0 ≤ 2 - normalC p := by linarith
  have hgrad : 0 ≤ (2 - normalC p) * ‖streamNormal ω p‖ ^ 2 +
      normalC p * ‖streamTangent ω p‖ ^ 2 := by positivity
  have hprod : normalCoeff p * ‖liftL2 ω p‖ ^ 2 = 0 := by
    change normalCoeff p * ‖liftL2 ω p‖ ^ 2 +
      (2 - normalC p) * ‖streamNormal ω p‖ ^ 2 +
      normalC p * ‖streamTangent ω p‖ ^ 2 = 0 at hp
    have hn : 0 ≤ normalCoeff p * ‖liftL2 ω p‖ ^ 2 := by positivity
    linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left hf.ne'))

/-- Nonnegative bulk integrals tending to a nonpositive limit vanish on every truncated
    set, hence on their union. No integrability on the full set is assumed. -/
theorem ae_zero_of_truncated_integral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {r J : α → ℝ}
    (hr : Measurable r) (hrpos : ∀ x ∈ s, 0 < r x) (hJ : ∀ x ∈ s, 0 ≤ J x)
    {ts : ℕ → ℝ} (htpos : ∀ n, 0 < ts n) (ht : Tendsto ts atTop (𝓝 0))
    (hi : ∀ n, IntegrableOn J {x | x ∈ s ∧ ts n < r x} μ)
    {b : ℝ} (hb : b ≤ 0)
    (hlim : Tendsto (fun n ↦ ∫ x in {x | x ∈ s ∧ ts n < r x}, J x ∂μ) atTop (𝓝 b)) :
    ∀ᵐ x ∂(μ.restrict s), J x = 0 := by
  let S : ℕ → Set α := fun n ↦ {x | x ∈ s ∧ ts n < r x}
  have hSm n : MeasurableSet (S n) := hs.inter (measurableSet_lt measurable_const hr)
  have hSn n : 0 ≤ᵐ[μ.restrict (S n)] J :=
    ae_restrict_of_forall_mem (hSm n) fun x hx ↦ hJ x hx.1
  have hzero n : (∫ x in S n, J x ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae (hSn n))
    apply le_trans _ hb
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [ht.eventually (gt_mem_nhds (htpos n))] with m hm
    exact setIntegral_mono_set (hi m) (hSn m)
      (Eventually.of_forall fun x hx ↦ ⟨hx.1, hm.trans hx.2⟩)
  have hza : ∀ n, ∀ᵐ x ∂μ, x ∈ S n → J x = 0 := fun n ↦
    (ae_restrict_iff' (hSm n)).1 ((integral_eq_zero_iff_of_nonneg_ae (hSn n) (hi n)).1 (hzero n))
  apply (ae_restrict_iff' hs).2
  filter_upwards [ae_all_iff.2 hza] with x hx hxs
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (hrpos x hxs))).exists
  exact hx n ⟨hxs, hn⟩

/-- Exclusion for a fixed rotation character, by the vorticity coefficient of the bulk. -/
theorem even_even_character_exclusion {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) : ω = 0 := by
  obtain ⟨he, Ng, hNg, hn, ht, hf⟩ := ee_gradient_traces hs
  obtain ⟨hd, hpairs⟩ := ee_transport_traces hlam hω hs hκ
  let B : ℝ → ℝ := fun h ↦
    levelIntegral h (fun p ↦
      gradNorm p * (streamLift ω p * (starRingEnd ℂ) (streamNormal ω p)).re) +
      (2 - 2 * h) * (levelIntegral h (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
        levelIntegral h (fun p ↦ ‖streamTangent ω p‖ ^ 2) -
        levelIntegral h (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re))
  let P : ℝ → Prop := fun h ↦
    IntegrableOn (eeBulkDensity ω) {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p} ∧
      (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p}, eeBulkDensity ω p) = B h
  have hv : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), P h := ee_truncated_virial hlam hω
  let Nv : Set ℝ := {h | h ∈ Ioo 0 1 ∧ ¬P h}
  have hNv : volume Nv = 0 := by
    have hv' := (ae_restrict_iff' measurableSet_Ioo).1 hv
    simpa only [ae_iff, not_imp] using hv'
  obtain ⟨seq, hseq, hlim, hpair⟩ :=
    hpairs (Ng ∪ Nv) (measure_union_null hNg hNv)
  have hP (j : ℕ) : P (seq j) := by
    by_contra hj
    exact (hseq j).2 (Or.inr ⟨(hseq j).1, hj⟩)
  have hwithin : Tendsto seq atTop (𝓝[Ioi 0 \ Ng] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun j ↦
      ⟨(hseq j).1.1, fun hj ↦ (hseq j).2 (Or.inl hj)⟩⟩
  have hsum : 0 ≤ ∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k) :=
    Finset.sum_nonneg fun k hk ↦ ee_canonicalArcForm_nonneg hlam hω hs hκ
      (Finset.mem_range.mp hk) (hd k (Finset.mem_range.mp hk)) (he k (Finset.mem_range.mp hk))
  have hscaled : Tendsto (fun j ↦ 2 * seq j) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 : ℝ)
  have hfactor : Tendsto (fun j ↦ 2 - 2 * seq j) atTop (𝓝 2) := by
    simpa using hscaled.const_sub (2 : ℝ)
  have hlimB : Tendsto (fun j ↦ B (seq j)) atTop
      (𝓝 (-2 * ∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k))) := by
    have hx := (hf.comp hwithin).add
      (hfactor.mul (((hn.comp hwithin).sub (ht.comp hwithin)).sub hpair))
    convert hx using 1
    · rfl
    · congr 1
      simp only [canonicalArcForm, Finset.sum_add_distrib, Function.comp_apply]
      ring
  apply hs.eq_zero_of_lift_ae_zero_on_cellSquare
  apply lift_ae_zero_of_eeBulkDensity_ae_zero
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  apply ae_zero_of_truncated_integral_tendsto hcell
    (show Measurable dipoleLift by unfold dipoleLift; fun_prop)
    (fun p hp ↦ by simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
    (fun _ hp ↦ eeBulkDensity_nonneg hp)
    (fun j ↦ mul_pos two_pos (hseq j).1.1) hscaled
    (fun j ↦ (hP j).1) (by linarith : -2 *
      (∑ k ∈ Finset.range 4, canonicalArcForm lam (contStream ω ∘ cellArc k)) ≤ 0)
  exact hlimB.congr fun j ↦ (hP j).2.symm

/-- An eigenfunction even under both separatrix reflections vanishes at every nonzero
    real spectral parameter, with no admitted dependencies. -/
theorem even_even_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector true true ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, even_even_character_exclusion hlam hep hsp hkp,
    even_even_character_exclusion hlam hem hsm hkm, add_zero]

end NoEmbeddedEigenvalues
