import NoEmbeddedEigenvalues.Transport.WeightedForcing.CellFolding

/-!
# Lifting a weighted cell gradient to a separatrix neighbourhood

Blueprint: `lem:weighted-gradient-affine`, `lem:weighted-gradient-periodic-cover`,
`lem:odd-odd-cell-fold-parity`, `lem:cell-fold-l2-cover`.

Reflected periodic cell copies cover every nonzero small level. A bounded
set needs only finitely many period indices. Weak uniqueness transfers each
cell estimate to the same specified ordinary spatial gradient; null level
sets and cell seams are used only for L², never to glue weak identities.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open Real

/-- The lifted separatrix is null. -/
theorem ae_dipoleLift_ne_zero : ∀ᵐ p : ℝ × ℝ, dipoleLift p ≠ 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | dipoleLift p ≠ 0} := by
    exact (isClosed_eq (show Continuous dipoleLift by unfold dipoleLift; fun_prop)
      continuous_const).isOpen_compl.measurableSet
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact Eventually.of_forall fun x ↦ by
    rw [ae_iff]
    simp only [not_not]
    have hsub : {y : ℝ | dipoleLift (x, y) = 0} ⊆
        range (fun n : ℤ ↦ (n : ℝ) * (2 * π) + π - x) ∪
        range (fun n : ℤ ↦ x - π - (n : ℝ) * (2 * π)) := by
      intro y hy
      have hz : Ψ (torusProj (x, y)) = 0 := by rwa [Ψ_torusProj]
      rcases (Ψ_eq_zero_iff _).mp hz with hs | hs
      · have he : ((x + y : ℝ) : Angle) = (π : Angle) := by
          simpa only [torusProj, Angle.coe_add] using hs
        obtain ⟨n, hn⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp he
        exact Or.inl ⟨n, by linarith only [hn]⟩
      · have he : ((x - y : ℝ) : Angle) = (π : Angle) := by
          simpa only [torusProj, Angle.coe_sub] using hs
        obtain ⟨n, hn⟩ := Angle.angle_eq_iff_two_pi_dvd_sub.mp he
        exact Or.inr ⟨n, by linarith only [hn]⟩
    exact ((countable_range _).union (countable_range _)).mono hsub |>.measure_zero volume

/-- Odd parity is an a.e. identity of actual lifted representatives. -/
theorem liftL2_separatrixReflect_ae {ω : L2} {b : Bool} (hs : InSector false b ω) :
    (liftL2 ω ∘ separatrixReflect) =ᵐ[volume] fun p ↦ -liftL2 ω p := by
  have he : pullback S₁ measurePreserving_S₁ ω = (-1 : ℂ) • ω := hs.1
  have ht := ae_comp_of_pullback_eq he
  have ht' : ∀ᵐ t : Torus, ω (S₁ t) = -ω t := by
    filter_upwards [ht, Lp.coeFn_smul (-1 : ℂ) ω] with t hp hsm
    simp only [hp, hsm, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  filter_upwards [ae_torusProj ht'] with p hp
  simpa only [Function.comp_apply, liftL2, separatrixReflect, torusProj, S₁, Angle.coe_sub] using hp

/-- Each fold acts by a nonzero constant on a raw lift odd in the first reflection. -/
theorem liftL2_cellFold_ae {ω : L2} {b : Bool} (hs : InSector false b ω)
    (s : Bool) (n : ℤ × ℤ) :
    (liftL2 ω ∘ cellFold s n) =ᵐ[volume] fun p ↦ (if s then -1 else 1 : ℂ) * liftL2 ω p := by
  cases s
  · exact Eventually.of_forall fun p ↦ by
      simp only [Function.comp_apply, cellFold_apply, Bool.false_eq_true, ite_false,
        liftL2_liftShift, one_mul]
  · filter_upwards [liftL2_separatrixReflect_ae hs] with p hp
    simpa only [Function.comp_apply, cellFold_apply, Bool.true_eq, ite_true,
      liftL2_liftShift, neg_one_mul] using hp

/-- Finite reflected-periodic covers transfer actual L² norms to every bounded
localization of a collar. The separatrix is omitted only for norms. -/
theorem memSobolevLocOn_zero_of_cellFold_cover {ε : ℝ} {U : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} (hFm : Measurable F)
    (hF : ∀ (s : Bool) (n : ℤ × ℤ), MemLp F 2
      (volume.restrict (U ∩ cellFold s n ⁻¹' cellSeparatrixStrip ε))) :
    MemSobolevLocOn 0 (U ∩ {p | |dipoleLift p| < ε}) F := by
  intro V _ hVc hVW
  obtain ⟨R, hR⟩ := hVc.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * Real.pi + R)
  let O := fun i : Bool × (shiftBox N) ↦ U ∩ cellFold i.1 i.2.val ⁻¹' cellSeparatrixStrip ε
  have hi : IntegrableOn (fun p ↦ ‖F p‖ ^ 2) (⋃ i : Bool × (shiftBox N), O i) :=
    integrableOn_finite_iUnion.mpr fun i ↦
      (memLp_two_iff_integrable_sq_norm (hF i.1 i.2.val).aestronglyMeasurable).mp
        (hF i.1 i.2.val)
  have hLu := (memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).mpr hi
  apply hLu.mono_measure (Measure.restrict_mono_ae ?_)
  filter_upwards [ae_dipoleLift_ne_zero] with p hp0 hpV
  have hpW := hVW (subset_closure hpV)
  obtain ⟨s, n, hn⟩ := exists_cellFold_mem_collar hp0 hpW.2
  have hnN := cellFold_mem_shiftBox hN (hR p (subset_closure hpV)) s hn.1
  exact mem_iUnion.mpr ⟨(s, ⟨n, hnN⟩), hpW.1, hn⟩

/-- Affine weak transport and exact distance invariance preserve weighted gradients. -/
theorem exists_weightedGradient_planeAffine
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ)
    (hmp : MeasurePreserving (planeAffine A c))
    (hr : ∀ p, saddleDist (planeAffine A c p) = saddleDist p)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℂ}
    {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn V j F (D j) ∧
      MemLp (fun p ↦ D j p / (saddleDist p : ℂ)) 2 (volume.restrict V))
    {a : ℂ} (ha : a ≠ 0) (hchar : (F ∘ planeAffine A c) =ᵐ[volume] fun p ↦ a * F p) :
    ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (planeAffine A c ⁻¹' V) j F (E j) ∧
      MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2
        (volume.restrict (planeAffine A c ⁻¹' V)) := by
  let E := fun (j : Fin 2) p ↦ a⁻¹ *
    (affineCoeff A 0 j * D 0 (planeAffine A c p) +
      affineCoeff A 1 j * D 1 (planeAffine A c p))
  have he : (fun p ↦ a⁻¹ * F (planeAffine A c p)) =ᵐ[volume] F := by
    filter_upwards [hchar] with p hp
    change F (planeAffine A c p) = a * F p at hp
    rw [hp, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  refine ⟨E, fun j ↦ ⟨?_, ?_⟩⟩
  · exact ((HasWeakPartialOn.comp_planeAffine A c hmp hV
      (fun i ↦ (hD i).1) j).const_mul a⁻¹).congr_left he
  · have hL (i : Fin 2) : MemLp (fun p ↦ D i (planeAffine A c p) / (saddleDist p : ℂ)) 2
        (volume.restrict (planeAffine A c ⁻¹' V)) := by
      simpa only [Function.comp_def, hr] using
        memLp_comp_planeAffine A c hmp hV.measurableSet (hD i).2
    convert (((hL 0).const_mul (affineCoeff A 0 j)).add
      ((hL 1).const_mul (affineCoeff A 1 j))).const_mul a⁻¹ using 1
    funext p
    dsimp [E]
    ring

/-- A whole-cell estimate gives local weighted L² for the same specified gradient
on a smaller lifted neighbourhood. Reflections use raw a.e. parity, not traces. -/
theorem weighted_gradient_neighbourhood_of_cell {ω : L2} (hs : InSector false false ω)
    {ε : ℝ} (hε : 0 < ε) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsep : {p | dipoleLift p = 0} ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hDm : ∀ j, Measurable (D j))
    (hD : ∀ j, HasWeakPartialOn U j (liftL2 ω) (D j))
    (hE : ∃ E : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (cellSeparatrixStrip ε) j (liftL2 ω) (E j) ∧
      MemLp (fun p ↦ E j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellSeparatrixStrip ε))) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ {p | dipoleLift p = 0} ⊆ W ∧
      ∀ j, HasWeakPartialOn W j (liftL2 ω) (D j) ∧
        MemSobolevLocOn 0 W (fun p ↦ D j p / (saddleDist p : ℂ)) := by
  let W := U ∩ {p | |dipoleLift p| < ε}
  have hW : IsOpen W := hU.inter (isOpen_lt (by unfold dipoleLift; fun_prop) continuous_const)
  have hWsep : {p | dipoleLift p = 0} ⊆ W := by
    intro p hp
    refine ⟨hsep hp, ?_⟩
    change dipoleLift p = 0 at hp
    change |dipoleLift p| < ε
    simpa only [hp, abs_zero] using hε
  obtain ⟨E, hE⟩ := hE
  have hfold (s : Bool) (n : ℤ × ℤ) : ∃ G : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn (cellFold s n ⁻¹' cellSeparatrixStrip ε) j (liftL2 ω) (G j) ∧
      MemLp (fun p ↦ G j p / (saddleDist p : ℂ)) 2
        (volume.restrict (cellFold s n ⁻¹' cellSeparatrixStrip ε)) := by
    exact exists_weightedGradient_planeAffine (cellFoldLinear s) (cellFoldTranslation s n)
      (measurePreserving_cellFold s n) (saddleDist_cellFold s n)
      (isOpen_cellSeparatrixStrip ε) hE (by cases s <;> norm_num) (liftL2_cellFold_ae hs s n)
  refine ⟨W, hW, hWsep, fun j ↦ ⟨(hD j).mono inter_subset_left, ?_⟩⟩
  apply memSobolevLocOn_zero_of_cellFold_cover
    ((hDm j).div (Complex.measurable_ofReal.comp
      (Metric.continuous_infDist_pt saddleSet).measurable))
  intro s n
  obtain ⟨G, hG⟩ := hfold s n
  have hO : IsOpen (U ∩ cellFold s n ⁻¹' cellSeparatrixStrip ε) := hU.inter
    ((isOpen_cellSeparatrixStrip ε).preimage (cellFold s n).continuous)
  have hi : MemLp (fun p ↦ G j p / (saddleDist p : ℂ)) 2
      (volume.restrict (U ∩ cellFold s n ⁻¹' cellSeparatrixStrip ε)) :=
    (hG j).2.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have he := ((hD j).mono inter_subset_left).ae_eq hO ((hG j).1.mono inter_subset_right)
  apply hi.ae_eq
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hO.measurableSet] with p hp hpO
  change G j p / (saddleDist p : ℂ) = D j p / (saddleDist p : ℂ)
  rw [hp hpO]

end NoEmbeddedEigenvalues
