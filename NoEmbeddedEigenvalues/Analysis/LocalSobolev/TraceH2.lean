import NoEmbeddedEigenvalues.Analysis.LocalSobolev.DiagonalACL
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceL2
import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalZeroExtension

/-!
# Differentiating an H² trace

Blueprint: `lem:trace-h2`.

The proof uses ACL slicing and the elementary L² trace estimate. No smooth
Sobolev approximation or fractional trace estimate is needed.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

/-- Local integrability under interchange of the two coordinates. -/
theorem locallyIntegrableOn_comp_swap {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : LocallyIntegrableOn F U) (hU : IsOpen U) :
    LocallyIntegrableOn (F ∘ Prod.swap) (Prod.swap ⁻¹' U) := by
  apply (locallyIntegrableOn_iff (hU.preimage continuous_swap).isLocallyClosed).2
  intro K hKU hK
  have hi := hF.integrableOn_compact_subset (image_subset_iff.2 hKU)
    (hK.image continuous_swap)
  have hm : Measure.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume = volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).map_eq
  have hp := (integrableOn_map_equiv (Homeomorph.prodComm ℝ ℝ).toMeasurableEquiv).1
    (show IntegrableOn F (Prod.swap '' K) (Measure.map Prod.swap volume) by rwa [hm])
  change IntegrableOn (F ∘ Prod.swap) (Prod.swap ⁻¹' (Prod.swap '' K)) at hp
  simpa only [(Function.Involutive.injective Prod.swap_swap).preimage_image] using hp

/-- Interchanging coordinates interchanges the weak partial derivatives. -/
theorem HasWeakPartialOn.comp_swap {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ} {j : Fin 2}
    (hU : IsOpen U) (hd : HasWeakPartialOn U j F D) :
    HasWeakPartialOn (Prod.swap ⁻¹' U) (1 - j) (F ∘ Prod.swap) (D ∘ Prod.swap) := by
  refine ⟨locallyIntegrableOn_comp_swap hd.1 hU,
    locallyIntegrableOn_comp_swap hd.2.1 hU, fun φ hφ ↦ ?_⟩
  have hψ : IsTestFunctionOn U (φ ∘ Prod.swap) := by
    refine ⟨hφ.contDiff.comp (contDiff_snd.prodMk contDiff_fst),
      hφ.hasCompactSupport.comp_homeomorph (Homeomorph.prodComm ℝ ℝ), ?_⟩
    intro p hp
    have ht : p.swap ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ Homeomorph.prodComm ℝ ℝ) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    simpa only [mem_preimage, Prod.swap_swap] using hφ.tsupport_subset ht
  have hw := hd.2.2 _ hψ
  have hi (f : ℝ × ℝ → ℂ) : (∫ p : ℝ × ℝ, f p.swap) = ∫ p, f p := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_swap f
  rw [← hi (fun p ↦ F p * coordPartial j (φ ∘ Prod.swap) p),
    ← hi (fun p ↦ D p * (φ ∘ Prod.swap) p)] at hw
  fin_cases j <;>
    simpa only [show (⟨0, by decide⟩ : Fin 2) = 0 by rfl,
      show (⟨1, by decide⟩ : Fin 2) = 1 by rfl,
      show (1 - 0 : Fin 2) = 1 by decide, sub_self, Function.comp_apply,
      coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, partialX, partialY,
      Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk, Prod.swap_swap] using hw

/-- Interchanging coordinates turns the first weak partial into the second. -/
theorem HasWeakPartialOn.comp_swap_fst {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hU : IsOpen U) (hd : HasWeakPartialOn U 0 F D) :
    HasWeakPartialOn (Prod.swap ⁻¹' U) 1 (F ∘ Prod.swap) (D ∘ Prod.swap) :=
  hd.comp_swap hU

/-- A uniform L¹ envelope for an interval H¹ section, anchored at an interior point. -/
theorem HasIntervalH1.norm_le_anchor {a b c t : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖F t‖ ≤ ‖F c‖ + ∫ s in Ioo a b, ‖D s‖ := by
  have he : F t = F c + ∫ s in c..t, D s := by rw [h.integral_eq_sub hc ht]; abel
  have hbound : ‖∫ s in c..t, D s‖ ≤ ∫ s in Ioo a b, ‖D s‖ := by
    apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    rw [← integral_Icc_eq_integral_Ioo]
    exact setIntegral_mono_set h.integrableOn_derivative.norm
      (Eventually.of_forall (fun s ↦ norm_nonneg _))
      (Eventually.of_forall (fun s hs ↦
        uIoc_subset_uIcc.trans (uIcc_subset_Icc (Ioo_subset_Icc_self hc)
          (Ioo_subset_Icc_self ht)) hs))
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hbound)

/-- Integration of transverse ACL sections is continuous in the transverse variable.
The L² trace estimate supplies an integrable anchor; the L¹ derivative supplies
a single integrable envelope for all transverse parameters. -/
theorem HasACLSectionsOn.continuousOn_integral {I : Set ℝ} {b₁ b₂ : ℝ}
    [IsFiniteMeasure (volume.restrict I)] {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I (Ioo b₁ b₂) G D) (hb : b₁ < b₂) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ContinuousOn (fun b ↦ ∫ a in I, G (a, b)) (Ioo b₁ b₂) := by
  let m := (b₁ + b₂) / 2
  have hm : m ∈ Ioo b₁ b₂ := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hanchor := (h.l2_trace hb hGm hG hD m (Ioo_subset_Icc_self hm)).1
  have hraw : MemLp (fun a ↦ G (a, m)) 2 (volume.restrict I) := by
    apply hanchor.ae_eq
    filter_upwards [h.ae_trace_eq hb hG hD] with a ha
    exact ha m hm
  have hDp : MemLp D 2 ((volume.restrict I).prod (volume.restrict (Ioo b₁ b₂))) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hD
  have iD := (hDp.integrable (by norm_num)).norm.integral_prod_left
  apply continuousOn_of_dominated
    (bound := fun a ↦ ‖G (a, m)‖ + ∫ t in Ioo b₁ b₂, ‖D (a, t)‖)
  · intro b _
    exact (hGm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · intro b hbJ
    filter_upwards [h.ae_hasIntervalH1 hG hD] with a ha
    exact ha.norm_le_anchor hm hbJ
  · exact (hraw.integrable (by norm_num)).norm.add iD
  · exact h.ae_continuousOn isOpen_Ioo

/-- Square integrability under interchange of coordinates. -/
theorem memLp_comp_swap {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict U)) :
    MemLp (F ∘ Prod.swap) 2 (volume.restrict (Prod.swap ⁻¹' U)) := by
  apply (Homeomorph.prodComm ℝ ℝ).measurableEmbedding.memLp_map_measure_iff.1
  change MemLp F 2 (Measure.map Prod.swap (volume.restrict (Prod.swap ⁻¹' U)))
  rw [← Measure.restrict_map measurable_swap hU]
  have hm : Measure.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume = volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).map_eq
  rwa [hm]

/-- Tangential FTC on almost every horizontal line, with any a.e. representative
of the weak tangential derivative. Continuity identifies the ACL value of `F`. -/
theorem HasWeakPartialOn.ae_horizontal_integral_eq {a₀ a₁ b₁ b₂ : ℝ}
    {F A V : ℝ × ℝ → ℂ} (ha : a₀ < a₁) (hb : b₁ < b₂)
    (hFc : ContinuousOn F (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂))
    (hF : MemLp F 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hA : MemLp A 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hd : HasWeakPartialOn (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) 0 F A)
    (hVA : V =ᵐ[volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)] A) :
    ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)), ∀ c ∈ Ioo a₀ a₁, ∀ d ∈ Ioo a₀ a₁,
      (∫ a in c..d, V (a, b)) = F (d, b) - F (c, b) := by
  have hs : Prod.swap ⁻¹' (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) = Ioo b₁ b₂ ×ˢ Ioo a₀ a₁ := by
    ext p; simp only [mem_preimage, mem_prod, Prod.fst_swap, Prod.snd_swap, and_comm]
  have hFo : IsOpen (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) := isOpen_Ioo.prod isOpen_Ioo
  have hFs := memLp_comp_swap hFo.measurableSet hF
  have hAs := memLp_comp_swap hFo.measurableSet hA
  have hds := hd.comp_swap_fst hFo
  rw [hs] at hFs hAs hds
  obtain ⟨K, -, hKF, hK⟩ := hds.exists_acl_sections isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 ha)
  have hKL := hFs.ae_eq hKF.symm
  have hcont : ∀ᵐ b ∂(volume.restrict (Ioo b₁ b₂)),
      ContinuousOn (fun a ↦ F (a, b)) (Ioo a₀ a₁) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hbJ
    exact hFc.comp (continuous_id.prodMk continuous_const).continuousOn (fun a haI ↦ ⟨haI, hbJ⟩)
  have hwhole := ae_eqOn_sections_of_ae_eq isOpen_Ioo hKF (hK.ae_continuousOn isOpen_Ioo) hcont
  have hvp : V =ᵐ[(volume.restrict (Ioo a₀ a₁)).prod (volume.restrict (Ioo b₁ b₂))] A := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hVA
  have hvps : ∀ᵐ p ∂((volume.restrict (Ioo b₁ b₂)).prod (volume.restrict (Ioo a₀ a₁))),
      V p.swap = A p.swap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hvp
  filter_upwards [hK.ae_hasIntervalH1 hKL hAs, hwhole, Measure.ae_ae_of_ae_prod hvps]
    with b hbK hbwhole hbV
  intro c hc d hd
  have hi : (∫ a in c..d, V (a, b)) = ∫ a in c..d, A (a, b) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hbV] with a ha hacd
    exact ha (uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hc hd) hacd)
  rw [hi]
  exact (hbK.integral_eq_sub hc hd).trans
    (congrArg₂ Sub.sub (hbwhole d hd) (hbwhole c hc))

/-- The horizontal FTC holds on every interior line once the tangential
weak derivative has transverse ACL regularity. Continuity in the transverse
parameter removes the exceptional set of horizontal lines. -/
theorem HasWeakPartialOn.horizontal_integral_eq {a₀ a₁ b₁ b₂ : ℝ}
    {F A V B : ℝ × ℝ → ℂ} (ha : a₀ < a₁) (hb : b₁ < b₂)
    (hFc : ContinuousOn F (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂))
    (hF : MemLp F 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hA : MemLp A 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)))
    (hd : HasWeakPartialOn (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂) 0 F A)
    (hVA : V =ᵐ[volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂)] A)
    (hVm : Measurable V) (hV : HasACLSectionsOn (Ioo a₀ a₁) (Ioo b₁ b₂) V B)
    (hB : MemLp B 2 (volume.restrict (Ioo a₀ a₁ ×ˢ Ioo b₁ b₂))) :
    ∀ b ∈ Ioo b₁ b₂, ∀ c ∈ Ioo a₀ a₁, ∀ d ∈ Ioo a₀ a₁,
      (∫ a in c..d, V (a, b)) = F (d, b) - F (c, b) := by
  have hVL := hA.ae_eq hVA.symm
  have hae := hd.ae_horizontal_integral_eq ha hb hFc hF hA hVA
  have hordered : ∀ c ∈ Ioo a₀ a₁, ∀ d ∈ Ioo a₀ a₁, c ≤ d → ∀ b ∈ Ioo b₁ b₂,
      (∫ a in c..d, V (a, b)) = F (d, b) - F (c, b) := by
    intro c hc d hd hcd
    have hsub : Icc c d ⊆ Ioo a₀ a₁ := Icc_subset_Ioo hc.1 hd.2
    have hVs : HasACLSectionsOn (Icc c d) (Ioo b₁ b₂) V B :=
      ae_restrict_of_ae_restrict_of_subset hsub hV
    have hVLs := hVL.mono_measure (Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl)
    have hBLs := hB.mono_measure (Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl)
    have hci := hVs.continuousOn_integral hb hVm hVLs hBLs
    have hleft : ContinuousOn (fun b ↦ ∫ a in c..d, V (a, b)) (Ioo b₁ b₂) := by
      simpa only [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc] using hci
    have hcf (x : ℝ) (hx : x ∈ Ioo a₀ a₁) :
        ContinuousOn (fun b ↦ F (x, b)) (Ioo b₁ b₂) :=
      hFc.comp (continuous_const.prodMk continuous_id).continuousOn (fun b hb ↦ ⟨hx, hb⟩)
    exact Measure.eqOn_open_of_ae_eq (hae.mono fun b h ↦ h c hc d hd)
      isOpen_Ioo hleft ((hcf d hd).sub (hcf c hc))
  intro b hbJ c hc d hd
  rcases le_total c d with hcd | hdc
  · exact hordered c hc d hd hcd b hbJ
  · rw [intervalIntegral.integral_symm, hordered d hd c hc hdc b hbJ]
    abel

/-- Traces of continuous `H²` functions on a line `b = b₀` are absolutely continuous, with
    derivative the trace of `∂_a F = ∂ₓF + ∂_yF`, which is square integrable. The returned
    representative of `Fx + Fy` is also locally absolutely continuous on almost every
    transverse line, so its values on `b = b₀` are genuine ACL trace values. -/
theorem absolutelyContinuous_trace_of_H2 {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F Fx Fy : ℝ × ℝ → ℂ} {a₀ a₁ b₁ b₂ b₀ : ℝ} (ha : a₀ < a₁)
    (hQ : diagRect (Set.Ioo a₀ a₁) (Set.Ioo b₁ b₂) ⊆ U) (hb₀ : b₀ ∈ Set.Ioo b₁ b₂)
    (hFc : ContinuousOn F U) (hF : MemSobolevOn 2 U F) (hx : HasWeakPartialOn U 0 F Fx)
    (hy : HasWeakPartialOn U 1 F Fy) :
    ∃ H : ℝ × ℝ → ℂ, (∀ᵐ p ∂(volume.restrict U), H p = Fx p + Fy p) ∧
      (∀ᵐ a ∂(volume.restrict (Set.Ioo a₀ a₁)), ∀ c d,
        b₁ < c → c ≤ d → d < b₂ →
          AbsolutelyContinuousOnInterval (fun b ↦ H (diagInv (a, b))) c d) ∧
      (∀ c d, a₀ < c → c ≤ d → d < a₁ →
        AbsolutelyContinuousOnInterval (fun a ↦ F (diagInv (a, b₀))) c d) ∧
      (∀ᵐ a ∂(volume.restrict (Set.Ioo a₀ a₁)),
        HasDerivAt (fun a ↦ F (diagInv (a, b₀))) (H (diagInv (a, b₀))) a) ∧
      MemLp (fun a ↦ H (diagInv (a, b₀))) 2 (volume.restrict (Set.Ioo a₀ a₁)) := by
  classical
  have hb : b₁ < b₂ := hb₀.1.trans hb₀.2
  obtain ⟨Dx, hDx, hDxL⟩ := hF.2 0
  obtain ⟨Dy, hDy, hDyL⟩ := hF.2 1
  let A := fun p ↦ Dx p + Dy p
  have hA : MemSobolevOn 1 U A := MemSobolevOnWith.add hDxL hDyL
  obtain ⟨Ax, hAx, hAxL⟩ := hA.2 0
  obtain ⟨Ay, hAy, hAyL⟩ := hA.2 1
  let R := Ioo a₀ a₁ ×ˢ Ioo b₁ b₂
  have hRm : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hRU : R ⊆ diagInv ⁻¹' U := by
    intro q hq
    apply hQ
    simpa only [R, mem_prod, diagRect, mem_ofPred_eq, diagCoord_diagInv] using hq
  have hFL := (memLp_comp_diagInv hU.measurableSet hF.1).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  have hAL := (memLp_comp_diagInv hU.measurableSet hA.1).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  have hBL := (memLp_comp_diagInv hU.measurableSet (hAxL.sub hAyL)).mono_measure
    (Measure.restrict_mono hRU le_rfl)
  have hda := (hDx.comp_diagInv_fst hU hDy).mono hRU
  have hdb := (hAx.comp_diagInv_snd hU hAy).mono hRU
  obtain ⟨V, hVm, hVA, hV⟩ := hdb.exists_acl_sections
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 ha)
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
  have hVL := hAL.ae_eq hVA.symm
  have hFcR : ContinuousOn (F ∘ diagInv) R :=
    hFc.comp diagInv.continuous.continuousOn hRU
  have hFTC := hda.horizontal_integral_eq ha hb hFcR hFL hAL hVA hVm hV hBL
  have hVT : MemLp (fun a ↦ V (a, b₀)) 2 (volume.restrict (Ioo a₀ a₁)) := by
    apply ((hV.l2_trace hb hVm hVL hBL b₀ (Ioo_subset_Icc_self hb₀)).1).ae_eq
    filter_upwards [hV.ae_trace_eq hb hVL hBL] with a ha
    exact ha b₀ hb₀
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq ha hVT (hFTC b₀ hb₀)
  let Q := diagInv.symm ⁻¹' R
  let H : ℝ × ℝ → ℂ := Q.piecewise (V ∘ diagInv.symm) (fun p ↦ Fx p + Fy p)
  have hHdiag : ∀ a ∈ Ioo a₀ a₁, ∀ b ∈ Ioo b₁ b₂, H (diagInv (a, b)) = V (a, b) := by
    intro a ha b hb
    have hmem : diagInv (a, b) ∈ Q := by
      simpa only [Q, mem_preimage, diagInv.symm_apply_apply] using (show (a, b) ∈ R from ⟨ha, hb⟩)
    change Q.piecewise (V ∘ diagInv.symm) (fun p ↦ Fx p + Fy p) (diagInv (a, b)) = _
    rw [piecewise_eq_of_mem Q _ _ hmem]
    exact congrArg V (diagInv.symm_apply_apply (a, b))
  have hVAp : ∀ᵐ p, p ∈ Q → V (diagInv.symm p) = A p := by
    have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    have h := (Measure.LinearMap.quasiMeasurePreserving volume
      (diagInvLinear.symm : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
      (LinearEquiv.isUnit_det' diagInvLinear.symm).ne_zero).ae
      ((ae_restrict_iff' hRm).1 hVA)
    change ∀ᵐ p, diagInv.symm p ∈ R → V (diagInv.symm p) = A (diagInv (diagInv.symm p)) at h
    simpa only [Q, mem_preimage, diagInv.apply_symm_apply] using h
  refine ⟨H, ?_, ?_, hac, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hVAp, ae_restrict_of_ae (hx.ae_eq hU hDx),
      ae_restrict_of_ae (hy.ae_eq hU hDy), ae_restrict_mem hU.measurableSet]
      with p hp hpx hpy hpU
    by_cases hpQ : p ∈ Q
    · exact (piecewise_eq_of_mem Q _ _ hpQ).trans
        ((hp hpQ).trans (congrArg₂ (· + ·) (hpx hpU).symm (hpy hpU).symm))
    · exact piecewise_eq_of_notMem Q _ _ hpQ
  · filter_upwards [hV, ae_restrict_mem measurableSet_Ioo] with a ha haI
    intro c d hc hcd hd
    have hsub : uIcc c d ⊆ Ioo b₁ b₂ := by
      rw [uIcc_of_le hcd]
      exact Icc_subset_Ioo hc hd
    exact (ha.1 c d hsub).congr (fun b hb ↦ (hHdiag a haI b (hsub hb)).symm)
  · filter_upwards [hder, ae_restrict_mem measurableSet_Ioo] with a ha haI
    rw [hHdiag a haI b₀ hb₀]
    exact ha
  · apply hVT.ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact (hHdiag a ha b₀ hb₀).symm



end NoEmbeddedEigenvalues
