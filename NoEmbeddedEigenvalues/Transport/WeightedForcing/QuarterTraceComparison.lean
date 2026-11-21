import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTraceAverages
import NoEmbeddedEigenvalues.Transport.WeightedForcing.EndpointTangentialTrace

/-! # Canonical endpoint traces in the two quarter charts -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Metric Filter
open scoped Topology ContDiff

private theorem ae_Ioo_of_compact_windows {b : ℝ} {P : ℝ → Prop}
    (h : ∀ a c, 0 < a → a < c → c < b → ∀ᵐ x ∂volume.restrict (Ioo a c), P x) :
    ∀ᵐ x ∂volume.restrict (Ioo 0 b), P x := by
  have ha : ∀ᵐ x : ℝ, ∀ a c : ℚ, 0 < (a : ℝ) → (a : ℝ) < c → (c : ℝ) < b →
      x ∈ Ioo (a : ℝ) c → P x := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro c
    by_cases hh : 0 < (a : ℝ) ∧ (a : ℝ) < c ∧ (c : ℝ) < b
    · exact ((ae_restrict_iff' measurableSet_Ioo).1 (h a c hh.1 hh.2.1 hh.2.2)).mono
        fun _ hx _ _ _ hm ↦ hx hm
    · exact Eventually.of_forall fun _ ha hac hc _ ↦ (hh ⟨ha, hac, hc⟩).elim
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_mem measurableSet_Ioo] with x hx hxb
  obtain ⟨a, ha, hax⟩ := exists_rat_btwn hxb.1
  obtain ⟨c, hxc, hc⟩ := exists_rat_btwn hxb.2
  exact hx a c ha (hax.trans hxc) hc ⟨hax, hxc⟩

private theorem quarterRay_physical_square {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn 1 U F)
    (side : Bool) :
    ∀ᵐ r ∂volume.restrict (Ioo 0 (1 / 2)),
      Tendsto (fun ε ↦ (∫ p in closedBall (quarterEndpointRay side r) ε,
        ‖F p - interiorChartTrace (rotatedQuarterEndpointChart 0 side) F r‖) / (2 * ε) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
  apply ae_Ioo_of_compact_windows
  intro a b ha hab hb
  let C := rotatedQuarterEndpointChart 0 side
  have hC : (planeAffine (endpointRayLinear side) (quarterEndpointRay side 0) :
      (ℝ × ℝ) → ℝ × ℝ) = C := planeAffine_endpointRayLinear side
  have hC' (p : ℝ × ℝ) : HasFDerivAt C
      (endpointRayLinear side : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rw [← hC]
    exact (endpointRayLinear side).toContinuousLinearMap.hasFDerivAt.add_const _
  have hCs : ContDiff ℝ ∞ C := by
    rw [← hC]
    exact (endpointRayLinear side).toContinuousLinearMap.contDiff.add contDiff_const
  have hK : IsCompact (Icc a b ×ˢ ({0} : Set ℝ)) := isCompact_Icc.prod isCompact_singleton
  have hKU : Icc a b ×ˢ ({0} : Set ℝ) ⊆ C ⁻¹' U := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    have ht' : t = 0 := ht
    subst t
    apply hcell
    apply subset_closure
    apply (quarterEndpointChart_cone side (q := (r, 0)) ?_).1
    exact ⟨⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩, by simpa using ha.trans_le hr.1⟩
  obtain ⟨w, hw, hwidth⟩ := hK.exists_cthickening_subset_open (hU.preimage hCs.continuous) hKU
  have hrect : C '' (Icc a b ×ˢ Icc (-w) w) ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    apply hwidth
    apply Metric.mem_cthickening_of_dist_le q (q.1, 0) w
      (Icc a b ×ˢ ({0} : Set ℝ)) ⟨hq.1, by simp⟩
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
    exact max_le hw.le (abs_le.mpr hq.2)
  have hT := hF.memSobolevLocOn.quarterRayTrace (1 / 2) 0 side a b ha hab hb w hw hrect
  exact hT.tendsto_physical_square_oscillation hU (neg_neg_of_pos hw) hw
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hF.1.locallyIntegrable (by norm_num)))
    hCs.contDiffOn (fun q hq ↦ hrect ⟨q, ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩, rfl⟩)
    (fun x _ ↦ ⟨endpointRayLinear side, hC' (x, 0)⟩)

private theorem normalizedChart_hasFDerivAt_equiv (θ : ℝ) {q : ℝ × ℝ}
    (hq : q.1 ∈ Ioo (0 : ℝ) 1) :
    ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt (fun p : ℝ × ℝ ↦ actionAngleInv (p.1, θ + p.2))
        (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q := by
  let W : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, (θ + p.2) * orbitPeriod p.1)
  let V : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, p.2 / orbitPeriod p.1 - θ)
  have hs (p : ℝ × ℝ) (hp : p.1 ∈ Ioo (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ orbitPeriod p.1) p :=
    (contDiffOn_orbitPeriod.contDiffAt (isOpen_Ioo.mem_nhds hp)).comp p contDiffAt_fst
  have hW : DifferentiableAt ℝ W q := (contDiffAt_fst.prodMk
    ((contDiffAt_const.add contDiffAt_snd).mul (hs q hq))).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V (W q) := (contDiffAt_fst.prodMk
    ((contDiffAt_snd.div (hs (W q) hq) (orbitPeriod_pos hq.1 hq.2).ne').sub
      contDiffAt_const)).differentiableAt (by simp)
  have hVW : V ∘ W =ᶠ[𝓝 q] id := by
    filter_upwards [continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hq)] with p hp
    change (p.1, (θ + p.2) * orbitPeriod p.1 / orbitPeriod p.1 - θ) = p
    rw [mul_div_cancel_right₀ _ (orbitPeriod_pos hp.1 hp.2).ne', add_sub_cancel_left]
  have hleft := ((hV.hasFDerivAt.comp q hW.hasFDerivAt).congr_of_eventuallyEq hVW.symm).unique
    (hasFDerivAt_id q)
  have hWinj : Function.Injective (fderiv ℝ W q) := by
    intro x y he
    have hx (x : ℝ × ℝ) : fderiv ℝ V (W q) (fderiv ℝ W q x) = x :=
      DFunLike.congr_fun hleft x
    rw [← hx x, ← hx y, he]
  let A := (LinearEquiv.ofBijective (fderiv ℝ W q).toLinearMap
    ⟨hWinj, LinearMap.injective_iff_surjective.mp hWinj⟩).toContinuousLinearEquiv
  let G : ℝ × ℝ → ℝ × ℝ := fun p ↦ dipoleOrbit p.1 p.2
  have hdet : (fderiv ℝ G (W q)).det ≠ 0 := by
    rcases q with ⟨h, s⟩
    change (fderiv ℝ G (h, (θ + s) * orbitPeriod h)).det ≠ 0
    rw [det_fderiv_orbitMap hq]
    norm_num
  let B := ((fderiv ℝ G (W q)).toLinearMap.equivOfDetNeZero hdet).toContinuousLinearEquiv
  have hG : DifferentiableAt ℝ G (W q) := (contDiffAt_orbitMap hq).differentiableAt (by simp)
  exact ⟨A.trans B, hG.hasFDerivAt.comp q hW.hasFDerivAt⟩

private theorem normalizedChart_memSobolevOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : cellSquare ⊆ U) {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn 1 U F)
    {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < d) (hd : d < 1) :
    MemSobolevOn 1 (Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)) (F ∘ actionAngleInv) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRs : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKS : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hd)⟩, mem_univ _⟩
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict U)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band hU hu ha hab hb hd (fun p hp ↦ hcell hp.1.1)
  choose E hE hEL using hF.2
  refine ⟨hP F hF.1, fun j ↦ ⟨actionAnglePullbackGradient E j, ?_, ?_⟩⟩
  · exact (HasWeakPartialOn.comp_actionAngleInv
      (fun i ↦ (hE i).mono (sdiff_subset.trans hcell)) j).mono (hRs.trans hKS)
  · have hC (π : (ℝ × ℝ) →L[ℝ] ℝ) : ContinuousOn
        (fun q ↦ ((coordPartial j (fun p ↦ π (actionAngleInv p)) q : ℝ) : ℂ)) K :=
      (Complex.ofRealCLM.continuous.comp_continuousOn
        ((contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ)
          (π.contDiff.comp_contDiffOn contDiffOn_actionAngleInv) j).continuousOn)).mono hKS
    exact (memLp_mul_on_compact hK (measurableSet_Ioo.prod measurableSet_Ioo) hRs
      (hC (ContinuousLinearMap.fst ℝ ℝ ℝ)) (hP _ (hEL 0))).add
      (memLp_mul_on_compact hK (measurableSet_Ioo.prod measurableSet_Ioo) hRs
        (hC (ContinuousLinearMap.snd ℝ ℝ ℝ)) (hP _ (hEL 1)))

/-- Canonical normalized and affine traces identify the same weak field at
both quarter endpoints, without pointwise regularity on the ray. -/
theorem quarterEndpointTrace_compare {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcell : closure cellSquare ⊆ U) {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn 1 U F)
    {d : ℝ} (hd : d < 1) (hρ : quarterEndpointRadius d < 1 / 2) (side : Bool) :
    ∀ᵐ h ∂volume.restrict (Ioo 0 d),
      HasContinuousSectionGerm (fun s ↦ F (actionAngleInv
        (h, ((if side then 1 else -1 : ℝ) / 8) + s))) ∧
      interiorSectionTrace (fun s ↦ F (actionAngleInv
        (h, ((if side then 1 else -1 : ℝ) / 8) + s))) =
      interiorChartTrace (rotatedQuarterEndpointChart 0 side) F (quarterEndpointRadius h) := by
  let θ : ℝ := (if side then 1 else -1) / 8
  let C : ℝ × ℝ → ℝ × ℝ := fun p ↦ actionAngleInv (p.1, θ + p.2)
  have hmap (h : ℝ) (hh : h ∈ Ioo 0 d) : C (h, 0) =
      quarterEndpointRay side (quarterEndpointRadius h) := by
    have hp := dipoleOrbit_quarterEndpointRay hh.1 (hh.2.trans hd) side
    have ht : (θ + 0) * orbitPeriod h = (if side then 1 else -1 : ℝ) * eighthPeriod h := by
      dsimp [θ, orbitPeriod]; ring
    change dipoleOrbit h ((θ + 0) * orbitPeriod h) = _
    rw [ht]
    cases side <;> simpa using hp
  have hFU := locallyIntegrableOn_of_locallyIntegrable_restrict (hF.1.locallyIntegrable (by norm_num))
  have hRay := ae_quarterEndpointRadius hd hρ (quarterRay_physical_square hU hcell hF side)
  have hNorm : ∀ᵐ h ∂volume.restrict (Ioo 0 d),
      HasContinuousSectionGerm (fun s ↦ F (C (h, s))) ∧
      Tendsto (fun ε ↦ (∫ p in closedBall (C (h, 0)) ε,
        ‖F p - interiorChartTrace C F h‖) / (2 * ε) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    apply ae_Ioo_of_compact_windows
    intro a b ha hab hb
    let W : ℝ × ℝ → ℝ × ℝ := planeAffine (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)) (0, θ)
    let R := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
    let S := Ioo a b ×ˢ Ioo (-1 / 16 : ℝ) (1 / 16)
    have hWS : S ⊆ W ⁻¹' R := by
      intro q hq
      change q.1 + 0 ∈ Ioo a b ∧ q.2 + θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4)
      refine ⟨by simpa using hq.1, ?_⟩
      have hθ : |θ| ≤ 1 / 8 := by cases side <;> norm_num [θ]
      constructor <;> linarith [hq.2.1, hq.2.2, (abs_le.mp hθ).1, (abs_le.mp hθ).2]
    have hW : MeasurePreserving W volume volume := by
      change MeasurePreserving (fun p : ℝ × ℝ ↦ p + (0, θ)) volume volume
      rw [Measure.volume_eq_prod]
      exact (measurePreserving_add_right volume (0 : ℝ)).prod
        (measurePreserving_add_right volume θ)
    have hsc : S ⊆ (fun p : ℝ × ℝ ↦ (p.1, θ + p.2)) ⁻¹' actionStrip :=
      fun q hq ↦ ⟨⟨ha.trans hq.1.1, hq.1.2.trans (hb.trans hd)⟩, mem_univ _⟩
    have hc : ContDiffOn ℝ ∞ C S := contDiffOn_actionAngleInv.comp (by fun_prop) hsc
    have hCU : MapsTo C S U := fun q hq ↦ hcell (subset_closure
      ((actionAngleInv_mem_puncturedCell (hsc hq).1.1 (hsc hq).1.2 _).1))
    have hPhi := ((normalizedChart_memSobolevOn hU (subset_closure.trans hcell) hF ha hab hb hd
      ).comp_planeAffine _ _ hW (isOpen_Ioo.prod isOpen_Ioo)).mono hWS
    have hC1 : MemSobolevOn 1 S (fun q ↦ F (C q)) := by
      convert hPhi using 1
      funext q
      rcases q with ⟨x, s⟩
      change F (actionAngleInv (x, θ + s)) = F (actionAngleInv (x + 0, s + θ))
      rw [add_zero, add_comm θ s]
    have ht := (hC1.hasInteriorChartTrace hab (by norm_num : (-1 / 16 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 16)).1
    exact (ht.ae_hasContinuousSectionGerm (by norm_num) (by norm_num)).and
      (ht.tendsto_physical_square_oscillation hU (by norm_num) (by norm_num) hFU hc hCU
        (fun x hx ↦ normalizedChart_hasFDerivAt_equiv θ (q := (x, 0))
          ⟨ha.trans hx.1, hx.2.trans (hb.trans hd)⟩))
  filter_upwards [hRay, hNorm, ae_restrict_mem measurableSet_Ioo] with h hr hn hh
  refine ⟨hn.1, ?_⟩
  have hp : C (h, 0) ∈ U := by
    change actionAngleInv (h, θ + 0) ∈ U
    exact hcell (subset_closure (actionAngleInv_mem_puncturedCell hh.1 (hh.2.trans hd) _).1)
  exact eq_of_tendsto_physical_square_oscillation hU hFU hp hn.2 (by rwa [hmap h hh])

end NoEmbeddedEigenvalues
