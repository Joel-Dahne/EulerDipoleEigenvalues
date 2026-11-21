module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.EdgeWindowTransport
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.BoundaryTraceCompare
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.BoundaryConeTrace
public import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.SaddleTaylorJet

/-!
# Whole-edge modulus and critical corner mass

Blueprint: `lem:common-edge-modulus`, `def:edge-corner-shift`,
`lem:edge-corner-distance`, `lem:edge-corner-mode-exclusion`.

Any two compact regular intervals are contained in a larger regular interval.
Trace uniqueness thus identifies one modulus, which the corner norm excludes.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- One modulus works on all windows in a flat inward strip. -/
theorem common_edge_window_modulus {w : ℝ} {V : ℝ × ℝ → ℂ}
    (hw : 0 < w)
    (h : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
      ∃ (T : ℝ → ℂ) (z : ℂ), HasTransverseH1Trace a b 0 w 0 id V T ∧
        ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖T s‖ = ‖z‖) :
    ∃ z : ℂ, ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
      ∃ T : ℝ → ℂ, HasTransverseH1Trace a b 0 w 0 id V T ∧
        ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖T s‖ = ‖z‖ := by
  have hπ := Real.pi_pos
  let x := -Real.pi / 4
  let y := Real.pi / 4
  have hxy : x < y := by dsimp [x,y]; linarith
  have hx : -Real.pi / 2 < x := by dsimp [x]; linarith
  have hy : y < Real.pi / 2 := by dsimp [y]; linarith
  obtain ⟨T₀,z,hT₀,hz⟩ := h x y hxy (Icc_subset_Ioo hx hy)
  refine ⟨z, ?_⟩
  intro a b hab hs
  have ha := (hs (left_mem_Icc.mpr hab.le)).1
  have hb := (hs (right_mem_Icc.mpr hab.le)).2
  let l := min a x
  let r := max b y
  have hlr : l < r := (min_le_left _ _).trans_lt (hab.trans_le (le_max_left _ _))
  obtain ⟨S,c,hS,hc⟩ := h l r hlr (Icc_subset_Ioo (lt_min ha hx) (max_lt hb hy))
  obtain ⟨T,d,hT, _⟩ := h a b hab hs
  have cmp {p q : ℝ} {A : ℝ → ℂ} (hA : HasTransverseH1Trace p q 0 w 0 id V A)
      (hsub : Ioo p q ⊆ Ioo l r) : A =ᵐ[volume.restrict (Ioo p q)] S :=
    hA.ae_eq_inward hS hw le_rfl hsub (fun _ hu ↦ hu) (MeasurePreserving.id volume)
      (MeasurePreserving.id volume) continuous_id rfl (fun _ _ _ _ ↦ rfl)
  have hsub : Ioo x y ⊆ Ioo l r := Ioo_subset_Ioo (min_le_right _ _) (le_max_right _ _)
  have hc0 : ‖c‖ = ‖z‖ := by
    have hne : (volume.restrict (Ioo x y)) ≠ 0 := by
      intro hzero
      have hvol := Measure.restrict_eq_zero.mp hzero
      rw [Real.volume_Ioo] at hvol
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)).ne' hvol
    have : (ae (volume.restrict (Ioo x y))).NeBot := ae_neBot.mpr hne
    have hEq : ∀ᵐ s ∂(volume.restrict (Ioo x y)), ‖c‖ = ‖z‖ := by
      filter_upwards [cmp hT₀ hsub, ae_restrict_of_ae_restrict_of_subset hsub hc, hz]
        with s he hcs hzs
      exact hcs.symm.trans (he ▸ hzs)
    exact hEq.exists.choose_spec
  have hsub' : Ioo a b ⊆ Ioo l r := Ioo_subset_Ioo (min_le_left _ _) (le_max_left _ _)
  refine ⟨T, hT, ?_⟩
  filter_upwards [cmp hT hsub', ae_restrict_of_ae_restrict_of_subset hsub' hc] with s hsT hcs
  rw [hsT, hcs, hc0]

/-- Shift the left saddle to the origin of the inward chart. -/
def edgeCornerShift : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeAffine (ContinuousLinearEquiv.refl ℝ _) (-Real.pi / 2, 0)

@[simp] theorem edgeCornerShift_apply (q : ℝ × ℝ) :
    edgeCornerShift q = (q.1 - Real.pi / 2, q.2) := by
  ext <;> simp [edgeCornerShift, sub_eq_add_neg, neg_div]

theorem measurePreserving_edgeCornerShift : MeasurePreserving edgeCornerShift := by
  apply measurePreserving_planeAffine
  change |LinearMap.det (LinearMap.id (R := ℝ) (M := ℝ × ℝ))| = 1
  simp

private theorem inwardEdge_left_corner_mem_saddle (j : Fin 2) (side : Bool) :
    inwardEdgeChart j side (-Real.pi / 2, 0) ∈ saddleSet := by
  have hn : -Real.pi / 2 = -(Real.pi / 2) := neg_div _ _
  fin_cases j <;> cases side
  · refine ⟨-1, 0, by decide, ?_⟩
    simp [inwardEdgeChart, diagonalTraceChart, edgeSideSign, hn] <;> ring
  · refine ⟨0, 1, by decide, ?_⟩
    simp [inwardEdgeChart, diagonalTraceChart, edgeSideSign, hn]
  · refine ⟨-1, 0, by decide, ?_⟩
    simp [inwardEdgeChart, diagonalTraceChart, edgeSideSign, hn] <;> ring
  · refine ⟨0, -1, by decide, ?_⟩
    simp [inwardEdgeChart, diagonalTraceChart, edgeSideSign, hn] <;> ring

/-- On the shifted Cartesian cone, the original saddle distance is at most
three times the tangential distance to the endpoint. -/
theorem saddleDist_inwardEdge_corner_le {r u : ℝ} (hu : u ∈ Ioo 0 r)
    (j : Fin 2) (side : Bool) :
    saddleDist (inwardEdgeChart j side (edgeCornerShift (r,u))) ≤ 3*r := by
  have hc := inwardEdge_left_corner_mem_saddle j side
  apply (Metric.infDist_le_dist_of_mem hc).trans
  have hr : 0 < r := hu.1.trans hu.2
  fin_cases j <;> cases side <;>
    simp [inwardEdgeChart, diagonalTraceChart, edgeSideSign, Prod.dist_eq, Real.dist_eq,
      abs_le] <;> exact ⟨⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩,
      ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩⟩

/-- The original area-weighted norm and H¹ norm exclude the common mode
on every regular window of this edge. -/
theorem inward_edge_common_modulus_eq_zero {ε w : ℝ} (hw : 0 < w)
    (hwε : 2 * w ≤ ε) (hwπ : w < Real.pi) {v : ℝ × ℝ → ℂ} (j : Fin 2) (side : Bool)
    (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) v)
    (hL : MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2 (volume.restrict (cellSeparatrixStrip ε)))
    {z : ℂ}
    (h : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
      ∃ T : ℝ → ℂ, HasTransverseH1Trace a b 0 w 0 id (v ∘ inwardEdgeChart j side) T ∧
        ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖T s‖ = ‖z‖) : z = 0 := by
  let C := inwardEdgeChart j side
  let P := cellSeparatrixStrip ε
  let V := v ∘ C
  let W := V ∘ edgeCornerShift
  let Q := cartesianHalfCone w
  have hP := isOpen_cellSeparatrixStrip ε
  have hCP := hP.preimage (continuous_inwardEdgeChart j side)
  have hsub : Q ⊆ edgeCornerShift ⁻¹' C ⁻¹' P := by
    intro q hq
    change C (edgeCornerShift q) ∈ P
    rw [edgeCornerShift_apply]
    apply inwardEdgeChart_mem_collar ⟨hq.2.1, hq.2.2.trans (hq.1.2.trans hwπ)⟩
    · linarith [hq.2.2, hq.1.2]
    · exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
  have hWW : MemSobolevOn 1 Q W := ((hv.comp_inwardEdgeChart hP j side).comp_planeAffine _ _
    measurePreserving_edgeCornerShift hCP).mono hsub
  obtain ⟨D, hd, hD⟩ := hWW.2 1
  have hm := (memLp_comp_planeAffine _ _ measurePreserving_edgeCornerShift hCP.measurableSet
    (memLp_comp_inwardEdgeChart hP hL j side)).mono_measure (Measure.restrict_mono_set _ hsub)
  have hqm : MeasurableSet Q := (measurable_fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst))
  have hWeight : MemLp (fun q ↦ W q / (q.1 : ℂ)) 2 (volume.restrict Q) := by
    have hCq : QuasiMeasurePreserving C volume volume :=
      (quasiMeasurePreserving_diagonalTraceChart j).comp
        (measurePreserving_edgeInward side).quasiMeasurePreserving
    have hne := (hCq.comp measurePreserving_edgeCornerShift.quasiMeasurePreserving).ae
      ae_saddleDist_ne_zero
    have hmeas : AEStronglyMeasurable (fun q ↦ W q / (q.1 : ℂ)) (volume.restrict Q) := by
      have hm' := hWW.1.aestronglyMeasurable.mul
        ((Complex.measurable_ofReal.comp measurable_fst).inv.aestronglyMeasurable)
      exact hm'.congr (Eventually.of_forall fun q ↦
        (div_eq_mul_inv (W q) (q.1 : ℂ)).symm)
    apply hm.of_le_mul hmeas (c := 3)
    filter_upwards [ae_restrict_mem hqm, ae_mono Measure.restrict_le_self hne] with q hq hn
    change ‖W q / (q.1 : ℂ)‖ ≤ 3 * ‖W q / (saddleDist (C (edgeCornerShift q)) : ℂ)‖
    have hs : 0 < saddleDist (C (edgeCornerShift q)) := lt_of_le_of_ne Metric.infDist_nonneg hn.symm
    have hle := saddleDist_inwardEdge_corner_le hq.2 j side
    rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hq.1.1, abs_of_pos hs]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hs).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hq.1.1).2
    nlinarith [mul_le_mul_of_nonneg_left hle (norm_nonneg (W q))]
  apply constant_modulus_boundary_trace_eq_zero hw hd hWeight hD
  intro a ha haR
  have hb : Ioo a (2*a) ×ˢ Ioo 0 a ⊆ Q := fun q hq ↦
    ⟨⟨ha.trans hq.1.1, hq.1.2.trans_le haR⟩, hq.2.1, hq.2.2.trans hq.1.1⟩
  have hab : a < 2*a := by linarith
  have hsub' : Icc (a - Real.pi / 2) (2*a - Real.pi / 2) ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) :=
    Icc_subset_Ioo (by linarith) (by linarith)
  obtain ⟨S,hS,hz⟩ := h (a - Real.pi / 2) (2*a - Real.pi / 2) (sub_lt_sub_right hab _) hsub'
  have hBW := hWW.mono hb
  obtain ⟨T,hT⟩ := (hd.mono hb).exists_left_trace hab ha hBW.1
    (hD.mono_measure (Measure.restrict_mono_set _ hb))
  have hk : MapsTo (fun s : ℝ ↦ s + -(Real.pi / 2)) (Ioo a (2*a))
      (Ioo (a - Real.pi / 2) (2*a - Real.pi / 2)) := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hkm := measurePreserving_add_right volume (-(Real.pi / 2))
  have haw : a ≤ w := by linarith
  have heq := hT.ae_eq_inward hS ha le_rfl hk
    (fun _ hu ↦ Ioo_subset_Ioo_right haw hu) hkm (MeasurePreserving.id volume)
    continuous_id rfl (fun s _ u _ ↦ by simp [W, V, C, sub_eq_add_neg])
  refine ⟨T,hT,?_⟩
  filter_upwards [heq, (hkm.quasiMeasurePreserving.restrict hk).ae hz] with s he hs
  rw [he]
  exact hs

end NoEmbeddedEigenvalues
