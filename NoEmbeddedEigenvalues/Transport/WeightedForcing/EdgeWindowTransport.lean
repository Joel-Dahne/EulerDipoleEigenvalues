module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.BoundaryTransportODE
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.DiagonalBoundaryTransport
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ReflectedTraces
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterCellCover

/-!
# Constant modulus on a physical edge window

Blueprint: `def:edge-inward-chart`, `lem:edge-inward-pullback`,
`lem:edge-window-modulus`.

The affine inward normal coordinate puts the chosen boundary at zero.
Tangential velocity is divided out only on compact regular edge intervals.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology

/-- Orientation of the original normal coordinate at an edge. -/
def edgeSideSign (side : Bool) : ℝ := if side then 1 else -1

/-- Affine inward coordinates, retaining the original tangential parameter. -/
def edgeInward (side : Bool) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeAffine (if side then normalReflectionLinear else ContinuousLinearEquiv.refl ℝ _)
    (0, cellEdgeNormal side)

@[simp] theorem edgeInward_apply (side : Bool) (q : ℝ × ℝ) :
    edgeInward side q = (q.1, edgeSideSign side * (Real.pi / 2 - q.2)) := by
  cases side <;> ext <;>
    simp [edgeInward, edgeSideSign, cellEdgeNormal, normalReflectionLinear] <;> ring

theorem measurePreserving_edgeInward (side : Bool) : MeasurePreserving (edgeInward side) := by
  cases side
  · apply measurePreserving_planeAffine
    change |LinearMap.det (LinearMap.id (R := ℝ) (M := ℝ × ℝ))| = 1
    simp
  · exact measurePreserving_normalReflection _

private theorem edgeInward_partial {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F A B : ℝ × ℝ → ℂ} (hA : HasWeakPartialOn U 0 F A) (hB : HasWeakPartialOn U 1 F B)
    (side : Bool) :
    HasWeakPartialOn (edgeInward side ⁻¹' U) 0 (F ∘ edgeInward side) (A ∘ edgeInward side) ∧
    HasWeakPartialOn (edgeInward side ⁻¹' U) 1 (F ∘ edgeInward side)
      (fun q ↦ -(edgeSideSign side : ℂ) * B (edgeInward side q)) := by
  let d : Fin 2 → ℝ × ℝ → ℂ := ![A, B]
  have hd (j : Fin 2) : HasWeakPartialOn U j F (d j) := by
    fin_cases j
    · exact hA
    · exact hB
  have hh (j : Fin 2) := HasWeakPartialOn.comp_planeAffine
    (if side then normalReflectionLinear else ContinuousLinearEquiv.refl ℝ _)
    (0, cellEdgeNormal side) (measurePreserving_edgeInward side) hU hd j
  cases side <;> constructor
  · simpa [edgeInward, d, affineCoeff, axisCoord, planeDirection, Function.comp_def] using hh 0
  · simpa [edgeInward, edgeSideSign, d, affineCoeff, axisCoord, planeDirection] using hh 1
  · simpa [edgeInward, d, affineCoeff, axisCoord, planeDirection, normalReflectionLinear,
      Function.comp_def] using hh 0
  · simpa [edgeInward, edgeSideSign, d, affineCoeff, axisCoord, planeDirection,
      normalReflectionLinear] using hh 1

/-- Canonical left trace for a specified weak normal derivative. -/
theorem HasWeakPartialOn.exists_left_trace {a b w : ℝ} (hab : a < b) (hw : 0 < w)
    {V D : ℝ × ℝ → ℂ} (hD : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 V D)
    (hV : MemLp V 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hL : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w))) :
    ∃ T, HasTransverseH1Trace a b 0 w 0 id V T := by
  obtain ⟨G, hm, he, ha, _, _⟩ := hD.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) hw hV hL
  exact ⟨_, hab, hw, ⟨le_rfl, hw.le⟩, G, D, hm, he, hV.ae_eq he.symm, hL, ha, EventuallyEq.rfl⟩

private theorem memLp_mul_of_continuousOn_compact {Q K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hQ : MeasurableSet Q) (hsub : Q ⊆ K) {χ V : ℝ × ℝ → ℂ}
    (hχ : ContinuousOn χ K) (hV : MemLp V 2 (volume.restrict Q)) :
    MemLp (fun q ↦ χ q * V q) 2 (volume.restrict Q) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hχ
  apply hV.of_le_mul ((hχ.mono hsub).aestronglyMeasurable hQ |>.mul hV.aestronglyMeasurable)
    (c := M)
  filter_upwards [ae_restrict_mem hQ] with q hq
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM q (hsub hq)) (norm_nonneg _)

/-- The weak transport equation restricts to a regular inward edge window,
with the continuous forcing included in the tangential unknown. -/
theorem edge_window_transport {a b w lam σ : ℝ} (hab : a < b) (hw : 0 < w)
    (hs : Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2)) (hσ : σ * σ = 1)
    {F V g A B D : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hV : MemLp V 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (ha : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 0 F A)
    (hb : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 F B)
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 V D)
    (hA : MemLp A 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (he : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)),
      (σ : ℂ) * ((Real.cos q.1 * Real.cos q.2 : ℝ) * A q +
        (Real.sin q.1 * Real.sin q.2 : ℝ) * B q) = Complex.I * (lam * V q))
    (hg : ∀ s ∈ Ioo a b, ContinuousOn (fun u ↦ g (s, u)) (Icc 0 w))
    (heF : F =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)] fun q ↦ V q + g q) :
    ∃ (TV T : ℝ → ℂ), HasTransverseH1Trace a b 0 w 0 id V TV ∧
      (T =ᵐ[volume.restrict (Ioo a b)] fun s ↦ TV s + g (s, 0)) ∧
      HasIntervalH1 a b T (fun s ↦ Complex.I * (↑(σ * lam / Real.cos s) : ℂ) * TV s) := by
  let Q := Ioo a b ×ˢ Ioo 0 w
  let K := Icc a b ×ˢ Icc 0 w
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hQK : Q ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hcos (q : ℝ × ℝ) (hq : q ∈ K) : Real.cos q.1 ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hs hq.1)).ne'
  let α := fun s ↦ σ * lam / Real.cos s
  let χ := fun q : ℝ × ℝ ↦ Complex.I * (α q.1 : ℂ)
  have hχ : ContDiffOn ℝ ∞ χ Q := by
    have hα : ContDiffOn ℝ ∞ α (Ioo a b) := contDiffOn_const.div
      Real.contDiff_cos.contDiffOn fun s hs' ↦ (Real.cos_pos_of_mem_Ioo
        (by simpa only [neg_div] using hs (Ioo_subset_Icc_self hs'))).ne'
    exact contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hα.comp contDiff_fst.contDiffOn fun _ hq ↦ hq.1))
  have hcχ : ContinuousOn χ K := continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_const.div (Real.continuous_cos.comp continuous_fst).continuousOn hcos))
  let R := fun q ↦ χ q * V q
  let DR := fun q ↦ χ q * D q
  have hχ1 : coordPartial 1 χ = 0 := by
    funext q
    simp [χ, coordPartial, partialY]
  have hr : HasWeakPartialOn Q 1 R DR := by
    simpa only [R, DR, hχ1, Pi.zero_apply, zero_mul, zero_add] using hd.mul_contDiffOn hQ hχ
  have hRL : MemLp R 2 (volume.restrict Q) :=
    memLp_mul_of_continuousOn_compact hK hQ.measurableSet hQK hcχ hV
  have hDR : MemLp DR 2 (volume.restrict Q) :=
    memLp_mul_of_continuousOn_compact hK hQ.measurableSet hQK hcχ hD
  let N := fun q : ℝ × ℝ ↦ (-(Real.sin q.1 / Real.cos q.1 * (Real.sin q.2 / q.2) : ℝ) : ℂ) * B q
  have hNL : MemLp N 2 (volume.restrict Q) := by
    let κ := fun q : ℝ × ℝ ↦ ((Real.sin q.1 / Real.cos q.1 : ℝ) : ℂ)
    have hcκ : ContinuousOn κ K := Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_sin.comp continuous_fst).continuousOn.div
        (Real.continuous_cos.comp continuous_fst).continuousOn hcos)
    have hL := memLp_mul_of_continuousOn_compact hK hQ.measurableSet hQK hcκ hB
    apply hL.of_le_mul (c := 1)
    · exact ((Complex.measurable_ofReal.comp
        ((Real.continuous_sin.measurable.comp measurable_snd).div measurable_snd)).neg
        |>.aestronglyMeasurable.mul hL.aestronglyMeasurable).congr
        (Eventually.of_forall fun q ↦ by simp [N, κ, Complex.ofReal_mul]; ring)
    · filter_upwards [ae_restrict_mem hQ.measurableSet] with q hq
      have hx : 0 < q.2 := hq.2.1
      have hle : |Real.sin q.2 / q.2| ≤ 1 := by
        rw [abs_div, abs_of_pos hx, div_le_iff₀ hx, one_mul]
        exact Real.abs_sin_le_abs.trans_eq (abs_of_pos hx)
      simp only [N, κ, Complex.ofReal_mul, norm_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, one_mul]
      calc _ ≤ (|Real.sin q.1 / Real.cos q.1| * 1) * ‖B q‖ := by gcongr
           _ = _ := by ring
  have : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2
    ((measure_mono hQK).trans_lt hK.measure_lt_top).ne
  have hEq : ∀ᵐ q ∂(volume.restrict Q),
      (Real.cos q.2 : ℂ) * A q = R q + (q.2 : ℂ) * N q := by
    filter_upwards [he, ae_restrict_mem hQ.measurableSet] with q hq hqQ
    have hcn : (Real.cos q.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hcos q (hQK hqQ))
    have hun : (q.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqQ.2.1.ne'
    have hσσ : (σ : ℂ) * σ = 1 := by exact_mod_cast hσ
    simp only [R, χ, α, N, Complex.ofReal_div, Complex.ofReal_mul] at hq ⊢
    field_simp [hcn, hun]
    linear_combination (σ : ℂ) * hq -
      ((Real.cos q.1 : ℂ) * Real.cos q.2 * A q +
        (Real.sin q.1 : ℂ) * Real.sin q.2 * B q) * hσσ
  obtain ⟨TF, hTF⟩ := hb.exists_left_trace hab hw hF hB
  obtain ⟨TV, hTV⟩ := hd.exists_left_trace hab hw hV hD
  obtain ⟨TR, hTR⟩ := hr.exists_left_trace hab hw hRL hDR
  obtain ⟨T, hT, hTd⟩ := hTF.boundary_weak_tangent hTR ha hb hr hA
    (hNL.integrable (by norm_num)) hB hDR
    (Complex.continuous_ofReal.comp Real.continuous_cos).continuousAt (by simp) hEq
  have ⟨heTF, heTR⟩ := hTF.boundary_mode_add hTV hTR hg heF EventuallyEq.rfl
  have hD' := hTd.memLp_derivative.ae_eq heTR
  refine ⟨TV, T, hTV, hT.trans heTF, hTd.memLp_value, hD',
    hTd.locally_absolutelyContinuous, ?_⟩
  filter_upwards [hTd.hasDerivAt_ae, (ae_restrict_iff' measurableSet_Ioo).1 heTR] with s hs he hsI
  simpa only [α, he hsI] using hs hsI

/-- A vanishing forcing trace makes the edge equation a pure phase equation. -/
theorem HasIntervalH1.exists_norm_eq_of_zero_forcing {a b : ℝ} {T TV g : ℝ → ℂ} {α : ℝ → ℝ}
    (hab : a < b)
    (hT : HasIntervalH1 a b T (fun s ↦ Complex.I * (α s : ℂ) * TV s))
    (he : T =ᵐ[volume.restrict (Ioo a b)] fun s ↦ TV s + g s)
    (hg : ∀ s ∈ Ioo a b, g s = 0) :
    ∃ z : ℂ, ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖TV s‖ = ‖z‖ := by
  have hm : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hE : T =ᵐ[volume.restrict (Ioo a b)] TV := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    simpa only [hg s hsI, add_zero] using hs
  refine ⟨T ((a + b) / 2), ?_⟩
  filter_upwards [hE, ae_restrict_mem measurableSet_Ioo] with s hs hsI
  rw [← hs]
  exact hT.norm_eq_of_imaginary_derivative
    (hE.mono fun s hs ↦ congrArg (Complex.I * (α s : ℂ) * ·) hs.symm) hsI hm

/-- In a regular inward rectangle a sign-normalized bulk transport equation
and zero continuous forcing trace give a canonical trace of constant modulus. -/
theorem edge_window_modulus {a b w lam σ : ℝ} (hab : a < b) (hw : 0 < w)
    (hs : Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2)) (hσ : σ * σ = 1)
    {F V g A B D : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hV : MemLp V 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (ha : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 0 F A)
    (hb : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 F B)
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo 0 w) 1 V D)
    (hA : MemLp A 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo 0 w)))
    (he : ∀ᵐ q ∂(volume.restrict (Ioo a b ×ˢ Ioo 0 w)),
      (σ : ℂ) * ((Real.cos q.1 * Real.cos q.2 : ℝ) * A q +
        (Real.sin q.1 * Real.sin q.2 : ℝ) * B q) = Complex.I * (lam * V q))
    (hg : ∀ s ∈ Ioo a b, ContinuousOn (fun u ↦ g (s, u)) (Icc 0 w))
    (hg0 : ∀ s ∈ Ioo a b, g (s, 0) = 0)
    (heF : F =ᵐ[volume.restrict (Ioo a b ×ˢ Ioo 0 w)] fun q ↦ V q + g q) :
    ∃ (T : ℝ → ℂ) (z : ℂ), HasTransverseH1Trace a b 0 w 0 id V T ∧
      ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖T s‖ = ‖z‖ := by
  obtain ⟨TV, T, hTV, heT, hT⟩ := edge_window_transport hab hw hs hσ
    hF hV ha hb hd hA hB hD he hg heF
  obtain ⟨z, hz⟩ := hT.exists_norm_eq_of_zero_forcing hab heT hg0
  exact ⟨TV, z, hTV, hz⟩

/-- Inward physical edge chart, with the original tangential parameter. -/
def inwardEdgeChart (j : Fin 2) (side : Bool) : ℝ × ℝ → ℝ × ℝ :=
  diagonalTraceChart j ∘ edgeInward side

theorem continuous_inwardEdgeChart (j : Fin 2) (side : Bool) :
    Continuous (inwardEdgeChart j side) :=
  (continuous_diagonalTraceChart j).comp (edgeInward side).continuous

theorem memLp_comp_inwardEdgeChart {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hU : IsOpen U) (hF : MemLp F 2 (volume.restrict U)) (j : Fin 2) (side : Bool) :
    MemLp (F ∘ inwardEdgeChart j side) 2 (volume.restrict (inwardEdgeChart j side ⁻¹' U)) := by
  have hl : MemLp (F ∘ diagonalTraceChart j) 2
      (volume.restrict (diagonalTraceChart j ⁻¹' U)) := by
    fin_cases j
    · exact memLp_comp_swap (hU.preimage diagInv.continuous).measurableSet
        (memLp_comp_diagInv hU.measurableSet hF)
    · exact memLp_comp_diagInv hU.measurableSet hF
  exact memLp_comp_planeAffine _ _ (measurePreserving_edgeInward side)
    (hU.preimage (continuous_diagonalTraceChart j)).measurableSet hl

theorem MemSobolevOn.comp_inwardEdgeChart {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ}
    (hF : MemSobolevOn 1 U F) (hU : IsOpen U) (j : Fin 2) (side : Bool) :
    MemSobolevOn 1 (inwardEdgeChart j side ⁻¹' U) (F ∘ inwardEdgeChart j side) :=
  (hF.comp_diagonalTraceChart hU j).comp_planeAffine _ _ (measurePreserving_edgeInward side)
    (hU.preimage (continuous_diagonalTraceChart j))

/-- The inward chart has a flat strip of explicitly controlled normal width
in every supplied physical collar. -/
theorem inwardEdgeChart_mem_collar {ε s u : ℝ} (hu : u ∈ Ioo 0 Real.pi) (he : 2 * u < ε)
    (hs : s ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) (j : Fin 2) (side : Bool) :
    inwardEdgeChart j side (s, u) ∈ cellSeparatrixStrip ε := by
  have hs' : |s| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
  have hut : |Real.pi / 2 - u| < Real.pi / 2 :=
    abs_lt.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hs)
  have hupper : 2 * Real.cos s * Real.sin u < ε := by
    calc
      _ ≤ 2 * Real.sin u := by nlinarith [Real.cos_le_one s]
      _ ≤ 2 * u := by linarith [Real.sin_le hu.1.le]
      _ < ε := he
  have ht : |(edgeInward side (s, u)).2| < Real.pi / 2 := by
    cases side <;> simp only [edgeInward_apply, edgeSideSign, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, abs_neg] <;> exact hut
  have htc : Real.cos (edgeInward side (s, u)).2 = Real.sin u := by
    cases side <;> simp only [edgeInward_apply, edgeSideSign, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, Real.cos_neg,
      Real.cos_pi_div_two_sub]
  have htf : (edgeInward side (s, u)).1 = s := by simp
  unfold inwardEdgeChart
  fin_cases j
  · change diagInv ((edgeInward side (s, u)).2, (edgeInward side (s, u)).1) ∈ _
    simp only [cellSeparatrixStrip, mem_ofPred_eq, cellSquare, dipoleLift_eq_diag, diagCoord_diagInv,
      ht, htc, htf, hs', and_self, true_and]
    exact ⟨by positivity, by simpa [mul_comm, mul_left_comm, mul_assoc] using hupper⟩
  · change diagInv (edgeInward side (s, u)) ∈ _
    simp only [cellSeparatrixStrip, mem_ofPred_eq, cellSquare, dipoleLift_eq_diag, diagCoord_diagInv,
      ht, htc, htf, hs', and_self, true_and]
    exact ⟨by positivity, hupper⟩

/-- Restrict the transport pair to a regular inward window, retaining
the continuous stream trace. -/
theorem IsTransportPair.inward_edge_window_transport {lam ε : ℝ}
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) v)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (j : Fin 2) (side : Bool)
    {a b w : ℝ} (hab : a < b) (hw : 0 < w)
    (hs : Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2))
    (hW : Ioo a b ×ˢ Ioo 0 w ⊆ inwardEdgeChart j side ⁻¹' cellSeparatrixStrip ε) :
    ∃ TV T : ℝ → ℂ,
      HasTransverseH1Trace a b 0 w 0 id (v ∘ inwardEdgeChart j side) TV ∧
      (T =ᵐ[volume.restrict (Ioo a b)]
        fun s ↦ TV s + g (diagonalTraceChart j (s, cellEdgeNormal side))) ∧
      HasIntervalH1 a b T (fun s ↦ Complex.I *
        (↑((if j = 0 then 1 else -1) * edgeSideSign side * lam / Real.cos s) : ℂ) * TV s) := by
  let P := cellSeparatrixStrip ε
  let C := inwardEdgeChart j side
  let E := edgeInward side
  let Q := Ioo a b ×ˢ Ioo (0 : ℝ) w
  have hP := isOpen_cellSeparatrixStrip ε
  have hPU : P ⊆ U := fun p hp' ↦ hcell (subset_closure hp'.1)
  have hf : MemSobolevOn 1 P f := MemSobolevOn.mono hp.memSobolevOn.of_succ hPU
  have hF : MemSobolevOn 1 P (fun p ↦ v p + f p) := hv.add hf
  obtain ⟨X, hx, hX⟩ := hF.2 0
  obtain ⟨Y, hy, hY⟩ := hF.2 1
  obtain ⟨A, B, ha, hb, hA, hB, he⟩ :=
    (hp.hasWeakL0On.mono hPU).diagonalTraceChart_partials hP hx hy hX hY j
  have ha' := edgeInward_partial (hP.preimage (continuous_diagonalTraceChart j)) ha hb side
  let A' := A ∘ E
  let B' := fun q ↦ -(edgeSideSign side : ℂ) * B (E q)
  let σ : ℝ := (if j = 0 then 1 else -1) * edgeSideSign side
  have hσ : σ * σ = 1 := by cases side <;> by_cases hj : j = 0 <;> norm_num [σ, edgeSideSign, hj]
  have hr := Measure.restrict_mono_set volume hW
  have hA' : MemLp A' 2 (volume.restrict Q) :=
    (memLp_comp_planeAffine _ _ (measurePreserving_edgeInward side)
      (hP.preimage (continuous_diagonalTraceChart j)).measurableSet hA).mono_measure hr
  have hB' : MemLp B' 2 (volume.restrict Q) :=
    ((memLp_comp_planeAffine _ _ (measurePreserving_edgeInward side)
      (hP.preimage (continuous_diagonalTraceChart j)).measurableSet hB).const_mul
        (-(edgeSideSign side : ℂ))).mono_measure hr
  have he' := ae_mono hr (((measurePreserving_edgeInward side).restrict_preimage
    (hP.preimage (continuous_diagonalTraceChart j)).measurableSet).quasiMeasurePreserving.ae he)
  have hEq : ∀ᵐ q ∂(volume.restrict Q),
      (σ : ℂ) * ((Real.cos q.1 * Real.cos q.2 : ℝ) * A' q +
        (Real.sin q.1 * Real.sin q.2 : ℝ) * B' q) = Complex.I * (lam * v (C q)) := by
    filter_upwards [he'] with q hq
    have ht : Real.sin (E q).2 = edgeSideSign side * Real.cos q.2 := by
      cases side <;> simp only [E, edgeInward_apply, edgeSideSign, Bool.false_eq_true, ite_false, ite_true,
        one_mul, neg_one_mul, Real.sin_neg, Real.sin_pi_div_two_sub]
    have hc : Real.cos (E q).2 = Real.sin q.2 := by
      cases side <;> simp only [E, edgeInward_apply, edgeSideSign, Bool.false_eq_true, ite_false, ite_true,
        one_mul, neg_one_mul, Real.cos_neg, Real.cos_pi_div_two_sub]
    have hs' : (E q).1 = q.1 := by simp [E]
    change (if j = 0 then 1 else -1 : ℂ) *
      ((Real.sin (E q).2 * Real.cos (E q).1 : ℝ) * A (E q) -
        (Real.sin (E q).1 * Real.cos (E q).2 : ℝ) * B (E q)) = _ at hq
    rw [ht, hc, hs'] at hq
    change (σ : ℂ) * (_ * A (E q) + _ * (-(edgeSideSign side : ℂ) * B (E q))) = _
    cases side <;> by_cases hj : j = 0 <;>
      simp only [σ, hj, ite_true, ite_false, edgeSideSign, Bool.false_eq_true, mul_neg,
        mul_one, one_mul, neg_mul, Complex.ofReal_neg, Complex.ofReal_one,
        Complex.ofReal_mul, C, inwardEdgeChart, Function.comp_apply] at hq ⊢ <;>
      linear_combination hq
  have hKU : Icc a b ×ˢ Icc 0 w ⊆ C ⁻¹' U := by
    have hc : closure Q ⊆ C ⁻¹' closure cellSquare :=
      closure_minimal (fun q hq ↦ subset_closure (hW hq).1)
        (isClosed_closure.preimage (continuous_inwardEdgeChart j side))
    dsimp [Q] at hc
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hw.ne] at hc
    exact fun q hq ↦ hcell (hc hq)
  have hg' : ∀ s ∈ Ioo a b, ContinuousOn (fun u ↦ g (C (s,u))) (Icc 0 w) := by
    intro s hsi
    exact hg.comp ((continuous_inwardEdgeChart j side).comp
      (continuous_const.prodMk continuous_id)).continuousOn
      (fun u hu ↦ hKU ⟨Ioo_subset_Icc_self hsi, hu⟩)
  have hEdge (s : ℝ) : C (s, 0) = diagonalTraceChart j (s, cellEdgeNormal side) := by
    change diagonalTraceChart j (E (s, 0)) = _
    congr 1
    cases side <;> simp [E, edgeSideSign, cellEdgeNormal, neg_div]
  have hfg' : (fun q ↦ v (C q) + f (C q)) =ᵐ[volume.restrict Q]
      fun q ↦ v (C q) + g (C q) := by
    have hC : QuasiMeasurePreserving C volume volume :=
      (quasiMeasurePreserving_diagonalTraceChart j).comp
        (measurePreserving_edgeInward side).quasiMeasurePreserving
    exact ((hC.restrict (fun q hq ↦ hPU (hW hq))).ae hfg).mono
      fun q e ↦ congrArg (v (C q) + ·) e
  have hV := (hv.comp_inwardEdgeChart hP j side).mono hW
  obtain ⟨D, hd, hD⟩ := hV.2 1
  obtain ⟨TV, T, hTV, heT, hT⟩ := edge_window_transport hab hw hs hσ
    ((hF.comp_inwardEdgeChart hP j side).1.mono_measure hr) hV.1
    (ha'.1.mono hW) (ha'.2.mono hW) hd hA' hB' hD hEq hg' hfg'
  exact ⟨TV, T, hTV, heT.mono fun s h ↦ by simpa only [hEdge] using h, hT⟩

/-- Every regular inward window contained in the original collar has a
canonical trace with constant modulus, for the original transport pair. -/
theorem IsTransportPair.inward_edge_window_modulus {lam ε : ℝ}
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hcell : closure cellSquare ⊆ U) (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) v)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (j : Fin 2) (side : Bool)
    (hz : ∀ s ∈ Ioo (-Real.pi / 2) (Real.pi / 2),
      g (diagonalTraceChart j (s, cellEdgeNormal side)) = 0)
    {a b w : ℝ} (hab : a < b) (hw : 0 < w)
    (hs : Icc a b ⊆ Ioo (-Real.pi / 2) (Real.pi / 2))
    (hW : Ioo a b ×ˢ Ioo 0 w ⊆ inwardEdgeChart j side ⁻¹' cellSeparatrixStrip ε) :
    ∃ (T : ℝ → ℂ) (z : ℂ),
      HasTransverseH1Trace a b 0 w 0 id (v ∘ inwardEdgeChart j side) T ∧
        ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖T s‖ = ‖z‖ := by
  obtain ⟨TV, T, hTV, heT, hT⟩ :=
    hp.inward_edge_window_transport hcell hv hg hfg j side hab hw hs hW
  obtain ⟨z, hz'⟩ := hT.exists_norm_eq_of_zero_forcing hab heT
    (fun s hs' ↦ hz s (hs (Ioo_subset_Icc_self hs')))
  exact ⟨TV, z, hTV, hz'⟩

end NoEmbeddedEigenvalues
