module

public import EulerDipoleEigenvalues.Mixed.BoundarySquare.MixedStaticForm

/-! # Neumann traces and the mixed second-order form -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- The continuous edge value and its derivative are the canonical
traces of the quotient and its tangential weak partial. -/
theorem mixed_quotient_side_traces {ω : L2} (d : MixedQuotientData ω) (j : Fin 2) (σ : Bool) :
    let a₀ := -Real.pi / 2
    let a₁ := Real.pi / 2
    let T := fun a ↦ d.phi (traceSideCoords j (a, cellEdgeNormal σ))
    AbsolutelyContinuousOnInterval T a₀ a₁ ∧
      MemLp (deriv T) 2 (volume.restrict (Ioo a₀ a₁)) ∧
      HasTransverseH1Trace a₀ a₁ a₀ a₁ (cellEdgeNormal σ) (traceSideCoords j) d.phi T ∧
      HasTransverseH1Trace a₀ a₁ a₀ a₁ (cellEdgeNormal σ) (traceSideCoords j)
        (d.jet [j]) (deriv T) := by
  let a₀ := -Real.pi / 2
  let a₁ := Real.pi / 2
  let I := Ioo a₀ a₁
  let b := cellEdgeNormal σ
  let T := fun a ↦ d.phi (traceSideCoords j (a, b))
  have hab : a₀ < a₁ := by dsimp [a₀, a₁]; linarith [Real.pi_pos]
  have hb : b = a₀ ∨ b = a₁ := by cases σ <;> simp [b, a₀, a₁, cellEdgeNormal]
  have hb' : b ∈ Icc a₀ a₁ := by
    rcases hb with h | h
    · rw [h]; exact left_mem_Icc.mpr hab.le
    · rw [h]; exact right_mem_Icc.mpr hab.le
  let D := d.jet
  have hD := d.weakJet
  have hL := d.h2.memLp_weakJet (isOpen_Ioo.prod isOpen_Ioo : IsOpen mixedOpenCell) hD
  have hpre : Prod.swap ⁻¹' (I ×ˢ I) = I ×ˢ I := by
    ext q
    exact and_comm
  have hrect : traceSideCoords j '' (I ×ˢ I) = mixedOpenCell := by
    fin_cases j
    · change id '' (I ×ˢ I) = I ×ˢ I
      rw [image_id]
    · change Prod.swap '' (I ×ˢ I) = I ×ˢ I
      exact (Equiv.prodComm ℝ ℝ).image_eq_preimage_symm (I ×ˢ I) |>.trans hpre
  have hc : Continuous (traceSideCoords j) := by
    fin_cases j
    · exact continuous_id
    · exact continuous_swap
  have hclosed (x y : ℝ) (hx : x ∈ Icc a₀ a₁) (hy : y ∈ Icc a₀ a₁) :
      traceSideCoords j (x, y) ∈ closure mixedOpenCell := by
    rw [mixedOpenCell, closure_prod_eq, closure_Ioo hab.ne]
    fin_cases j
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩
  have hcomp {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict mixedOpenCell)) :
      MemLp (f ∘ traceSideCoords j) 2 (volume.restrict (I ×ˢ I)) := by
    fin_cases j
    · exact hf
    · exact hpre ▸ memLp_comp_swap (measurableSet_Ioo.prod measurableSet_Ioo) hf
  obtain ⟨G, H, R, hG, hH, hGacl, hHacl, _, hHt, hRt, hRac, hRc, _, hRd, hGm, hHm⟩ :=
    hasWeakJetOn_h2_boundary_trace (F := d.phi) (D := D) j hab hab hb
      (hrect.symm ▸ hD) (fun w hw ↦ hrect.symm ▸ hL w hw)
  have hD' : MemLp (D [1 - j] ∘ traceSideCoords j) 2 (volume.restrict (I ×ˢ I)) :=
    hcomp (hL _ (by simp))
  have hGmem : MemLp G 2 (volume.restrict (I ×ˢ I)) := by
    have h : MemLp d.phi 2 (volume.restrict mixedOpenCell) := by
      rw [← hD.1]
      exact hL [] (by decide)
    exact (memLp_congr_ae hG).mpr (hcomp h)
  have hphiC : ∀ a ∈ Icc a₀ a₁,
      ContinuousOn (fun y ↦ d.phi (traceSideCoords j (a, y))) (Icc a₀ a₁) := by
    intro a ha
    exact d.continuous.comp' (f := fun y ↦ traceSideCoords j (a, y))
      (hc.comp (continuous_const.prodMk continuous_id)).continuousOn (fun y hy ↦ hclosed a y ha hy)
  have hGae : ∀ᵐ a ∂volume.restrict I, ∀ᵐ y ∂volume.restrict I,
      G (a, y) = d.phi (traceSideCoords j (a, y)) := by
    refine Measure.ae_ae_of_ae_prod (p := fun z ↦ G z = (d.phi ∘ traceSideCoords j) z) ?_
    rw [Measure.prod_restrict I I]
    exact hG
  have hre : R =ᵐ[volume.restrict I] T := by
    filter_upwards [hRt, hGae, ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo,
      hGacl.ae_hasIntervalH1 hGmem hD'] with a hrt hae ha hline
    have hcont := hphiC a (Ioo_subset_Icc_self ha)
    have he := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
      ((hline.continuousOn_extension hab).mono Ioo_subset_Icc_self |>.congr
        (hline.extension_eq hab).symm) (hcont.mono Ioo_subset_Icc_self)
    rw [hrt]
    unfold aclTrace
    exact (hline.extension_unique hab hcont (fun y hy ↦ (he hy).symm) hb').symm
  have hTc : ContinuousOn T (Icc a₀ a₁) := by
    exact d.continuous.comp' (f := fun a ↦ traceSideCoords j (a, b))
      (hc.comp (continuous_id.prodMk continuous_const)).continuousOn (fun a ha ↦ hclosed a b ha hb')
  have heq : EqOn R T (Icc a₀ a₁) := by
    apply (Measure.eqOn_open_of_ae_eq hre isOpen_Ioo (hRc.mono Ioo_subset_Icc_self)
      (hTc.mono Ioo_subset_Icc_self)).of_subset_closure
    · exact hRc
    · exact hTc
    · exact Ioo_subset_Icc_self
    · rw [closure_Ioo hab.ne]
  have hder : deriv T =ᵐ[volume.restrict I]
      aclTrace a₀ a₁ H (D [1 - j, j] ∘ traceSideCoords j) b := by
    filter_upwards [hRd, ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with a ha hm
    have he : R =ᶠ[𝓝 a] T := by
      filter_upwards [isOpen_Ioo.mem_nhds hm] with y hy using heq (Ioo_subset_Icc_self hy)
    exact (ha.congr_of_eventuallyEq he.symm).deriv
  refine ⟨hRac.congr (fun a ha ↦ heq (by simpa only [uIcc_of_le hab.le] using ha)),
    hHt.ae_eq hder.symm, ?_, ?_⟩
  · exact ⟨hab, hab, hb', G, _, hGm, hG, hGmem, hD', hGacl, hre.symm.trans hRt⟩
  · exact ⟨hab, hab, hb', H, _, hHm, hH, (hcomp (hL [j] (by simp))).ae_eq hH.symm,
      hcomp (hL _ (by simp)), hHacl, hder⟩

/-- The continuous Neumann edge value and its derivative are the canonical
traces of the quotient and its tangential weak partial. -/
theorem mixed_quotient_neumann_traces {ω : L2} (d : MixedQuotientData ω) (σ : Bool) :
    let a₀ := -Real.pi / 2
    let a₁ := Real.pi / 2
    let T := fun a ↦ d.phi (a, cellEdgeNormal σ)
    AbsolutelyContinuousOnInterval T a₀ a₁ ∧
      MemLp (deriv T) 2 (volume.restrict (Ioo a₀ a₁)) ∧
      HasMixedEdgeTrace 1 σ d.phi T ∧ HasMixedEdgeTrace 1 σ (d.jet [0]) (deriv T) :=
  mixed_quotient_side_traces d 0 σ

/-- The continuous Neumann edge value belongs to the bounded-interval H¹ domain. -/
theorem mixed_quotient_edge_h1 {ω : L2} (d : MixedQuotientData ω) (σ : Bool) :
    let a₀ := -Real.pi / 2
    let a₁ := Real.pi / 2
    let T := fun a ↦ d.phi (a, cellEdgeNormal σ)
    AbsolutelyContinuousOnInterval T a₀ a₁ ∧
      MemLp (deriv T) 2 (volume.restrict (Ioo a₀ a₁)) :=
  ⟨(mixed_quotient_neumann_traces d σ).1, (mixed_quotient_neumann_traces d σ).2.1⟩

/-- `C₀ = 1 - div_μ W`, in diagonal coordinates. -/
def mixedC₀ (q : Plane) : ℝ :=
  -mixedFieldCoeff q + 2 * Real.sin q.1 ^ 2 / (Real.cos q.1 * (Real.cos q.1 + Real.cos q.2))

/-- Interior density of the second-order form. -/
def mixedSecondOrderDensity (φ da db : Plane → ℂ) (q : Plane) : ℝ :=
  mixedGradientForm (mixedComparisonDiagonal q) (mixedComparisonOffDiagonal q) (da q) (db q) +
    mixedComparisonPotential q * ‖φ q‖ ^ 2

/-- Full-cell second-order form. The inputs on the Robin sides are canonical
Sobolev traces for H¹ functions; for the continuous quotient use `mixedEdgeValue`. -/
def mixedSecondOrderForm (φ da db : Plane → ℂ) (edge : Bool → ℝ → ℂ) : ℝ :=
  (∫ q in mixedOpenCell, mixedSecondOrderDensity φ da db q) +
  ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖edge σ a‖ ^ 2

/-- Nonnegative fourth-order square, with the ratio totalized at the center. -/
def mixedCompletionDensity (φ : Plane → ℂ) (D : List (Fin 2) → Plane → ℂ) (q : Plane) : ℝ :=
  Real.cos q.1 ^ 2 * mixedFieldCoeff q / 2 *
    ‖mixedWeightedLaplacian D q + (mixedC₀ q / mixedFieldCoeff q : ℝ) • φ q‖ ^ 2

end EulerDipoleEigenvalues
