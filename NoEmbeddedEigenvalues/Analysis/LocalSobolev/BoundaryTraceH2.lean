module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.BoundaryTransportODE
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets

/-! # Tangential differentiation of the one-sided H² trace -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology

/-- The rectangle coordinates with the tangential coordinate listed first. -/
def traceSideCoords (j : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then p else p.swap

/-- On either side normal to coordinate `1 - j`, the canonical L² traces of an H²
function and its tangential weak partial are represented by an absolutely continuous
function on the closed side and its a.e. derivative, respectively. The interior
function need not have a pointwise representative on the side. -/
theorem hasWeakJetOn_h2_boundary_trace (j : Fin 2) {a₀ a₁ b₀ b₁ t : ℝ}
    (ha : a₀ < a₁) (hb : b₀ < b₁) (ht : t = b₀ ∨ t = b₁)
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (traceSideCoords j '' (Ioo a₀ a₁ ×ˢ Ioo b₀ b₁)) F D)
    (hL : ∀ w, w.length ≤ 2 →
      MemLp (D w) 2 (volume.restrict (traceSideCoords j '' (Ioo a₀ a₁ ×ˢ Ioo b₀ b₁)))) :
    ∃ G H : ℝ × ℝ → ℂ, ∃ T : ℝ → ℂ,
      let I := Ioo a₀ a₁
      let J := Ioo b₀ b₁
      let E := D [1 - j] ∘ traceSideCoords j
      let E' := D [1 - j, j] ∘ traceSideCoords j
      G =ᵐ[volume.restrict (I ×ˢ J)] (F ∘ traceSideCoords j) ∧
      H =ᵐ[volume.restrict (I ×ˢ J)] (D [j] ∘ traceSideCoords j) ∧
      HasACLSectionsOn I J G E ∧ HasACLSectionsOn I J H E' ∧
      MemLp (aclTrace b₀ b₁ G E t) 2 (volume.restrict I) ∧
      MemLp (aclTrace b₀ b₁ H E' t) 2 (volume.restrict I) ∧
      T =ᵐ[volume.restrict I] aclTrace b₀ b₁ G E t ∧
      AbsolutelyContinuousOnInterval T a₀ a₁ ∧
      ContinuousOn T (Icc a₀ a₁) ∧
      (∃ M : ℝ, ∀ a ∈ Icc a₀ a₁, ‖T a‖ ≤ M) ∧
      (∀ᵐ a ∂volume.restrict I, HasDerivAt T (aclTrace b₀ b₁ H E' t a) a) ∧
      Measurable G ∧ Measurable H := by
  let I := Ioo a₀ a₁
  let J := Ioo b₀ b₁
  let Q := I ×ˢ J
  let C := traceSideCoords j
  let E := D [1 - j] ∘ C
  let A := D [j] ∘ C
  let B := D [1 - j, j] ∘ C
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hs : Function.Involutive (Prod.swap : ℝ × ℝ → ℝ × ℝ) := Prod.swap_swap
  have he : Prod.swap ⁻¹' (Prod.swap '' Q) = Q := hs.injective.preimage_image Q
  have hU : IsOpen (C '' Q) := by
    fin_cases j
    · change IsOpen (id '' Q)
      simpa using hQ
    · change IsOpen (Prod.swap '' Q)
      exact (Homeomorph.prodComm ℝ ℝ).isOpenMap _ hQ
  have hpart {k : Fin 2} {f g : ℝ × ℝ → ℂ}
      (h : HasWeakPartialOn (C '' Q) k f g) :
      HasWeakPartialOn Q (if j = 0 then k else 1 - k) (f ∘ C) (g ∘ C) := by
    fin_cases j
    · change HasWeakPartialOn (id '' Q) k f g at h
      change HasWeakPartialOn Q k f g
      simpa using h
    · change HasWeakPartialOn Q (1 - k) (f ∘ Prod.swap) (g ∘ Prod.swap)
      have hh := h.comp_swap hU
      change HasWeakPartialOn (Prod.swap ⁻¹' (Prod.swap '' Q)) (1 - k)
        (f ∘ Prod.swap) (g ∘ Prod.swap) at hh
      simpa only [he] using hh
  have hmem {f : ℝ × ℝ → ℂ} (h : MemLp f 2 (volume.restrict (C '' Q))) :
      MemLp (f ∘ C) 2 (volume.restrict Q) := by
    fin_cases j
    · change MemLp f 2 (volume.restrict (id '' Q)) at h
      change MemLp f 2 (volume.restrict Q)
      simpa using h
    · change MemLp (f ∘ Prod.swap) 2 (volume.restrict Q)
      have hh := memLp_comp_swap hU.measurableSet h
      change MemLp (f ∘ Prod.swap) 2 (volume.restrict (Prod.swap ⁻¹' (Prod.swap '' Q))) at hh
      simpa only [he] using hh
  have hp0 : HasWeakPartialOn Q 0 (F ∘ C) A := by
    have h := hpart (hD.2 [] (by decide) j)
    rw [hD.1] at h
    fin_cases j <;> exact h
  have hp1 : HasWeakPartialOn Q 1 (F ∘ C) E := by
    have h := hpart (hD.2 [] (by decide) (1 - j))
    rw [hD.1] at h
    fin_cases j <;> exact h
  have hpB : HasWeakPartialOn Q 1 A B := by
    have h := hpart (hD.2 [j] (by simp) (1 - j))
    fin_cases j <;> exact h
  have hF := hmem (hD.1 ▸ hL [] (by decide))
  have hE : MemLp E 2 (volume.restrict Q) := hmem (hL [1 - j] (by simp))
  have hA : MemLp A 2 (volume.restrict Q) := hmem (hL [j] (by simp))
  have hB : MemLp B 2 (volume.restrict Q) := hmem (hL [1 - j, j] (by simp))
  obtain ⟨G, hGm, hGF, hG⟩ := hp1.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 ha) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
  obtain ⟨H, hHm, hHA, hH⟩ := hpB.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 ha) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
  have hGL := hF.ae_eq hGF.symm
  have hHL := hA.ae_eq hHA.symm
  have ht' : t ∈ Icc b₀ b₁ := by
    rcases ht with rfl | rfl
    · exact left_mem_Icc.mpr hb.le
    · exact right_mem_Icc.mpr hb.le
  obtain ⟨T, hT, hTac, hTd⟩ := hG.trace_weak_tangent ha hb ht' hp0 hH hGm hHm hGL hHL
    hE hB hGF hHA
  have hTc : ContinuousOn T (Icc a₀ a₁) := by
    simpa only [uIcc_of_le ha.le] using hTac.continuousOn
  exact ⟨G, H, T, hGF, hHA, hG, hH, (hG.l2_trace hb hGm hGL hE t ht').1,
    (hH.l2_trace hb hHm hHL hB t ht').1, hT, hTac, hTc,
    isCompact_Icc.exists_bound_of_continuousOn hTc, hTd, hGm, hHm⟩

end NoEmbeddedEigenvalues
