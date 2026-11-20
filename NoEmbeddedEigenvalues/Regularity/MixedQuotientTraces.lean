import NoEmbeddedEigenvalues.Regularity.MixedStreamDivision
import NoEmbeddedEigenvalues.MixedStaticForm
import NoEmbeddedEigenvalues.Analysis.BoundaryTraceCompare
import NoEmbeddedEigenvalues.TraceWindowRestriction

/-! # Zero normal traces of the mixed quotient -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
local notation "π" => Real.pi
local notation "Plane" => ℝ × ℝ

/-- The raw stream quotient is even about every side of the diagonal cell.
Here real-valued cosines and complex division are used on the entire plane. -/
theorem mixed_raw_quotient_reflect {ω : L2} (hs : InSector false true ω)
    (j : Fin 2) (σ : Bool) (q : Plane) :
    let Q := fun p : Plane ↦ contStream ω (diagInv p) / (Real.cos p.1 : ℂ)
    Q (axisTraceChart j (normalReflection (2 * cellEdgeNormal σ) q)) =
      Q (axisTraceChart j q) := by
  have hψ := contStream_diagonalTraceChart_character hs j σ q
  have hχ (x : ℝ) : Real.cos (2 * cellEdgeNormal σ - x) = -Real.cos x := by
    cases σ
    · rw [show 2 * cellEdgeNormal false - x = -(π - -x) by simp [cellEdgeNormal]; ring]
      rw [Real.cos_neg, Real.cos_pi_sub, Real.cos_neg]
    · rw [show 2 * cellEdgeNormal true = π by simp [cellEdgeNormal]; ring, Real.cos_pi_sub]
  fin_cases j
  · have h : contStream ω (diagInv (2 * cellEdgeNormal σ - q.2, q.1)) =
        -contStream ω (diagInv (q.2, q.1)) := by
      simpa [diagonalTraceChart, paritySign] using hψ
    simp only [axisTraceChart, normalReflection_apply,
      show (⟨0, by decide⟩ : Fin 2) = 0 by decide, ite_true]
    change contStream ω (diagInv (2 * cellEdgeNormal σ - q.2, q.1)) /
        (Real.cos (2 * cellEdgeNormal σ - q.2) : ℂ) =
      contStream ω (diagInv (q.2, q.1)) / (Real.cos q.2 : ℂ)
    rw [h, hχ, Complex.ofReal_neg, neg_div_neg_eq]
  · have h : contStream ω (diagInv (q.1, 2 * cellEdgeNormal σ - q.2)) =
        contStream ω (diagInv q) := by
      simpa [diagonalTraceChart, paritySign] using hψ
    simp only [axisTraceChart, normalReflection_apply,
      show (⟨1, by decide⟩ : Fin 2) ≠ 0 by decide, ite_false]
    change contStream ω (diagInv (q.1, 2 * cellEdgeNormal σ - q.2)) /
        (Real.cos q.1 : ℂ) = contStream ω (diagInv q) / (Real.cos q.1 : ℂ)
    rw [h]


/-- A symmetric transverse window through the edge identifies a canonical
normal derivative trace with its negative. -/
private theorem trace_eq_zero_of_even {l r t δ : ℝ} {f d T : Plane → ℂ} {S : ℝ → ℂ}
    (h : ∀ j, HasWeakPartialOn (Ioo l r ×ˢ Ioo (t - δ) (t + δ)) j f
      (if j = 0 then d else T))
    (hT : HasTransverseH1Trace l r (t - δ) (t + δ) t id T S)
    (he : (f ∘ normalReflection (2 * t)) =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo (t - δ) (t + δ))] f) :
    (fun _ ↦ (0 : ℂ)) =ᵐ[volume.restrict (Ioo l r)] S := by
  let W := Ioo l r ×ˢ Ioo (t - δ) (t + δ)
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_Ioo
  have ha : 2 * t - (t + δ) = t - δ := by ring
  have hb : 2 * t - (t - δ) = t + δ := by ring
  have ht : 2 * t - t = t := by ring
  have hpre : normalReflection (2 * t) ⁻¹' W = W := by
    rw [show W = Ioo l r ×ˢ Ioo (t - δ) (t + δ) from rfl,
      normalReflection_preimage_rectangle, ha, hb]
  have hR := HasWeakPartialOn.comp_planeAffine normalReflectionLinear (0, 2 * t)
    (measurePreserving_normalReflection (2 * t)) hW h 1
  change HasWeakPartialOn (normalReflection (2 * t) ⁻¹' W) 1
    (f ∘ normalReflection (2 * t)) _ at hR
  rw [hpre] at hR
  have hR' : HasWeakPartialOn W 1 f (fun q ↦ -T (normalReflection (2 * t) q)) := by
    have h := hR.congr_ae_on hW.measurableSet ((ae_restrict_iff' hW.measurableSet).mp he)
      (Eventually.of_forall fun _ _ ↦ rfl)
    simpa [normalReflection, affineCoeff, normalReflectionLinear, axisCoord, planeDirection] using h
  have hTd : HasWeakPartialOn W 1 f T := by simpa using h 1
  have hE := (ae_restrict_iff' hW.measurableSet).mpr (hTd.ae_eq hW hR')
  have hTr : HasTransverseH1Trace l r (2 * t - (t + δ)) (2 * t - (t - δ)) (2 * t - t) id T S := by
    rw [ha, hb, ht]; exact hT
  have hE' : (T ∘ id) =ᵐ[volume.restrict
      (Ioo l r ×ˢ Ioo (2 * t - (t + δ)) (2 * t - (t - δ)))]
      fun q ↦ (-1 : ℂ) * T (id (normalReflection (2 * t) q)) := by
    rw [ha, hb]
    filter_upwards [hE] with q hq
    exact hq.trans (neg_one_mul _).symm
  filter_upwards [hT.ae_eq_reflected hTr hE'] with s hs
  exact (CharZero.eq_neg_self_iff.mp (by simpa only [neg_one_mul] using hs)).symm

/-- An H² extension of the quotient, with its specified jet, yields the
zero normal traces on the *whole* cell rectangles in `MixedQuotientData`. -/
theorem mixed_quotient_normal_zero {ω : L2} (hs : InSector false true ω)
    {φ : Plane → ℂ} {D : List (Fin 2) → Plane → ℂ}
    (hφ : MemSobolevOn 2 (Ioo (-(3 * π / 4)) (3 * π / 4) ×ˢ
      Ioo (-(3 * π / 4)) (3 * π / 4)) φ)
    (hD : HasWeakJetOn 2 (Ioo (-(3 * π / 4)) (3 * π / 4) ×ˢ
      Ioo (-(3 * π / 4)) (3 * π / 4)) φ D)
    (he : (fun q ↦ contStream ω (diagInv q) / (Real.cos q.1 : ℂ)) =ᵐ[volume.restrict
      (Ioo (-(3 * π / 4)) (3 * π / 4) ×ˢ Ioo (-(3 * π / 4)) (3 * π / 4))] φ)
    (j : Fin 2) (σ : Bool) : HasMixedEdgeTrace j σ (D [j]) (fun _ ↦ 0) := by
  let a := -π / 2
  let b := π / 2
  let δ := π / 4
  let x := -(3 * π / 4)
  let y := 3 * π / 4
  let t := cellEdgeNormal σ
  let I := Ioo a b
  let J := Ioo x y
  let K := J ×ˢ J
  let C := axisTraceChart j
  let H := I ×ˢ J
  let W := I ×ˢ Ioo (t - δ) (t + δ)
  let G := D [j] ∘ C
  have hπ := Real.pi_pos
  have hab : a < b := by dsimp [a, b]; linarith
  have hxy : x < y := by dsimp [x, y]; linarith
  have hax : x ≤ a := by dsimp [x, a]; linarith
  have hby : b ≤ y := by dsimp [b, y]; linarith
  have ht : t ∈ Icc a b := by cases σ <;> simp [t, a, b, cellEdgeNormal, hab.le]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw₁ : x ≤ t - δ := by dsimp [x, δ, t, cellEdgeNormal]; split <;> linarith
  have hw₂ : t + δ ≤ y := by dsimp [y, δ, t, cellEdgeNormal]; split <;> linarith
  have hK : IsOpen K := isOpen_Ioo.prod isOpen_Ioo
  have hHK : H ⊆ K := prod_mono (Ioo_subset_Ioo hax hby) Subset.rfl
  have hWH : W ⊆ H := prod_mono Subset.rfl (Ioo_subset_Ioo hw₁ hw₂)
  have hCK : C ⁻¹' K = K := by
    ext p
    fin_cases j <;> simp [C, axisTraceChart, K, and_comm]
  have hCm : MeasurePreserving C := by
    fin_cases j
    · change MeasurePreserving (Prod.swap : Plane → Plane)
      rw [Measure.volume_eq_prod]
      exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id volume
  have hF' (k : Fin 2) : HasWeakPartialOn K k (φ ∘ C)
      (D [if j = 0 then (if k = 0 then 1 else 0) else k] ∘ C) := by
    have hh (i : Fin 2) : HasWeakPartialOn K i φ (D [i]) := by
      simpa only [hD.1] using hD.2 [] (by decide) i
    fin_cases j <;> fin_cases k
    · have h := (hh 1).comp_swap hK
      change HasWeakPartialOn (C ⁻¹' K) 0 _ _ at h
      rw [hCK] at h
      exact h
    · have h := (hh 0).comp_swap hK
      change HasWeakPartialOn (C ⁻¹' K) 1 _ _ at h
      rw [hCK] at h
      exact h
    · exact hh 0
    · exact hh 1
  have hG' : HasWeakPartialOn K 1 G (D [j, j] ∘ C) := by
    have hh (i : Fin 2) : HasWeakPartialOn K i (D [j]) (D [i, j]) :=
      hD.2 [j] (by simp) i
    fin_cases j
    · have h := (hh 0).comp_swap hK
      change HasWeakPartialOn (C ⁻¹' K) 1 _ _ at h
      rw [hCK] at h
      exact h
    · exact hh 1
  have hnorm (w : List (Fin 2)) (hw : w.length ≤ 2) :
      MemLp (D w ∘ C) 2 (volume.restrict H) := by
    have h := (hφ.memLp_weakJet hK hD w hw).comp_measurePreserving
      (hCm.restrict_preimage hK.measurableSet)
    rw [hCK] at h
    exact h.mono_measure (Measure.restrict_mono hHK le_rfl)
  obtain ⟨S, hS⟩ := (hG'.mono hHK).exists_transverse_trace hab hxy
    (Icc_subset_Icc hax hby ht) (hnorm [j] (by simp)) (hnorm [j, j] (by simp))
  have hS₁ := hS.restrict_normal hax hby hab ht
  have hS₂ := hS.restrict_normal hw₁ hw₂ (by linarith) (show t ∈ Icc (t - δ) (t + δ) from
    ⟨by linarith, by linarith⟩)
  have hc := (hCm.restrict_preimage hK.measurableSet).quasiMeasurePreserving.ae_eq_comp he
  rw [hCK] at hc
  have hcW := ae_restrict_of_ae_restrict_of_subset (hWH.trans hHK) hc
  have hmaps : MapsTo (normalReflection (2 * t)) W W := by
    intro q hq
    rw [normalReflection_apply]
    exact ⟨hq.1, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩⟩
  have hRe := ((measurePreserving_normalReflection (2 * t)).quasiMeasurePreserving.restrict hmaps
    ).ae_eq_comp hcW
  have heven : ((φ ∘ C) ∘ normalReflection (2 * t)) =ᵐ[volume.restrict W] (φ ∘ C) := by
    filter_upwards [hRe, hcW] with q h₁ h₂
    exact h₁.symm.trans ((mixed_raw_quotient_reflect hs j σ q).trans h₂)
  have hDnormal : HasWeakPartialOn W 1 (φ ∘ C) G := by
    have h : (if j = 0 then (if (1 : Fin 2) = 0 then 1 else 0) else 1) = j := by
      fin_cases j <;> decide
    simpa only [G, h] using (hF' 1).mono (hWH.trans hHK)
  have hDtan := (hF' 0).mono (hWH.trans hHK)
  have h0 := trace_eq_zero_of_even (T := G)
    (fun k ↦ by
      fin_cases k
      · exact hDtan
      · exact hDnormal) hS₂ heven
  exact (hS₁.congr_trace h0).congr_ae_pullback (Eventually.of_forall fun _ ↦ rfl)

end NoEmbeddedEigenvalues
