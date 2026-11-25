module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.DiagonalSobolev
public import EulerDipoleEigenvalues.Mixed.Conclusion.SecondOrderCoercivity

/-! # The weak equation after division by the odd-side defining function -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter
open scoped ContDiff

private def mixedCos (q : ℝ × ℝ) : ℂ := Real.cos q.1

private theorem smooth_mixedCos : ContDiff ℝ ∞ mixedCos := by
  exact Complex.ofRealCLM.contDiff.comp (by fun_prop :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ Real.cos q.1))

private theorem mixedCos_partial (j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j mixedCos q = if j = 0 then -(Real.sin q.1 : ℂ) else 0 := by
  fin_cases j
  · change partialX mixedCos q = _
    have h : HasDerivAt (fun t : ℝ ↦ (Real.cos t : ℂ)) (-(Real.sin q.1 : ℂ)) q.1 := by
      simpa only [Complex.ofReal_neg] using (Real.hasDerivAt_cos q.1).ofReal_comp
    simpa [partialX, mixedCos] using h.deriv
  · change partialY mixedCos q = 0
    simp [partialY, mixedCos]

private theorem mixedCos_partial_two (j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j (coordPartial j mixedCos) q = if j = 0 then -mixedCos q else 0 := by
  have h := funext (mixedCos_partial j)
  rw [h]
  fin_cases j
  · change partialX (fun p : ℝ × ℝ ↦ -(Real.sin p.1 : ℂ)) q = -mixedCos q
    simpa [partialX, mixedCos] using ((Real.hasDerivAt_sin q.1).ofReal_comp.neg).deriv
  · change partialY (fun _ : ℝ × ℝ ↦ (0 : ℂ)) q = 0
    simp [partialY]

/-- The gradient of the specified quotient recovers the Fourier-defined
stream gradient almost everywhere on the diagonal cell. -/
theorem MixedQuotientData.stream_partials_ae {ζ : L2} (d : MixedQuotientData ζ) :
    ∀ᵐ q ∂volume.restrict mixedOpenCell,
      d.streamA q = streamLiftX ζ (diagInv q) + streamLiftY ζ (diagInv q) ∧
      d.streamB q = streamLiftX ζ (diagInv q) - streamLiftY ζ (diagInv q) := by
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hpre : diagInv ⁻¹' cellSquare = mixedOpenCell := by
    ext q
    simp only [mixedOpenCell, cellSquare, mem_preimage, mem_ofPred_eq, diagCoord_diagInv,
      mem_prod, mem_Ioo, abs_lt, neg_div]
  have hx := hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ζ 0) cellSquare
  have hy := hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ζ 1) cellSquare
  have ha := hx.comp_diagInv_fst isOpen_cellSquare hy
  have hb := hx.comp_diagInv_snd isOpen_cellSquare hy
  rw [hpre] at ha hb
  have he : (liftL2 (invLap ζ) ∘ diagInv) =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ mixedCos q * d.phi q := d.stream_eq
  have hw (j : Fin 2) : HasWeakPartialOn mixedOpenCell j d.phi (d.jet [j]) := by
    simpa only [d.weakJet.1] using d.weakJet.2 [] (by decide) j
  have hprod (j : Fin 2) :=
    (hw j).mul_smooth hU smooth_mixedCos
  have ha' : HasWeakPartialOn mixedOpenCell 0 (fun q ↦ mixedCos q * d.phi q) d.streamA := by
    change HasWeakPartialOn _ _ _ (fun q ↦ (Real.cos q.1 : ℂ) * d.jet [0] q -
      (Real.sin q.1 : ℂ) * d.phi q)
    simpa only [mixedCos_partial, ite_true, mixedCos, neg_mul, add_comm, sub_eq_add_neg]
      using hprod 0
  have hb' : HasWeakPartialOn mixedOpenCell 1 (fun q ↦ mixedCos q * d.phi q) d.streamB := by
    change HasWeakPartialOn _ _ _ (fun q ↦ (Real.cos q.1 : ℂ) * d.jet [1] q)
    simpa only [mixedCos_partial, one_ne_zero, ite_false, zero_mul, zero_add, mixedCos]
      using hprod 1
  have hv := (ae_restrict_iff' hU.measurableSet).1 he
  have ea := ha'.ae_eq hU (ha.congr_ae_on hU.measurableSet hv (.of_forall fun _ _ ↦ rfl))
  have eb := hb'.ae_eq hU (hb.congr_ae_on hU.measurableSet hv (.of_forall fun _ _ ↦ rfl))
  exact (ae_restrict_iff' hU.measurableSet).2
    (ea.mp (eb.mono fun _ hy hx hq ↦ ⟨hx hq, hy hq⟩))

/-- Once the stream factorization is known for an H² quotient, its specified
weak jet satisfies the divided diagonal Poisson equation. -/
theorem mixed_divided_equation {ζ : L2} (hζ : MeanZero ζ)
    {φ : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 mixedOpenCell φ D)
    (he : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
      liftL2 (invLap ζ) (diagInv q) = (Real.cos q.1 : ℂ) * φ q) :
    ∀ᵐ q ∂(volume.restrict mixedOpenCell),
      mixedWeightedLaplacian D q = 2 * (liftL2 ζ (diagInv q) / (Real.cos q.1 : ℂ)) + φ q := by
  let U := mixedOpenCell
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let E (w : List (Fin 2)) (q : ℝ × ℝ) : ℂ := match w with
    | [] => mixedCos q * φ q
    | [j] => coordPartial j mixedCos q * φ q + mixedCos q * D [j] q
    | i :: j :: _ =>
      (coordPartial i (coordPartial j mixedCos) q * φ q +
        coordPartial j mixedCos q * D [i] q) +
      (coordPartial i mixedCos q * D [j] q + mixedCos q * D [i, j] q)
  have hd (i : Fin 2) : HasWeakPartialOn U i φ (D [i]) := by
    simpa only [hD.1] using hD.2 [] (by decide) i
  have hE : HasWeakJetOn 2 U (fun q ↦ mixedCos q * φ q) E := by
    refine ⟨rfl, fun w hw i ↦ ?_⟩
    rcases w with _ | ⟨j, w⟩
    · exact (hd i).mul_smooth hU smooth_mixedCos
    cases w with
    | nil =>
      exact ((hd i).mul_smooth hU (contDiff_coordPartial_top j smooth_mixedCos)).add
        ((hD.2 [j] (by simp) i).mul_smooth hU smooth_mixedCos)
    | cons k w => simp at hw
  obtain ⟨J, hJ, hΔ⟩ := contStream_diagInv_weak_poisson hζ U
  have hs := ae_restrict_of_ae (s := U)
    (quasiMeasurePreserving_diagInv.ae (streamLift_ae_eq_contStream ζ))
  have he' : (contStream ζ ∘ diagInv) =ᵐ[volume.restrict U] fun q ↦ mixedCos q * φ q := by
    filter_upwards [hs, he] with q hq h
    exact hq.symm.trans h
  have hjet := hJ.ae_eq_of_value_ae hU hE he'
  filter_upwards [hΔ, (ae_restrict_iff' hU.measurableSet).mpr (hjet [0, 0] (by decide)),
    (ae_restrict_iff' hU.measurableSet).mpr (hjet [1, 1] (by decide)),
    ae_restrict_mem hU.measurableSet] with q hΔ h0 h1 hq
  rw [h0, h1] at hΔ
  have hn : (Real.cos q.1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1)).ne'
  simp only [E, mixedCos_partial_two, mixedCos_partial, ite_true, one_ne_zero, ite_false,
    mixedCos, zero_mul, zero_add, add_zero] at hΔ
  unfold mixedWeightedLaplacian
  rw [Complex.real_smul, Real.tan_eq_sin_div_cos]
  rw [Complex.ofReal_mul, Complex.ofReal_div]
  norm_num only [Complex.ofReal_ofNat]
  field_simp [hn]
  linear_combination hΔ

end EulerDipoleEigenvalues
