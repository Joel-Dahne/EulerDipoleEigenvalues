import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleBootstrapMass
import NoEmbeddedEigenvalues.Regularity.SaddleEstimates.SaddleCylinderRemainder

/-!
# Physical subcritical stream estimates from the first vorticity weight

The first lattice-weighted norm is localized before cylinder inversion. The
inverse orthogonal affine frame transports actual weak first derivatives,
then uniqueness identifies them with the fixed Fourier derivatives. No
ordinary vorticity H¹ or downstream saddle remainder is used.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The first vorticity gain supplies the subcritical cylinder input at every
lifted saddle, and its output retains the physical specified Fourier gradient. -/
theorem oddOdd_saddle_subcritical_of_first_weight {ω : L2} (hω : MeanZero ω)
    (hs : InSector false false ω)
    (hfirst : MemLp (fun p ↦ liftL2 ω p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood)) :
    ∀ P ∈ saddleSet, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      (∀ p ∈ localDisk P r, ‖contStream ω p‖ ≤ C * Real.rpow (localRadius P p) (3 / 2)) ∧
      ∀ j : Fin 2, MemLp (fun p ↦ liftL2 (streamPartial j ω) p /
        (Real.rpow (localRadius P p) (3 / 2) : ℂ)) 2 (volume.restrict (localDisk P r)) := by
  intro P hP
  let A := saddleLinear P hP
  have hmpA : MeasurePreserving (planeAffine A P) := by
    simpa only [A, planeAffine_saddleLinear] using measurePreserving_saddleChart hP
  have hU₁ : IsOpen (localDisk P 1) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hpre₁ : planeAffine A P ⁻¹' localDisk P 1 = localDisk 0 1 := by
    ext q
    change localRadius P (planeAffine A P q) < 1 ↔ localRadius 0 q < 1
    rw [planeAffine_saddleLinear, localRadius_saddleChart hP]
  have hfirstR : MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) 1 : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using hfirst
  have hb : Bornology.IsBounded (localDisk P 1) :=
    Metric.isBounded_ball.subset fun p hp ↦ (dist_le_localRadius P p).trans_lt hp
  have hrad := memLp_div_radius_of_saddleDist (measurable_liftL2 ω) hP
    (by norm_num : (0 : ℝ) ≤ 1) (memLp_saddleDist_of_neighbourhood hfirstR hb)
  have hrad' : MemLp (fun p ↦ liftL2 ω p / (localRadius P p ^ 1 : ℂ)) 2
      (volume.restrict (localDisk P 1)) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one, pow_one, Complex.ofReal_pow] using hrad
  have hhalf := memLp_div_localRadius_rpow (m := 1) (t := 1 / 2) (by norm_num) hrad'
  have hchart := memLp_comp_planeAffine A P hmpA hU₁.measurableSet hhalf
  rw [hpre₁] at hchart
  have hchart' : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) (1 / 2) : ℂ)) 2 (volume.restrict (localDisk 0 1)) := by
    simpa only [Function.comp_def, A, planeAffine_saddleLinear,
      localRadius_saddleChart hP] using hchart
  obtain ⟨r, C, hr, hr1, hC, hv, hg⟩ :=
    oddOdd_stream_cylinder_subcritical hω hs hP zero_lt_one hchart'
  let b := -A.symm P
  have hinv (p : ℝ × ℝ) : saddleOrthoChart P (planeAffine A.symm b p) = p := by
    rw [← planeAffine_saddleLinear P hP]
    change A (A.symm p + -A.symm P) + P = p
    simp only [map_add, map_neg, A.apply_symm_apply, neg_add_cancel_right]
  have hmp : MeasurePreserving (planeAffine A.symm b) := by
    have heq : (planeAffine A.symm b : (ℝ × ℝ) → ℝ × ℝ) = (planeAffine A P).symm := by
      funext p
      change A.symm p + -A.symm P = A.symm (p - P)
      simpa only [sub_eq_add_neg] using (A.symm.map_sub p P).symm
    rw [heq]
    exact MeasurePreserving.symm (planeAffine A P).toMeasurableEquiv hmpA
  have hrad (p : ℝ × ℝ) : localRadius 0 (planeAffine A.symm b p) = localRadius P p := by
    have he := localRadius_saddleChart hP (planeAffine A.symm b p)
    rw [hinv] at he
    exact he.symm
  have hpre : planeAffine A.symm b ⁻¹' localDisk 0 r = localDisk P r := by
    ext p
    change localRadius 0 (planeAffine A.symm b p) < r ↔ localRadius P p < r
    rw [hrad]
  have hU : IsOpen (localDisk 0 r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hV : IsOpen (localDisk P r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  let E := affineJet A P (streamJet2 ω)
  have hE : HasWeakJetOn 2 (localDisk 0 r) (contStream ω ∘ saddleOrthoChart P) E :=
    streamJet2_saddle_weak ω hP r
  have hback := hE.comp_planeAffine A.symm b hmp hU
  have hfun : (contStream ω ∘ saddleOrthoChart P) ∘ planeAffine A.symm b = contStream ω := by
    funext p
    exact congrArg (contStream ω) (hinv p)
  rw [hpre, hfun] at hback
  have hident := (streamJet2_weak ω (localDisk P r)).ae_eq hV hback
  have hmass (i : Fin 2) : MemLp (fun p ↦ E [i] (planeAffine A.symm b p) /
      (Real.rpow (localRadius P p) (3 / 2) : ℂ)) 2 (volume.restrict (localDisk P r)) := by
    have hm := memLp_comp_planeAffine A.symm b hmp hU.measurableSet (hg i)
    rw [hpre] at hm
    simpa only [Function.comp_def, hrad, E, A] using hm
  refine ⟨r, C, hr, hC, ?_, fun j ↦ ?_⟩
  · intro p hp
    have hq : planeAffine A.symm b p ∈ localDisk 0 r := by
      change localRadius 0 (planeAffine A.symm b p) < r
      rw [hrad]
      exact hp
    have hh := hv _ hq
    rw [hinv, hrad] at hh
    exact hh
  · apply (((hmass 0).const_mul (affineCoeff A.symm 0 j)).add
      ((hmass 1).const_mul (affineCoeff A.symm 1 j))).ae_eq
    filter_upwards [ae_restrict_of_ae (hident [j] (by simp)),
      ae_restrict_mem hV.measurableSet] with p hp hpV
    have he : liftL2 (streamPartial j ω) p =
        affineCoeff A.symm 0 j * E [0] (planeAffine A.symm b p) +
        affineCoeff A.symm 1 j * E [1] (planeAffine A.symm b p) := by
      simpa only [streamJet2, affineJet, Function.comp_apply] using hp hpV
    dsimp only [Pi.add_apply]
    rw [he]
    ring

end NoEmbeddedEigenvalues
