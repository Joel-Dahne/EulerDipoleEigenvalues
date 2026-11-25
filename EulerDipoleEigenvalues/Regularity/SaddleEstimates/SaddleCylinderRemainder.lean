module

public import EulerDipoleEigenvalues.Regularity.SaddleEstimates.HarmonicSaddleJets
public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.SaddleStreamCoordinates
public import EulerDipoleEigenvalues.Regularity.SaddleEstimates.SaddleCoefficient

/-!
# The critical cylinder step for the canonical stream

The physical weighted vorticity norm remains an explicit premise. Cylinder
inversion and the finite harmonic Taylor remainder yield the actual remainder
jet, first in normalized coordinates and then in the original Cartesian disk.
Weak uniqueness transfers the bounds to the fixed Fourier stream jet minus the
classical jet of the same normalized quadratic.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- At exponent three, the actual charted stream has a critical weighted
quadratic remainder with its specified Fourier jet. -/
theorem oddOdd_stream_cylinder_quadratic {ω : L2} (hω : MeanZero ω)
    (hs : InSector false false ω) {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hF : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (localRadius 0 q ^ 2 : ℂ)) 2 (volume.restrict (localDisk 0 ρ))) :
    ∃ r : ℝ, 0 < r ∧ r < ρ ∧ ∃ a : ℂ,
      HasWeakJetOn 2 (localDisk 0 r)
        (fun q ↦ contStream ω (saddleOrthoChart P q) - saddleAxisQuadratic a q)
        (fun w q ↦ affineJet (saddleLinear P hP) P (streamJet2 ω) w q -
          classicalComplexJet w (saddleAxisQuadratic a) q) ∧
      ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk 0 r) 0
        (fun w q ↦ affineJet (saddleLinear P hP) P (streamJet2 ω) w q -
          classicalComplexJet w (saddleAxisQuadratic a) q) := by
  have hFr : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) ((3 : ℝ) - 1) : ℂ)) 2
        (volume.restrict (localDisk 0 ρ)) := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_eq_pow,
      Real.rpow_ofNat, Complex.ofReal_pow] using hF
  obtain ⟨ρ₁, C, hρ₁, hρ₁ρ, hC, u₀, h, E, hu, hE, hcu, hbound, hw, hΔ,
    hpu, hh, hph, hz, heq⟩ := oddOdd_stream_cylinder_inverse hω hs hP hρ
      (by norm_num : (1 : ℝ) < 3) oddOdd_cylinder_gap_three hFr
  obtain ⟨r, hr, hrρ, a, hR, hRw⟩ := oddOdd_quadratic_remainder_mass hρ₁ hh.1 hph hz
  have hsub : localDisk 0 r ⊆ localDisk 0 ρ₁ := fun p hp ↦
    show localRadius 0 p < ρ₁ from lt_trans hp hrρ
  have hU : IsOpen (localDisk 0 r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hJ := (streamJet2_saddle_weak ω hP r).sub
    (classicalComplexJet_weak (contDiff_saddleAxisQuadratic a) 2 (localDisk 0 r))
  have hsum := (hE.mono hsub).add hR
  have hv : (fun q ↦ contStream ω (saddleOrthoChart P q) - saddleAxisQuadratic a q) =ᵐ[
      volume.restrict (localDisk 0 r)] (fun q ↦ u₀ q + (h q - saddleAxisQuadratic a q)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heq] with q hq
    rw [hq]
    ring
  have hident := hJ.ae_eq_of_value_ae hU hsum hv
  refine ⟨r, hr, hrρ.trans hρ₁ρ, a, hJ, ?_⟩
  intro k hk
  have he : (3 : ℝ) + 1 - (k : ℝ) = ((4 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show k ≤ 4 by omega)]
    norm_num
  have hm : RadialJetLp k (4 - k) (localDisk 0 r) 0 E := by
    intro w hw'
    have hb := (hw k hk w hw').mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [he, Real.rpow_eq_pow, Real.rpow_natCast, Complex.ofReal_pow] using hb
  have hm' := hm.add (hRw k hk)
  intro w hw'
  apply (hm' w hw').ae_eq
  filter_upwards [ae_restrict_of_ae (hident w (by omega)),
    ae_restrict_mem hU.measurableSet] with q hq hqU
  exact congrArg (fun z : ℂ ↦ z / (localRadius 0 q ^ (4 - k) : ℂ)) (hq hqU).symm

/-- The subcritical cylinder decomposition supplies the actual continuous
stream bound and the three-halves weighted specified first jet. -/
theorem oddOdd_stream_cylinder_subcritical {ω : L2} (hω : MeanZero ω)
    (hs : InSector false false ω) {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hF : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) (1 / 2) : ℂ)) 2
        (volume.restrict (localDisk 0 ρ))) :
    ∃ r C : ℝ, 0 < r ∧ r < ρ ∧ 0 < C ∧
      (∀ q ∈ localDisk 0 r, ‖contStream ω (saddleOrthoChart P q)‖ ≤
        C * Real.rpow (localRadius 0 q) (3 / 2)) ∧
      ∀ j : Fin 2, MemLp (fun q ↦
        affineJet (saddleLinear P hP) P (streamJet2 ω) [j] q /
          (Real.rpow (localRadius 0 q) (3 / 2) : ℂ)) 2 (volume.restrict (localDisk 0 r)) := by
  have hFr : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) ((3 / 2 : ℝ) - 1) : ℂ)) 2
        (volume.restrict (localDisk 0 ρ)) := by
    simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using hF
  obtain ⟨ρ₁, C₁, hρ₁, hρ₁ρ, hC₁, u₀, h, E, hu, hE, hcu, hbound, hw, hΔ,
    hpu, hh, hph, hz, heq⟩ := oddOdd_stream_cylinder_inverse hω hs hP hρ
      (by norm_num : (1 : ℝ) < 3 / 2) (fun m _ ↦ cylinder_gap_three_halves m) hFr
  obtain ⟨r, C₂, hr, hrρ, hC₂, hboundH, hwH⟩ := oddOdd_subcritical_smooth_mass hρ₁ hh.1 hz
  have hsub : localDisk 0 r ⊆ localDisk 0 ρ₁ := fun p hp ↦
    show localRadius 0 p < ρ₁ from lt_trans hp hrρ
  have hU : IsOpen (localDisk 0 r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have heq' := ae_restrict_of_ae_restrict_of_subset hsub heq
  have hc : Continuous (saddleOrthoChart P) := by unfold saddleOrthoChart; fun_prop
  have hevery := Measure.eqOn_open_of_ae_eq heq' hU
    ((continuous_contStream ω).comp hc).continuousOn
    ((hcu.mono hsub).add (hh.1.continuousOn.mono hsub))
  have hJ := streamJet2_saddle_weak ω hP r
  have hsum := (hE.mono hsub).add (classicalComplexJet_weakOn hU (hh.1.mono hsub) 2)
  have hident := hJ.ae_eq_of_value_ae hU hsum heq'
  refine ⟨r, C₁ + C₂, hr, hrρ.trans hρ₁ρ, by positivity, ?_, fun j ↦ ?_⟩
  · intro q hq
    have he := hevery hq
    dsimp only at he
    rw [he]
    calc
      ‖u₀ q + h q‖ ≤ ‖u₀ q‖ + ‖h q‖ := norm_add_le _ _
      _ ≤ C₁ * Real.rpow (localRadius 0 q) (3 / 2) +
          C₂ * Real.rpow (localRadius 0 q) (3 / 2) :=
        add_le_add (hbound q (hsub hq)) (hboundH q hq)
      _ = _ := by ring
  · have hm := (hw 1 (by omega) [j] rfl).mono_measure
      (Measure.restrict_mono hsub le_rfl)
    have hm' : MemLp (fun q ↦ E [j] q / (Real.rpow (localRadius 0 q) (3 / 2) : ℂ)) 2
        (volume.restrict (localDisk 0 r)) := by
      simpa only [show (3 / 2 : ℝ) + 1 - (1 : ℕ) = 3 / 2 by norm_num] using hm
    apply (hm'.add (hwH j)).ae_eq
    filter_upwards [ae_restrict_of_ae (hident [j] (by simp)),
      ae_restrict_mem hU.measurableSet] with q hq hqU
    simpa only [Pi.add_apply, ← add_div, classicalComplexJet] using
      congrArg (fun z : ℂ ↦ z / (Real.rpow (localRadius 0 q) (3 / 2) : ℂ)) (hq hqU).symm

/-- Inverse-chart weak transport and radial mass preserve the same Cartesian
quadratic, including its coefficient and all derivative indices. -/
theorem saddle_quadratic_jet_pushforward {ω : L2} {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    {ρ : ℝ} {a : ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk 0 ρ)
      (fun q ↦ contStream ω (saddleOrthoChart P q) - saddleAxisQuadratic a q) D)
    (hw : ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk 0 ρ) 0 D) :
    ∃ G : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 (localDisk P ρ) (fun p ↦ contStream ω p - saddleQuadratic P a p) G ∧
      ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk P ρ) P G := by
  let A := saddleLinear P hP
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
    apply MeasurePreserving.symm (planeAffine A P).toMeasurableEquiv
    change MeasurePreserving (planeAffine A P)
    simpa only [A, planeAffine_saddleLinear] using measurePreserving_saddleChart hP
  have hr (p : ℝ × ℝ) : localRadius 0 (planeAffine A.symm b p) = localRadius P p := by
    have he := localRadius_saddleChart hP (planeAffine A.symm b p)
    rw [hinv] at he
    exact he.symm
  have hpre : planeAffine A.symm b ⁻¹' localDisk 0 ρ = localDisk P ρ := by
    ext p
    change localRadius 0 (planeAffine A.symm b p) < ρ ↔ localRadius P p < ρ
    rw [hr]
  have hfun : (fun q ↦ contStream ω (saddleOrthoChart P q) - saddleAxisQuadratic a q) ∘
      planeAffine A.symm b = (fun p ↦ contStream ω p - saddleQuadratic P a p) := by
    funext p
    dsimp only [Function.comp_apply]
    rw [hinv]
    have he := saddleQuadratic_comp_chart hP a (planeAffine A.symm b p)
    rw [hinv] at he
    exact congrArg (fun z : ℂ ↦ contStream ω p - z) he.symm
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hd := hD.comp_planeAffine A.symm b hmp hU
  rw [hpre, hfun] at hd
  refine ⟨affineJet A.symm b D, hd, fun k hk ↦ ?_⟩
  simpa only [hpre] using (hw k hk).comp_planeAffine A.symm b hmp hU.measurableSet hr

/-- Supplying the physical vorticity weight produces the original unique
saddle coefficient and weighted remainder jet on a smaller physical disk. -/
theorem oddOdd_saddle_jet_of_radial_vorticity {ω : L2} (hω : MeanZero ω)
    (hs : InSector false false ω) {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hF : MemLp (fun p ↦ liftL2 ω p / (localRadius P p ^ 2 : ℂ)) 2
      (volume.restrict (localDisk P ρ))) :
    ∃ r : ℝ, 0 < r ∧ r < ρ ∧ ∃! a : ℂ,
      ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 2 (localDisk P r) (fun p ↦ contStream ω p - saddleQuadratic P a p) D ∧
        ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk P r) P D := by
  have hU : IsOpen (localDisk P ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hmp : MeasurePreserving (planeAffine (saddleLinear P hP) P) := by
    simpa only [planeAffine_saddleLinear] using measurePreserving_saddleChart hP
  have hpre : planeAffine (saddleLinear P hP) P ⁻¹' localDisk P ρ = localDisk 0 ρ := by
    ext q
    change localRadius P (planeAffine (saddleLinear P hP) P q) < ρ ↔ localRadius 0 q < ρ
    rw [planeAffine_saddleLinear, localRadius_saddleChart hP]
  have he := memLp_comp_planeAffine (saddleLinear P hP) P hmp hU.measurableSet hF
  rw [hpre] at he
  have hchart : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (localRadius 0 q ^ 2 : ℂ)) 2 (volume.restrict (localDisk 0 ρ)) := by
    simpa only [Function.comp_def, planeAffine_saddleLinear,
      localRadius_saddleChart hP] using he
  obtain ⟨r, hr, hrρ, a, hd, hw⟩ := oddOdd_stream_cylinder_quadratic hω hs hP hρ hchart
  obtain ⟨G, hG, hGw⟩ := saddle_quadratic_jet_pushforward hP hd hw
  refine ⟨r, hr, hrρ, ?_⟩
  apply (existsUnique_saddle_coefficient_iff hP hr).mpr
  have hV : IsOpen (localDisk P r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (saddleQuadratic P a) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (((contDiff_snd.sub contDiff_const).pow 2).sub
        ((contDiff_fst.sub contDiff_const).pow 2)))
  have hJ := (streamJet2_weak ω (localDisk P r)).sub
    (classicalComplexJet_weak hQ 2 (localDisk P r))
  refine ⟨a, _, hJ, fun k hk w hw' ↦ ?_⟩
  apply (hGw k hk w hw').ae_eq
  filter_upwards [ae_restrict_of_ae (hJ.ae_eq hV hG w (by omega)),
    ae_restrict_mem hV.measurableSet] with p hp hpU
  exact congrArg (fun z : ℂ ↦ z / (localRadius P p ^ (4 - k) : ℂ)) (hp hpU).symm

end EulerDipoleEigenvalues
