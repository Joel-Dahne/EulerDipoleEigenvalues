module

public import EulerDipoleEigenvalues.Regularity.SaddleEstimates.OddOddSaddle
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SmoothJetBounds

/-! # The linear saddle jet in either mixed sector

The first vorticity weight is already the forcing weight for exponent two.
The chart is orthonormal: the linear term is in the coordinate reversed by
the odd torus reflection, and the radius and area are physical.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- The parity-permitted linear term in orthonormal saddle coordinates. -/
def mixedAxisLinear (j : Fin 2) (a : ℂ) (q : ℝ × ℝ) : ℂ :=
  a * (axisCoord j q : ℂ)

private theorem contDiff_mixedAxisLinear (j : Fin 2) (a : ℂ) :
    ContDiff ℝ ∞ (mixedAxisLinear j a) := by
  fin_cases j
  · exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)
  · exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)

private theorem mixedAxisLinear_first (i j : Fin 2) (a : ℂ) :
    classicalComplexJet [i] (mixedAxisLinear j a) = fun _ ↦ if i = j then a else 0 := by
  funext q
  fin_cases i <;> fin_cases j
  · simpa [classicalComplexJet, coordPartial, mixedAxisLinear, axisCoord, partialX] using
      ((hasDerivAt_id q.1).ofReal_comp.const_mul a).deriv
  · simp [classicalComplexJet, coordPartial, mixedAxisLinear, axisCoord, partialX]
  · simp [classicalComplexJet, coordPartial, mixedAxisLinear, axisCoord, partialY]
  · simpa [classicalComplexJet, coordPartial, mixedAxisLinear, axisCoord, partialY] using
      ((hasDerivAt_id q.2).ofReal_comp.const_mul a).deriv

private theorem mixedAxisLinear_second (i k j : Fin 2) (a : ℂ) :
    classicalComplexJet [i, k] (mixedAxisLinear j a) = 0 := by
  change coordPartial i (classicalComplexJet [k] (mixedAxisLinear j a)) = 0
  rw [mixedAxisLinear_first]
  by_cases hkj : k = j
  · rw [ite_eq_left hkj]
    exact funext fun q ↦ by fin_cases i <;> simp [coordPartial, partialX, partialY]
  · rw [ite_eq_right hkj]
    exact funext fun q ↦ by fin_cases i <;> simp [coordPartial, partialX, partialY]

private theorem mixed_cylinder_gap_two {ε : Fin 2 → Bool} (hne : ε 0 ≠ ε 1)
    (m : ℕ) (hm : AllowedSaddleDegree ε m) : (2 : ℝ) ≠ (m : ℝ) := by
  intro he
  have hm2 : m = 2 := by exact_mod_cast he.symm
  exact hne (hm.1.mp (hm2 ▸ even_two))

/-- The smooth summand loses its constant and quadratic jets by mixed parity,
and only the derivative in the odd coordinate can be nonzero at order one. -/
private theorem mixed_linear_flat_jet {ρ : ℝ} (hρ : 0 < ρ) {h : ℝ × ℝ → ℂ}
    {ε : Fin 2 → Bool} {j : Fin 2} (hj : ε j = false) (he : ∀ i, i ≠ j → ε i = true)
    (hs : ContDiffOn ℝ ∞ h (localDisk 0 ρ))
    (hp : HasAxisParityOn ε (localDisk 0 ρ) h)
    (hz : ∀ w : List (Fin 2), ¬AllowedSaddleDegree ε w.length → classicalComplexJet w h 0 = 0) :
    ∀ w : List (Fin 2), w.length < 3 →
      classicalComplexJet w (fun q ↦ h q - mixedAxisLinear j (classicalComplexJet [j] h 0) q) 0 =
        0 := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hε : ε 0 ≠ ε 1 := by
    fin_cases j
    · change ε 0 = false at hj
      have h₁ : ε 1 = true := he 1 (by decide)
      rw [hj, h₁]
      decide
    · change ε 1 = false at hj
      have h₀ : ε 0 = true := he 0 (by decide)
      rw [hj, h₀]
      decide
  intro w hw
  rw [classicalComplexJet_sub_on hU hs (contDiff_mixedAxisLinear _ _).contDiffOn w h0]
  rcases w with _ | ⟨i, w⟩
  · have hc := hz [] (fun hdeg ↦ hε (hdeg.1.mp (by decide)))
    simpa [classicalComplexJet, mixedAxisLinear, axisCoord] using hc
  rcases w with _ | ⟨k, w⟩
  · rw [mixedAxisLinear_first]
    by_cases hij : i = j
    · subst i
      simp
    · have hc := hp.classicalJet_at_zero hρ hs [i] i
      simp [he i hij, paritySign] at hc
      simp [hij, show classicalComplexJet [i] h 0 = 0 by linear_combination -hc / 2]
  rcases w with _ | ⟨l, w⟩
  · rw [mixedAxisLinear_second]
    simp only [Pi.zero_apply, sub_zero]
    exact hz [i, k] (fun hdeg ↦ hε (hdeg.1.mp even_two))
  · simp only [List.length_cons] at hw
    omega

private theorem mixed_linear_remainder_mass {ρ : ℝ} (hρ : 0 < ρ) {h : ℝ × ℝ → ℂ}
    {ε : Fin 2 → Bool} {j : Fin 2} (hj : ε j = false) (he : ∀ i, i ≠ j → ε i = true)
    (hs : ContDiffOn ℝ ∞ h (localDisk 0 ρ))
    (hp : HasAxisParityOn ε (localDisk 0 ρ) h)
    (hz : ∀ w : List (Fin 2), ¬AllowedSaddleDegree ε w.length → classicalComplexJet w h 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ localDisk 0 r ⊆ localDisk 0 ρ ∧
      ∃ a : ℂ, ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 2 (localDisk 0 r) (fun q ↦ h q - mixedAxisLinear j a q) D ∧
        ∀ k ≤ 2, RadialJetLp k (3 - k) (localDisk 0 r) 0 D := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  obtain ⟨r, hr, hsub, hD, hm⟩ := exists_radial_classicalJet_flat_memLp hU h0
    (hs.sub (contDiff_mixedAxisLinear j _).contDiffOn) 3
    (mixed_linear_flat_jet hρ hj he hs hp hz)
  exact ⟨r, hr, hsub, _, _, ⟨hD.1, fun w hw i ↦ hD.2 w (by omega) i⟩,
    fun k hk ↦ hm k (by omega)⟩

private theorem mixed_linear_coefficient_unique {ρ : ℝ} (hρ : 0 < ρ)
    {f : ℝ × ℝ → ℂ} {j : Fin 2} {a b : ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) (fun q ↦ f q - mixedAxisLinear j a q) D)
    (hE : HasWeakJetOn 2 (localDisk 0 ρ) (fun q ↦ f q - mixedAxisLinear j b q) E)
    (hDw : RadialJetLp 1 2 (localDisk 0 ρ) 0 D) (hEw : RadialJetLp 1 2 (localDisk 0 ρ) 0 E) :
    a = b := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hG : HasWeakJetOn 2 (localDisk 0 ρ) (mixedAxisLinear j (b - a))
      (fun w q ↦ D w q - E w q) := by
    convert hD.sub hE using 1
    funext q
    unfold mixedAxisLinear
    ring
  have he := hG.ae_eq hU (classicalComplexJet_weak (contDiff_mixedAxisLinear _ _) 2 _) [j]
    (by simp)
  have hw : MemLp (fun q ↦ (b - a) / (localRadius 0 q ^ 2 : ℂ)) 2
      (volume.restrict (localDisk 0 ρ)) := by
    apply ((hDw [j] rfl).sub (hEw [j] rfl)).ae_eq
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hU.measurableSet] with q hq hqU
    have hd := hq hqU
    rw [mixedAxisLinear_first, ite_eq_left rfl] at hd
    simp only [Pi.sub_apply, ← sub_div, hd]
  exact (sub_eq_zero.mp ((memLp_const_div_sq_localRadius_iff 0 hρ _).mp hw)).symm

/-- Mixed saddle jet (`cor:mixed-saddle-jet`). The odd coordinate is
`0` for odd–even, and `1` for even–odd. The three physical weights
are `r⁻³`, `r⁻²` and `r⁻¹`, respectively. -/
theorem mixed_saddle_jet {lam : ℝ} (hlam : lam ≠ 0) {vort : L2}
    (hvort : IsEigenSolution lam vort) {ε : Bool} (hs : InSector ε (!ε) vort) :
    ∀ P ∈ saddleSet, ∃ r : ℝ, 0 < r ∧ ∃! a : ℂ,
      ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 2 (localDisk 0 r)
          (fun q ↦ contStream vort (saddleOrthoChart P q) -
            mixedAxisLinear (if ε then 1 else 0) a q) D ∧
        ∀ k ≤ 2, RadialJetLp k (3 - k) (localDisk 0 r) 0 D := by
  intro P hP
  let e : Fin 2 → Bool := fun j ↦ if j = 0 then ε else !ε
  let j : Fin 2 := if ε then 1 else 0
  have hj : e j = false := by cases ε <;> simp [e, j]
  have he (i : Fin 2) (hi : i ≠ j) : e i = true := by
    cases ε <;> fin_cases i <;> simp_all [e, j]
  have hne : e 0 ≠ e 1 := by cases ε <;> decide
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
  have hfirstR : MemLp (fun p ↦ liftL2 vort p / (Real.rpow (saddleDist p) 1 : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using saddle_first_gain hlam hvort
  have hb : Bornology.IsBounded (localDisk P 1) :=
    Metric.isBounded_ball.subset fun p hp ↦ (dist_le_localRadius P p).trans_lt hp
  have hrad := memLp_div_radius_of_saddleDist (measurable_liftL2 vort) hP
    (by norm_num : (0 : ℝ) ≤ 1) (memLp_saddleDist_of_neighbourhood hfirstR hb)
  have hchart := memLp_comp_planeAffine A P hmpA hU₁.measurableSet hrad
  rw [hpre₁] at hchart
  have hF : MemLp (fun q ↦ liftL2 vort (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) ((2 : ℝ) - 1) : ℂ)) 2 (volume.restrict (localDisk 0 1)) := by
    simpa only [Function.comp_def, A, planeAffine_saddleLinear, localRadius_saddleChart hP,
      show (2 : ℝ) - 1 = 1 by norm_num] using hchart
  have hp : HasAxisParityOn e (localDisk 0 1) (contStream vort ∘ saddleOrthoChart P) := by
    let hm := (measurePreserving_saddleChart hP).quasiMeasurePreserving.ae
      (streamLift_ae_eq_contStream vort)
    intro i
    apply ae_restrict_of_ae
    filter_upwards [saddle_chart_sector_parity hP hs.invLap i, hm,
      (measurePreserving_axisReflect i).quasiMeasurePreserving.ae hm] with q hq h0 h1
    change streamLift vort (saddleOrthoChart P (axisReflect i q)) =
      paritySign (e i) * streamLift vort (saddleOrthoChart P q) at hq
    simpa only [Function.comp_apply, h0, h1] using hq
  obtain ⟨R, C, hR, _, _, u₀, h, E, _, hE, _, _, hw, _, _, hh, hph, hz, hmatch⟩ :=
    cylinder_inverse zero_lt_one (by norm_num : (1 : ℝ) < 2) (mixed_cylinder_gap_two hne)
      (memSobolevOn_contStream_saddleChart vort hP 1) (streamJet2_saddle_weak vort hP 1)
      (ae_restrict_of_ae (streamJet2_saddle_laplacian hvort.1 hP)) hp hF
  obtain ⟨r, hr, hsub, a, G, hG, hGw⟩ := mixed_linear_remainder_mass hR hj he hh.1 hph hz
  have hU : IsOpen (localDisk 0 r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hJ := (streamJet2_saddle_weak vort hP r).sub
    (classicalComplexJet_weak (contDiff_mixedAxisLinear j a) 2 (localDisk 0 r))
  have hsum := (hE.mono hsub).add hG
  have hv : (fun q ↦ contStream vort (saddleOrthoChart P q) - mixedAxisLinear j a q) =ᵐ[
      volume.restrict (localDisk 0 r)] (fun q ↦ u₀ q + (h q - mixedAxisLinear j a q)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hmatch] with q hq
    rw [show contStream vort (saddleOrthoChart P q) = u₀ q + h q from hq]
    ring
  have hident := hJ.ae_eq_of_value_ae hU hsum hv
  have hW (k : ℕ) (hk : k ≤ 2) : RadialJetLp k (3 - k) (localDisk 0 r) 0
      (fun w q ↦ affineJet (saddleLinear P hP) P (streamJet2 vort) w q -
        classicalComplexJet w (mixedAxisLinear j a) q) := by
    have hpow : (2 : ℝ) + 1 - (k : ℝ) = ((3 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show k ≤ 3 by omega)]
      norm_num
    have hm : RadialJetLp k (3 - k) (localDisk 0 r) 0 E := by
      intro w hlen
      have hm := (hw k hk w hlen).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [hpow, Real.rpow_eq_pow, Real.rpow_natCast, Complex.ofReal_pow] using hm
    intro w hlen
    apply (((hm.add (hGw k hk)) w hlen)).ae_eq
    filter_upwards [ae_restrict_of_ae (hident w (by omega)),
      ae_restrict_mem hU.measurableSet] with q hq hqU
    simpa only [Pi.add_apply, ← add_div] using
      congrArg (fun z : ℂ ↦ z / (localRadius 0 q ^ (3 - k) : ℂ)) (hq hqU).symm
  refine ⟨r, hr, a, ⟨_, hJ, hW⟩, ?_⟩
  rintro b ⟨D, hD, hDw⟩
  exact mixed_linear_coefficient_unique hr hD hJ (hDw 1 (by omega)) (hW 1 (by omega))

end EulerDipoleEigenvalues
