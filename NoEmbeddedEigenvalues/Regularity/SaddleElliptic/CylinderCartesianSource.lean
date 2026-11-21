import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderCartesianJet
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier

/-!
# Real-angle weak calculus for the Cartesian cylinder coefficients

Only smooth scalar coefficients are differentiated classically. Each weak
cylinder entry is retained with its specified outer derivative, so the time
derivative of the first angular entry and the angular derivative of the first
time entry are not identified.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff

private theorem angularUnit_lift (θ : ℝ) :
    _root_.fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi)) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [_root_.fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem cylinderRadialFrame_lift (i : Fin 2) (q : ℝ × ℝ) :
    cylinderLift (cylinderRadialFrame i) q =
      if i = 0 then (Real.cos q.2 : ℂ) else (Real.sin q.2 : ℂ) := by
  simp only [cylinderLift, Function.comp_apply, cylinderRadialFrame, logCylinderProjection,
    angularUnit_lift, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem cylinderAngularFrame_lift (i : Fin 2) (q : ℝ × ℝ) :
    cylinderLift (cylinderAngularFrame i) q =
      if i = 0 then -(Real.sin q.2 : ℂ) else (Real.cos q.2 : ℂ) := by
  simp only [cylinderLift, Function.comp_apply, cylinderAngularFrame, logCylinderProjection,
    angularUnit_lift, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem contDiff_cylinderRadialFrame_lift (i : Fin 2) :
    ContDiff ℝ ∞ (cylinderLift (cylinderRadialFrame i)) := by
  simp only [show cylinderLift (cylinderRadialFrame i) = _ from
    funext (cylinderRadialFrame_lift i)]
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp contDiff_snd.cos
  · exact Complex.ofRealCLM.contDiff.comp contDiff_snd.sin

theorem contDiff_cylinderAngularFrame_lift (i : Fin 2) :
    ContDiff ℝ ∞ (cylinderLift (cylinderAngularFrame i)) := by
  simp only [show cylinderLift (cylinderAngularFrame i) = _ from
    funext (cylinderAngularFrame_lift i)]
  split_ifs
  · exact (Complex.ofRealCLM.contDiff.comp contDiff_snd.sin).neg
  · exact Complex.ofRealCLM.contDiff.comp contDiff_snd.cos

theorem coordPartial_cylinderRadialFrame_lift (i j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j (cylinderLift (cylinderRadialFrame i)) q =
      if j = 0 then 0 else cylinderLift (cylinderAngularFrame i) q := by
  fin_cases j
  · by_cases hi : i = 0 <;>
      simp [coordPartial, partialX, cylinderRadialFrame_lift, hi]
  · by_cases hi : i = 0
    · simpa [coordPartial, partialY, cylinderRadialFrame_lift,
        cylinderAngularFrame_lift, hi] using (Real.hasDerivAt_cos q.2).ofReal_comp.deriv
    · simpa [coordPartial, partialY, cylinderRadialFrame_lift,
        cylinderAngularFrame_lift, hi] using (Real.hasDerivAt_sin q.2).ofReal_comp.deriv

theorem coordPartial_cylinderAngularFrame_lift (i j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j (cylinderLift (cylinderAngularFrame i)) q =
      if j = 0 then 0 else -cylinderLift (cylinderRadialFrame i) q := by
  fin_cases j
  · by_cases hi : i = 0 <;>
      simp [coordPartial, partialX, cylinderAngularFrame_lift, hi]
  · by_cases hi : i = 0
    · simpa [coordPartial, partialY, cylinderRadialFrame_lift,
        cylinderAngularFrame_lift, hi] using (Real.hasDerivAt_sin q.2).ofReal_comp.neg.deriv
    · simpa [coordPartial, partialY, cylinderRadialFrame_lift,
        cylinderAngularFrame_lift, hi] using (Real.hasDerivAt_cos q.2).ofReal_comp.deriv

/-- The homogeneous radial factor on the real-angle source plane. -/
def cylinderSourceWeight (a : ℝ) (q : ℝ × ℝ) : ℂ := Real.exp (-a * q.1)

@[fun_prop]
theorem contDiff_cylinderSourceWeight (a : ℝ) :
    ContDiff ℝ ∞ (cylinderSourceWeight a) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst).exp

theorem coordPartial_cylinderSourceWeight (a : ℝ) (j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j (cylinderSourceWeight a) q =
      if j = 0 then (-a : ℂ) * cylinderSourceWeight a q else 0 := by
  fin_cases j
  · simpa [coordPartial, partialX, cylinderSourceWeight, mul_comm] using
      (((hasDerivAt_id q.1).const_mul (-a)).exp.ofReal_comp).deriv
  · simp [coordPartial, partialY, cylinderSourceWeight]

theorem cylinderSourceWeight_pred (a : ℝ) (q : ℝ × ℝ) :
    (Real.exp (-q.1) : ℂ) * cylinderSourceWeight (a - 1) q = cylinderSourceWeight a q := by
  unfold cylinderSourceWeight
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Homogeneity multiplication of a supplied weak cylinder derivative. -/
theorem cylinderSourceWeight_hasWeakPartial {K D : ℝ × AddCircle (2 * Real.pi) → ℂ}
    (h : HasWeakPartialOn univ j (cylinderLift K) (cylinderLift D)) (a : ℝ) :
    HasWeakPartialOn univ j (fun q ↦ cylinderSourceWeight a q * cylinderLift K q)
      (fun q ↦ cylinderSourceWeight a q *
        (cylinderLift D q - if j = 0 then (a : ℂ) * cylinderLift K q else 0)) := by
  have hs := h.mul_contDiffOn isOpen_univ (contDiff_cylinderSourceWeight a).contDiffOn
  refine hs.congr_ae_on MeasurableSet.univ (Eventually.of_forall fun _ _ ↦ rfl)
    (Eventually.of_forall fun q _ ↦ ?_)
  rw [coordPartial_cylinderSourceWeight]
  split_ifs <;> ring

/-- The first coefficient has the prescribed time and angular weak derivatives. -/
theorem cylinderCartesianFirst_hasWeakPartial {a : ℝ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : ∀ w, w.length < 2 → ∀ j,
      HasWeakPartialOn univ j (cylinderLift (J w)) (cylinderLift (J (j :: w))))
    (i j : Fin 2) :
    HasWeakPartialOn univ j (cylinderLift (cylinderCartesianFirst a J i))
      (if j = 0 then cylinderLift (cylinderCartesianFirst a (fun w ↦ J (0 :: w)) i)
       else cylinderLift (cylinderCartesianFirstAngle a J i)) := by
  have hU := ((hJ [] (by simp) j).const_mul (a : ℂ)).add
    ((hJ [0] (by simp) j).const_mul (-1))
  have hV := hJ [1] (by simp) j
  have hs := (hU.mul_contDiffOn isOpen_univ
    (contDiff_cylinderRadialFrame_lift i).contDiffOn).add
      (hV.mul_contDiffOn isOpen_univ (contDiff_cylinderAngularFrame_lift i).contDiffOn)
  refine hs.congr_ae_on MeasurableSet.univ (Eventually.of_forall fun q _ ↦ ?_)
    (Eventually.of_forall fun q _ ↦ ?_)
  · dsimp only [cylinderLift, Function.comp_apply, cylinderCartesianFirst]
    ring
  · rw [coordPartial_cylinderRadialFrame_lift, coordPartial_cylinderAngularFrame_lift]
    fin_cases j <;>
      (simp [cylinderLift, cylinderCartesianFirst, cylinderCartesianFirstAngle]; ring_nf)
    all_goals simp

end NoEmbeddedEigenvalues
