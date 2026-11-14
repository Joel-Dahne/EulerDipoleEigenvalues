import NoEmbeddedEigenvalues.Analysis.CylinderPhysicalL2
import NoEmbeddedEigenvalues.Regularity.CylinderWeak

/-!
# Ordered Cartesian cylinder-jet candidates

These explicit entries preserve both mixed cylinder entries separately. Joint
L² of the cylinder jet gives genuine weighted physical norms. The trace of the
second candidates equals the conjugated cylinder operator algebraically, before
any weak derivative identification. Neither norms nor this equation assert a
weak Cartesian jet.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The radial Cartesian frame coefficient, as a real-valued complex number. -/
def cylinderRadialFrame (i : Fin 2) (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  if i = 0 then (_root_.fourier 1 q.2).re else (_root_.fourier 1 q.2).im

/-- The positively oriented angular Cartesian frame coefficient. -/
def cylinderAngularFrame (i : Fin 2) (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  if i = 0 then -((_root_.fourier 1 q.2).im : ℂ) else (_root_.fourier 1 q.2).re

private theorem norm_angular_unit (q : ℝ × AddCircle (2 * Real.pi)) :
    ‖_root_.fourier 1 q.2‖ = 1 := by simp [_root_.fourier_apply]

theorem cylinderRadialFrame_memLp (i : Fin 2) :
    MemLp (cylinderRadialFrame i) ⊤ logCylinderMeasure := by
  apply memLp_top_of_bound (by unfold cylinderRadialFrame; split_ifs <;> fun_prop) 1
  apply Filter.Eventually.of_forall
  intro q
  unfold cylinderRadialFrame
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs, norm_angular_unit] using
      Complex.abs_re_le_norm (_root_.fourier 1 q.2)
  · simpa only [Complex.norm_real, Real.norm_eq_abs, norm_angular_unit] using
      Complex.abs_im_le_norm (_root_.fourier 1 q.2)

theorem cylinderAngularFrame_memLp (i : Fin 2) :
    MemLp (cylinderAngularFrame i) ⊤ logCylinderMeasure := by
  apply memLp_top_of_bound (by unfold cylinderAngularFrame; split_ifs <;> fun_prop) 1
  apply Filter.Eventually.of_forall
  intro q
  unfold cylinderAngularFrame
  split_ifs
  · simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_angular_unit] using
      Complex.abs_im_le_norm (_root_.fourier 1 q.2)
  · simpa only [Complex.norm_real, Real.norm_eq_abs, norm_angular_unit] using
      Complex.abs_re_le_norm (_root_.fourier 1 q.2)

/-- The order-one homogeneous coefficient. -/
def cylinderCartesianFirst (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) (i : Fin 2)
    (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  cylinderRadialFrame i q * ((a : ℂ) * J [] q - J [0] q) + cylinderAngularFrame i q * J [1] q

/-- The formal angular derivative of the first coefficient. Each order is kept. -/
def cylinderCartesianFirstAngle (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) (i : Fin 2)
    (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  cylinderAngularFrame i q * ((a : ℂ) * J [] q - J [0] q) - cylinderRadialFrame i q * J [1] q +
    cylinderRadialFrame i q * ((a : ℂ) * J [1] q - J [1, 0] q) +
    cylinderAngularFrame i q * J [1, 1] q

/-- The ordered second coefficient; j is the outer Cartesian derivative. -/
def cylinderCartesianSecond (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) (j i : Fin 2)
    (q : ℝ × AddCircle (2 * Real.pi)) : ℂ :=
  ((a : ℂ) - 1) * (cylinderRadialFrame j q * cylinderCartesianFirst a J i q) -
    cylinderRadialFrame j q * cylinderCartesianFirst a (fun w ↦ J (0 :: w)) i q +
    cylinderAngularFrame j q * cylinderCartesianFirstAngle a J i q

theorem cylinderCartesianFirst_memLp {a : ℝ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (h0 : MemLp (J []) 2 logCylinderMeasure) (ht : MemLp (J [0]) 2 logCylinderMeasure)
    (hθ : MemLp (J [1]) 2 logCylinderMeasure) (i : Fin 2) :
    MemLp (cylinderCartesianFirst a J i) 2 logCylinderMeasure :=
  ((cylinderRadialFrame_memLp i).mul ((h0.const_mul (a : ℂ)).sub ht)).add
    ((cylinderAngularFrame_memLp i).mul hθ)

theorem cylinderCartesianSecond_memLp {a : ℝ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : ∀ w, w.length ≤ 2 → MemLp (J w) 2 logCylinderMeasure) (j i : Fin 2) :
    MemLp (cylinderCartesianSecond a J j i) 2 logCylinderMeasure := by
  have hF := cylinderCartesianFirst_memLp (a := a)
    (hJ [] (by simp)) (hJ [0] (by simp)) (hJ [1] (by simp)) i
  have hT := cylinderCartesianFirst_memLp (a := a) (J := fun w ↦ J (0 :: w))
    (hJ [0] (by simp)) (hJ [0, 0] (by simp)) (hJ [0, 1] (by simp)) i
  have hA : MemLp (cylinderCartesianFirstAngle a J i) 2 logCylinderMeasure :=
    ((((cylinderAngularFrame_memLp i).mul
      (((hJ [] (by simp)).const_mul (a : ℂ)).sub (hJ [0] (by simp)))).sub
        ((cylinderRadialFrame_memLp i).mul (hJ [1] (by simp)))).add
          ((cylinderRadialFrame_memLp i).mul
            (((hJ [1] (by simp)).const_mul (a : ℂ)).sub (hJ [1, 0] (by simp))))).add
              ((cylinderAngularFrame_memLp i).mul (hJ [1, 1] (by simp)))
  exact ((((cylinderRadialFrame_memLp j).mul hF).const_mul ((a : ℂ) - 1)).sub
    ((cylinderRadialFrame_memLp j).mul hT)).add ((cylinderAngularFrame_memLp j).mul hA)

/-- The trace cancels each mixed word separately, without commuting them. -/
theorem cylinderCartesianSecond_trace (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ)
    (q : ℝ × AddCircle (2 * Real.pi)) :
    cylinderCartesianSecond a J 0 0 q + cylinderCartesianSecond a J 1 1 q =
      cylinderJetOperator a J q := by
  have hreal : (_root_.fourier 1 q.2).re ^ 2 + (_root_.fourier 1 q.2).im ^ 2 = 1 := by
    have h := Complex.sq_norm (_root_.fourier 1 q.2)
    rw [norm_angular_unit] at h
    simpa [Complex.normSq_apply, pow_two] using h.symm
  have hc : (((_root_.fourier 1 q.2).re : ℂ)) ^ 2 +
      (((_root_.fourier 1 q.2).im : ℂ)) ^ 2 = 1 := by exact_mod_cast hreal
  simp only [cylinderCartesianSecond, cylinderCartesianFirst, cylinderCartesianFirstAngle,
    cylinderRadialFrame, cylinderAngularFrame, Fin.isValue, ite_true, one_ne_zero, ite_false,
    cylinderJetOperator]
  linear_combination
    (J [0, 0] q - (2 * (a : ℂ)) * J [0] q + (a : ℂ) ^ 2 * J [] q + J [1, 1] q) * hc

/-- A fixed physical candidate family; words longer than two are unused. -/
def cylinderCartesianJet (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) :
    List (Fin 2) → ℝ × ℝ → ℂ
  | [] => cylinderPhysicalValue a (J [])
  | [i] => cylinderPhysicalValue (a - 1) (cylinderCartesianFirst a J i)
  | [j, i] => cylinderPhysicalValue (a - 2) (cylinderCartesianSecond a J j i)
  | _ => 0

/-- Genuine global weighted norms of all candidate entries through order two. -/
theorem cylinderCartesianJet_weighted {a : ℝ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : ∀ w, w.length ≤ 2 → MemLp (J w) 2 logCylinderMeasure)
    (w : List (Fin 2)) (hw : w.length ≤ 2) :
    MemLp (fun p ↦ cylinderCartesianJet a J w p /
      (Real.rpow (localRadius 0 p) (a + 1 - (w.length : ℝ)) : ℂ)) 2 volume := by
  cases w with
  | nil => simpa [cylinderCartesianJet] using
      memLp_cylinderPhysicalValue_weighted a (hJ [] (by simp))
  | cons j w =>
    cases w with
    | nil =>
      simpa [cylinderCartesianJet] using
        (memLp_cylinderPhysicalValue_weighted (a - 1)
          (cylinderCartesianFirst_memLp (hJ [] (by simp))
            (hJ [0] (by simp)) (hJ [1] (by simp)) j))
    | cons i w =>
      cases w with
      | nil =>
        have he : a - 2 + 1 = a + 1 - 2 := by ring
        simpa [cylinderCartesianJet, he] using
          memLp_cylinderPhysicalValue_weighted (a - 2) (cylinderCartesianSecond_memLp hJ j i)
      | cons k w => simp only [List.length_cons] at hw; omega

/-- Whole-disk finite norms, not merely local norms on the puncture. -/
theorem cylinderCartesianJet_memLp {a ρ : ℝ} (ha : 1 < a)
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : ∀ w, w.length ≤ 2 → MemLp (J w) 2 logCylinderMeasure)
    (w : List (Fin 2)) (hw : w.length ≤ 2) :
    MemLp (cylinderCartesianJet a J w) 2 (volume.restrict (localDisk 0 ρ)) := by
  have hlen : (w.length : ℝ) ≤ 2 := by exact_mod_cast hw
  exact memLp_of_div_localRadius_rpow (by linarith)
    ((cylinderCartesianJet_weighted hJ w hw).mono_measure Measure.restrict_le_self)

/-- This is an algebraic identity of candidates, not yet a weak Poisson claim. -/
theorem cylinderCartesianJet_laplacian (a : ℝ)
    (J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ) (p : ℝ × ℝ) :
    cylinderCartesianJet a J [0, 0] p + cylinderCartesianJet a J [1, 1] p =
      (Real.rpow (localRadius 0 p) (a - 2) : ℂ) *
        cylinderJetOperator a J (logCylinderCoordinates p) := by
  simp only [cylinderCartesianJet, cylinderPhysicalValue]
  rw [← mul_add, cylinderCartesianSecond_trace]

/-- Joint transport identifies the original physical forcing in these same
candidates. Weak derivative identification is a separate obligation. -/
theorem cylinderCartesianJet_forcing {a ρ : ℝ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ} {F : ℝ × ℝ → ℂ}
    (hP : cylinderJetOperator a J =ᵐ[logCylinderMeasure] cylinderForcing a ρ F) :
    ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)),
      cylinderCartesianJet a J [0, 0] p + cylinderCartesianJet a J [1, 1] p = F p := by
  have hU : MeasurableSet (localDisk 0 ρ) := by
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hn : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), p ≠ 0 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp [Measure.volume_eq_prod])
  have hPe := quasiMeasurePreserving_logCylinderCoordinates.ae hP
  filter_upwards [hn, ae_restrict_mem hU, ae_restrict_of_ae hPe] with p hp hpU hPe
  have hr := localRadius_pos_of_ne_zero hp
  have he : Real.exp (-(logCylinderCoordinates p).1) = localRadius 0 p := by
    change Real.exp (-(-Real.log (localRadius 0 p))) = _
    rw [neg_neg, Real.exp_log hr]
  rw [cylinderCartesianJet_laplacian, hPe, cylinderForcing_apply, he,
    ite_eq_left (show localRadius 0 p < ρ from hpU), logCylinderPlane_coordinates hp]
  have hc : (Real.rpow (localRadius 0 p) (a - 2) : ℂ) *
      (Real.exp ((a - 2) * (logCylinderCoordinates p).1) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    change Complex.ofReal (Real.rpow (localRadius 0 p) (a - 2) *
      Real.exp ((a - 2) * (-Real.log (localRadius 0 p)))) = 1
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hr, ← Real.exp_add]
    have hz : Real.log (localRadius 0 p) * (a - 2) +
        (a - 2) * -Real.log (localRadius 0 p) = 0 := by ring
    rw [hz, Real.exp_zero, Complex.ofReal_one]
  rw [← mul_assoc, hc, one_mul]

end NoEmbeddedEigenvalues
