import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderPhysicalWeak

/-!
# Specified ordered weak Cartesian cylinder reconstruction

The supplied cylinder jet gives the source weak pairs. Pointwise pullbacks of
the same physical candidates allow negative-Jacobian cofactor transport on
overlapping charts. Their previously established whole-disk finite norms
supply local integrability independently at every ordered level.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped Topology

/-- Finite norms on every bounded disk give physical local integrability,
including at zero, without claiming global unweighted L2. -/
theorem cylinderCartesianJet_locallyIntegrable {a : ℝ} (ha : 1 < a)
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : ∀ w, w.length ≤ 2 → MemLp (J w) 2 logCylinderMeasure)
    (w : List (Fin 2)) (hw : w.length ≤ 2) :
    LocallyIntegrableOn (cylinderCartesianJet a J w) univ := by
  intro p _
  let R := localRadius 0 p + 1
  have hU : IsOpen (localDisk 0 R) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hp : p ∈ localDisk 0 R := by
    change localRadius 0 p < localRadius 0 p + 1
    linarith
  have hi := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((cylinderCartesianJet_memLp (ρ := R) ha hJ w hw).locallyIntegrable (by norm_num)) p hp
  rw [hU.nhdsWithin_eq hp] at hi
  exact hi.filter_mono nhdsWithin_le_nhds

/-- Every prescribed ordered pair is weak on the entire punctured plane.
No angular seam is discarded. -/
theorem cylinderCartesianJet_hasWeakPartial {a : ℝ} (ha : 1 < a)
    {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : HasCylinderH2Jet S J) (w : List (Fin 2)) (hw : w.length < 2) (j : Fin 2) :
    HasWeakPartialOn (univ \ {0}) j (cylinderCartesianJet a J w)
      (cylinderCartesianJet a J (j :: w)) := by
  have hLI := cylinderCartesianJet_locallyIntegrable ha hJ.2.2
  cases w with
  | nil =>
    apply cylinderPhysical_hasWeakPartial (a := a) (K := J)
      (fun i ↦ hJ.2.1.2 [] (by simp) i)
      (hLI [] (by simp)) (hLI [j] (by simp)) j
    · exact cylinderPhysicalValue_logPolarPlane a (J [])
    · exact cylinderPhysicalValue_logPolarPlane (a - 1) (cylinderCartesianFirst a J j)
  | cons i w =>
    cases w with
    | nil =>
      let K : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ :=
        fun v ↦ if v = [] then cylinderCartesianFirst a J i
          else if v = [0] then cylinderCartesianFirst a (fun v ↦ J (0 :: v)) i
          else cylinderCartesianFirstAngle a J i
      have hK (k : Fin 2) :
          HasWeakPartialOn univ k (cylinderLift (K [])) (cylinderLift (K [k])) := by
        have hh := cylinderCartesianFirst_hasWeakPartial (a := a) hJ.2.1.2 i k
        fin_cases k <;> simpa [K] using hh
      apply cylinderPhysical_hasWeakPartial (a := a - 1) (K := K) hK
        (hLI [i] (by simp)) (hLI [j, i] (by simp)) j
      · simpa only [K, ite_true, cylinderCartesianJet] using
          cylinderPhysicalValue_logPolarPlane (a - 1) (cylinderCartesianFirst a J i)
      · intro q
        change cylinderPhysicalValue (a - 2) (cylinderCartesianSecond a J j i)
          (logPolarPlane q) = _
        rw [cylinderPhysicalValue_logPolarPlane]
        have he : a - 1 - 1 = a - 2 := by ring
        rw [he]
        congr 1
        simp [cylinderLift, cylinderCartesianFirst, cylinderCartesianSecond, K]
        ring
    | cons k w => simp only [List.length_cons] at hw; omega

end NoEmbeddedEigenvalues
