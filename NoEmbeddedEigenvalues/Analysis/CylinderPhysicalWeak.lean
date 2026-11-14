import NoEmbeddedEigenvalues.Analysis.CylinderCartesianSource
import NoEmbeddedEigenvalues.Analysis.LogPolarAtlas
import NoEmbeddedEigenvalues.WeakChartTransportVariable
import NoEmbeddedEigenvalues.WeakPartialLocality

/-!
# Weak homogeneous reconstruction on the entire punctured plane

Physical local integrability is supplied independently. Cofactor-weighted tests
transport each weak pair on a genuine open angular chart. Two overlapping cuts
then cover every nonzero point, including each chart's omitted ray.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff

/-- Both chart branches have the same radial/angular cofactor coefficients. -/
theorem chartCofactor_logPolarChart (b : Bool) (j : Fin 2) {q : ℝ × ℝ}
    (hq : q ∈ (logPolarChart b).source) :
    chartCofactor (logPolarChart b) j 0 q =
        (Real.exp (-q.1) : ℂ) * cylinderLift (cylinderRadialFrame j) q ∧
      chartCofactor (logPolarChart b) j 1 q =
        -(Real.exp (-q.1) : ℂ) * cylinderLift (cylinderAngularFrame j) q := by
  have hc := chartCofactor_values (contDiff_logPolarChart b).contDiffOn j hq
  rw [fderiv_logPolarChart] at hc
  fin_cases j <;>
    simpa [logPolarDeriv, Matrix.toLin_finTwoProd_toContinuousLinearMap,
      cylinderRadialFrame_lift, cylinderAngularFrame_lift] using hc

/-- The pointwise pullback uses the actual cylinder value, not an L2 class. -/
theorem cylinderPhysicalValue_logPolarPlane (a : ℝ)
    (K : ℝ × AddCircle (2 * Real.pi) → ℂ) (q : ℝ × ℝ) :
    cylinderPhysicalValue a K (logPolarPlane q) =
      cylinderSourceWeight a q * cylinderLift K q := by
  rw [← logCylinderPlane_coe q.1 q.2, cylinderPhysicalValue_plane]
  rfl

/-- A homogeneous value and its specified Cartesian candidate form a weak pair
on the whole punctured plane. The physical local norms are separate inputs. -/
theorem cylinderPhysical_hasWeakPartial {a : ℝ}
    {K : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hK : ∀ i, HasWeakPartialOn univ i (cylinderLift (K [])) (cylinderLift (K [i])))
    {f d : ℝ × ℝ → ℂ} (hf : LocallyIntegrableOn f univ)
    (hd : LocallyIntegrableOn d univ) (j : Fin 2)
    (hv : ∀ q, f (logPolarPlane q) = cylinderSourceWeight a q * cylinderLift (K []) q)
    (hder : ∀ q, d (logPolarPlane q) = cylinderSourceWeight (a - 1) q *
      cylinderLift (cylinderCartesianFirst a K j) q) :
    HasWeakPartialOn (univ \ {0}) j f d := by
  let G (i : Fin 2) (q : ℝ × ℝ) := cylinderSourceWeight a q *
    (cylinderLift (K [i]) q - if i = 0 then (a : ℂ) * cylinderLift (K []) q else 0)
  have hg (i : Fin 2) : HasWeakPartialOn univ i
      (fun q ↦ cylinderSourceWeight a q * cylinderLift (K []) q) (G i) :=
    cylinderSourceWeight_hasWeakPartial (hK i) a
  apply hasWeakPartialOn_of_locally
  intro p hp
  obtain ⟨b, hpb⟩ := exists_logPolarChart_target (show p ≠ 0 by simpa using hp.2)
  refine ⟨(logPolarChart b).target, (logPolarChart b).open_target, hpb, ?_⟩
  have hneg : ∀ q ∈ (logPolarChart b).source,
      (fderiv ℝ (logPolarChart b) q).det < 0 := by
    intro q _
    rw [det_fderiv_logPolarChart]
    linarith [sq_pos_of_pos (Real.exp_pos (-q.1))]
  refine HasWeakPartialOn.of_comp_chart_neg (contDiff_logPolarChart b).contDiffOn
    hneg (fun i ↦ (hg i).mono (subset_univ _))
    (hf.mono_set (subset_univ _)) (hd.mono_set (subset_univ _)) j ?_ ?_
  · intro q _
    rw [logPolarChart_apply]
    exact hv q
  · intro q hq
    rw [det_fderiv_logPolarChart, logPolarChart_apply, hder q,
      (chartCofactor_logPolarChart b j hq).1, (chartCofactor_logPolarChart b j hq).2]
    dsimp only [G]
    simp only [ite_true, one_ne_zero, ite_false, sub_zero]
    dsimp only [cylinderLift, Function.comp_apply, cylinderCartesianFirst]
    simp only [Complex.ofReal_neg, Complex.ofReal_pow]
    linear_combination -(Real.exp (-q.1) : ℂ) *
      (cylinderRadialFrame j (logCylinderProjection q) *
        ((a : ℂ) * K [] (logCylinderProjection q) - K [0] (logCylinderProjection q)) +
      cylinderAngularFrame j (logCylinderProjection q) * K [1] (logCylinderProjection q)) *
        cylinderSourceWeight_pred a q

end NoEmbeddedEigenvalues
