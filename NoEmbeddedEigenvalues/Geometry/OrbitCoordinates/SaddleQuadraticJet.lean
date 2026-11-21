import NoEmbeddedEigenvalues.Geometry.OrbitCoordinates.SaddleTaylorJet
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.StreamJet

/-! # The first jet of the saddle quadratic -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The first classical quadratic jet, in the original Cartesian coordinates. -/
theorem first_saddleQuadratic (c : ℝ × ℝ) (a : ℂ) (j : Fin 2) (p : ℝ × ℝ) :
    classicalComplexJet [j] (saddleQuadratic c a) p =
      (if j = 0 then -1 else 1 : ℂ) * (a * (Real.cos c.1 : ℂ)) *
        ((axisCoord j p - axisCoord j c : ℝ) : ℂ) := by
  fin_cases j
  · have hd := ((((hasDerivAt_id p.1).sub_const c.1).pow 2).const_sub
        ((p.2 - c.2) ^ 2)).ofReal_comp.const_mul (a * (Real.cos c.1 : ℂ) / 2)
    convert hd.deriv using 1 <;>
      simp [classicalComplexJet, coordPartial, partialX, saddleQuadratic, axisCoord]
    ring
  · have hd := ((((hasDerivAt_id p.2).sub_const c.2).pow 2).sub_const
        ((p.1 - c.1) ^ 2)).ofReal_comp.const_mul (a * (Real.cos c.1 : ℂ) / 2)
    convert hd.deriv using 1 <;>
      simp [classicalComplexJet, coordPartial, partialY, saddleQuadratic, axisCoord]
    ring

/-- Linear growth of the fixed classical quadratic gradient. -/
theorem norm_first_saddleQuadratic_le (c : ℝ × ℝ) (a : ℂ) (j : Fin 2)
    (p : ℝ × ℝ) :
    ‖classicalComplexJet [j] (saddleQuadratic c a) p‖ ≤
      ‖a * (Real.cos c.1 : ℂ)‖ * localRadius c p := by
  have hcoord : |axisCoord j p - axisCoord j c| ≤ dist p c := by
    fin_cases j <;> simp [axisCoord, Prod.dist_eq, Real.dist_eq]
  have hsign : ‖(if j = 0 then -1 else 1 : ℂ)‖ = 1 := by split_ifs <;> norm_num
  rw [first_saddleQuadratic, norm_mul, norm_mul, hsign, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hcoord.trans (dist_le_localRadius c p)) (norm_nonneg _)

end NoEmbeddedEigenvalues
