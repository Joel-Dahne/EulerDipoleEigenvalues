import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.DipoleCalculus
import NoEmbeddedEigenvalues.OrbitCoordinates
import NoEmbeddedEigenvalues.Sectors
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Explicit orthonormal saddle charts

The sign in the chart is cos(Pₓ), which is ±1 at a saddle. The factorization is
therefore Ψ = uv m at both torus saddle types, with the same smooth sinc factor.
Orthogonality is expressed using the Euclidean radius, not the maximum product norm.

Taylor bounds for the explicit function include derivatives through order three;
they do not come from formally differentiating a value-only big-O assertion.
The linearized Hamiltonian on linear polynomials is a separate, mixed-sector input.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff

/-- The quadratic Taylor polynomial of `a * Ψ` at a saddle. -/
def saddleQuadratic (c : ℝ × ℝ) (a : ℂ) (p : ℝ × ℝ) : ℂ :=
  a * (Real.cos c.1 : ℂ) / 2 * (((p.2 - c.2) ^ 2 - (p.1 - c.1) ^ 2 : ℝ) : ℂ)

/-- The affine saddle chart, with signs normalized so the leading dipole is uv. -/
def saddleOrthoChart (P q : ℝ × ℝ) : ℝ × ℝ :=
  (P.1 + (q.1 - Real.cos P.1 * q.2) / Real.sqrt 2,
   P.2 + (q.1 + Real.cos P.1 * q.2) / Real.sqrt 2)

/-- Inverse orthonormal coordinates, valid when P is a saddle. -/
def saddleOrthoCoord (P p : ℝ × ℝ) : ℝ × ℝ :=
  (((p.1 - P.1) + (p.2 - P.2)) / Real.sqrt 2,
   Real.cos P.1 * ((p.2 - P.2) - (p.1 - P.1)) / Real.sqrt 2)

/-- Smooth extension of the two sine ratios. -/
def saddleFactor (q : ℝ × ℝ) : ℝ :=
  Real.sinc (q.1 / Real.sqrt 2) * Real.sinc (q.2 / Real.sqrt 2)

/-- Classical derivatives, used only for the explicit smooth dipole remainder. -/
def classicalRealJet : List (Fin 2) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], f => f
  | j :: w, f => coordPartial j (classicalRealJet w f)

/-- The product metric is bounded by the Euclidean radius. -/
theorem dist_le_localRadius (c p : ℝ × ℝ) : dist p c ≤ localRadius c p := by
  simp only [Prod.dist_eq, Real.dist_eq, max_le_iff, localRadius]
  exact ⟨Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _)),
    Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))⟩

open Filter in
private theorem contDiff_sinc : ContDiff ℝ ∞ Real.sinc := by
  rw [contDiff_iff_contDiffAt]
  intro x
  suffices h : AnalyticAt ℝ Real.sinc x from h.contDiffAt
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Real.sinc_eq_dslope]
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · refine (Real.analyticAt_sin.div analyticAt_id hx).congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy using (Real.sinc_of_ne_zero hy).symm

/-- The sinc factor is smooth, even, normalized and locally positive. -/
theorem saddleFactor_regular :
    ContDiff ℝ ∞ saddleFactor ∧ saddleFactor 0 = 1 ∧
      (∀ j q, saddleFactor (axisReflect j q) = saddleFactor q) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ localDisk 0 ρ, 0 < saddleFactor q := by
  have hs : ContDiff ℝ ∞ saddleFactor := by
    unfold saddleFactor
    exact (contDiff_sinc.comp (by fun_prop)).mul (contDiff_sinc.comp (by fun_prop))
  have hzero : saddleFactor 0 = 1 := by simp [saddleFactor]
  refine ⟨hs, hzero, ?_, ?_⟩
  · intro j q
    fin_cases j <;> simp [axisReflect, saddleFactor, neg_div]
  · have hpos : (0 : ℝ × ℝ) ∈ {q | 0 < saddleFactor q} := by simp [hzero]
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hs.continuous).mem_nhds hpos)
    exact ⟨ρ, hρ, fun q hq ↦ hsub ((dist_le_localRadius 0 q).trans_lt hq)⟩

/-- Affine inverse and Euclidean orthogonality of the saddle chart. -/
theorem saddleOrthoChart_orthogonal {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    (∀ q, saddleOrthoCoord P (saddleOrthoChart P q) = q) ∧
    (∀ p, saddleOrthoChart P (saddleOrthoCoord P p) = p) ∧
    (∀ q, localRadius P (saddleOrthoChart P q) = localRadius 0 q) := by
  have hsq : Real.cos P.1 ^ 2 = 1 := by
    obtain ⟨m, n, _, rfl⟩ := hP
    nlinarith [Real.abs_cos_int_mul_pi m, sq_abs (Real.cos (m * Real.pi))]
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨?_, ?_, ?_⟩
  · intro q
    ext <;> dsimp [saddleOrthoCoord, saddleOrthoChart]
    all_goals field_simp; ring_nf; simp [hsq, hsqrt]; ring
  · intro p
    ext <;> dsimp [saddleOrthoCoord, saddleOrthoChart]
    all_goals field_simp; ring_nf; simp [hsq, hsqrt]; ring
  · intro q
    unfold localRadius saddleOrthoChart
    simp only [Prod.fst_zero, Prod.snd_zero, add_sub_cancel_left, sub_zero]
    congr 1
    simp only [div_pow, hsqrt]
    ring_nf
    rw [hsq]
    ring

/-- Exact global identity in each normalized chart (`lem:saddle-normal-form`). -/
theorem saddle_dipole_factorization {P : ℝ × ℝ} (hP : P ∈ saddleSet) (q : ℝ × ℝ) :
    dipoleLift (saddleOrthoChart P q) = q.1 * q.2 * saddleFactor q := by
  have hx : Real.sin P.1 = 0 := by
    obtain ⟨m, n, _, rfl⟩ := hP
    exact Real.sin_int_mul_pi m
  have hy : Real.sin P.2 = 0 := by
    obtain ⟨m, n, _, rfl⟩ := hP
    exact Real.sin_int_mul_pi n
  have hsq : Real.cos P.1 ^ 2 = 1 := by
    obtain ⟨m, n, _, rfl⟩ := hP
    nlinarith [Real.abs_cos_int_mul_pi m, sq_abs (Real.cos (m * Real.pi))]
  have hcos : Real.cos P.2 = -Real.cos P.1 := by
    obtain ⟨m, n, hmn, rfl⟩ := hP
    have he : Real.cos ((m : ℝ) * Real.pi + n * Real.pi) = -1 := by
      rw [← add_mul, ← Int.cast_add, Real.cos_int_mul_pi, hmn.neg_one_zpow]
    rw [Real.cos_add, Real.sin_int_mul_pi, Real.sin_int_mul_pi, mul_zero, sub_zero] at he
    change Real.cos (n * Real.pi) = -Real.cos (m * Real.pi)
    apply mul_left_cancel₀ (show Real.cos (m * Real.pi) ≠ 0 from by
      intro h
      simp [h] at hsq)
    nlinarith [he, hsq]
  have hsinc (t : ℝ) : t * Real.sinc t = Real.sin t := by
    by_cases ht : t = 0
    · simp [ht]
    · rw [Real.sinc_of_ne_zero ht]
      field_simp
  have hprod : q.1 * q.2 * saddleFactor q =
      2 * Real.sin (q.1 / Real.sqrt 2) * Real.sin (q.2 / Real.sqrt 2) := by
    unfold saddleFactor
    calc
      _ = 2 * ((q.1 / Real.sqrt 2) * Real.sinc (q.1 / Real.sqrt 2)) *
          ((q.2 / Real.sqrt 2) * Real.sinc (q.2 / Real.sqrt 2)) := by
        field_simp
        ring_nf
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ = _ := by rw [hsinc, hsinc]
  rw [hprod]
  simp only [saddleOrthoChart, dipoleLift, Real.cos_add, hx, hy, hcos,
    zero_mul, sub_zero]
  rcases (sq_eq_one_iff).mp hsq with hs | hs
  all_goals
    simp only [hs, one_mul, neg_one_mul, neg_neg, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [sub_div, add_div, Real.cos_sub, Real.cos_add]
    ring

/-- The Cartesian normalization uses exactly the uv coefficient in the chart
(`lem:saddle-quadratic-chart`), with no extra sign or factor of two. -/
theorem saddleQuadratic_comp_chart {P : ℝ × ℝ} (hP : P ∈ saddleSet) (a : ℂ)
    (q : ℝ × ℝ) :
    saddleQuadratic P a (saddleOrthoChart P q) = a * ((q.1 * q.2 : ℝ) : ℂ) := by
  have hsq : (Real.cos P.1 : ℂ) ^ 2 = 1 := by
    have hr : Real.cos P.1 ^ 2 = 1 := by
      obtain ⟨m, n, _, rfl⟩ := hP
      nlinarith [Real.abs_cos_int_mul_pi m, sq_abs (Real.cos (m * Real.pi))]
    exact_mod_cast hr
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [saddleQuadratic, saddleOrthoChart, add_sub_cancel_left,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp
  ring_nf
  simp only [hsq, hsqrt]
  ring

/-- Value, gradient-square and differentiated Taylor bounds for the explicit dipole
(`lem:saddle-normal-form-derivatives`). The constants do not depend on the point q. -/
theorem saddle_normal_form_derivatives {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ q ∈ localDisk 0 ρ,
      (∀ w : List (Fin 2), w.length ≤ 3 →
        |classicalRealJet w (fun v ↦ dipoleLift (saddleOrthoChart P v) - v.1 * v.2) q| ≤
          C * localRadius 0 q ^ (4 - w.length)) ∧
      |gradSq dipoleLift (saddleOrthoChart P q) - localRadius 0 q ^ 2| ≤
        C * localRadius 0 q ^ 4 := by
  sorry

end NoEmbeddedEigenvalues
