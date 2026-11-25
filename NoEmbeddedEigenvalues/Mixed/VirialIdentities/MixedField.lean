module

public import NoEmbeddedEigenvalues.Mixed.PositiveComparisons.MixedComparison
public import NoEmbeddedEigenvalues.Geometry.Cells.Cells
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # The adapted field in the odd–even mixed sector -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Set

/-- Cartesian components of the mixed adapted field. -/
def mixedFieldX (p : ℝ × ℝ) : ℝ := tan (p.1 / 2)
def mixedFieldY (p : ℝ × ℝ) : ℝ := tan (p.2 / 2)

/-- Components of the same field in the diagonal chart. -/
def mixedFieldA (q : ℝ × ℝ) : ℝ := sin q.1 / (cos q.1 + cos q.2)
def mixedFieldB (q : ℝ × ℝ) : ℝ := sin q.2 / (cos q.1 + cos q.2)

/-- The adapted coefficient in diagonal coordinates. -/
def mixedFieldCoeff (q : ℝ × ℝ) : ℝ :=
  (sin q.1 ^ 2 + sin q.2 ^ 2) / (cos q.1 + cos q.2) ^ 2

/-- The off-diagonal entry of `2 sym DW - f I` in the orthonormal diagonal basis. -/
def mixedFieldMatrixOffDiagonal (q : ℝ × ℝ) : ℝ :=
  2 * sin q.1 * sin q.2 / (cos q.1 + cos q.2) ^ 2

private theorem mixed_field_diagonal_partials {q : ℝ × ℝ} (hp : cos q.1 + cos q.2 ≠ 0) :
    2 * partialX mixedFieldA q - mixedFieldCoeff q = 1 ∧
    2 * partialY mixedFieldB q - mixedFieldCoeff q = 1 ∧
    partialY mixedFieldA q + partialX mixedFieldB q = mixedFieldMatrixOffDiagonal q := by
  have a := (hasDerivAt_sin q.1).div ((hasDerivAt_cos q.1).add_const (cos q.2)) hp
  have b := (hasDerivAt_sin q.2).div ((hasDerivAt_cos q.2).const_add (cos q.1)) hp
  have c := (hasDerivAt_const q.2 (sin q.1)).div
    ((hasDerivAt_cos q.2).const_add (cos q.1)) hp
  have d := (hasDerivAt_const q.1 (sin q.2)).div
    ((hasDerivAt_cos q.1).add_const (cos q.2)) hp
  replace a := a.deriv
  replace b := b.deriv
  replace c := c.deriv
  replace d := d.deriv
  change partialX mixedFieldA q = _ at a
  change partialY mixedFieldB q = _ at b
  change partialY mixedFieldA q = _ at c
  change partialX mixedFieldB q = _ at d
  rw [a, b, c, d]
  simp only [mixedFieldCoeff, mixedFieldMatrixOffDiagonal]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
  · linear_combination sin_sq_add_cos_sq q.1 - sin_sq_add_cos_sq q.2
  · linear_combination sin_sq_add_cos_sq q.2 - sin_sq_add_cos_sq q.1
  · ring

private theorem mixed_field_half_angles {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    0 < cos (p.1 / 2) ∧ 0 < cos (p.2 / 2) := by
  have ha := abs_lt.mp hp.1
  have hb := abs_lt.mp hp.2
  simp only [diagCoord] at ha hb
  exact ⟨cos_pos_of_mem_Ioo ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩,
    cos_pos_of_mem_Ioo ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩⟩

theorem mixed_field_trig {x : ℝ} (hx : cos (x / 2) ≠ 0) :
    1 / cos (x / 2) ^ 2 = 1 + tan (x / 2) ^ 2 ∧
    sin x * tan (x / 2) = 1 - cos x ∧
    cos x * tan (x / 2) = sin x * (1 - tan (x / 2) ^ 2) / 2 := by
  have hs : sin x = 2 * sin (x / 2) * cos (x / 2) := by
    nth_rw 1 [show x = 2 * (x / 2) by ring]
    rw [sin_two_mul]
  have hc : cos x = cos (x / 2) ^ 2 - sin (x / 2) ^ 2 := by
    nth_rw 1 [show x = 2 * (x / 2) by ring]
    rw [cos_two_mul]
    linarith [sin_sq_add_cos_sq (x / 2)]
  rw [hs, hc, tan_eq_sin_div_cos]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
  · linear_combination -(sin_sq_add_cos_sq (x / 2))
  · linear_combination sin_sq_add_cos_sq (x / 2)

theorem mixed_field_cartesian_partials_of_cos_ne {p : ℝ × ℝ}
    (hx : cos (p.1 / 2) ≠ 0) (hy : cos (p.2 / 2) ≠ 0) :
    partialX mixedFieldX p = (cos (p.1 / 2) ^ 2)⁻¹ / 2 ∧
    partialY mixedFieldY p = (cos (p.2 / 2) ^ 2)⁻¹ / 2 ∧
    partialY mixedFieldX p = 0 ∧ partialX mixedFieldY p = 0 := by
  have hd (x : ℝ) (h : cos (x / 2) ≠ 0) :
      HasDerivAt (fun t : ℝ ↦ tan (t / 2)) ((cos (x / 2) ^ 2)⁻¹ / 2) x := by
    have h' := (hasDerivAt_tan h).comp x ((hasDerivAt_id x).div_const 2)
    exact h'.congr_deriv (by simp only [div_eq_mul_inv, one_mul])
  exact ⟨(hd _ hx).deriv, (hd _ hy).deriv,
    (hasDerivAt_const p.2 (tan (p.1 / 2))).deriv,
    (hasDerivAt_const p.1 (tan (p.2 / 2))).deriv⟩

private theorem mixed_field_cartesian_partials {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    partialX mixedFieldX p = (cos (p.1 / 2) ^ 2)⁻¹ / 2 ∧
    partialY mixedFieldY p = (cos (p.2 / 2) ^ 2)⁻¹ / 2 ∧
    partialY mixedFieldX p = 0 ∧ partialX mixedFieldY p = 0 :=
  mixed_field_cartesian_partials_of_cos_ne (mixed_field_half_angles hp).1.ne'
    (mixed_field_half_angles hp).2.ne'

private theorem mixed_field_cos_sum (p : ℝ × ℝ) :
    cos (diagCoord p).1 + cos (diagCoord p).2 = 2 * cos (p.1 / 2) * cos (p.2 / 2) := by
  simp only [diagCoord,
    show (p.1 + p.2) / 2 = p.1 / 2 + p.2 / 2 by ring,
    show (p.1 - p.2) / 2 = p.1 / 2 - p.2 / 2 by ring, cos_add, cos_sub]
  ring

/-- Algebra of the mixed field, including the coordinate change. In Cartesian
coordinates the symmetric Jacobian is diagonal, with the two stated eigenvalues. -/
theorem mixed_field_algebra :
    IsAdaptedOn mixedFieldX mixedFieldY (mixedFieldCoeff ∘ diagCoord) cellSquare ∧
    ∀ p ∈ cellSquare,
      let q := diagCoord p
      mixedFieldA q = (mixedFieldX p + mixedFieldY p) / 2 ∧
      mixedFieldB q = (mixedFieldX p - mixedFieldY p) / 2 ∧
      fieldDeriv mixedFieldX mixedFieldY dipoleLift p = dipoleLift p - 2 ∧
      divergence mixedFieldX mixedFieldY p = mixedFieldCoeff q + 1 ∧
      2 * partialX mixedFieldA q - mixedFieldCoeff q = 1 ∧
      2 * partialY mixedFieldB q - mixedFieldCoeff q = 1 ∧
      partialY mixedFieldA q + partialX mixedFieldB q = mixedFieldMatrixOffDiagonal q ∧
      partialY mixedFieldX p = 0 ∧ partialX mixedFieldY p = 0 ∧
      2 * partialX mixedFieldX p = (cos ((q.1 + q.2) / 2) ^ 2)⁻¹ ∧
      2 * partialY mixedFieldY p = (cos ((q.1 - q.2) / 2) ^ 2)⁻¹ := by
  have hlocal (p : ℝ × ℝ) (hp : p ∈ cellSquare) :
      let q := diagCoord p
      mixedFieldA q = (mixedFieldX p + mixedFieldY p) / 2 ∧
      mixedFieldB q = (mixedFieldX p - mixedFieldY p) / 2 ∧
      mixedFieldCoeff q = (mixedFieldX p ^ 2 + mixedFieldY p ^ 2) / 2 := by
    obtain ⟨hx, hy⟩ := mixed_field_half_angles hp
    have ha : (diagCoord p).1 = p.1 / 2 + p.2 / 2 := by unfold diagCoord; dsimp; ring
    have hb : (diagCoord p).2 = p.1 / 2 - p.2 / 2 := by unfold diagCoord; dsimp; ring
    dsimp only
    simp only [mixedFieldA, mixedFieldB, mixedFieldCoeff, mixed_field_cos_sum,
      mixedFieldX, mixedFieldY, tan_eq_sin_div_cos]
    simp only [ha, hb, sin_add, sin_sub]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · field_simp
    · field_simp
      ring
  constructor
  · intro p hp
    obtain ⟨dx, dy, cx, cy⟩ := mixed_field_cartesian_partials hp
    obtain ⟨⟨hx, _, htx⟩, ⟨hy, _, hty⟩⟩ :=
      And.intro (mixed_field_trig (mixed_field_half_angles hp).1.ne')
        (mixed_field_trig (mixed_field_half_angles hp).2.ne')
    have hf := (hlocal p hp).2.2
    simp only [Function.comp_apply, classicalL0, smul_eq_mul, dx, dy, cx, cy, mul_zero,
      sub_zero, zero_sub, hf, mixedFieldX, mixedFieldY]
    rw [← one_div, ← one_div, hx, hy, htx, hty]
    constructor <;> ring
  · intro p hp
    obtain ⟨dx, dy, cx, cy⟩ := mixed_field_cartesian_partials hp
    obtain ⟨⟨hx, hsinx, _⟩, ⟨hy, hsiny, _⟩⟩ :=
      And.intro (mixed_field_trig (mixed_field_half_angles hp).1.ne')
        (mixed_field_trig (mixed_field_half_angles hp).2.ne')
    obtain ⟨hA, hB, hf⟩ := hlocal p hp
    obtain ⟨hpx, hpy⟩ := mixed_field_half_angles hp
    have hp' : cos (diagCoord p).1 + cos (diagCoord p).2 ≠ 0 := by
      rw [mixed_field_cos_sum]
      positivity
    obtain ⟨hda, hdb, hcross⟩ := mixed_field_diagonal_partials hp'
    refine ⟨hA, hB, ?_, ?_, hda, hdb, hcross, cx, cy, ?_, ?_⟩
    · simp only [fieldDeriv, smul_eq_mul, partialX_dipoleLift, partialY_dipoleLift,
        mixedFieldX, mixedFieldY, dipoleLift]
      linear_combination -hsinx - hsiny
    · simp only [divergence, dx, dy, hf, mixedFieldX, mixedFieldY]
      rw [← one_div, ← one_div, hx, hy]
      ring
    · rw [dx, show ((diagCoord p).1 + (diagCoord p).2) / 2 = p.1 / 2 by
        unfold diagCoord; dsimp; ring]
      ring
    · rw [dy, show ((diagCoord p).1 - (diagCoord p).2) / 2 = p.2 / 2 by
        unfold diagCoord; dsimp; ring]
      ring

end NoEmbeddedEigenvalues
