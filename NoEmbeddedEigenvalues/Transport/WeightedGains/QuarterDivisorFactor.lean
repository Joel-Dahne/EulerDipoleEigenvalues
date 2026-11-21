module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorGeometry
public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterDivisorCalculus
public import NoEmbeddedEigenvalues.Analysis.Inequalities.SmoothLinearFactor

/-!
# A uniformly controlled inverse divisor factor on complete phase cells

Blueprint: `lem:quarter-divisor-inverse-factor`.

Write `D(h) = (h-z) g(h)` using smooth segment averaging. Logarithmic phase
geometry and the chord inequality keep `g` away from zero throughout a complete
cell. The second divisor derivative bounds `g'`, hence the derivative of `1/g`.
The constants depend only on the nonzero real spectral parameter.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- The inverse of the linear divisor factor is smooth, of size O(z), and has a
uniformly bounded derivative on every complete cell in one small collar. -/
theorem quarterDivisor_inverse_factor {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ B H r : ℝ, 0 < B ∧ 0 < H ∧ 0 < r ∧ r < 1 ∧
      ∀ (κ : ℂ) (a z b : ℝ), 0 < a → a < z → z < b → b < r →
        quarterDivisor lam κ z = 0 →
        |quarterPhase lam a - quarterPhase lam z| = Real.pi →
        |quarterPhase lam b - quarterPhase lam z| = Real.pi →
        ∃ R R₁ : ℝ → ℂ, ContDiffOn ℝ ∞ R (Icc a b) ∧
          (∀ h ∈ Icc a b, HasDerivAt R (R₁ h) h) ∧
          (∀ h ∈ Icc a b, quarterDivisor lam κ h * R h = ((h - z : ℝ) : ℂ)) ∧
          (∀ h ∈ Icc a b, z / B ≤ h ∧ h ≤ B * z ∧
            ‖R h‖ ≤ B * z ∧ ‖R₁ h‖ ≤ H) := by
  obtain ⟨c, C, r₀, hc, hC, hr₀, hr₀1, hp⟩ := eighthPeriod_derivative_bounds
  obtain ⟨cD, CD, rD, hcD, hCD, hrD, hrD1, hDb⟩ := quarterDivisor_derivative_bounds hlam
  let r := min r₀ rD
  have hr : 0 < r := lt_min hr₀ hrD
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrrD : r ≤ rD := min_le_right _ _
  have hr1 : r < 1 := hrr₀.trans_lt hr₀1
  let A := 2 * |lam|
  let P := quarterPhase |lam|
  have hA : 0 < A := mul_pos (by norm_num) (abs_pos.2 hlam)
  have hder (h : ℝ) (hh : h ∈ Ioo 0 r) :
      HasDerivAt P (A * deriv eighthPeriod h) h :=
    (deriv_eighthPeriod_neg hh.1 (hh.2.trans hr1)).1.hasDerivAt.const_mul A
  have hPa : AntitoneOn P (Ioo 0 r) := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left
      (eighthPeriod_strictAntiOn.antitoneOn ⟨hx.1, hx.2.trans hr1⟩
        ⟨hy.1, hy.2.trans hr1⟩ hxy) hA.le
  have hPb (h : ℝ) (hh : h ∈ Ioo 0 r) :
      A * c ≤ -h * deriv P h ∧ -h * deriv P h ≤ A * C := by
    rw [(hder h hh).deriv]
    obtain ⟨hl, hu, -⟩ := hp h ⟨hh.1, hh.2.trans_le hrr₀⟩
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hA.le,
      mul_le_mul_of_nonneg_left hu hA.le]
  obtain ⟨K, hK, hcell⟩ := logarithmic_cell_geometry (mul_pos hA hc) hPa
    (fun h hh ↦ (hder h hh).differentiableAt) hPb
  let B := max K (1 / cD) + 1
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hKB : K ≤ B := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hB : 0 < B := hK0.trans_le hKB
  have hBc : 1 ≤ B * cD := by
    apply (div_le_iff₀ hcD).1
    exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨B, CD * K ^ 2 * B ^ 2, r, hB, by positivity, hr, hr1, ?_⟩
  intro κ a z b ha haz hzb hbr hzero hleft hright
  have hzc : z ∈ Icc a b := ⟨haz.le, hzb.le⟩
  have hz : z ∈ Ioo 0 r := ⟨ha.trans haz, hzb.trans hbr⟩
  have habr : Icc a b ⊆ Ioo 0 r := fun h hh ↦
    ⟨ha.trans_le hh.1, hh.2.trans_lt hbr⟩
  have hab1 : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun h hh ↦
    ⟨(habr hh).1, (habr hh).2.trans hr1⟩
  have hphase (h : ℝ) : |P h - P z| =
      |quarterPhase lam h - quarterPhase lam z| := by
    dsimp only [P, quarterPhase]
    rw [← mul_sub, ← mul_sub]
    simp only [abs_mul, abs_abs]
  have hspan (h : ℝ) (hh : h ∈ Icc a b) : |P h - P z| ≤ Real.pi := by
    have hla : |P a - P z| ≤ Real.pi := by rw [hphase, hleft]
    have hlb : |P b - P z| ≤ Real.pi := by rw [hphase, hright]
    have hupper := hPa (habr ⟨le_rfl, (haz.trans hzb).le⟩) (habr hh) hh.1
    have hlower := hPa (habr hh) (habr ⟨(haz.trans hzb).le, le_rfl⟩) hh.2
    rw [abs_le] at hla hlb ⊢
    constructor <;> linarith [hla.1, hla.2, hlb.1, hlb.2]
  have hgeo (h : ℝ) (hh : h ∈ Icc a b) :
      z / K ≤ h ∧ h ≤ K * z ∧
        |h - z| / (K * z) ≤ ‖quarterDivisor lam κ h‖ := by
    obtain ⟨hl, hu, hd⟩ := hcell z hz h (habr hh) (hspan h hh)
    refine ⟨hl, hu, hd.trans ?_⟩
    rw [hphase, quarterDivisor, sub_eq_zero.1 hzero, norm_sub_rev]
    exact phase_chord_lower (by rw [← hphase]; exact hspan h hh)
  let M := CD * K ^ 2 / z ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsecond (h : ℝ) (hh : h ∈ Icc a b) :
      ‖deriv (deriv (quarterDivisor lam κ)) h‖ ≤ M := by
    have hd := (hDb κ h ⟨(habr hh).1, (habr hh).2.trans_le hrrD⟩).2.2
    have hzle : z ≤ K * h := by
      simpa only [mul_comm] using (div_le_iff₀ hK0).1 (hgeo h hh).1
    have hs := (sq_le_sq₀ hz.1.le (mul_nonneg hK0.le (habr hh).1.le)).2 hzle
    apply (le_div_iff₀ (sq_pos_of_pos hz.1)).2
    nlinarith [mul_le_mul_of_nonneg_right hs
      (norm_nonneg (deriv (deriv (quarterDivisor lam κ)) h)),
      mul_le_mul_of_nonneg_left hd (sq_nonneg K)]
  obtain ⟨g, g₁, hg, hgd, hgz, hgf, hg₁⟩ := smooth_linear_factor
    (contDiffOn_quarterDivisor lam κ) hzc hab1 hzero hM hsecond
  have hcoerce (h : ℝ) (hh : h ∈ Icc a b) : 1 ≤ B * z * ‖g h‖ := by
    by_cases he : h = z
    · subst h
      rw [hgz]
      have hd := (hDb κ z ⟨hz.1, hz.2.trans_le hrrD⟩).1
      nlinarith [mul_le_mul_of_nonneg_left hd hB.le]
    · have hd := (div_le_iff₀ (mul_pos hK0 hz.1)).1 (hgeo h hh).2.2
      rw [hgf h (hab1 hh), norm_smul, Real.norm_eq_abs] at hd
      have hl : 1 ≤ K * z * ‖g h‖ := by
        apply le_of_mul_le_mul_left (a := |h - z|) _ (abs_pos.2 (sub_ne_zero.2 he))
        nlinarith
      exact hl.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKB hz.1.le) (norm_nonneg _))
  have hgnz (h : ℝ) (hh : h ∈ Icc a b) : g h ≠ 0 := by
    intro he
    have hc := hcoerce h hh
    rw [he, norm_zero, mul_zero] at hc
    linarith
  let R := fun h ↦ (g h)⁻¹
  let R₁ := fun h ↦ -(g₁ h) / (g h) ^ 2
  have hR (h : ℝ) (hh : h ∈ Icc a b) : ‖R h‖ ≤ B * z := by
    rw [show ‖R h‖ = (‖g h‖)⁻¹ from norm_inv _]
    exact (inv_le_iff_one_le_mul₀ (norm_pos_iff.2 (hgnz h hh))).2 (hcoerce h hh)
  refine ⟨R, R₁, (hg.mono hab1).inv hgnz, ?_, ?_, ?_⟩
  · intro h hh
    exact (hgd h (hab1 hh)).inv (hgnz h hh)
  · intro h hh
    rw [hgf h (hab1 hh), Complex.real_smul, mul_assoc,
      mul_inv_cancel₀ (hgnz h hh), mul_one]
  · intro h hh
    refine ⟨?_, (hgeo h hh).2.1.trans (by nlinarith [hz.1]), hR h hh, ?_⟩
    · exact (div_le_div_of_nonneg_left hz.1.le hK0 hKB).trans (hgeo h hh).1
    · have hs := (sq_le_sq₀ (norm_nonneg (R h)) (mul_nonneg hB.le hz.1.le)).2 (hR h hh)
      have hm := mul_le_mul (hg₁ h hh) hs (sq_nonneg _) hM
      have he : ‖R₁ h‖ = ‖g₁ h‖ * ‖R h‖ ^ 2 := by
        dsimp only [R₁, R]
        rw [norm_div, norm_neg, norm_pow, norm_inv, div_eq_mul_inv, inv_pow]
      rw [he]
      apply hm.trans_eq
      dsimp [M]
      field_simp [hz.1.ne']

end NoEmbeddedEigenvalues
