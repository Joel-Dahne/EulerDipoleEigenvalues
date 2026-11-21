module

public import NoEmbeddedEigenvalues.Certificates.Tools.Bernstein
public import NoEmbeddedEigenvalues.Certificates.Inequalities.OddOddResidual
public import Mathlib.Data.Fin.VecNotation

/-!
# The upper endpoint polynomial for the Odd–odd residual

Blueprint: `cert:dd-residual-upper`. Lean normalizes the polynomial identity
for the quotient `Q_+` and checks the rational Bernstein coefficients on each
of the four boxes separately. The power table can be reproduced with
`scripts/verify_dd_residual.py --lean-power upper`; the script is not trusted
by the proof.
-/

@[expose] public section

namespace NoEmbeddedEigenvalues

open Set

/-- Power coefficients of `Q_+`, ordered by increasing powers of `x` (rows)
and `y` (columns). -/
private def ddUpperPower : Fin 16 → Fin 10 → ℚ :=
  ![
    ![0, 0, 0, 65536, (843776 / 3), (-742400 / 3), 93184, (148480 / 3), (1068032 / 3), 0],
    ![0, 0, 393216, (6356992 / 3), (-10209280 / 3), 3221504, (2315264 / 3), (16663552 / 3),
      -4205568, -68608],
    ![0, 524288, (17088512 / 3), (-45211648 / 3), (75968512 / 3), (-2020352 / 3),
      (104212480 / 3), (-187927552 / 3), 21463040, 960512],
    ![0, 5832704, (-86228992 / 3), 83902464, (-65148928 / 3), (367904768 / 3), -390356992,
      (897836032 / 3), (-173486080 / 3), -6243328],
    ![(2424832 / 3), -25346048, (416890880 / 3), (-169705472 / 3), (765079552 / 3),
      (-4060341248 / 3), (5180594176 / 3), (-2352984064 / 3), 64699392, 24973312],
    ![(-33980416 / 3), 117932032, -30244864, (833060864 / 3), (-8612288512 / 3), 5491236864,
      (-12330268672 / 3), (3249848320 / 3), 107244544, -68676608],
    ![(116916224 / 3), 55951360, 100319232, (-11571666944 / 3), (31747698688 / 3),
      (-34513263616 / 3), 5175500800, (-343660544 / 3), (-1850877952 / 3), 137353216],
    ![57638912, -28278784, -3307749376, (38061654016 / 3), (-56526874624 / 3), 12030035968,
      -953970688, -2823350272, 1391892480, -206029824],
    ![8060928, -1729331200, (27580350464 / 3), (-54440280064 / 3), (44042776576 / 3), 199944192,
      -9035977728, 6629297152, -2032419840, 235462656],
    ![-411238400, 3551035392, (-28486696960 / 3), 8258289664, (19554279424 / 3),
      (-60989925376 / 3), 18824616960, (-26476444672 / 3), (6350046208 / 3), -206029824],
    ![(1488977920 / 3), -2084241408, (888012800 / 3), 12370755584, -29442727936, 33190506496,
      (-63963441152 / 3), (23924188160 / 3), -1617285120, 137353216],
    ![(-135921664 / 3), -1488060416, (29281058816 / 3), -25234243584, 35535060992,
      (-90534916096 / 3), (47711031296 / 3), (-15272619008 / 3), 906084352, -68676608],
    ![(-1090256896 / 3), 3309961216, (-34873016320 / 3), 21787213824, (-73848848384 / 3),
      (52866654208 / 3), -8057700352, (6842451968 / 3), (-1091548160 / 3), 24973312],
    ![(1105985536 / 3), -2449866752, (20613890048 / 3), -10784636928, (31508463616 / 3),
      (-19822649344 / 3), (8077291520 / 3), (-2059225088 / 3), 99456000, -6243328],
    ![(-485490688 / 3), 900726784, -2173435904, 2989490176, (-7758118912 / 3), 1460174848,
      (-1615364096 / 3), (375259136 / 3), -16611328, 960512],
    ![(83886080 / 3), -136839168, 293601280, (-1086717952 / 3), (849379328 / 3),
      (-436060160 / 3), 49004544, (-31375360 / 3), (3844096 / 3), -68608]]

/-- Numerator after clearing the upper logarithm bound's denominators. -/
private noncomputable def ddUpperNumerator (s r : ℝ) : ℝ :=
  r * (ddResidualA s r * (r + 2) ^ 3 + r * ddResidualB s r *
    ((r - 2) * (r + 2) ^ 2 / 2 + (r - 2) ^ 3 / 6))

/-- Removing the common boundary factor gives the tabulated quotient. -/
private theorem ddUpperPower_identity (x y : ℝ) :
    ddUpperNumerator (2 * x) (2 * (1 - x) * (2 * x + (1 - x) * y)) =
      (1 - x) ^ 4 * certificatePolynomial ddUpperPower x y := by
  simp [certificatePolynomial, Fin.sum_univ_succ, ddUpperPower, ddUpperNumerator,
    ddResidualA, ddResidualB]
  ring

private theorem ddUpper_bottom_left_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddUpperPower 0 (1 / 4) 0 (1 / 2) i j := by
  decide +kernel

private theorem ddUpper_bottom_right_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddUpperPower (1 / 4) (1 / 2) 0 (1 / 2) i j := by
  decide +kernel

private theorem ddUpper_top_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddUpperPower 0 (1 / 2) (1 / 2) 1 i j := by
  decide +kernel

private theorem ddUpper_right_coeff_nonneg :
    ∀ i j, 0 ≤ certificateBoxCoeff ddUpperPower (1 / 2) 1 0 1 i j := by
  decide +kernel

private theorem ddUpperPower_nonneg {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ certificatePolynomial ddUpperPower x y := by
  rcases le_total x (1 / 2) with hx' | hx'
  · rcases le_total y (1 / 2) with hy' | hy'
    · rcases le_total x (1 / 4) with hx'' | hx''
      · exact certificate_bernstein_nonneg ddUpperPower (by norm_num) (by norm_num)
          ddUpper_bottom_left_coeff_nonneg (by norm_num; exact ⟨hx.1, hx''⟩)
          (by norm_num; exact ⟨hy.1, hy'⟩)
      · exact certificate_bernstein_nonneg ddUpperPower (by norm_num) (by norm_num)
          ddUpper_bottom_right_coeff_nonneg (by norm_num; exact ⟨hx'', hx'⟩)
          (by norm_num; exact ⟨hy.1, hy'⟩)
    · exact certificate_bernstein_nonneg ddUpperPower (by norm_num) (by norm_num)
        ddUpper_top_coeff_nonneg (by norm_num; exact ⟨hx.1, hx'⟩)
        (by norm_num; exact ⟨hy', hy.2⟩)
  · exact certificate_bernstein_nonneg ddUpperPower (by norm_num) (by norm_num)
      ddUpper_right_coeff_nonneg (by norm_num; exact ⟨hx', hx.2⟩) (by norm_num; exact hy)

/-- The odd–odd residual with `log (r/2)` replaced by the upper ratio bound. -/
theorem dd_residual_upper_nonneg {s r : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hrlo : s * (2 - s) ≤ r) (hrhi : r ≤ 2 - s ^ 2 / 2) :
    0 ≤ s * ddResidualA s r / (384 * r ^ 3) + s * ddResidualB s r / (1536 * r ^ 2) *
      (2 * (r - 2) / (r + 2) + 2 * (r - 2) ^ 3 / (3 * (r + 2) ^ 3)) := by
  have hr : 0 < r := (mul_pos hs (sub_pos.mpr hs2)).trans_le hrlo
  have h2 : 0 < r + 2 := by positivity
  obtain ⟨x, hx, y, hy, hsx, hry⟩ := dd_residual_box_coordinates hs hs2 hrlo hrhi
  have hclear := ddUpperPower_identity x y
  rw [hry, hsx] at hclear
  have hprod : 0 ≤ ddUpperNumerator s r := by
    rw [hclear]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (ddUpperPower_nonneg hx hy)
  calc
    0 ≤ s / (384 * r ^ 4 * (r + 2) ^ 3) * ddUpperNumerator s r :=
      mul_nonneg (by positivity) hprod
    _ = _ := by unfold ddUpperNumerator; field_simp [hr.ne', h2.ne']; ring

end NoEmbeddedEigenvalues
