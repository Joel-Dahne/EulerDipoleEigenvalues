module

public import EulerDipoleEigenvalues.Certificates.Tools.Bernstein
public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddAData
public import EulerDipoleEigenvalues.Mixed.PositiveComparisons.MixedComparison

/-!
# Clearing the mixed odd-in-a residual

The exponent has denominator `2000 * S^6`, with `S = h + k`.
Writing all partials with a common power of `S` keeps the denominator
clearing separate from the expanded power tables.
-/

@[expose] public section

namespace EulerDipoleEigenvalues

open Filter
open scoped Topology

noncomputable section

/-- First-order coefficients in the normalized odd-in-a reduction. -/
def mixedOddACoeffH (p : ℝ × ℝ) : ℝ :=
  3 * p.1 * mixedD p - (1 - p.1 ^ 2) * partialX mixedD p +
    (1 - p.1 ^ 2) * (p.2 * mixedC p - (1 - p.2 ^ 2) * partialY mixedC p)

def mixedOddACoeffK (p : ℝ × ℝ) : ℝ :=
  (1 - p.2 ^ 2) * (-(1 - p.1 ^ 2) * partialX mixedC p +
    3 * p.1 * mixedC p - partialY mixedD p) + p.2 * mixedD p

def mixedOddACoeffZero (p : ℝ × ℝ) : ℝ :=
  mixedD p + p.1 * partialX mixedD p - p.1 * p.2 * mixedC p +
    p.1 * (1 - p.2 ^ 2) * partialY mixedC p + mixedV p

/-- Rational normalized odd-in-a residual; division by the comparison has removed
    the positive exponential before any polynomial denominator clearing. -/
def mixedOddAResidual (p : ℝ × ℝ) : ℝ :=
  mixedOddACoeffZero p + mixedOddACoeffH p * partialX mixedOddAExponent p +
    mixedOddACoeffK p * partialY mixedOddAExponent p -
    mixedD p * ((1 - p.1 ^ 2) *
      (partialX (partialX mixedOddAExponent) p + partialX mixedOddAExponent p ^ 2) +
      (1 - p.2 ^ 2) *
        (partialY (partialY mixedOddAExponent) p + partialY mixedOddAExponent p ^ 2)) -
    2 * mixedC p * (1 - p.1 ^ 2) * (1 - p.2 ^ 2) *
      (partialY (partialX mixedOddAExponent) p +
        partialX mixedOddAExponent p * partialY mixedOddAExponent p) - p.1 ^ 2 / 200

-- Numerator of the exponent and its first and second partials, with the
-- powers of S kept factored. Partial differentiation here includes S = h + k.
private def m (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^6 * (106) +
      h^5 * (74 * k - 526) +
      h^4 * (248 * k^2 + 1354 * k - 480) +
      h^3 * (-1684 * k^3 - 1166 * k + 1562) +
      h^2 * (1780 * k^4 - 158 * k^2 - 196) +
      h * (-800 * k^5 - 52 * k^3 - 128 * k^2 - 1038 * k - 1) +
      170 * k^6 + 120 * k^4 - 214 * k^3 + 1442 * k^2 - 8 * k) +
  s ^ 5 * (448 * h^4) +
  s ^ 4 * (-8 * h^3) +
  s ^ 2 * (-5488 * h^6) +
  s * (470 * h^8) +
  (2066 * h^8)

private def mx (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^5 * (636) +
      h^4 * (370 * k - 2630) +
      h^3 * (992 * k^2 + 5416 * k - 1920) +
      h^2 * (-5052 * k^3 - 3498 * k + 4686) +
      h * (3560 * k^4 - 316 * k^2 - 392) +
      -800 * k^5 - 52 * k^3 - 128 * k^2 - 1038 * k - 1) +
  s ^ 5 * (
      h^6 * (636) +
      h^5 * (444 * k - 3156) +
      h^4 * (1488 * k^2 + 8124 * k - 2880) +
      h^3 * (-10104 * k^3 - 6996 * k + 11164) +
      h^2 * (10680 * k^4 - 948 * k^2 - 1176) +
      h * (-4800 * k^5 - 312 * k^3 - 768 * k^2 - 6228 * k - 6) +
      1020 * k^6 + 720 * k^4 - 1284 * k^3 + 8652 * k^2 - 48 * k) +
  s ^ 4 * (
      h^4 * (2240) +
      h^2 * (-24)) +
  s ^ 3 * (-32 * h^3) +
  s ^ 2 * (-32928 * h^5) +
  s * (
      h^7 * (3760) +
      h^6 * (-10976)) +
  (
      h^8 * (470) +
      h^7 * (16528))

private def my (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^5 * (74) +
      h^4 * (496 * k + 1354) +
      h^3 * (-5052 * k^2 - 1166) +
      h^2 * (7120 * k^3 - 316 * k) +
      h * (-4000 * k^4 - 156 * k^2 - 256 * k - 1038) +
      1020 * k^5 + 480 * k^3 - 642 * k^2 + 2884 * k - 8) +
  s ^ 5 * (
      h^6 * (636) +
      h^5 * (444 * k - 3156) +
      h^4 * (1488 * k^2 + 8124 * k - 2880) +
      h^3 * (-10104 * k^3 - 6996 * k + 9372) +
      h^2 * (10680 * k^4 - 948 * k^2 - 1176) +
      h * (-4800 * k^5 - 312 * k^3 - 768 * k^2 - 6228 * k - 6) +
      1020 * k^6 + 720 * k^4 - 1284 * k^3 + 8652 * k^2 - 48 * k) +
  s ^ 4 * (2240 * h^4) +
  s ^ 3 * (-32 * h^3) +
  s * (-10976 * h^6) +
  (470 * h^8)

private def mxx (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^4 * (3180) +
      h^3 * (1480 * k - 10520) +
      h^2 * (2976 * k^2 + 16248 * k - 5760) +
      h * (-10104 * k^3 - 6996 * k + 9372) +
      3560 * k^4 - 316 * k^2 - 392) +
  s ^ 5 * (
      h^5 * (7632) +
      h^4 * (4440 * k - 31560) +
      h^3 * (11904 * k^2 + 64992 * k - 23040) +
      h^2 * (-60624 * k^3 - 41976 * k + 61608) +
      h * (42720 * k^4 - 3792 * k^2 - 4704) +
      -9600 * k^5 - 624 * k^3 - 1536 * k^2 - 12456 * k - 12) +
  s ^ 4 * (
      h^6 * (3180) +
      h^5 * (2220 * k - 15780) +
      h^4 * (7440 * k^2 + 40620 * k - 14400) +
      h^3 * (-50520 * k^3 - 34980 * k + 64780) +
      h^2 * (53400 * k^4 - 4740 * k^2 - 5880) +
      h * (-24000 * k^5 - 1560 * k^3 - 3840 * k^2 - 31140 * k - 78) +
      5100 * k^6 + 3600 * k^4 - 6420 * k^3 + 43260 * k^2 - 240 * k) +
  s ^ 3 * (
      h^4 * (8960) +
      h^2 * (-192)) +
  s ^ 2 * (
      h^4 * (-164640) +
      h^3 * (-96)) +
  s * (
      h^6 * (26320) +
      h^5 * (-131712)) +
  (
      h^7 * (7520) +
      h^6 * (104720))

private def mxy (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^4 * (370) +
      h^3 * (1984 * k + 5416) +
      h^2 * (-15156 * k^2 - 3498) +
      h * (14240 * k^3 - 632 * k) +
      -4000 * k^4 - 156 * k^2 - 256 * k - 1038) +
  s ^ 5 * (
      h^5 * (4260) +
      h^4 * (5196 * k - 7656) +
      h^3 * (-24360 * k^2 + 32496 * k - 18516) +
      h^2 * (12408 * k^3 - 22884 * k + 28116) +
      h * (-2640 * k^4 - 2832 * k^2 - 1536 * k - 8580) +
      1320 * k^5 + 2568 * k^3 - 4620 * k^2 + 11076 * k - 54) +
  s ^ 4 * (
      h^6 * (3180) +
      h^5 * (2220 * k - 15780) +
      h^4 * (7440 * k^2 + 40620 * k - 14400) +
      h^3 * (-50520 * k^3 - 34980 * k + 55820) +
      h^2 * (53400 * k^4 - 4740 * k^2 - 5880) +
      h * (-24000 * k^5 - 1560 * k^3 - 3840 * k^2 - 31140 * k - 30) +
      5100 * k^6 + 3600 * k^4 - 6420 * k^3 + 43260 * k^2 - 240 * k) +
  s ^ 3 * (
      h^4 * (8960) +
      h^2 * (-96)) +
  s ^ 2 * (-96 * h^3) +
  s * (-65856 * h^5) +
  (
      h^7 * (3760) +
      h^6 * (-10976))

private def myy (h k s : ℝ) : ℝ :=
  s ^ 6 * (
      h^4 * (496) +
      h^3 * (-10104 * k) +
      h^2 * (21360 * k^2 - 316) +
      h * (-16000 * k^3 - 312 * k - 256) +
      5100 * k^4 + 1440 * k^2 - 1284 * k + 2884) +
  s ^ 5 * (
      h^5 * (888) +
      h^4 * (5952 * k + 16248) +
      h^3 * (-60624 * k^2 - 13992) +
      h^2 * (85440 * k^3 - 3792 * k) +
      h * (-48000 * k^4 - 1872 * k^2 - 3072 * k - 12456) +
      12240 * k^5 + 5760 * k^3 - 7704 * k^2 + 34608 * k - 96) +
  s ^ 4 * (
      h^6 * (3180) +
      h^5 * (2220 * k - 15780) +
      h^4 * (7440 * k^2 + 40620 * k - 14400) +
      h^3 * (-50520 * k^3 - 34980 * k + 46860) +
      h^2 * (53400 * k^4 - 4740 * k^2 - 5880) +
      h * (-24000 * k^5 - 1560 * k^3 - 3840 * k^2 - 31140 * k - 30) +
      5100 * k^6 + 3600 * k^4 - 6420 * k^3 + 43260 * k^2 - 240 * k) +
  s ^ 3 * (8960 * h^4) +
  s ^ 2 * (-96 * h^3) +
  (-10976 * h^6)


private theorem exponent_num (h k : ℝ) (hs : h + k ≠ 0) :
    mixedOddAExponent (h, k) = m h k (h + k) / (2000 * (h + k) ^ 6) := by
  unfold mixedOddAExponent mixedOddAPolynomial m
  dsimp only
  field_simp [hs]
  ring

private theorem deriv_over_pow {f : ℝ → ℝ} {a b w : ℝ} {n : ℕ}
    (hf : DifferentiableAt ℝ f a) (hs : a + b ≠ 0) (hw : w ≠ 0) :
    deriv (fun x ↦ f x / (w * (x + b) ^ (n + 1))) a =
      ((a + b) * deriv f a - (n + 1 : ℕ) * f a) /
        (w * (a + b) ^ (n + 2)) := by
  have hd := (((hasDerivAt_id a).add_const b).pow (n + 1)).const_mul w
  have he := (hf.hasDerivAt.div hd (mul_ne_zero hw (pow_ne_zero _ hs))).deriv
  change deriv (fun x ↦ f x / (w * (x + b) ^ (n + 1))) a = _ at he
  rw [he]
  simp only [Pi.pow_apply, mul_one, id_eq, Nat.add_sub_cancel]
  simp only [pow_succ (a + b) (n + 1), pow_succ (a + b) n]
  push_cast
  field_simp [hs, hw, pow_ne_zero n hs]

-- The quotient rule with the fixed coordinate on the other side of the sum.
private theorem deriv_over_pow' {f : ℝ → ℝ} {a b w : ℝ} {n : ℕ}
    (hf : DifferentiableAt ℝ f a) (hs : b + a ≠ 0) (hw : w ≠ 0) :
    deriv (fun x ↦ f x / (w * (b + x) ^ (n + 1))) a =
      ((b + a) * deriv f a - (n + 1 : ℕ) * f a) /
        (w * (b + a) ^ (n + 2)) := by
  simpa only [add_comm b] using deriv_over_pow (n := n) hf
    (show a + b ≠ 0 by rwa [add_comm]) hw

private theorem deriv_comp_pow {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a) (n : ℕ) :
    deriv (fun x ↦ f x ^ n) a = n * f a ^ (n - 1) * deriv f a :=
  (hf.hasDerivAt.pow n).deriv

private theorem deriv_mx (h k : ℝ) :
    deriv (fun x ↦ m x k (x + k)) h = mx h k (h + k) := by
  unfold m mx
  simp (disch := fun_prop) only [deriv_const, deriv_pow_field, deriv_comp_pow,
    deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_id'']
  ring

private theorem deriv_my (h k : ℝ) :
    deriv (fun y ↦ m h y (h + y)) k = my h k (h + k) := by
  unfold m my
  simp (disch := fun_prop) only [deriv_const, deriv_pow_field, deriv_comp_pow,
    deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const_add_id, deriv_const_mul_id]
  ring

private theorem deriv_mxx (h k : ℝ) :
    deriv (fun x ↦ mx x k (x + k)) h = mxx h k (h + k) := by
  unfold mx mxx
  simp (disch := fun_prop) only [deriv_const, deriv_pow_field, deriv_comp_pow,
    deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_id'']
  ring

private theorem deriv_mxy (h k : ℝ) :
    deriv (fun y ↦ mx h y (h + y)) k = mxy h k (h + k) := by
  unfold mx mxy
  simp (disch := fun_prop) only [deriv_const, deriv_pow_field, deriv_comp_pow,
    deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const_add_id, deriv_const_mul_id]
  ring

private theorem deriv_myy (h k : ℝ) :
    deriv (fun y ↦ my h y (h + y)) k = myy h k (h + k) := by
  unfold my myy
  simp (disch := fun_prop) only [deriv_const, deriv_pow_field, deriv_comp_pow,
    deriv_fun_mul, deriv_fun_add, deriv_fun_sub, deriv_const_add_id, deriv_const_mul_id]
  ring

private def fx (h k s : ℝ) : ℝ := s * mx h k s - 6 * m h k s
private def fy (h k s : ℝ) : ℝ := s * my h k s - 6 * m h k s
private def fxx (h k s : ℝ) : ℝ := s ^ 2 * mxx h k s - 12 * s * mx h k s + 42 * m h k s
private def fxy (h k s : ℝ) : ℝ :=
  s ^ 2 * mxy h k s - 6 * s * (mx h k s + my h k s) + 42 * m h k s
private def fyy (h k s : ℝ) : ℝ := s ^ 2 * myy h k s - 12 * s * my h k s + 42 * m h k s

private theorem exponent_x (h k : ℝ) (hs : h + k ≠ 0) :
    partialX mixedOddAExponent (h, k) = fx h k (h + k) / (2000 * (h + k) ^ 7) := by
  have he : (fun x ↦ mixedOddAExponent (x, k)) =ᶠ[𝓝 h]
      fun x ↦ m x k (x + k) / (2000 * (x + k) ^ 6) := by
    filter_upwards [(continuous_id.add_const k).continuousAt.eventually_ne hs] with x hx
    exact exponent_num x k hx
  unfold partialX
  dsimp only
  rw [he.deriv_eq, deriv_over_pow (n := 5) (by unfold m; fun_prop) hs (by norm_num),
    deriv_mx]
  norm_num [fx]

private theorem exponent_y (h k : ℝ) (hs : h + k ≠ 0) :
    partialY mixedOddAExponent (h, k) = fy h k (h + k) / (2000 * (h + k) ^ 7) := by
  have he : (fun y ↦ mixedOddAExponent (h, y)) =ᶠ[𝓝 k]
      fun y ↦ m h y (h + y) / (2000 * (h + y) ^ 6) := by
    have hc : Continuous (fun y : ℝ ↦ h + y) := continuous_const.add continuous_id
    filter_upwards [hc.continuousAt.eventually_ne hs] with y hy
    exact exponent_num h y hy
  unfold partialY
  dsimp only
  rw [he.deriv_eq, deriv_over_pow' (n := 5) (by unfold m; fun_prop) hs (by norm_num),
    deriv_my]
  norm_num [fy]

private theorem exponent_xx (h k : ℝ) (hs : h + k ≠ 0) :
    partialX (partialX mixedOddAExponent) (h, k) =
      fxx h k (h + k) / (2000 * (h + k) ^ 8) := by
  have he : (fun x ↦ partialX mixedOddAExponent (x, k)) =ᶠ[𝓝 h]
      fun x ↦ fx x k (x + k) / (2000 * (x + k) ^ 7) := by
    filter_upwards [(continuous_id.add_const k).continuousAt.eventually_ne hs] with x hx
    exact exponent_x x k hx
  unfold partialX at *
  dsimp only at *
  rw [he.deriv_eq, deriv_over_pow (n := 6) (by unfold fx mx m; fun_prop) hs (by norm_num)]
  have hp : HasDerivAt (fun x ↦ mx x k (x + k)) (mxx h k (h + k)) h := by
    rw [← deriv_mxx]
    exact (show DifferentiableAt ℝ _ h by unfold mx; fun_prop).hasDerivAt
  have hm : HasDerivAt (fun x ↦ m x k (x + k)) (mx h k (h + k)) h := by
    rw [← deriv_mx]
    exact (show DifferentiableAt ℝ _ h by unfold m; fun_prop).hasDerivAt
  have he' := ((((hasDerivAt_id h).add_const k).mul hp).sub (hm.const_mul 6)).deriv
  change deriv (fun x ↦ fx x k (x + k)) h = _ at he'
  rw [he']
  norm_num only [Nat.cast_ofNat, id_eq, one_mul, mul_one]
  congr 1
  unfold fxx fx
  ring

private theorem exponent_xy (h k : ℝ) (hs : h + k ≠ 0) :
    partialY (partialX mixedOddAExponent) (h, k) =
      fxy h k (h + k) / (2000 * (h + k) ^ 8) := by
  have he : (fun y ↦ partialX mixedOddAExponent (h, y)) =ᶠ[𝓝 k]
      fun y ↦ fx h y (h + y) / (2000 * (h + y) ^ 7) := by
    have hc : Continuous (fun y : ℝ ↦ h + y) := continuous_const.add continuous_id
    filter_upwards [hc.continuousAt.eventually_ne hs] with y hy
    exact exponent_x h y hy
  unfold partialY
  dsimp only
  rw [he.deriv_eq, deriv_over_pow' (n := 6) (by unfold fx mx m; fun_prop) hs (by norm_num)]
  have hp : HasDerivAt (fun y ↦ mx h y (h + y)) (mxy h k (h + k)) k := by
    rw [← deriv_mxy]
    exact (show DifferentiableAt ℝ _ k by unfold mx; fun_prop).hasDerivAt
  have hm : HasDerivAt (fun y ↦ m h y (h + y)) (my h k (h + k)) k := by
    rw [← deriv_my]
    exact (show DifferentiableAt ℝ _ k by unfold m; fun_prop).hasDerivAt
  have he' := ((((hasDerivAt_id k).const_add h).mul hp).sub (hm.const_mul 6)).deriv
  change deriv (fun y ↦ fx h y (h + y)) k = _ at he'
  rw [he']
  norm_num only [Nat.cast_ofNat, id_eq, one_mul, mul_one]
  congr 1
  unfold fxy fx
  ring

private theorem exponent_yy (h k : ℝ) (hs : h + k ≠ 0) :
    partialY (partialY mixedOddAExponent) (h, k) =
      fyy h k (h + k) / (2000 * (h + k) ^ 8) := by
  have he : (fun y ↦ partialY mixedOddAExponent (h, y)) =ᶠ[𝓝 k]
      fun y ↦ fy h y (h + y) / (2000 * (h + y) ^ 7) := by
    have hc : Continuous (fun y : ℝ ↦ h + y) := continuous_const.add continuous_id
    filter_upwards [hc.continuousAt.eventually_ne hs] with y hy
    exact exponent_y h y hy
  unfold partialY at *
  dsimp only at *
  rw [he.deriv_eq, deriv_over_pow' (n := 6) (by unfold fy my m; fun_prop) hs (by norm_num)]
  have hp : HasDerivAt (fun y ↦ my h y (h + y)) (myy h k (h + k)) k := by
    rw [← deriv_myy]
    exact (show DifferentiableAt ℝ _ k by unfold my; fun_prop).hasDerivAt
  have hm : HasDerivAt (fun y ↦ m h y (h + y)) (my h k (h + k)) k := by
    rw [← deriv_my]
    exact (show DifferentiableAt ℝ _ k by unfold m; fun_prop).hasDerivAt
  have he' := ((((hasDerivAt_id k).const_add h).mul hp).sub (hm.const_mul 6)).deriv
  change deriv (fun y ↦ fy h y (h + y)) k = _ at he'
  rw [he']
  norm_num only [Nat.cast_ofNat, id_eq, one_mul, mul_one]
  congr 1
  unfold fyy fy
  ring

private def dNum (h s : ℝ) : ℝ := h ^ 2 * s + 2 * h * (1 - h ^ 2)
private def cNum (h : ℝ) : ℝ := 2 * h ^ 2
private def dxNum (h s : ℝ) : ℝ :=
  s * (2 * h * s + h ^ 2 + 2 - 6 * h ^ 2) - dNum h s
private def dyNum (h s : ℝ) : ℝ := s * h ^ 2 - dNum h s
private def cxNum (h s : ℝ) : ℝ := s * (4 * h) - 2 * cNum h
private def cyNum (h : ℝ) : ℝ := -2 * cNum h

private theorem matrix_partials (h k : ℝ) (hs : h + k ≠ 0) :
    partialX mixedD (h, k) = dxNum h (h + k) / (h + k) ^ 2 ∧
    partialY mixedD (h, k) = dyNum h (h + k) / (h + k) ^ 2 ∧
    partialX mixedC (h, k) = cxNum h (h + k) / (h + k) ^ 3 ∧
    partialY mixedC (h, k) = cyNum h / (h + k) ^ 3 := by
  have hx : deriv (fun x : ℝ ↦ x + k) h = 1 := ((hasDerivAt_id h).add_const k).deriv
  have hy : deriv (fun y : ℝ ↦ h + y) k = 1 := ((hasDerivAt_id k).const_add h).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [partialX, partialY, mixedD, mixedC, dxNum, dyNum, cxNum, cyNum, dNum, cNum]
    simp (disch := first | positivity | assumption | fun_prop)
      only [deriv_fun_div, deriv_fun_add, deriv_fun_mul, deriv_fun_sub, deriv_const,
        deriv_const_mul_id, deriv_pow_field, deriv_comp_pow, hx, hy]
    field_simp [hs]
    ring

private def ahNum (h k s u v : ℝ) : ℝ :=
  3 * h * dNum h s * s ^ 2 - u * dxNum h s * s + u * (k * cNum h * s - v * cyNum h)
private def akNum (h k s u v : ℝ) : ℝ :=
  v * (-u * cxNum h s + 3 * h * cNum h * s - dyNum h s * s) + k * dNum h s * s ^ 2
private def a0Num (h k s r u v : ℝ) : ℝ :=
  (dNum h s * s ^ 2 + h * dxNum h s * s - h * k * cNum h * s + h * v * cyNum h) * r +
    s * (-h ^ 2 * r ^ 2 + 2 * h * u * s * r - 2 * u ^ 2 * s ^ 2)

private theorem first_order_clear (h k : ℝ) (hs : h + k ≠ 0)
    (hr : 2 - h ^ 2 - k ^ 2 ≠ 0) :
    let s := h + k
    let r := 2 - h ^ 2 - k ^ 2
    let u := 1 - h ^ 2
    let v := 1 - k ^ 2
    mixedD (h, k) = dNum h s / s ∧
    mixedC (h, k) = cNum h / s ^ 2 ∧
    mixedOddACoeffH (h, k) = ahNum h k s u v / s ^ 3 ∧
    mixedOddACoeffK (h, k) = akNum h k s u v / s ^ 3 ∧
    mixedOddACoeffZero (h, k) = a0Num h k s r u v / (s ^ 3 * r) := by
  obtain ⟨hdx, hdy, hcx, hcy⟩ := matrix_partials h k hs
  have hd : mixedD (h, k) = dNum h (h + k) / (h + k) := by
    unfold mixedD dNum
    dsimp only
    field_simp [hs]
  dsimp only
  refine ⟨hd, rfl, ?_, ?_, ?_⟩
  all_goals
    first | unfold mixedOddACoeffH | unfold mixedOddACoeffK | unfold mixedOddACoeffZero
    simp only [hd, hdx, hdy, hcx, hcy, mixedC, mixedV, ahNum, akNum, a0Num, cNum]
    field_simp [hs, hr]

/-- Cleared numerator, with an extra positive integer scale for integer tables. -/
@[no_expose] def mixedOddAScaledNumerator (h k : ℝ) : ℝ :=
  let s := h + k
  let r := 2 - h ^ 2 - k ^ 2
  let u := 1 - h ^ 2
  let v := 1 - k ^ 2
  let x := fx h k s
  let y := fy h k s
  let w : ℝ := 2000
  w ^ 2 * a0Num h k s r u v * s ^ 13 - 20000 * h ^ 2 * r * s ^ 16 +
    (ahNum h k s u v * x + akNum h k s u v * y) * w * r * s ^ 6 -
    dNum h s * r * s * (u * (w * s ^ 6 * fxx h k s + x ^ 2) +
      v * (w * s ^ 6 * fyy h k s + y ^ 2)) -
    2 * cNum h * u * v * r * (w * s ^ 6 * fxy h k s + x * y)

theorem mixed_odd_a_clear (h k : ℝ) (hs : h + k ≠ 0) (hr : 2 - h ^ 2 - k ^ 2 ≠ 0) :
    mixedOddAScaledNumerator h k =
      2000 ^ 2 * (h + k) ^ 16 * (2 - h ^ 2 - k ^ 2) * mixedOddAResidual (h, k) := by
  obtain ⟨hd, hc, hh, hk, h₀⟩ := first_order_clear h k hs hr
  unfold mixedOddAScaledNumerator mixedOddAResidual
  rw [hd, hc, hh, hk, h₀, exponent_x h k hs, exponent_y h k hs,
    exponent_xx h k hs, exponent_xy h k hs, exponent_yy h k hs]
  generalize h + k = s at hs ⊢
  generalize 2 - h ^ 2 - k ^ 2 = r at hr ⊢
  dsimp only
  field_simp [hs, hr]
  ring

/-- The rational power table for triangle 1. -/
def mixedOddAPower1 (i : Fin 18) (j : Fin 33) : ℚ := mixedOddAPowerInt1 i j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- Normalize the expanded 18 by 33 coefficient table against the factored numerator.
/-- The triangle 1 change of variables extracts the common radial factor. -/
theorem mixed_odd_a_power1_identity (t q : ℝ) :
    mixedOddAScaledNumerator (t * q) t =
      t ^ 15 * certificatePolynomial mixedOddAPower1 t q := by
  unfold mixedOddAScaledNumerator a0Num ahNum akNum dxNum dyNum cxNum cyNum
    dNum cNum fx fy fxx fxy fyy m mx my mxx mxy myy
  simp [certificatePolynomial, Fin.sum_univ_succ, mixedOddAPower1, mixedOddAPowerInt1]
  ring

/-- The rational power table for triangle 2. -/
def mixedOddAPower2 (i : Fin 18) (j : Fin 31) : ℚ := mixedOddAPowerInt2 i j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- Normalize the expanded 18 by 31 coefficient table against the factored numerator.
/-- The triangle 2 change of variables extracts the common radial factor. -/
theorem mixed_odd_a_power2_identity (t q : ℝ) :
    mixedOddAScaledNumerator t (t * q) =
      t ^ 15 * certificatePolynomial mixedOddAPower2 t q := by
  unfold mixedOddAScaledNumerator a0Num ahNum akNum dxNum dyNum cxNum cyNum
    dNum cNum fx fy fxx fxy fyy m mx my mxx mxy myy
  simp [certificatePolynomial, Fin.sum_univ_succ, mixedOddAPower2, mixedOddAPowerInt2]
  ring

end

end EulerDipoleEigenvalues
