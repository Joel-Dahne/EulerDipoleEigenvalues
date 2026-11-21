import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import NoEmbeddedEigenvalues.Virial.VirialAlgebra

/-!
# Integration by parts on the periodic lift

Blueprint: `def:square-integral`, `lem:square-integral-partial`, `lem:square-pairing`,
`lem:commutator-algebra`.

Smooth functions on the torus are modelled, as elsewhere, by their periodic lifts
to `ℝ²`; integrals over the torus are integrals over the square `[0, 2π]²`.
The basic fact is that `∫ ∂ₓ g = ∫ ∂_y g = 0` for periodic `C¹` functions `g`.
From it, the half-density generator `D` of a periodic `C²` field is
skew-symmetric for the pairing `⟨u, v⟩ = ∫ u v̄`, and so is `L₀`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function on the lift `ℝ²` that is `2π`-periodic in both variables. -/
def IsPeriodicLift (u : ℝ × ℝ → E) : Prop :=
  ∀ p : ℝ × ℝ, u (p.1 + 2 * π, p.2) = u p ∧ u (p.1, p.2 + 2 * π) = u p

/-- The square `[0, 2π]²`, a fundamental domain of the torus. -/
def periodSquare : Set (ℝ × ℝ) := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)

/-- The integral over the torus of a periodic lift, as an integral over `[0, 2π]²`. -/
def squareIntegral (g : ℝ × ℝ → E) : E := ∫ p in periodSquare, g p

theorem isCompact_periodSquare : IsCompact periodSquare :=
  isCompact_Icc.prod isCompact_Icc

omit [NormedSpace ℝ E] in
theorem integrableOn_periodSquare {g : ℝ × ℝ → E} (hg : Continuous g) :
    IntegrableOn g periodSquare :=
  hg.continuousOn.integrableOn_compact isCompact_periodSquare

/-- `∫ ∂_y g = 0` over the period square, for periodic `C¹` functions. -/
theorem squareIntegral_partialY [CompleteSpace E] {g : ℝ × ℝ → E} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodicLift g) : squareIntegral (partialY g) = 0 := by
  have hcont : Continuous (partialY g) :=
    (contDiff_partialY (n := 0) (by simpa using hg)).continuous
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hline : ∀ x, ∫ y in Icc 0 (2 * π), partialY g (x, y) = 0 := by
    intro x
    have hii : IntervalIntegrable (fun y ↦ partialY g (x, y)) volume 0 (2 * π) :=
      (hcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y ↦ g (x, y))
      (fun y _ ↦ hasDerivAt_partialY (p := (x, y)) (hd _)) hii
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ, hftc]
    simpa using congrArg (· - g (x, 0)) (hper (x, 0)).2
  rw [squareIntegral, periodSquare, Measure.volume_eq_prod,
    setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrableOn_periodSquare hcont)]
  simp [hline]

/-- `∫ ∂ₓ g = 0` over the period square, for periodic `C¹` functions. -/
theorem squareIntegral_partialX [CompleteSpace E] {g : ℝ × ℝ → E} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodicLift g) : squareIntegral (partialX g) = 0 := by
  have hcont : Continuous (partialX g) :=
    (contDiff_partialX (n := 0) (by simpa using hg)).continuous
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hline : ∀ y, ∫ x in Icc 0 (2 * π), partialX g (x, y) = 0 := by
    intro y
    have hii : IntervalIntegrable (fun x ↦ partialX g (x, y)) volume 0 (2 * π) :=
      (hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ g (x, y))
      (fun x _ ↦ hasDerivAt_partialX (p := (x, y)) (hd _)) hii
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ, hftc]
    simpa using congrArg (· - g (0, y)) (hper (0, y)).1
  have hswap : Continuous fun z : ℝ × ℝ ↦ partialX g z.swap := hcont.comp continuous_swap
  rw [squareIntegral, periodSquare, Measure.volume_eq_prod, ← setIntegral_prod_swap,
    setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrableOn_periodSquare hswap)]
  simp [hline]

/-- Partial derivatives of periodic functions are periodic. -/
theorem IsPeriodicLift.partialX {u : ℝ × ℝ → E} (h : IsPeriodicLift u) :
    IsPeriodicLift (partialX u) := by
  intro p
  constructor
  · change deriv (fun t ↦ u (t, p.2)) (p.1 + 2 * π) = deriv (fun t ↦ u (t, p.2)) p.1
    rw [← deriv_comp_add_const]
    congr 1
    funext t
    exact (h (t, p.2)).1
  · change deriv (fun t ↦ u (t, p.2 + 2 * π)) p.1 = deriv (fun t ↦ u (t, p.2)) p.1
    congr 1
    funext t
    exact (h (t, p.2)).2

theorem IsPeriodicLift.partialY {u : ℝ × ℝ → E} (h : IsPeriodicLift u) :
    IsPeriodicLift (partialY u) := by
  intro p
  constructor
  · change deriv (fun t ↦ u (p.1 + 2 * π, t)) p.2 = deriv (fun t ↦ u (p.1, t)) p.2
    congr 1
    funext t
    exact (h (p.1, t)).1
  · change deriv (fun t ↦ u (p.1, t)) (p.2 + 2 * π) = deriv (fun t ↦ u (p.1, t)) p.2
    rw [← deriv_comp_add_const]
    congr 1
    funext t
    exact (h (p.1, t)).2

theorem isPeriodicLift_sin_fst : IsPeriodicLift (fun q : ℝ × ℝ ↦ sin q.1) := fun p ↦ by
  simp [sin_add_two_pi]

theorem isPeriodicLift_sin_snd : IsPeriodicLift (fun q : ℝ × ℝ ↦ sin q.2) := fun p ↦ by
  simp [sin_add_two_pi]

/-- For the velocity `Y = (sin y, -sin x)`, which is divergence free, `D = L₀`. -/
theorem halfDensityGen_velocity (u : ℝ × ℝ → E) (p : ℝ × ℝ) :
    halfDensityGen (fun q ↦ sin q.2) (fun q ↦ -sin q.1) u p = classicalL0 u p := by
  have h : partialY (fun q : ℝ × ℝ ↦ -sin q.1) p = 0 := (hasDerivAt_const p.2 (-sin p.1)).deriv
  simp [halfDensityGen, fieldDeriv, divergence, classicalL0, h, sub_eq_add_neg]

/-! ### Complex-valued functions -/

section Complex

open ComplexConjugate

variable {u v : ℝ × ℝ → ℂ} {p : ℝ × ℝ}

theorem partialX_mul (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialX (fun q ↦ u q * v q) p = partialX u p * v p + u p * partialX v p :=
  ((hasDerivAt_partialX hu).mul (hasDerivAt_partialX hv)).deriv

theorem partialY_mul (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    partialY (fun q ↦ u q * v q) p = partialY u p * v p + u p * partialY v p :=
  ((hasDerivAt_partialY hu).mul (hasDerivAt_partialY hv)).deriv

theorem partialX_conj (hu : DifferentiableAt ℝ u p) :
    partialX (fun q ↦ conj (u q)) p = conj (partialX u p) :=
  (hasDerivAt_partialX hu).star.deriv

theorem partialY_conj (hu : DifferentiableAt ℝ u p) :
    partialY (fun q ↦ conj (u q)) p = conj (partialY u p) :=
  (hasDerivAt_partialY hu).star.deriv

theorem contDiff_conj {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun q ↦ conj (u q)) :=
  Complex.conjCLE.contDiff.comp hu

/-- The pairing `⟨u, v⟩ = ∫ u v̄` over the period square. -/
def squarePairing (u v : ℝ × ℝ → ℂ) : ℂ := squareIntegral fun p ↦ u p * conj (v p)

/-- Pointwise, `(Du) v̄ + u (Dv)‾ = div (u v̄ W)`. -/
theorem halfDensityGen_mul_conj_add {W₁ W₂ : ℝ × ℝ → ℝ} (hW₁ : Differentiable ℝ W₁)
    (hW₂ : Differentiable ℝ W₂) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (p : ℝ × ℝ) :
    halfDensityGen W₁ W₂ u p * conj (v p) + u p * conj (halfDensityGen W₁ W₂ v p) =
      partialX (fun q ↦ W₁ q • (u q * conj (v q))) p +
        partialY (fun q ↦ W₂ q • (u q * conj (v q))) p := by
  have hvc : Differentiable ℝ (fun q ↦ conj (v q)) := fun q ↦
    (Complex.conjCLE.differentiableAt).comp q (hv q)
  simp (disch := fun_prop) only [partialX_smul, partialY_smul, partialX_mul, partialY_mul,
    partialX_conj, partialY_conj]
  simp only [halfDensityGen, fieldDeriv, divergence, Complex.real_smul, map_add, map_mul,
    Complex.conj_ofReal]
  push_cast
  ring

/-- `D` is skew-symmetric: `⟨Du, v⟩ = -⟨u, Dv⟩` for periodic `C¹` data. -/
theorem squarePairing_halfDensityGen {W₁ W₂ : ℝ × ℝ → ℝ} (hW₁ : ContDiff ℝ 1 W₁)
    (hW₂ : ContDiff ℝ 1 W₂) (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hpu : IsPeriodicLift u)
    (hpv : IsPeriodicLift v) :
    squarePairing (halfDensityGen W₁ W₂ u) v = -squarePairing u (halfDensityGen W₁ W₂ v) := by
  have hc : ∀ {g : ℝ × ℝ → ℝ}, ContDiff ℝ 1 g → Continuous (partialX g) ∧
      Continuous (partialY g) := fun hg ↦
    ⟨(contDiff_partialX (n := 0) (by simpa using hg)).continuous,
      (contDiff_partialY (n := 0) (by simpa using hg)).continuous⟩
  have hcC : ∀ {g : ℝ × ℝ → ℂ}, ContDiff ℝ 1 g → Continuous (partialX g) ∧
      Continuous (partialY g) := fun hg ↦
    ⟨(contDiff_partialX (n := 0) (by simpa using hg)).continuous,
      (contDiff_partialY (n := 0) (by simpa using hg)).continuous⟩
  obtain ⟨h1x, h1y⟩ := hc hW₁
  obtain ⟨h2x, h2y⟩ := hc hW₂
  obtain ⟨hux, huy⟩ := hcC hu
  obtain ⟨hvx, hvy⟩ := hcC hv
  have hW₁c := hW₁.continuous
  have hW₂c := hW₂.continuous
  have huc := hu.continuous
  have hvc := hv.continuous
  have hD : ∀ {g : ℝ × ℝ → ℂ}, Continuous g → Continuous (partialX g) →
      Continuous (partialY g) → Continuous (halfDensityGen W₁ W₂ g) := by
    intro g hg hgx hgy
    unfold halfDensityGen fieldDeriv divergence
    fun_prop
  have hDu := hD huc hux huy
  have hDv := hD hvc hvx hvy
  -- The flux `u v̄ W` is periodic and `C¹`.
  have hG : ContDiff ℝ 1 (fun q ↦ u q * conj (v q)) := hu.mul (contDiff_conj hv)
  have hG₁ : ContDiff ℝ 1 (fun q ↦ W₁ q • (u q * conj (v q))) := hW₁.smul hG
  have hG₂ : ContDiff ℝ 1 (fun q ↦ W₂ q • (u q * conj (v q))) := hW₂.smul hG
  have hpG₁ : IsPeriodicLift (fun q ↦ W₁ q • (u q * conj (v q))) := fun q ↦ by
    simp only [(hpW₁ q).1, (hpW₁ q).2, (hpu q).1, (hpu q).2, (hpv q).1, (hpv q).2, and_self]
  have hpG₂ : IsPeriodicLift (fun q ↦ W₂ q • (u q * conj (v q))) := fun q ↦ by
    simp only [(hpW₂ q).1, (hpW₂ q).2, (hpu q).1, (hpu q).2, (hpv q).1, (hpv q).2, and_self]
  have hsum : squarePairing (halfDensityGen W₁ W₂ u) v +
      squarePairing u (halfDensityGen W₁ W₂ v) = 0 := by
    rw [squarePairing, squarePairing, squareIntegral, squareIntegral, ← integral_add
      (integrableOn_periodSquare (by fun_prop)) (integrableOn_periodSquare (by fun_prop))]
    simp_rw [halfDensityGen_mul_conj_add (hW₁.differentiable one_ne_zero)
      (hW₂.differentiable one_ne_zero) (hu.differentiable one_ne_zero)
      (hv.differentiable one_ne_zero)]
    rw [integral_add (integrableOn_periodSquare (hcC hG₁).1)
      (integrableOn_periodSquare (hcC hG₂).2)]
    have h1 := squareIntegral_partialX hG₁ hpG₁
    have h2 := squareIntegral_partialY hG₂ hpG₂
    simp only [squareIntegral] at h1 h2
    rw [h1, h2, add_zero]
  exact eq_neg_of_add_eq_zero_left hsum

/-- `L₀` is skew-symmetric: `⟨L₀u, v⟩ = -⟨u, L₀v⟩`, so `H = -iL₀` is symmetric. -/
theorem squarePairing_classicalL0 (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hpu : IsPeriodicLift u) (hpv : IsPeriodicLift v) :
    squarePairing (classicalL0 u) v = -squarePairing u (classicalL0 v) := by
  have hY₁ : ContDiff ℝ 1 (fun q : ℝ × ℝ ↦ sin q.2) := by fun_prop
  have hY₂ : ContDiff ℝ 1 (fun q : ℝ × ℝ ↦ -sin q.1) := by fun_prop
  have hpY₂ : IsPeriodicLift (fun q : ℝ × ℝ ↦ -sin q.1) := fun p ↦ by simp [sin_add_two_pi]
  have h := squarePairing_halfDensityGen hY₁ hY₂ isPeriodicLift_sin_snd hpY₂ hu hv hpu hpv
  simpa only [show ∀ g : ℝ × ℝ → ℂ, halfDensityGen (fun q ↦ sin q.2) (fun q ↦ -sin q.1) g =
    classicalL0 g from fun g ↦ funext (halfDensityGen_velocity g)] using h

theorem squarePairing_add_left {w : ℝ × ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    squarePairing (fun p ↦ u p + v p) w = squarePairing u w + squarePairing v w := by
  simp only [squarePairing, squareIntegral, add_mul]
  exact integral_add (integrableOn_periodSquare (by fun_prop))
    (integrableOn_periodSquare (by fun_prop))

theorem squarePairing_sub_left {w : ℝ × ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    squarePairing (fun p ↦ u p - v p) w = squarePairing u w - squarePairing v w := by
  simp only [squarePairing, squareIntegral, sub_mul]
  exact integral_sub (integrableOn_periodSquare (by fun_prop))
    (integrableOn_periodSquare (by fun_prop))

theorem squarePairing_const_mul_left (c : ℂ) (w : ℝ × ℝ → ℂ) :
    squarePairing (fun p ↦ c * u p) w = c * squarePairing u w := by
  simp only [squarePairing, squareIntegral, mul_assoc]
  exact integral_const_mul c _

theorem squarePairing_const_mul_right (c : ℂ) (w : ℝ × ℝ → ℂ) :
    squarePairing u (fun p ↦ c * w p) = conj c * squarePairing u w := by
  simp only [squarePairing, squareIntegral, map_mul, mul_left_comm (u _)]
  exact integral_const_mul (conj c) _

theorem squarePairing_comm (u v : ℝ × ℝ → ℂ) : squarePairing v u = conj (squarePairing u v) := by
  simp only [squarePairing, squareIntegral]
  rw [← integral_conj]
  congr 1
  funext p
  simp [mul_comm]

/-- A real multiplier moves across the pairing. -/
theorem squarePairing_real_smul (f : ℝ × ℝ → ℝ) (w : ℝ × ℝ → ℂ) :
    squarePairing (fun p ↦ f p • u p) w = squarePairing u (fun p ↦ f p • w p) := by
  simp only [squarePairing, squareIntegral]
  congr 1
  funext p
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

end Complex

end NoEmbeddedEigenvalues
