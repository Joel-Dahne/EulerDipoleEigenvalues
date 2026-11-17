import NoEmbeddedEigenvalues.OrbitNumeratorDerivative

/-!
# The weak moving-endpoint derivative of the half numerator

Blueprint: `lem:half-numerator-moving-endpoints`.

The fixed upper endpoint is physical time zero. Its angular flux vanishes
because its angular coordinate is zero, not because the forcing vanishes
there. The remaining endpoint is the original continuous forcing at negative
eighth-period time. No raw gradient is evaluated on an endpoint ray.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The half numerator's exact fixed-time bulk and negative-endpoint derivative. -/
def quarterHalfNumeratorDerivative (lam : ℝ) (g : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  (∫ t in (-eighthPeriod h)..0,
    quarterForcingLevelDerivative D (h, t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) +
  ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (-eighthPeriod h)) *
      Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ)))

/-- Normalization of any negative half-quarter time integral. -/
theorem quarterHalfIntervalIntegral_eq_normalized (h : ℝ) (F : ℝ → ℂ) :
    (∫ t in (-eighthPeriod h)..0, F t) =
      ∫ θ in Icc (-1 / 8 : ℝ) 0, (orbitPeriod h : ℂ) * F (θ * orbitPeriod h) := by
  have he := intervalIntegral.smul_integral_comp_mul_right F
    (a := (-1 / 8 : ℝ)) (b := 0) (orbitPeriod h)
  have hm : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by unfold orbitPeriod; ring
  rw [hm, zero_mul] at he
  rw [← he, Complex.real_smul, ← intervalIntegral.integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by norm_num : (-1 / 8 : ℝ) ≤ 0)]

/-- The original continuous forcing on its fixed negative angular window. -/
theorem quarterHalfNumerator_eq_normalized (lam : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ) :
    quarterHalfNumerator lam g h = ∫ θ in Icc (-1 / 8 : ℝ) 0,
      (orbitPeriod h : ℂ) *
        Complex.exp (-Complex.I * ((lam * (θ * orbitPeriod h) : ℝ) : ℂ)) *
          g (actionAngleInv (h, θ)) := by
  rw [quarterHalfNumerator, quarterHalfIntervalIntegral_eq_normalized]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only [actionAngleInv]
  ring

/-- Compatible local H¹ data use the original continuous forcing and its
specified first weak gradient. No zero midpoint or endpoint premise is needed. -/
theorem quarterHalfNumerator_hasIntervalH1_derivative {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgL : MemLp g 2 (volume.restrict U))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) :
    HasIntervalH1 a b (quarterHalfNumerator lam g)
      (quarterHalfNumeratorDerivative lam g D) := by
  have hN := normalizedOrbitWindow_hasIntervalH1_flux (lam := lam) hU hg hgL hD hDL hcell
    ha hab hb hh₀ (l := (-1 / 8 : ℝ)) (r := 0)
    (by norm_num) (by norm_num) (by norm_num)
  have hNv := hN.congr_Ioo (G := quarterHalfNumerator lam g) (by
    intro h _
    rw [quarterHalfNumerator_eq_normalized])
  apply hNv.congr_derivative
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hH : (∫ θ in Icc (-1 / 8 : ℝ) 0, (orbitPeriod h : ℂ) *
      Complex.exp (-Complex.I * ((lam * (θ * orbitPeriod h) : ℝ) : ℂ)) *
        quarterForcingLevelDerivative D (h, θ * orbitPeriod h)) =
      ∫ t in (-eighthPeriod h)..0, quarterForcingLevelDerivative D (h, t) *
        Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)) := by
    rw [quarterHalfIntervalIntegral_eq_normalized]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    ring
  have hL := ((contDiffOn_eighthPeriod.contDiffAt
    (Ioo_mem_nhds (ha.trans hh.1) (hh.2.trans (hb.trans hh₀)))).differentiableAt
      (by simp)).hasDerivAt
  have hd : deriv orbitPeriod h = 8 * deriv eighthPeriod h := (hL.const_mul 8).deriv
  have hm : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by unfold orbitPeriod; ring
  rw [hH]
  dsimp only [quarterHalfNumeratorDerivative, actionAngleInv]
  rw [hm, hd]
  push_cast
  ring

/-- One specified derivative works on every compact interior level interval. -/
theorem quarterHalfNumerator_derivative_h1Loc {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgL : MemLp g 2 (volume.restrict U))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {h₀ : ℝ} (hh₀ : h₀ < 1) :
    HasIntervalH1Loc 0 h₀ (quarterHalfNumerator lam g)
      (quarterHalfNumeratorDerivative lam g D) :=
  fun _ _ ha hab hb ↦ quarterHalfNumerator_hasIntervalH1_derivative hU hg hgL hD hDL hcell
    ha hab hb hh₀

end NoEmbeddedEigenvalues
