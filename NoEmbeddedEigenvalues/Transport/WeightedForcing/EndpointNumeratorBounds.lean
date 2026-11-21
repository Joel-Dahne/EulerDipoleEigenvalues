module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.EndpointTangentialTrace

/-!
# Quantitative moving-endpoint value-flux estimate

Blueprint: `lem:numerator-endpoint-flux-energy`.

Only the tangential derivative of the endpoint value is identified across
charts here. This does not identify the individual gradient traces.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

private theorem norm_sq_le_two_add (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (norm_add_le _ _) |>.trans (by nlinarith [sq_nonneg (‖x‖ - ‖y‖)])

private theorem endpointValueEnergy_eq_sum (g : ℝ × ℝ → ℂ) (h : ℝ) :
    quarterEndpointValueEnergy g h = ∑ side : Bool,
      ‖g (quarterEndpointRay side (quarterEndpointRadius h)) / (h : ℂ)‖ ^ 2 := by
  simp only [quarterEndpointValueEnergy, Finset.sum_div, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem endpointGradientEnergy_eq_sum {h : ℝ} (hh : 0 ≤ h)
    (T : Bool → Fin 2 → ℝ → ℂ) :
    quarterEndpointGradientEnergy T h = ∑ side : Bool, ∑ j : Fin 2,
      ‖T side j (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2 := by
  simp only [quarterEndpointGradientEnergy, Finset.sum_div, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hh]

/-- The derivative of the endpoint-value flux is controlled pointwise in level
by the endpoint value and canonical affine-gradient energies. The weaker
global norm alone would not suffice for logarithmic summation. -/
theorem IsTransportPair.quarterNumeratorEndpointDerivative_sq_le
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D [j])) (μ : ℝ) :
    ∃ b K : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ 0 < K ∧
      ∀ᵐ (h : ℝ) ∂(volume.restrict (Ioo 0 b)),
        ‖(h : ℂ) * quarterNumeratorEndpointDerivative μ g D h‖ ^ 2 ≤ K *
          (quarterEndpointGradientEnergy (quarterGradientTrace (fun j ↦ D [j])) h +
            quarterEndpointValueEnergy g h) := by
  obtain ⟨r, hr, _, hc⟩ := quarterEndpointCoefficient_weighted_bounds
  obtain ⟨C, hC, hCb⟩ := hc μ
  let b := min r (1 / 256)
  have hb : 0 < b := lt_min hr (by norm_num)
  have hbr : b ≤ r := min_le_left _ _
  have hbs : b ≤ 1 / 256 := min_le_right _ _
  have hb1 : b < 1 := by linarith
  have hρ : quarterEndpointRadius b < 1 / 2 := by
    have hs : Real.sqrt b ≤ 1 / 16 := by
      apply (Real.sqrt_le_iff).2
      constructor <;> nlinarith
    linarith [quarterEndpointRadius_le_four_sqrt hb hb1]
  let T := quarterGradientTrace (fun j ↦ D [j])
  have htrace (side : Bool) := hp.quarterEndpointLevelTrace_eq_ae hcell hg hfg hD hb1 hρ side
  refine ⟨b, 16 * C ^ 2 + 1, hb, hbs, by positivity, ?_⟩
  filter_upwards [htrace true, htrace false, ae_restrict_mem measurableSet_Ioo] with h hp' hm hh
  have hh1 := hh.2.trans hb1
  have hch : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.1.ne'
  have hs : 0 < Real.sqrt (1 - h) := Real.sqrt_pos.2 (by linarith)
  have hs' : (1 / 2 : ℝ) ≤ Real.sqrt (1 - h) :=
    Real.le_sqrt_of_sq_le (by linarith [hh.2.trans_le hbs])
  have hcoef : ‖((1 / Real.sqrt (1 - h) : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hs)]
    exact (div_le_iff₀ hs).2 (by linarith)
  let ε : Bool → ℝ := fun side ↦ if side then 1 else -1
  let j : Bool → Fin 2 := fun side ↦ if side then 1 else 0
  let V := fun side ↦ ‖g (quarterEndpointRay side (quarterEndpointRadius h)) / (h : ℂ)‖ ^ 2
  let G := fun side ↦ ‖T side (j side) (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2
  let A := fun side ↦ deriv (quarterEndpointCoefficient μ (ε side)) h *
    g (dipoleOrbit h (ε side * eighthPeriod h))
  let B := fun side ↦ quarterEndpointCoefficient μ (ε side) h *
    quarterEndpointLevelTrace (fun i ↦ D [i]) side h
  have he (side : Bool) : ε side = -1 ∨ ε side = 1 := by cases side <;> simp [ε]
  have hAc (side : Bool) : ‖(h : ℂ) * A side‖ ^ 2 ≤ C ^ 2 * V side := by
    have hpoint := dipoleOrbit_quarterEndpointRay hh.1 hh1 side
    have hpoint' : dipoleOrbit h (ε side * eighthPeriod h) =
        quarterEndpointRay side (quarterEndpointRadius h) := by
      cases side <;> simpa [ε] using hpoint
    have hrewrite : (h : ℂ) * A side =
        (((h ^ 2 : ℝ) : ℂ) * deriv (quarterEndpointCoefficient μ (ε side)) h) *
          (g (quarterEndpointRay side (quarterEndpointRadius h)) / (h : ℂ)) := by
      dsimp [A]
      rw [hpoint']
      push_cast
      field_simp [hch]
    rw [hrewrite, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hC).2
        (hCb (ε side) (he side) h ⟨hh.1, hh.2.trans_le hbr⟩).2) (sq_nonneg _)
  have hT (side : Bool) :
      ‖quarterEndpointLevelTrace (fun i ↦ D [i]) side h‖ ^ 2 ≤ 4 * G side := by
    have ht : quarterEndpointLevelTrace (fun i ↦ D [i]) side h =
        ((1 / Real.sqrt (1 - h) : ℝ) : ℂ) *
          ((if side then T side (j side) (quarterEndpointRadius h)
           else -T side (j side) (quarterEndpointRadius h)) / (Real.sqrt h : ℂ)) := by
      cases side
      · rw [hm]; simp only [j, Bool.false_eq_true, ↓reduceIte, T]; push_cast; ring
      · rw [hp']; simp only [j, ↓reduceIte, T]; push_cast; ring
    have hnorm :
        ‖(if side then T side (j side) (quarterEndpointRadius h)
           else -T side (j side) (quarterEndpointRadius h)) / (Real.sqrt h : ℂ)‖ ^ 2 =
            G side := by
      cases side <;> simp [G, neg_div]
    rw [ht, norm_mul, mul_pow, hnorm]
    exact mul_le_mul_of_nonneg_right
      (show ‖((1 / Real.sqrt (1 - h) : ℝ) : ℂ)‖ ^ 2 ≤ 4 by
        rw [← show (2 : ℝ) ^ 2 = 4 by norm_num]
        exact (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hcoef)
      (sq_nonneg _)
  have hBc (side : Bool) : ‖(h : ℂ) * B side‖ ^ 2 ≤ C ^ 2 * (4 * G side) := by
    dsimp only [B]
    rw [← mul_assoc, norm_mul, mul_pow]
    exact mul_le_mul
      ((sq_le_sq₀ (norm_nonneg _) hC).2
        (hCb (ε side) (he side) h ⟨hh.1, hh.2.trans_le hbr⟩).1)
      (hT side) (sq_nonneg _) (sq_nonneg _)
  have hEs : V true + V false = quarterEndpointValueEnergy g h := by
    simp [V, endpointValueEnergy_eq_sum, add_comm]
  have hGs : G true + G false ≤ quarterEndpointGradientEnergy T h := by
    rw [endpointGradientEnergy_eq_sum hh.1.le, Fintype.sum_bool]
    have hsingle (s : Bool) : G s ≤ ∑ i : Fin 2,
        ‖T s i (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i ↦ ‖T s i (quarterEndpointRadius h) / (Real.sqrt h : ℂ)‖ ^ 2)
        (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (j s))
    simpa only [add_comm] using add_le_add (hsingle false) (hsingle true)
  have hrewrite : (h : ℂ) * quarterNumeratorEndpointDerivative μ g D h =
      ((h : ℂ) * A true + (h : ℂ) * B true) +
        ((h : ℂ) * A false + (h : ℂ) * B false) := by
    simp [quarterNumeratorEndpointDerivative, A, B, ε, quarterEndpointLevelTrace, mul_add]
  rw [hrewrite]
  have hpair (side : Bool) :
      ‖(h : ℂ) * A side + (h : ℂ) * B side‖ ^ 2 ≤
        2 * (C ^ 2 * V side + C ^ 2 * (4 * G side)) :=
    (norm_sq_le_two_add _ _).trans (mul_le_mul_of_nonneg_left
      (add_le_add (hAc side) (hBc side)) (by norm_num))
  apply (norm_sq_le_two_add _ _).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (hpair true) (hpair false)) (by norm_num)).trans
  calc
    _ = 4 * C ^ 2 * (V true + V false) + 16 * C ^ 2 * (G true + G false) := by ring
    _ ≤ _ := by
      rw [hEs]
      have hVp : 0 ≤ quarterEndpointValueEnergy g h := by rw [← hEs]; positivity
      have hGp : 0 ≤ quarterEndpointGradientEnergy T h :=
        (by positivity : 0 ≤ G true + G false).trans hGs
      let K := 16 * C ^ 2
      have hK : 0 ≤ K := by dsimp [K]; positivity
      calc
        _ ≤ K * quarterEndpointValueEnergy g h +
            K * quarterEndpointGradientEnergy T h :=
          add_le_add (mul_le_mul_of_nonneg_right (by dsimp [K]; nlinarith) hVp)
            (mul_le_mul_of_nonneg_left hGs hK)
        _ ≤ _ := by
          change _ ≤ (K + 1) * (quarterEndpointGradientEnergy T h + quarterEndpointValueEnergy g h)
          rw [← mul_add, add_comm (quarterEndpointValueEnergy g h)]
          exact mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hGp hVp)

end NoEmbeddedEigenvalues
