import NoEmbeddedEigenvalues.Virial.VirialQuadratic
import NoEmbeddedEigenvalues.Analysis.TorusSobolev.LiftTorus

/-!
# Fourier integration by parts for the virial forms

Blueprint: `lem:virial-h1` (skew-symmetry part) and the quadratic form in `lem:virial-l2`.

The pairings of `VirialL2.lean` are integrals over the period square of lifts of `L²`
functions, weighted by real periodic coefficients. Here they are written as torus inner
products `⟪v, c u⟫` with `c` the coefficient as a continuous function on the torus
(`squarePairing_smul_liftL2`). Integration by parts is then Parseval
(`inner_swap_of_hasFourierPartial`) together with the product rule
(`hasFourierPartial_mulL2`), applied to Fourier derivative witnesses. No smooth
approximation is used.

Main results: skew-symmetry of `D = W·∇ + ½ div W` on `H¹` (`inner_halfDensityGenL2`), and
the identity relating the two forms of the virial identity for every `ω` with mean zero
(`re_virialForm_eq_quadratic`).
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Complex ComplexConjugate
open scoped InnerProductSpace

/-! ### Real coefficients on the torus -/

section Coefficients

variable {g : ℝ × ℝ → ℝ}

theorem IsPeriodicLift.ofReal (hp : IsPeriodicLift g) : IsPeriodicLift (fun q ↦ (g q : ℂ)) :=
  fun q ↦ by simp only [(hp q).1, (hp q).2, and_self]

theorem IsPeriodicLift.add {a b : ℝ × ℝ → ℝ} (ha : IsPeriodicLift a) (hb : IsPeriodicLift b) :
    IsPeriodicLift (fun q ↦ a q + b q) :=
  fun q ↦ by simp only [(ha q).1, (ha q).2, (hb q).1, (hb q).2, and_self]

theorem IsPeriodicLift.sub {a b : ℝ × ℝ → ℝ} (ha : IsPeriodicLift a) (hb : IsPeriodicLift b) :
    IsPeriodicLift (fun q ↦ a q - b q) :=
  fun q ↦ by simp only [(ha q).1, (ha q).2, (hb q).1, (hb q).2, and_self]

theorem IsPeriodicLift.const_mul (r : ℝ) (ha : IsPeriodicLift g) :
    IsPeriodicLift (fun q ↦ r * g q) :=
  fun q ↦ by simp only [(ha q).1, (ha q).2, and_self]

/-- A real continuous periodic lift as a continuous function on the torus. -/
def torusFunR (hc : Continuous g) (hp : IsPeriodicLift g) : C(Torus, ℂ) :=
  torusFun (continuous_ofReal.comp hc) hp.ofReal

theorem torusFunR_torusProj (hc : Continuous g) (hp : IsPeriodicLift g) (q : ℝ × ℝ) :
    torusFunR hc hp (torusProj q) = g q :=
  torusFun_torusProj _ _ q

theorem conj_torusFunR (hc : Continuous g) (hp : IsPeriodicLift g) (t : Torus) :
    conj (torusFunR hc hp t) = torusFunR hc hp t := by
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  rw [torusFunR_torusProj, conj_ofReal]

/-- Continuous maps on the torus agree if their lifts agree. -/
theorem torusMap_ext {a b : C(Torus, ℂ)} (h : ∀ q, a (torusProj q) = b (torusProj q)) :
    a = b := by
  ext t
  obtain ⟨q, rfl⟩ := torusProj_surjective t
  exact h q

theorem continuous_partialX_real (hg : ContDiff ℝ 1 g) : Continuous (partialX g) :=
  (contDiff_partialX (n := 0) (by simpa using hg)).continuous

theorem continuous_partialY_real (hg : ContDiff ℝ 1 g) : Continuous (partialY g) :=
  (contDiff_partialY (n := 0) (by simpa using hg)).continuous

theorem hasClassicalPartial_torusFunR_x (hg : ContDiff ℝ 1 g) (hp : IsPeriodicLift g) :
    HasClassicalPartial 0 (torusFunR hg.continuous hp)
      (torusFunR (continuous_partialX_real hg) hp.partialX) := by
  have hgc : ContDiff ℝ 1 (fun q ↦ (g q : ℂ)) := ofRealCLM.contDiff.comp hg
  have h := hasClassicalPartial_torusFun_x hgc hp.ofReal
  rwa [show torusFun (continuous_partialX_of_contDiff hgc) hp.ofReal.partialX =
      torusFunR (continuous_partialX_real hg) hp.partialX from torusMap_ext fun q ↦ by
    rw [torusFun_torusProj, torusFunR_torusProj, partialX_ofReal (hg.differentiable one_ne_zero)]]
    at h

theorem hasClassicalPartial_torusFunR_y (hg : ContDiff ℝ 1 g) (hp : IsPeriodicLift g) :
    HasClassicalPartial 1 (torusFunR hg.continuous hp)
      (torusFunR (continuous_partialY_real hg) hp.partialY) := by
  have hgc : ContDiff ℝ 1 (fun q ↦ (g q : ℂ)) := ofRealCLM.contDiff.comp hg
  have h := hasClassicalPartial_torusFun_y hgc hp.ofReal
  rwa [show torusFun (continuous_partialY_of_contDiff hgc) hp.ofReal.partialY =
      torusFunR (continuous_partialY_real hg) hp.partialY from torusMap_ext fun q ↦ by
    rw [torusFun_torusProj, torusFunR_torusProj, partialY_ofReal (hg.differentiable one_ne_zero)]]
    at h

end Coefficients

/-! ### Multiplication operators -/

theorem mulL2_add_left (a b : C(Torus, ℂ)) (u : L2) :
    mulL2 (a + b) u = mulL2 a u + mulL2 b u := by
  apply Lp.ext
  filter_upwards [mulL2_ae (a + b) u, mulL2_ae a u, mulL2_ae b u,
    Lp.coeFn_add (mulL2 a u) (mulL2 b u)] with t h h₁ h₂ h₃
  rw [h, h₃, Pi.add_apply, h₁, h₂, ContinuousMap.add_apply, add_mul]

theorem mulL2_sub_left (a b : C(Torus, ℂ)) (u : L2) :
    mulL2 (a - b) u = mulL2 a u - mulL2 b u := by
  apply Lp.ext
  filter_upwards [mulL2_ae (a - b) u, mulL2_ae a u, mulL2_ae b u,
    Lp.coeFn_sub (mulL2 a u) (mulL2 b u)] with t h h₁ h₂ h₃
  rw [h, h₃, Pi.sub_apply, h₁, h₂, ContinuousMap.sub_apply, sub_mul]

theorem mulL2_smul_left (r : ℂ) (a : C(Torus, ℂ)) (u : L2) :
    mulL2 (r • a) u = r • mulL2 a u := by
  apply Lp.ext
  filter_upwards [mulL2_ae (r • a) u, mulL2_ae a u, Lp.coeFn_smul r (mulL2 a u)] with t h h₁ h₂
  rw [h, h₂, Pi.smul_apply, h₁, ContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- For real `c`, `⟪v, c u⟫ = ⟪c v, u⟫`. -/
theorem inner_mulL2_right {c : C(Torus, ℂ)} (hr : ∀ t, conj (c t) = c t) (u v : L2) :
    ⟪v, mulL2 c u⟫_ℂ = ⟪mulL2 c v, u⟫_ℂ := by
  rw [← inner_conj_symm, inner_mulL2_swap hr, conj_conj]

/-! ### Pairings over the period square as torus inner products -/

section Pairing

variable {g : ℝ × ℝ → ℝ}

/-- `∫ g u v̄` over the period square is `⟪v, c u⟫` on the torus. -/
theorem squarePairing_smul_liftL2 (hc : Continuous g) (hp : IsPeriodicLift g) (u v : L2) :
    squarePairing (fun p ↦ g p • liftL2 u p) (liftL2 v) = ⟪v, mulL2 (torusFunR hc hp) u⟫_ℂ := by
  rw [inner_mulL2_right (conj_torusFunR hc hp), inner_mulL2 (conj_torusFunR hc hp)]
  have hi := integrable_continuous_mul_inner (torusFunR hc hp) v u
  rw [← squareIntegral_comp_torusProj hi.1]
  unfold squarePairing
  congr 1
  funext q
  simp only [liftL2, torusFunR_torusProj, real_smul]
  ring

theorem integrableOn_smul_liftL2_mul_conj (hc : Continuous g) (hp : IsPeriodicLift g)
    (u v : L2) :
    IntegrableOn (fun p ↦ (g p • liftL2 u p) * conj (liftL2 v p)) periodSquare := by
  have h := integrableOn_periodSquare_comp
    (integrable_continuous_mul_inner (torusFunR hc hp) v u)
  have e : (fun p ↦ (g p • liftL2 u p) * conj (liftL2 v p)) = fun q ↦
      torusFunR hc hp (torusProj q) * (conj (v (torusProj q)) * u (torusProj q)) := by
    funext q
    simp only [liftL2, torusFunR_torusProj, real_smul]
    ring
  rw [e]
  exact h

theorem squarePairing_liftL2 (u v : L2) :
    squarePairing (liftL2 u) (liftL2 v) = ⟪v, u⟫_ℂ := by
  have h := squarePairing_smul_liftL2 (g := fun _ ↦ 1) continuous_const
    (isPeriodicLift_const 1) u v
  have e : mulL2 (torusFunR (g := fun _ ↦ 1) continuous_const (isPeriodicLift_const 1)) u = u := by
    apply Lp.ext
    filter_upwards [mulL2_ae (torusFunR (g := fun _ ↦ 1) continuous_const
      (isPeriodicLift_const 1)) u] with t ht
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    rw [ht, torusFunR_torusProj, ofReal_one, one_mul]
  simpa only [one_smul, e] using h

theorem squarePairing_add_left_of_integrableOn {a b w : ℝ × ℝ → ℂ}
    (ha : IntegrableOn (fun p ↦ a p * conj (w p)) periodSquare)
    (hb : IntegrableOn (fun p ↦ b p * conj (w p)) periodSquare) :
    squarePairing (fun p ↦ a p + b p) w = squarePairing a w + squarePairing b w := by
  unfold squarePairing squareIntegral
  rw [← integral_add ha hb]
  congr 1
  funext p
  ring

theorem squarePairing_add_right_of_integrableOn {a v w : ℝ × ℝ → ℂ}
    (hv : IntegrableOn (fun p ↦ a p * conj (v p)) periodSquare)
    (hw : IntegrableOn (fun p ↦ a p * conj (w p)) periodSquare) :
    squarePairing a (fun p ↦ v p + w p) = squarePairing a v + squarePairing a w := by
  unfold squarePairing squareIntegral
  rw [← integral_add hv hw]
  congr 1
  funext p
  simp only [map_add]
  ring

/-- The pairing of `g u` with a sum of two lifts. -/
theorem squarePairing_smul_liftL2_add_right (hc : Continuous g) (hp : IsPeriodicLift g)
    (u v w : L2) :
    squarePairing (fun p ↦ g p • liftL2 u p) (fun p ↦ liftL2 v p + liftL2 w p) =
      ⟪v, mulL2 (torusFunR hc hp) u⟫_ℂ + ⟪w, mulL2 (torusFunR hc hp) u⟫_ℂ := by
  rw [squarePairing_add_right_of_integrableOn (a := fun p ↦ g p • liftL2 u p)
    (v := liftL2 v) (w := liftL2 w) (integrableOn_smul_liftL2_mul_conj hc hp u v)
    (integrableOn_smul_liftL2_mul_conj hc hp u w), squarePairing_smul_liftL2,
    squarePairing_smul_liftL2]

/-- The pairing of a first-order expression `g₁ u₁ + g₂ u₂ + g₃ u₃` with a lift. -/
theorem squarePairing_smul_liftL2_add₃ {g₁ g₂ g₃ : ℝ × ℝ → ℝ} (hc₁ : Continuous g₁)
    (hp₁ : IsPeriodicLift g₁) (hc₂ : Continuous g₂) (hp₂ : IsPeriodicLift g₂)
    (hc₃ : Continuous g₃) (hp₃ : IsPeriodicLift g₃) (u₁ u₂ u₃ v : L2) :
    squarePairing (fun p ↦ g₁ p • liftL2 u₁ p + g₂ p • liftL2 u₂ p + g₃ p • liftL2 u₃ p)
        (liftL2 v) =
      ⟪v, mulL2 (torusFunR hc₁ hp₁) u₁⟫_ℂ + ⟪v, mulL2 (torusFunR hc₂ hp₂) u₂⟫_ℂ +
        ⟪v, mulL2 (torusFunR hc₃ hp₃) u₃⟫_ℂ := by
  have I₁ := integrableOn_smul_liftL2_mul_conj hc₁ hp₁ u₁ v
  have I₂ := integrableOn_smul_liftL2_mul_conj hc₂ hp₂ u₂ v
  have I₃ := integrableOn_smul_liftL2_mul_conj hc₃ hp₃ u₃ v
  have I₁₂ : IntegrableOn (fun p ↦ (g₁ p • liftL2 u₁ p + g₂ p • liftL2 u₂ p) *
      conj (liftL2 v p)) periodSquare := by
    simpa only [add_mul, Pi.add_def] using I₁.add I₂
  rw [squarePairing_add_left_of_integrableOn
      (a := fun p ↦ g₁ p • liftL2 u₁ p + g₂ p • liftL2 u₂ p) (b := fun p ↦ g₃ p • liftL2 u₃ p)
      I₁₂ I₃,
    squarePairing_add_left_of_integrableOn (a := fun p ↦ g₁ p • liftL2 u₁ p)
      (b := fun p ↦ g₂ p • liftL2 u₂ p) I₁ I₂,
    squarePairing_smul_liftL2, squarePairing_smul_liftL2, squarePairing_smul_liftL2]

end Pairing

/-! ### Integration by parts on the torus -/

section IBP

variable {j : Fin 2} {c dc ddc : C(Torus, ℂ)}

/-- For real `c`, `Re ⟪∂ⱼu, c u⟫ = -½ Re ⟪u, (∂ⱼc) u⟫`. -/
theorem re_inner_partial_mulL2 (hr : ∀ t, conj (c t) = c t) (hdr : ∀ t, conj (dc t) = dc t)
    (hc : HasClassicalPartial j c dc) {u du : L2} (hu : HasFourierPartial j u du) :
    (⟪du, mulL2 c u⟫_ℂ).re = -(1 / 2) * (⟪u, mulL2 dc u⟫_ℂ).re := by
  have h := inner_swap_of_hasFourierPartial hu (hasFourierPartial_mulL2 hc hu)
  rw [inner_add_left, inner_mulL2_swap hr du u] at h
  rw [← inner_conj_symm du (mulL2 c u), conj_re, inner_mulL2_right hdr]
  have := congrArg re h
  simp only [neg_re, add_re, conj_re] at this
  linarith

/-- For real `c`, `Re ⟪∂ⱼ²u, c u⟫ = -Re ⟪∂ⱼu, c ∂ⱼu⟫ + ½ Re ⟪u, (∂ⱼ²c) u⟫`. -/
theorem re_inner_partial_partial_mulL2 (hr : ∀ t, conj (c t) = c t)
    (hdr : ∀ t, conj (dc t) = dc t) (hddr : ∀ t, conj (ddc t) = ddc t)
    (hc : HasClassicalPartial j c dc) (hdc : HasClassicalPartial j dc ddc) {u u₁ u₂ : L2}
    (h₁ : HasFourierPartial j u u₁) (h₂ : HasFourierPartial j u₁ u₂) :
    (⟪u₂, mulL2 c u⟫_ℂ).re = -(⟪u₁, mulL2 c u₁⟫_ℂ).re + (1 / 2) * (⟪u, mulL2 ddc u⟫_ℂ).re := by
  have h := inner_swap_of_hasFourierPartial h₂ (hasFourierPartial_mulL2 hc h₁)
  rw [inner_add_left] at h
  have ha := re_inner_partial_mulL2 hdr hddr hdc h₁
  rw [← inner_conj_symm u₂ (mulL2 c u), conj_re, inner_mulL2_right hr]
  rw [← inner_conj_symm u₁ (mulL2 dc u), conj_re] at ha
  have := congrArg re h
  simp only [neg_re, add_re] at this
  linarith

end IBP

/-! ### The half-density generator on `H¹` -/

theorem HasFourierPartial.add {j : Fin 2} {g dg h dh : L2} (hg : HasFourierPartial j g dg)
    (hh : HasFourierPartial j h dh) : HasFourierPartial j (g + h) (dg + dh) := fun k ↦ by
  rw [fourierCoeff_add, fourierCoeff_add, hg k, hh k]
  ring

theorem HasFourierPartial.const_smul {j : Fin 2} {g dg : L2} (r : ℂ)
    (hg : HasFourierPartial j g dg) : HasFourierPartial j (r • g) (r • dg) := fun k ↦ by
  rw [fourierCoeff_smul, fourierCoeff_smul, hg k]
  ring

theorem conj_half : conj (1 / 2 : ℂ) = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, conj_ofReal]

section HalfDensity

variable {c₁ c₂ c₁₀ c₂₁ cd : C(Torus, ℂ)}

/-- Skew-symmetry of `D = c₁∂ₓ + c₂∂_y + ½ cd` on functions with Fourier partial derivatives,
for real `c₁, c₂` and `cd = ∂ₓc₁ + ∂_yc₂`: `⟪v, Du⟫ = -⟪Dv, u⟫`. -/
theorem inner_halfDensityGenL2 (hr₁ : ∀ t, conj (c₁ t) = c₁ t)
    (hr₂ : ∀ t, conj (c₂ t) = c₂ t) (hrd : ∀ t, conj (cd t) = cd t)
    (h₁ : HasClassicalPartial 0 c₁ c₁₀) (h₂ : HasClassicalPartial 1 c₂ c₂₁)
    (hd : cd = c₁₀ + c₂₁) {u u₀ u₁ v v₀ v₁ : L2} (hu₀ : HasFourierPartial 0 u u₀)
    (hu₁ : HasFourierPartial 1 u u₁) (hv₀ : HasFourierPartial 0 v v₀)
    (hv₁ : HasFourierPartial 1 v v₁) :
    ⟪v, mulL2 c₁ u₀ + mulL2 c₂ u₁ + (1 / 2 : ℂ) • mulL2 cd u⟫_ℂ =
      -⟪mulL2 c₁ v₀ + mulL2 c₂ v₁ + (1 / 2 : ℂ) • mulL2 cd v, u⟫_ℂ := by
  have ex := inner_swap_of_hasFourierPartial hu₀ (hasFourierPartial_mulL2 h₁ hv₀)
  have ey := inner_swap_of_hasFourierPartial hu₁ (hasFourierPartial_mulL2 h₂ hv₁)
  rw [inner_add_left] at ex ey
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_mulL2_right hr₁,
    inner_mulL2_right hr₂, inner_mulL2_right hrd, inner_add_left, inner_add_left,
    inner_smul_left, ex, ey, hd, mulL2_add_left, inner_add_left, conj_half]
  ring

/-- `Re ⟪u, Du⟫ = 0` for `u` with Fourier partial derivatives. -/
theorem re_inner_halfDensityGenL2_self (hr₁ : ∀ t, conj (c₁ t) = c₁ t)
    (hr₂ : ∀ t, conj (c₂ t) = c₂ t) (hrd : ∀ t, conj (cd t) = cd t)
    (h₁ : HasClassicalPartial 0 c₁ c₁₀) (h₂ : HasClassicalPartial 1 c₂ c₂₁)
    (hd : cd = c₁₀ + c₂₁) {u u₀ u₁ : L2} (hu₀ : HasFourierPartial 0 u u₀)
    (hu₁ : HasFourierPartial 1 u u₁) :
    (⟪u, mulL2 c₁ u₀ + mulL2 c₂ u₁ + (1 / 2 : ℂ) • mulL2 cd u⟫_ℂ).re = 0 := by
  have h := inner_halfDensityGenL2 hr₁ hr₂ hrd h₁ h₂ hd hu₀ hu₁ hu₀ hu₁
  rw [← inner_conj_symm u (mulL2 c₁ u₀ + mulL2 c₂ u₁ + (1 / 2 : ℂ) • mulL2 cd u)] at h ⊢
  rw [conj_re]
  have := congrArg re h
  simp only [neg_re, conj_re] at this
  linarith

/-- One coordinate of the `Dψ` term: with `w = ∂ⱼu`, `w₂ = ∂ⱼw`, `eᵢ = ∂ⱼcᵢ` and
`ee = ∂ⱼ² cd`, `Re ⟪w₂, Du⟫ = -Re ⟪w, e₁u₀⟫ - Re ⟪w, e₂u₁⟫ + ¼ Re ⟪u, ee u⟫`.
The witnesses `w₀, w₁` are the partial derivatives of `w`; they also serve as `∂ⱼu₀` and
`∂ⱼu₁`, which is the symmetry of second derivatives. -/
theorem re_inner_partial_partial_halfDensityGenL2 {j : Fin 2} {e₁ e₂ e ee : C(Torus, ℂ)}
    (hr₁ : ∀ t, conj (c₁ t) = c₁ t) (hr₂ : ∀ t, conj (c₂ t) = c₂ t)
    (hrd : ∀ t, conj (cd t) = cd t) (hre : ∀ t, conj (e t) = e t)
    (hree : ∀ t, conj (ee t) = ee t)
    (h₁ : HasClassicalPartial 0 c₁ c₁₀) (h₂ : HasClassicalPartial 1 c₂ c₂₁)
    (hd : cd = c₁₀ + c₂₁) (he₁ : HasClassicalPartial j c₁ e₁)
    (he₂ : HasClassicalPartial j c₂ e₂) (he : HasClassicalPartial j cd e)
    (hee : HasClassicalPartial j e ee) {u u₀ u₁ w w₀ w₁ w₂ : L2}
    (hw : HasFourierPartial j u w) (hu₀j : HasFourierPartial j u₀ w₀)
    (hu₁j : HasFourierPartial j u₁ w₁) (hw₀ : HasFourierPartial 0 w w₀)
    (hw₁ : HasFourierPartial 1 w w₁) (hw₂ : HasFourierPartial j w w₂) :
    (⟪w₂, mulL2 c₁ u₀ + mulL2 c₂ u₁ + (1 / 2 : ℂ) • mulL2 cd u⟫_ℂ).re =
      -(⟪w, mulL2 e₁ u₀⟫_ℂ).re - (⟪w, mulL2 e₂ u₁⟫_ℂ).re +
        (1 / 4) * (⟪u, mulL2 ee u⟫_ℂ).re := by
  have hD := (((hasFourierPartial_mulL2 he₁ hu₀j).add (hasFourierPartial_mulL2 he₂ hu₁j)).add
    ((hasFourierPartial_mulL2 he hw).const_smul (1 / 2 : ℂ)))
  have h := inner_swap_of_hasFourierPartial hw₂ hD
  have h0 := re_inner_halfDensityGenL2_self hr₁ hr₂ hrd h₁ h₂ hd hw₀ hw₁
  have hb := re_inner_partial_mulL2 hre hree hee hw
  have hc : conj (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by rw [conj_half]; push_cast; ring
  rw [← inner_conj_symm w₂, conj_re, h, ← inner_conj_symm w (mulL2 e₁ u₀), conj_re,
    ← inner_conj_symm w (mulL2 e₂ u₁), conj_re]
  rw [← inner_conj_symm w, conj_re] at h0
  rw [← inner_conj_symm w, conj_re] at hb
  simp only [inner_add_left, inner_smul_left, hc, neg_re, add_re, re_ofReal_mul] at h0 ⊢
  linarith

end HalfDensity

/-! ### The two forms of the virial identity -/

/-- Symmetry of the second derivatives of the stream function. -/
theorem streamSecondPartial_comm (ω : L2) :
    streamSecondPartial 0 1 ω = streamSecondPartial 1 0 ω :=
  fourierCoeff_ext fun k ↦ by
    rw [hasFourierSecondPartial_streamSecondPartial ω 0 1 k,
      hasFourierSecondPartial_streamSecondPartial ω 1 0 k]
    ring

/-- For `ω` with mean zero and `ψ = Δ⁻¹ω`, the two forms of the virial identity differ by
integrations by parts: `Re⟨fω, ω + ψ⟩ - 2 Re⟨Dψ, ω⟩` equals
`∫ f|ω|² + ∫ (2 sym DW - f I)∇ψ·∇ψ̄ + ½ ∫ Δ(f - div W)|ψ|²`.
Only `ψ ∈ H²` is used; no equation for `ω` and no adaptedness of `W`. -/
theorem re_virialForm_eq_quadratic {W₁ W₂ f : ℝ × ℝ → ℝ}
    (hW₁ : ContDiff ℝ 3 W₁) (hW₂ : ContDiff ℝ 3 W₂) (hf : ContDiff ℝ 2 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {ω : L2} (hω : MeanZero ω) :
    (squarePairing (fun p ↦ f p • liftL2 ω p) (fun p ↦ liftL2 ω p + streamLift ω p)).re -
      2 * (squarePairing (fun p ↦ W₁ p • streamLiftX ω p + W₂ p • streamLiftY ω p +
        ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift ω p) (liftL2 ω)).re =
    (squarePairing (fun p ↦ f p • liftL2 ω p) (liftL2 ω)).re +
      2 * ((squarePairing (fun p ↦ partialX W₁ p • streamLiftX ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialX W₂ p • streamLiftY ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialY W₁ p • streamLiftX ω p) (streamLiftY ω)).re +
        (squarePairing (fun p ↦ partialY W₂ p • streamLiftY ω p) (streamLiftY ω)).re) -
      (squarePairing (fun p ↦ f p • streamLiftX ω p) (streamLiftX ω)).re -
      (squarePairing (fun p ↦ f p • streamLiftY ω p) (streamLiftY ω)).re +
      (1 / 2) * (squarePairing
        (fun p ↦ laplacian (fun q ↦ f q - divergence W₁ W₂ q) p • streamLift ω p)
        (streamLift ω)).re := by
  -- Regularity and periodicity of the coefficients.
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdiv : ContDiff ℝ 2 (divergence W₁ W₂) :=
    (contDiff_partialX (n := 2) hW₁).add (contDiff_partialY (n := 2) hW₂)
  have hdiv1 : ContDiff ℝ 1 (divergence W₁ W₂) := hdiv.of_le (by norm_num)
  have hdx := contDiff_partialX_one hdiv
  have hdy := contDiff_partialY_one hdiv
  have hfx := contDiff_partialX_one hf
  have hfy := contDiff_partialY_one hf
  have hpd : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  -- Classical partial derivatives of the coefficients on the torus.
  have P1 := hasClassicalPartial_torusFunR_x hW₁1 hpW₁
  have P2 := hasClassicalPartial_torusFunR_y hW₂1 hpW₂
  have hd : torusFunR hdiv1.continuous hpd =
      torusFunR (continuous_partialX_real hW₁1) hpW₁.partialX +
        torusFunR (continuous_partialY_real hW₂1) hpW₂.partialY :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.add_apply, torusFunR_torusProj, divergence, ofReal_add]
  have r {g : ℝ × ℝ → ℝ} (hc : Continuous g) (hp : IsPeriodicLift g) := conj_torusFunR hc hp
  -- The stream function and its derivatives.
  have d0 := hasFourierPartial_streamPartial ω 0
  have d1 := hasFourierPartial_streamPartial ω 1
  have d00 := hasFourierPartial_streamPartial_streamSecondPartial ω 0 0
  have d11 := hasFourierPartial_streamPartial_streamSecondPartial ω 1 1
  have d10 := hasFourierPartial_streamPartial_streamSecondPartial ω 1 0
  have d01 := hasFourierPartial_streamPartial_streamSecondPartial ω 0 1
  rw [streamSecondPartial_comm] at d01
  -- The `Dψ` term, one coordinate at a time.
  have Dx := re_inner_partial_partial_halfDensityGenL2 (r _ _) (r _ _) (r _ _) (r _ _) (r _ _)
    P1 P2 hd P1 (hasClassicalPartial_torusFunR_x hW₂1 hpW₂)
    (hasClassicalPartial_torusFunR_x hdiv1 hpd) (hasClassicalPartial_torusFunR_x hdx hpd.partialX)
    d0 d00 d01 d00 d10 d00
  have Dy := re_inner_partial_partial_halfDensityGenL2 (r _ _) (r _ _) (r _ _) (r _ _) (r _ _)
    P1 P2 hd (hasClassicalPartial_torusFunR_y hW₁1 hpW₁) P2
    (hasClassicalPartial_torusFunR_y hdiv1 hpd) (hasClassicalPartial_torusFunR_y hdy hpd.partialY)
    d1 d10 d11 d01 d11 d11
  -- The `f` term.
  have Fx := re_inner_partial_partial_mulL2 (r _ _) (r _ _) (r _ _)
    (hasClassicalPartial_torusFunR_x hf1 hpf) (hasClassicalPartial_torusFunR_x hfx hpf.partialX)
    d0 d00
  have Fy := re_inner_partial_partial_mulL2 (r _ _) (r _ _) (r _ _)
    (hasClassicalPartial_torusFunR_y hf1 hpf) (hasClassicalPartial_torusFunR_y hfy hpf.partialY)
    d1 d11
  -- `ω = ∂ₓ²ψ + ∂_y²ψ` in the `f ψ` and `D ψ` terms.
  have hB : (⟪invLap ω, mulL2 (torusFunR hf.continuous hpf) ω⟫_ℂ).re =
      (⟪streamSecondPartial 0 0 ω, mulL2 (torusFunR hf.continuous hpf) (invLap ω)⟫_ℂ).re +
        (⟪streamSecondPartial 1 1 ω, mulL2 (torusFunR hf.continuous hpf) (invLap ω)⟫_ℂ).re := by
    rw [inner_mulL2_right (r _ _), ← inner_conj_symm, conj_re, ← add_re, ← inner_add_left,
      streamSecondPartial_add hω]
  have hhalf : Continuous (fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p) :=
    continuous_const.mul hdiv1.continuous
  have ehalf : torusFunR hhalf (hpd.const_mul (1 / 2)) =
      (1 / 2 : ℂ) • torusFunR hdiv1.continuous hpd :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.smul_apply, torusFunR_torusProj, smul_eq_mul]
      push_cast
      ring
  have hD : (⟪ω, mulL2 (torusFunR hW₁1.continuous hpW₁) (streamPartial 0 ω)⟫_ℂ +
      ⟪ω, mulL2 (torusFunR hW₂1.continuous hpW₂) (streamPartial 1 ω)⟫_ℂ +
      ⟪ω, mulL2 (torusFunR hhalf (hpd.const_mul (1 / 2))) (invLap ω)⟫_ℂ).re =
      (⟪streamSecondPartial 0 0 ω, mulL2 (torusFunR hW₁1.continuous hpW₁) (streamPartial 0 ω) +
        mulL2 (torusFunR hW₂1.continuous hpW₂) (streamPartial 1 ω) +
        (1 / 2 : ℂ) • mulL2 (torusFunR hdiv1.continuous hpd) (invLap ω)⟫_ℂ).re +
      (⟪streamSecondPartial 1 1 ω, mulL2 (torusFunR hW₁1.continuous hpW₁) (streamPartial 0 ω) +
        mulL2 (torusFunR hW₂1.continuous hpW₂) (streamPartial 1 ω) +
        (1 / 2 : ℂ) • mulL2 (torusFunR hdiv1.continuous hpd) (invLap ω)⟫_ℂ).re := by
    rw [ehalf, mulL2_smul_left, ← inner_add_right, ← inner_add_right, ← add_re,
      ← inner_add_left, streamSecondPartial_add hω]
  -- `Δ(f - div W) = ∂ₓ²f + ∂_y²f - ∂ₓ² div W - ∂_y² div W`.
  have hlap : laplacian (fun q ↦ f q - divergence W₁ W₂ q) = fun p ↦
      partialX (partialX f) p + partialY (partialY f) p -
        partialX (partialX (divergence W₁ W₂)) p - partialY (partialY (divergence W₁ W₂)) p := by
    have hfd : Differentiable ℝ f := hf.differentiable two_ne_zero
    have hdd : Differentiable ℝ (divergence W₁ W₂) := hdiv.differentiable two_ne_zero
    have h1 : partialX (fun q ↦ f q - divergence W₁ W₂ q) =
        fun q ↦ partialX f q - partialX (divergence W₁ W₂) q :=
      funext fun q ↦ partialX_sub (hfd q) (hdd q)
    have h2 : partialY (fun q ↦ f q - divergence W₁ W₂ q) =
        fun q ↦ partialY f q - partialY (divergence W₁ W₂) q :=
      funext fun q ↦ partialY_sub (hfd q) (hdd q)
    funext p
    simp only [laplacian, h1, h2, partialX_sub ((hfx.differentiable one_ne_zero) p)
      ((hdx.differentiable one_ne_zero) p), partialY_sub ((hfy.differentiable one_ne_zero) p)
      ((hdy.differentiable one_ne_zero) p)]
    ring
  have hcl : Continuous (fun p ↦ partialX (partialX f) p + partialY (partialY f) p -
      partialX (partialX (divergence W₁ W₂)) p - partialY (partialY (divergence W₁ W₂)) p) :=
    (((continuous_partialX_real hfx).add (continuous_partialY_real hfy)).sub
      (continuous_partialX_real hdx)).sub (continuous_partialY_real hdy)
  have hpl : IsPeriodicLift (fun p ↦ partialX (partialX f) p + partialY (partialY f) p -
      partialX (partialX (divergence W₁ W₂)) p - partialY (partialY (divergence W₁ W₂)) p) :=
    ((hpf.partialX.partialX.add hpf.partialY.partialY).sub hpd.partialX.partialX).sub
      hpd.partialY.partialY
  have elap : torusFunR hcl hpl =
      torusFunR (continuous_partialX_real hfx) hpf.partialX.partialX +
        torusFunR (continuous_partialY_real hfy) hpf.partialY.partialY -
        torusFunR (continuous_partialX_real hdx) hpd.partialX.partialX -
        torusFunR (continuous_partialY_real hdy) hpd.partialY.partialY :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, torusFunR_torusProj]
      push_cast
      ring
  -- All pairings as torus inner products.
  simp only [streamLift, streamLiftX, streamLiftY]
  rw [hlap, squarePairing_smul_liftL2 hcl hpl, elap, mulL2_sub_left, mulL2_sub_left,
    mulL2_add_left, inner_sub_right, inner_sub_right, inner_add_right,
    squarePairing_smul_liftL2_add_right hf.continuous hpf,
    squarePairing_smul_liftL2_add₃ hW₁1.continuous hpW₁ hW₂1.continuous hpW₂ hhalf
      (hpd.const_mul (1 / 2)),
    squarePairing_smul_liftL2 hf.continuous hpf,
    squarePairing_smul_liftL2 hf.continuous hpf,
    squarePairing_smul_liftL2 hf.continuous hpf,
    squarePairing_smul_liftL2 (continuous_partialX_real hW₁1) hpW₁.partialX,
    squarePairing_smul_liftL2 (continuous_partialX_real hW₂1) hpW₂.partialX,
    squarePairing_smul_liftL2 (continuous_partialY_real hW₁1) hpW₁.partialY,
    squarePairing_smul_liftL2 (continuous_partialY_real hW₂1) hpW₂.partialY]
  simp only [add_re, sub_re] at hD ⊢
  linarith

end NoEmbeddedEigenvalues
