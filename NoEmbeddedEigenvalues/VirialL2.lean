import NoEmbeddedEigenvalues.CellPeriodization

/-!
# The virial identities on the `L²` domain

Blueprint: `lem:virial-exact-identity`, `lem:stream-ibp`, `lem:half-density-skew-h1`,
`lem:virial-h1` and `lem:virial-l2` (all proved, the last from admitted inputs).

For a smooth adapted field `W` supported in a compact annulus `{2h₁ ≤ Ψ ≤ 2h₂}` of the
cells, `0 < h₁`, `h₂ < 1` (away from the separatrix and the centers), the two smooth virial
identities (`VirialSmooth.lean`, `VirialQuadratic.lean`) hold for every eigenfunction
`ω ∈ L²`, with no further regularity. Derivatives of `ψ = Δ⁻¹ω` are the lifts of the
Fourier-defined ones and `Δψ = ω`.

The proof of `virial_l2` needs no flow of `W`. `virial_l2_first` mollifies in the level
variable of action-angle coordinates (`TransversalMollifier.lean`), periodizes the outputs
through the box `(-π, π]²` (`CellPeriodization.lean`), applies the `H¹` identity at each
scale (`virial_eps_identity`) and passes to the limit (`virial_limit`): the commutator
error is `O(ε)` while the derivatives of the mollified `ω` are `o(1/ε)`. The quadratic form
then follows from `re_virialForm_eq_quadratic` (`VirialFourier.lean`).

The `H¹` statements take Fourier derivative witnesses explicitly (they exist for every `H¹`
input by `MemSobolev.exists_hasFourierPartial`). Their displayed generators use the lifts
of those derivatives, not classical derivatives of arbitrary representatives. Only first
derivatives occur in the conclusions; no assertion that `HDu` or `DHu` is in `L²` is made.
Both are proved without approximation. For the commutator identity `virial_h1` the only
second-order part of `[H, D]` is a mixed term `Im ∫ g ∂ₓu ∂_y ū`, which
`two_im_inner_partial_mulL2` reduces to first-order terms by the symmetry of mixed
derivatives in Fourier variables (`inner_partial_swap`); adaptedness then cancels the rest
pointwise.
-/
noncomputable section

namespace NoEmbeddedEigenvalues

open Complex MeasureTheory Filter ComplexConjugate
open scoped InnerProductSpace

/-- The exact identity behind the virial argument (`lem:virial-exact-identity`): if
    `a = ω + ψ` and `Ha = λω` with `λ` real, then for every linear `V` defined on `ω` and `ψ`,
    `⟨Va, Ha⟩ - ⟨VHa, a⟩ = λ(⟨Vψ, ω⟩ - ⟨Vω, ψ⟩)`, because the two `⟨Vω, ω⟩` terms cancel.
    Mathlib's inner product is conjugate-linear in the first slot, so `⟨u, v⟩` here is
    `⟪v, u⟫`. -/
theorem inner_virial_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {M : Submodule ℂ E} (V : M →ₗ[ℂ] E) (ω ψ : M) (lam : ℝ) :
    ⟪(lam : ℂ) • (ω : E), V (ω + ψ)⟫_ℂ - ⟪((ω + ψ : M) : E), V ((lam : ℂ) • ω)⟫_ℂ =
      lam * (⟪(ω : E), V ψ⟫_ℂ - ⟪(ψ : E), V ω⟫_ℂ) := by
  simp only [map_add, map_smul, Submodule.coe_add, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_ofReal]
  ring

/-! ### The virial form on `H¹` (`lem:virial-h1`, stated) -/

/-- Skew-symmetry of the half-density generator on `H¹(𝕋²)`.
The functions `du j`, `dv j` are Fourier partial derivatives in `L²`; their existence is
the `H¹` assumption. The proof is `inner_halfDensityGenL2`. -/
theorem squarePairing_halfDensityGen_h1 {W₁ W₂ : ℝ × ℝ → ℝ}
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    {u v : L2} {du dv : Fin 2 → L2} (hdu : ∀ j, HasFourierPartial j u (du j))
    (hdv : ∀ j, HasFourierPartial j v (dv j)) :
    let Du : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (du 0) p + W₂ p • liftL2 (du 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 u p
    let Dv : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (dv 0) p + W₂ p • liftL2 (dv 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 v p
    squarePairing Du (liftL2 v) = -squarePairing (liftL2 u) Dv := by
  intro Du Dv
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hpd : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hdc : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real hW₁1).add (continuous_partialY_real hW₂1)
  have hhalf : Continuous (fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p) :=
    continuous_const.mul hdc
  have hd : torusFunR hdc hpd =
      torusFunR (continuous_partialX_real hW₁1) hpW₁.partialX +
        torusFunR (continuous_partialY_real hW₂1) hpW₂.partialY :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.add_apply, torusFunR_torusProj, divergence, ofReal_add]
  have ehalf : torusFunR hhalf (hpd.const_mul (1 / 2)) = (1 / 2 : ℂ) • torusFunR hdc hpd :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.smul_apply, torusFunR_torusProj, smul_eq_mul]
      push_cast
      ring
  have h := inner_halfDensityGenL2 (conj_torusFunR hW₁1.continuous hpW₁)
    (conj_torusFunR hW₂1.continuous hpW₂) (conj_torusFunR hdc hpd)
    (hasClassicalPartial_torusFunR_x hW₁1 hpW₁) (hasClassicalPartial_torusFunR_y hW₂1 hpW₂) hd
    (hdu 0) (hdu 1) (hdv 0) (hdv 1)
  rw [squarePairing_comm Dv (liftL2 u)]
  simp only [Du, Dv]
  rw [squarePairing_smul_liftL2_add₃ hW₁1.continuous hpW₁
    hW₂1.continuous hpW₂ hhalf (hpd.const_mul (1 / 2)),
    squarePairing_smul_liftL2_add₃ hW₁1.continuous hpW₁ hW₂1.continuous hpW₂ hhalf
      (hpd.const_mul (1 / 2)), ehalf, mulL2_smul_left, mulL2_smul_left, ← inner_add_right,
    ← inner_add_right, ← inner_add_right, ← inner_add_right, inner_conj_symm, h]

/-! ### The commutator identity on `H¹` (`lem:virial-h1`) -/

/-- Symmetry of mixed derivatives in the weak sense: `⟪∂ₓu, ∂_y v⟫ = ⟪∂_y u, ∂ₓv⟫` for `u, v`
with Fourier partial derivatives, from Parseval. -/
theorem inner_partial_swap {u u₀ u₁ v v₀ v₁ : L2} (hu₀ : HasFourierPartial 0 u u₀)
    (hu₁ : HasFourierPartial 1 u u₁) (hv₀ : HasFourierPartial 0 v v₀)
    (hv₁ : HasFourierPartial 1 v v₁) : ⟪u₀, v₁⟫_ℂ = ⟪u₁, v₀⟫_ℂ := by
  have hs := torusFourierBasis.hasSum_inner_mul_inner u₀ v₁
  have ht := torusFourierBasis.hasSum_inner_mul_inner u₁ v₀
  refine hs.unique (ht.congr_fun fun k ↦ ?_)
  rw [← inner_conj_symm (𝕜 := ℂ) u₀ (torusFourierBasis k),
    ← inner_conj_symm (𝕜 := ℂ) u₁ (torusFourierBasis k)]
  simp only [← HilbertBasis.repr_apply_apply, torusFourierBasis_repr, hu₀ k, hu₁ k, hv₀ k,
    hv₁ k, map_mul, Complex.conj_I, map_intCast, map_ofNat, Complex.conj_ofReal,
    frequencyComponent]
  simp
  ring

/-- For real `c`, `Im ⟪v, c w⟫ = -Im ⟪w, c v⟫`. -/
theorem im_inner_mulL2_swap {c : C(Torus, ℂ)} (hr : ∀ t, conj (c t) = c t) (v w : L2) :
    (⟪v, mulL2 c w⟫_ℂ).im = -(⟪w, mulL2 c v⟫_ℂ).im := by
  rw [inner_mulL2_right hr, ← inner_conj_symm, conj_im]

theorem conj_mul_of_real {a b : C(Torus, ℂ)} (ha : ∀ t, conj (a t) = a t)
    (hb : ∀ t, conj (b t) = b t) (t : Torus) : conj ((a * b) t) = (a * b) t := by
  rw [ContinuousMap.mul_apply, map_mul, ha, hb]

/-- The null-Lagrangian identity: for real `c`,
`2 Im ⟪∂ₓu, c ∂_y u⟫ = Im ⟪∂_y u, (∂ₓc) u⟫ - Im ⟪∂ₓu, (∂_y c) u⟫`. Only first derivatives
of `u` occur; the proof applies `inner_partial_swap` to `u` and `cu`. -/
theorem two_im_inner_partial_mulL2 {c cx cy : C(Torus, ℂ)} (hr : ∀ t, conj (c t) = c t)
    (hx : HasClassicalPartial 0 c cx) (hy : HasClassicalPartial 1 c cy) {u u₀ u₁ : L2}
    (hu₀ : HasFourierPartial 0 u u₀) (hu₁ : HasFourierPartial 1 u u₁) :
    2 * (⟪u₀, mulL2 c u₁⟫_ℂ).im = (⟪u₁, mulL2 cx u⟫_ℂ).im - (⟪u₀, mulL2 cy u⟫_ℂ).im := by
  have h := inner_partial_swap hu₀ hu₁ (hasFourierPartial_mulL2 hx hu₀)
    (hasFourierPartial_mulL2 hy hu₁)
  rw [inner_add_right, inner_add_right] at h
  have h2 := im_inner_mulL2_swap hr u₁ u₀
  have := congrArg im h
  simp only [add_im] at this
  linarith

/-- The commutator identity for torus coefficients: with `Hu = -i(s u₀ - t u₁)`,
`Du = c₁u₀ + c₂u₁ + ch u`, `G = s c₂ + t c₁`, `∂ₓG = 2t ch - f t` and `∂_y G = 2s ch - f s`,
`2 Re ⟪Hu, Du⟫ = Re ⟪u, f Hu⟫`. The `u₀u₁` terms of `⟪Hu, Du⟫` form `Im ⟪u₀, G u₁⟫`, which
`two_im_inner_partial_mulL2` turns into lower-order terms. -/
theorem re_inner_transport_mulL2 {s t c₁ c₂ ch f G Gx Gy : C(Torus, ℂ)}
    (hrs : ∀ x, conj (s x) = s x) (hrt : ∀ x, conj (t x) = t x)
    (hr₁ : ∀ x, conj (c₁ x) = c₁ x) (hr₂ : ∀ x, conj (c₂ x) = c₂ x)
    (hrf : ∀ x, conj (f x) = f x) (hrG : ∀ x, conj (G x) = G x)
    (hGx : HasClassicalPartial 0 G Gx) (hGy : HasClassicalPartial 1 G Gy)
    (hG : G = s * c₂ + t * c₁) (eGx : Gx = (2 : ℂ) • (t * ch) - f * t)
    (eGy : Gy = (2 : ℂ) • (s * ch) - f * s) {u u₀ u₁ : L2}
    (hu₀ : HasFourierPartial 0 u u₀) (hu₁ : HasFourierPartial 1 u u₁) :
    2 * (⟪-I • (mulL2 s u₀ - mulL2 t u₁), mulL2 c₁ u₀ + mulL2 c₂ u₁ + mulL2 ch u⟫_ℂ).re =
      (⟪u, mulL2 f (-I • (mulL2 s u₀ - mulL2 t u₁))⟫_ℂ).re := by
  have key := two_im_inner_partial_mulL2 hrG hGx hGy hu₀ hu₁
  rw [hG, eGx, eGy] at key
  simp only [mulL2_add_left, mulL2_sub_left, mulL2_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, add_im, sub_im, mul_im, re_ofNat, im_ofNat, zero_mul,
    add_zero] at key
  have a1 := im_inner_mulL2_swap (conj_mul_of_real hrs hr₁) u₀ u₀
  have a2 := im_inner_mulL2_swap (conj_mul_of_real hrt hr₂) u₁ u₁
  have a3 := im_inner_mulL2_swap (conj_mul_of_real hrt hr₁) u₁ u₀
  have a4 := im_inner_mulL2_swap (conj_mul_of_real hrf hrs) u u₀
  have a5 := im_inner_mulL2_swap (conj_mul_of_real hrf hrt) u u₁
  rw [inner_smul_left, inner_sub_left, ← inner_mulL2_right hrs, ← inner_mulL2_right hrt,
    mulL2_smul_right, mulL2_sub_right, mulL2_mulL2, mulL2_mulL2, inner_smul_right,
    inner_sub_right]
  simp only [mulL2_add_right, mulL2_mulL2, inner_add_right, map_neg, Complex.conj_I, neg_neg,
    mul_re, I_re, I_im, neg_re, neg_im, add_im, sub_im, sub_re, zero_mul, one_mul, zero_sub]
  linarith

/-- The commutator identity as an identity of torus inner products: with
`Du = W₁u₀ + W₂u₁ + ½ div W u` and `Hu = -i(sin y u₀ - sin x u₁)`,
`2 Re ⟪Hu, Du⟫ = Re ⟪u, f Hu⟫`. Adaptedness enters only through the derivatives of
`G = sin y W₂ + sin x W₁`. -/
theorem virial_h1_torus {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    (hhalf : Continuous fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p)
    (hphalf : IsPeriodicLift fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p)
    {u : L2} {du : Fin 2 → L2} (hdu : ∀ j, HasFourierPartial j u (du j)) :
    2 * (⟪-I • (mulL2 sinYTorus (du 0) - mulL2 sinXTorus (du 1)),
        mulL2 (torusFunR hW₁.continuous hpW₁) (du 0) +
          mulL2 (torusFunR hW₂.continuous hpW₂) (du 1) +
          mulL2 (torusFunR hhalf hphalf) u⟫_ℂ).re =
      (⟪u, mulL2 (torusFunR hf.continuous hpf)
        (-I • (mulL2 sinYTorus (du 0) - mulL2 sinXTorus (du 1)))⟫_ℂ).re := by
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  set g : ℝ × ℝ → ℝ := fun q ↦ Real.sin q.2 * W₂ q + Real.sin q.1 * W₁ q with hg_def
  have hg : ContDiff ℝ 1 g :=
    ((Real.contDiff_sin.comp contDiff_snd).mul hW₂1).add
      ((Real.contDiff_sin.comp contDiff_fst).mul hW₁1)
  have hpg : IsPeriodicLift g := fun q ↦ by
    simp only [hg_def, (hpW₁ q).1, (hpW₁ q).2, (hpW₂ q).1, (hpW₂ q).2, Real.sin_add_two_pi,
      and_self]
  have d₁ (q : ℝ × ℝ) : DifferentiableAt ℝ W₁ q := hW₁1.differentiable one_ne_zero q
  have d₂ (q : ℝ × ℝ) : DifferentiableAt ℝ W₂ q := hW₂1.differentiable one_ne_zero q
  have gx (q : ℝ × ℝ) : partialX g q =
      Real.sin q.2 * partialX W₂ q + (Real.cos q.1 * W₁ q + Real.sin q.1 * partialX W₁ q) := by
    have h := ((hasDerivAt_partialX (d₂ q)).const_mul (Real.sin q.2)).add
      ((Real.hasDerivAt_sin q.1).mul (hasDerivAt_partialX (d₁ q)))
    exact h.deriv
  have gy (q : ℝ × ℝ) : partialY g q =
      (Real.cos q.2 * W₂ q + Real.sin q.2 * partialY W₂ q) + Real.sin q.1 * partialY W₁ q := by
    have h := ((Real.hasDerivAt_sin q.2).mul (hasDerivAt_partialY (d₂ q))).add
      ((hasDerivAt_partialY (d₁ q)).const_mul (Real.sin q.1))
    exact h.deriv
  have r {g : ℝ × ℝ → ℝ} (hc : Continuous g) (hp : IsPeriodicLift g) := conj_torusFunR hc hp
  refine re_inner_transport_mulL2 (r _ _) (r _ _) (r _ _) (r _ _) (r _ _) (r hg.continuous hpg)
    (hasClassicalPartial_torusFunR_x hg hpg) (hasClassicalPartial_torusFunR_y hg hpg)
    ?_ ?_ ?_ (hdu 0) (hdu 1)
  · refine torusMap_ext fun q ↦ ?_
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, torusFunR_torusProj,
      Function.comp_apply, hg_def]
    push_cast
    ring
  · refine torusMap_ext fun q ↦ ?_
    obtain ⟨-, h2⟩ := had q (Set.mem_univ q)
    simp only [classicalL0, smul_eq_mul] at h2
    have h2' := congrArg (fun x : ℝ ↦ (x : ℂ)) h2
    push_cast at h2'
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      torusFunR_torusProj, Function.comp_apply, smul_eq_mul, gx, divergence]
    push_cast
    linear_combination h2'
  · refine torusMap_ext fun q ↦ ?_
    obtain ⟨h1, -⟩ := had q (Set.mem_univ q)
    simp only [classicalL0, smul_eq_mul] at h1
    have h1' := congrArg (fun x : ℝ ↦ (x : ℂ)) h1
    push_cast at h1'
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      torusFunR_torusProj, Function.comp_apply, smul_eq_mul, gy, divergence]
    push_cast
    linear_combination -h1'

/-- The commutator identity as a continuous quadratic form on `H¹(𝕋²)`.
`Du` and `Hu = -i L₀u` use the supplied Fourier partial derivatives; no second derivatives
of `u` occur. -/
theorem virial_h1 {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {u : L2} {du : Fin 2 → L2} (hdu : ∀ j, HasFourierPartial j u (du j)) :
    let Du : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (du 0) p + W₂ p • liftL2 (du 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 u p
    let Hu : ℝ × ℝ → ℂ := fun p ↦ -I *
      (Real.sin p.2 • liftL2 (du 0) p - Real.sin p.1 • liftL2 (du 1) p)
    2 * (squarePairing Du Hu).re =
      (squarePairing (fun p ↦ f p • Hu p) (liftL2 u)).re := by
  intro Du Hu
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hpd : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hhalf : Continuous fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p :=
    continuous_const.mul ((continuous_partialX_real hW₁1).add (continuous_partialY_real hW₂1))
  have V := virial_h1_torus had hW₁ hW₂ hf hpW₁ hpW₂ hpf hhalf (hpd.const_mul (1 / 2)) hdu
  set Hu' := -I • (mulL2 sinYTorus (du 0) - mulL2 sinXTorus (du 1))
  have hH : Hu =ᵐ[volume] liftL2 Hu' := by
    filter_upwards [liftL2_smul_ae (-I) (mulL2 sinYTorus (du 0) - mulL2 sinXTorus (du 1)),
      liftL2_sub_ae (mulL2 sinYTorus (du 0)) (mulL2 sinXTorus (du 1)),
      liftL2_mulL2_ae sinYTorus (du 0), liftL2_mulL2_ae sinXTorus (du 1)] with p h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    simp only [Hu, sinYTorus, sinXTorus, torusFunR_torusProj, real_smul, Function.comp_apply]
  have hfH : (fun p ↦ f p • Hu p) =ᵐ[volume] fun p ↦ f p • liftL2 Hu' p := by
    filter_upwards [hH] with p hp
    rw [hp]
  rw [squarePairing_congr_ae EventuallyEq.rfl hH, squarePairing_congr_ae hfH EventuallyEq.rfl,
    squarePairing_smul_liftL2_add₃ hW₁.continuous hpW₁ hW₂.continuous hpW₂ hhalf
      (hpd.const_mul (1 / 2)),
    squarePairing_smul_liftL2 hf.continuous hpf]
  rw [inner_add_right, inner_add_right] at V
  exact V

/-- The virial identity for a pair `ω', ψ'` with Fourier derivatives, when the transport
derivative of `a = ω' + ψ'` is `λω'` up to an error `r`:
`2λ Re ⟪ω', Dψ'⟫ = λ Re ⟪a, fω'⟫ + Re ⟪a, f r⟫ - 2 Re ⟪r, Da⟫`. This is `virial_h1_torus`
for `a`, where `Re ⟪ω', Dω'⟫ = 0` removes the `ω'ω'` term. -/
theorem virial_eps_identity {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    (hhalf : Continuous fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p)
    (hphalf : IsPeriodicLift fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p)
    {lam : ℝ} {ω' ψ' r : L2} {dω dψ : Fin 2 → L2}
    (hdω : ∀ j, HasFourierPartial j ω' (dω j)) (hdψ : ∀ j, HasFourierPartial j ψ' (dψ j))
    (hr : -I • (mulL2 sinYTorus (dω 0 + dψ 0) - mulL2 sinXTorus (dω 1 + dψ 1)) =
      (lam : ℂ) • ω' + r) :
    2 * lam * (⟪ω', mulL2 (torusFunR hW₁.continuous hpW₁) (dψ 0) +
        mulL2 (torusFunR hW₂.continuous hpW₂) (dψ 1) +
        mulL2 (torusFunR hhalf hphalf) ψ'⟫_ℂ).re =
      lam * (⟪ω' + ψ', mulL2 (torusFunR hf.continuous hpf) ω'⟫_ℂ).re +
        (⟪ω' + ψ', mulL2 (torusFunR hf.continuous hpf) r⟫_ℂ).re -
        2 * (⟪r, mulL2 (torusFunR hW₁.continuous hpW₁) (dω 0 + dψ 0) +
          mulL2 (torusFunR hW₂.continuous hpW₂) (dω 1 + dψ 1) +
          mulL2 (torusFunR hhalf hphalf) (ω' + ψ')⟫_ℂ).re := by
  have hda (j : Fin 2) : HasFourierPartial j (ω' + ψ') (dω j + dψ j) := (hdω j).add (hdψ j)
  have V := virial_h1_torus had hW₁ hW₂ hf hpW₁ hpW₂ hpf hhalf hphalf hda
  rw [hr] at V
  -- `Re ⟪ω', Dω'⟫ = 0`.
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hpd : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hdc : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real hW₁1).add (continuous_partialY_real hW₂1)
  have hd : torusFunR hdc hpd =
      torusFunR (continuous_partialX_real hW₁1) hpW₁.partialX +
        torusFunR (continuous_partialY_real hW₂1) hpW₂.partialY :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.add_apply, torusFunR_torusProj, divergence, ofReal_add]
  have ehalf : torusFunR hhalf hphalf = (1 / 2 : ℂ) • torusFunR hdc hpd :=
    torusMap_ext fun q ↦ by
      simp only [ContinuousMap.smul_apply, torusFunR_torusProj, smul_eq_mul]
      push_cast
      ring
  have h0 := re_inner_halfDensityGenL2_self (conj_torusFunR hW₁.continuous hpW₁)
    (conj_torusFunR hW₂.continuous hpW₂) (conj_torusFunR hdc hpd)
    (hasClassicalPartial_torusFunR_x hW₁1 hpW₁) (hasClassicalPartial_torusFunR_y hW₂1 hpW₂) hd
    (hdω 0) (hdω 1)
  rw [← mulL2_smul_left, ← ehalf] at h0
  have hc : conj (lam : ℂ) = lam := conj_ofReal lam
  simp only [mulL2_add_right, mulL2_smul_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hc] at V h0 ⊢
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at V h0 ⊢
  linear_combination V - 2 * lam * h0

/-- The cutoff `χ(Ψ/2)` is `1` near every point where `W`, `f` or `div W` is nonzero. -/
theorem levelCutoff_eventuallyEq_one {W₁ W₂ f : ℝ × ℝ → ℝ} {h₁ h₂ : ℝ}
    (hsupp : ∀ p, (W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0) →
      2 * h₁ ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * h₂)
    {χ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hχ1 : ∀ s ∈ Set.Ioo (h₁ - δ) (h₂ + δ), χ s = 1)
    {p : ℝ × ℝ} (hp : W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0) :
    (fun q ↦ χ (dipoleLift q / 2)) =ᶠ[nhds p] fun _ ↦ 1 := by
  have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hband : 2 * h₁ ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * h₂ := by
    rcases hp with h | h | h | h
    · exact hsupp p (Or.inl h)
    · exact hsupp p (Or.inr (Or.inl h))
    · exact hsupp p (Or.inr (Or.inr h))
    · by_contra hn
      apply h
      have hcl : IsClosed {q | 2 * h₁ ≤ dipoleLift q ∧ dipoleLift q ≤ 2 * h₂} :=
        (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
      have hev : ∀ᶠ q in nhds p, W₁ q = 0 ∧ W₂ q = 0 := by
        filter_upwards [hcl.isOpen_compl.mem_nhds hn] with q hq
        refine ⟨?_, ?_⟩ <;> by_contra hw
        · exact hq (hsupp q (Or.inl hw))
        · exact hq (hsupp q (Or.inr (Or.inl hw)))
      have h1 := coordPartial_congr_of_eventuallyEq (u := W₁) (w := fun _ ↦ 0)
        (hev.mono fun q hq ↦ hq.1) 0
      have h2 := coordPartial_congr_of_eventuallyEq (u := W₂) (w := fun _ ↦ 0)
        (hev.mono fun q hq ↦ hq.2) 1
      simp only [coordPartial, ite_true, one_ne_zero, ite_false, partialX, partialY,
        deriv_const] at h1 h2
      simp only [divergence, partialX, partialY, h1, h2, add_zero]
  have hO : Set.Ioo (h₁ - δ) (h₂ + δ) ∈ nhds (dipoleLift p / 2) :=
    Ioo_mem_nhds (by linarith [hband.1]) (by linarith [hband.2])
  filter_upwards [((hc.div_const 2).continuousAt (x := p)).preimage_mem_nhds hO] with q hq
  exact hχ1 _ hq

open Topology in
/-- Passing to the limit in `virial_eps_identity`: the error terms vanish because
`‖r_ε‖ = O(ε)` while the derivatives of the mollified `ω` are `o(1/ε)` and those of the
mollified `ψ` converge. -/
theorem virial_limit {c₁ c₂ ch cf : C(Torus, ℂ)} {lam M : ℝ} {ωε ψε rε : ℝ → L2}
    {ωd ψd : ℝ → Fin 2 → L2} {ω₀ ψ₀ : L2} {ψd₀ : Fin 2 → L2}
    (hstar : ∀ᶠ ε in 𝓝[>] 0,
      2 * lam * (⟪ωε ε, mulL2 c₁ (ψd ε 0) + mulL2 c₂ (ψd ε 1) + mulL2 ch (ψε ε)⟫_ℂ).re =
        lam * (⟪ωε ε + ψε ε, mulL2 cf (ωε ε)⟫_ℂ).re +
          (⟪ωε ε + ψε ε, mulL2 cf (rε ε)⟫_ℂ).re -
          2 * (⟪rε ε, mulL2 c₁ (ωd ε 0 + ψd ε 0) + mulL2 c₂ (ωd ε 1 + ψd ε 1) +
            mulL2 ch (ωε ε + ψε ε)⟫_ℂ).re)
    (hω : Tendsto ωε (𝓝[>] 0) (𝓝 ω₀)) (hψ : Tendsto ψε (𝓝[>] 0) (𝓝 ψ₀))
    (hψd : ∀ j, Tendsto (fun ε ↦ ψd ε j) (𝓝[>] 0) (𝓝 (ψd₀ j)))
    (hr : ∀ᶠ ε in 𝓝[>] 0, ‖rε ε‖ ≤ M * ε)
    (hωd : ∀ j, Tendsto (fun ε ↦ ε * ‖ωd ε j‖) (𝓝[>] 0) (𝓝 0)) :
    2 * lam * (⟪ω₀, mulL2 c₁ (ψd₀ 0) + mulL2 c₂ (ψd₀ 1) + mulL2 ch ψ₀⟫_ℂ).re =
      lam * (⟪ω₀ + ψ₀, mulL2 cf ω₀⟫_ℂ).re := by
  have hre := Complex.continuous_re.tendsto
  have hε : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hεpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  -- The error `r_ε` tends to zero.
  have hr0 : Tendsto rε (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hr ?_
    simpa using hε.const_mul M
  -- The main terms.
  have hL : Tendsto (fun ε ↦ 2 * lam * (⟪ωε ε, mulL2 c₁ (ψd ε 0) + mulL2 c₂ (ψd ε 1) +
      mulL2 ch (ψε ε)⟫_ℂ).re) (𝓝[>] 0)
      (𝓝 (2 * lam * (⟪ω₀, mulL2 c₁ (ψd₀ 0) + mulL2 c₂ (ψd₀ 1) + mulL2 ch ψ₀⟫_ℂ).re)) :=
    ((hre _).comp (hω.inner (((tendsto_mulL2 c₁ (hψd 0)).add (tendsto_mulL2 c₂ (hψd 1))).add
      (tendsto_mulL2 ch hψ)))).const_mul _
  have hR1 : Tendsto (fun ε ↦ lam * (⟪ωε ε + ψε ε, mulL2 cf (ωε ε)⟫_ℂ).re) (𝓝[>] 0)
      (𝓝 (lam * (⟪ω₀ + ψ₀, mulL2 cf ω₀⟫_ℂ).re)) :=
    ((hre _).comp ((hω.add hψ).inner (tendsto_mulL2 cf hω))).const_mul _
  have hR2 : Tendsto (fun ε ↦ (⟪ωε ε + ψε ε, mulL2 cf (rε ε)⟫_ℂ).re) (𝓝[>] 0) (𝓝 0) := by
    have := (hre _).comp ((hω.add hψ).inner (tendsto_mulL2 cf hr0))
    have e : mulL2 cf 0 = 0 := by
      have := mulL2_smul_right cf 0 0
      simpa using this
    simpa [e, Function.comp_def] using this
  -- The commutator error: `‖r_ε‖ ‖D a_ε‖ ≤ M ε ‖D a_ε‖ → 0`.
  have hR3 : Tendsto (fun ε ↦ (⟪rε ε, mulL2 c₁ (ωd ε 0 + ψd ε 0) + mulL2 c₂ (ωd ε 1 + ψd ε 1) +
      mulL2 ch (ωε ε + ψε ε)⟫_ℂ).re) (𝓝[>] 0) (𝓝 0) := by
    set B : ℝ → ℝ := fun ε ↦ M * (‖c₁‖ * (ε * ‖ωd ε 0‖ + ε * ‖ψd ε 0‖) +
      ‖c₂‖ * (ε * ‖ωd ε 1‖ + ε * ‖ψd ε 1‖) + ‖ch‖ * (ε * ‖ωε ε‖ + ε * ‖ψε ε‖))
    have hεn {x : ℝ → L2} {y : L2} (h : Tendsto x (𝓝[>] 0) (𝓝 y)) :
        Tendsto (fun ε ↦ ε * ‖x ε‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using hε.mul h.norm
    have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
      have := (((((hωd 0).add (hεn (hψd 0))).const_mul ‖c₁‖).add
        (((hωd 1).add (hεn (hψd 1))).const_mul ‖c₂‖)).add
        (((hεn hω).add (hεn hψ)).const_mul ‖ch‖)).const_mul M
      simpa [B] using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hB
    filter_upwards [hr, hεpos] with ε hrε hε0
    have hM : 0 ≤ M := by
      by_contra hM
      have := (norm_nonneg (rε ε)).trans hrε
      nlinarith
    refine (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans ?_)
    have hD : ‖mulL2 c₁ (ωd ε 0 + ψd ε 0) + mulL2 c₂ (ωd ε 1 + ψd ε 1) +
        mulL2 ch (ωε ε + ψε ε)‖ ≤ ‖c₁‖ * (‖ωd ε 0‖ + ‖ψd ε 0‖) +
          ‖c₂‖ * (‖ωd ε 1‖ + ‖ψd ε 1‖) + ‖ch‖ * (‖ωε ε‖ + ‖ψε ε‖) := by
      refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_) <;>
        refine (norm_mulL2_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (norm_nonneg _))
    calc ‖rε ε‖ * _ ≤ (M * ε) * (‖c₁‖ * (‖ωd ε 0‖ + ‖ψd ε 0‖) +
          ‖c₂‖ * (‖ωd ε 1‖ + ‖ψd ε 1‖) + ‖ch‖ * (‖ωε ε‖ + ‖ψε ε‖)) :=
          mul_le_mul hrε hD (norm_nonneg _) (by positivity)
      _ = B ε := by simp only [B]; ring
  have hR := (hR1.add hR2).sub (hR3.const_mul 2)
  simp only [add_zero, mul_zero, sub_zero] at hR
  exact tendsto_nhds_unique (hL.congr' hstar) hR

open MeasureTheory in
/-- Integration by parts for the stream function (`lem:stream-ibp`): for `ω ∈ L²` with mean
    zero, `ψ = Δ⁻¹ω ∈ H²` and smooth periodic real `φ`, with `K = |∇ψ|² + Re(ωψ̄)`,
    `½∫ Δφ |ψ|² = ∫ φK = -∫ Re(ψ̄ ∇φ·∇ψ)` over the period square. On the torus both are
    integrations by parts `⟪b, ∂ⱼa⟫ = -⟪∂ⱼb, a⟫` (Parseval) with `b = φψ` or `b = ∂ⱼφ ψ`,
    whose Fourier derivatives come from the product rule; `Δψ = ω` uses the mean zero. No
    approximation of `ψ` is needed. -/
theorem stream_ibp {ω : L2} (hω : MeanZero ω) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hpφ : IsPeriodicLift φ) :
    (1 / 2) * (squarePairing (fun p ↦ laplacian φ p • streamLift ω p) (streamLift ω)).re =
      squareIntegral (fun p ↦ φ p * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 +
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) ∧
    squareIntegral (fun p ↦ φ p * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 +
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) =
      -squareIntegral (fun p ↦ (streamLift ω p * (starRingEnd ℂ)
        (partialX φ p • streamLiftX ω p + partialY φ p • streamLiftY ω p)).re) := by
  -- The multipliers `φ`, `∂ⱼφ`, `∂ⱼ²φ` as continuous real-valued functions on the torus.
  let φc : ℝ × ℝ → ℂ := fun q ↦ (φ q : ℂ)
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φc := Complex.ofRealCLM.contDiff.comp hφ
  have h2 : ContDiff ℝ (1 + 1) φc := hφc.of_le (WithTop.coe_le_coe.2 le_top)
  have h1 : ContDiff ℝ 1 φc := hφc.of_le (by exact_mod_cast le_top)
  have hpc : IsPeriodicLift φc := fun q ↦ by simp only [φc, (hpφ q).1, (hpφ q).2, and_self]
  have h2x : ContDiff ℝ 1 (partialX φc) := contDiff_partialX h2
  have h2y : ContDiff ℝ 1 (partialY φc) := contDiff_partialY h2
  have hdx : Differentiable ℝ (partialX φ) :=
    (contDiff_partialX (n := 1) (hφ.of_le (WithTop.coe_le_coe.2 le_top))).differentiable one_ne_zero
  have hdy : Differentiable ℝ (partialY φ) :=
    (contDiff_partialY (n := 1) (hφ.of_le (WithTop.coe_le_coe.2 le_top))).differentiable one_ne_zero
  have hx : partialX φc = fun q ↦ ((partialX φ q : ℝ) : ℂ) := partialX_ofReal hd
  have hy : partialY φc = fun q ↦ ((partialY φ q : ℝ) : ℂ) := partialY_ofReal hd
  let c := torusFun h1.continuous hpc
  let cx := torusFun h2x.continuous hpc.partialX
  let cy := torusFun h2y.continuous hpc.partialY
  let cxx := torusFun (continuous_partialX_of_contDiff h2x) hpc.partialX.partialX
  let cyy := torusFun (continuous_partialY_of_contDiff h2y) hpc.partialY.partialY
  have hcx : HasClassicalPartial 0 c cx := hasClassicalPartial_torusFun_x h1 hpc
  have hcy : HasClassicalPartial 1 c cy := hasClassicalPartial_torusFun_y h1 hpc
  have hcxx : HasClassicalPartial 0 cx cxx := hasClassicalPartial_torusFun_x h2x hpc.partialX
  have hcyy : HasClassicalPartial 1 cy cyy := hasClassicalPartial_torusFun_y h2y hpc.partialY
  have vc (q : ℝ × ℝ) : c (torusProj q) = (φ q : ℂ) := torusFun_torusProj _ _ q
  have vcx (q : ℝ × ℝ) : cx (torusProj q) = ((partialX φ q : ℝ) : ℂ) := by
    simp only [cx, torusFun_torusProj, hx]
  have vcy (q : ℝ × ℝ) : cy (torusProj q) = ((partialY φ q : ℝ) : ℂ) := by
    simp only [cy, torusFun_torusProj, hy]
  have vcxx (q : ℝ × ℝ) : cxx (torusProj q) = ((partialX (partialX φ) q : ℝ) : ℂ) := by
    simp only [cxx, torusFun_torusProj, hx, partialX_ofReal hdx]
  have vcyy (q : ℝ × ℝ) : cyy (torusProj q) = ((partialY (partialY φ) q : ℝ) : ℂ) := by
    simp only [cyy, torusFun_torusProj, hy, partialY_ofReal hdy]
  have real {b : C(Torus, ℂ)} {v : ℝ × ℝ → ℝ} (hv : ∀ q, b (torusProj q) = (v q : ℂ))
      (t : Torus) : (starRingEnd ℂ) (b t) = b t := by
    obtain ⟨q, rfl⟩ := torusProj_surjective t
    rw [hv, Complex.conj_ofReal]
  -- The integrations by parts on the torus.
  set ψ := invLap ω
  set ψx := streamPartial 0 ω
  set ψy := streamPartial 1 ω
  have dψx : HasFourierPartial 0 ψ ψx := hasFourierPartial_streamPartial ω 0
  have dψy : HasFourierPartial 1 ψ ψy := hasFourierPartial_streamPartial ω 1
  have IBx := inner_swap_of_hasFourierPartial
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0) (hasFourierPartial_mulL2 hcx dψx)
  have IBy := inner_swap_of_hasFourierPartial
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1) (hasFourierPartial_mulL2 hcy dψy)
  have IAx := inner_swap_of_hasFourierPartial dψx (hasFourierPartial_mulL2 hcxx dψx)
  have IAy := inner_swap_of_hasFourierPartial dψy (hasFourierPartial_mulL2 hcyy dψy)
  rw [inner_add_left, inner_mulL2_swap (real vcx) ψx ψ] at IAx
  rw [inner_add_left, inner_mulL2_swap (real vcy) ψy ψ] at IAy
  have eB : ⟪mulL2 c ψ, ω⟫_ℂ = -(⟪mulL2 cx ψ, ψx⟫_ℂ + ⟪mulL2 c ψx, ψx⟫_ℂ) -
      (⟪mulL2 cy ψ, ψy⟫_ℂ + ⟪mulL2 c ψy, ψy⟫_ℂ) := by
    rw [← streamSecondPartial_add hω, inner_add_right, IBx, IBy, inner_add_left, inner_add_left]
    ring
  have eAx := congrArg Complex.re IAx
  have eAy := congrArg Complex.re IAy
  have eBr := congrArg Complex.re eB
  simp only [Complex.neg_re, Complex.add_re, Complex.sub_re, Complex.conj_re] at eAx eAy eBr
  -- The three integrals over the period square as torus inner products.
  have i (b : C(Torus, ℂ)) (g h : L2) := integrable_continuous_mul_inner b g h
  have T0 : squarePairing (fun p ↦ laplacian φ p • streamLift ω p) (streamLift ω) =
      ⟪mulL2 cxx ψ, ψ⟫_ℂ + ⟪mulL2 cyy ψ, ψ⟫_ℂ := by
    rw [inner_mulL2 (real vcxx), inner_mulL2 (real vcyy), ← integral_add (i _ _ _) (i _ _ _)]
    refine Eq.trans ?_ (squareIntegral_comp_torusProj ((i _ _ _).add (i _ _ _)).1)
    unfold squarePairing
    congr 1
    funext q
    simp only [streamLift, liftL2, vcxx, vcyy, laplacian, Complex.real_smul]
    push_cast
    ring
  have T1 : squareIntegral (fun p ↦ φ p * (‖streamLiftX ω p‖ ^ 2 + ‖streamLiftY ω p‖ ^ 2 +
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re)) =
      (⟪mulL2 c ψx, ψx⟫_ℂ + ⟪mulL2 c ψy, ψy⟫_ℂ + ⟪mulL2 c ψ, ω⟫_ℂ).re := by
    have h12 : Integrable (fun t ↦ c t * ((starRingEnd ℂ) (ψx t) * ψx t) +
        c t * ((starRingEnd ℂ) (ψy t) * ψy t)) := (i _ _ _).add (i _ _ _)
    have h123 : Integrable (fun t ↦ c t * ((starRingEnd ℂ) (ψx t) * ψx t) +
        c t * ((starRingEnd ℂ) (ψy t) * ψy t) + c t * ((starRingEnd ℂ) (ψ t) * ω t)) :=
      h12.add (i _ _ _)
    rw [inner_mulL2 (real vc), inner_mulL2 (real vc), inner_mulL2 (real vc),
      ← integral_add (i _ _ _) (i _ _ _), ← integral_add h12 (i _ _ _)]
    have hre := integral_re h123
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine Eq.trans ?_ (squareIntegral_comp_torusProj h123.1.re)
    congr 1
    funext q
    simp only [streamLift, streamLiftX, streamLiftY, liftL2, vc,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    ring
  have T2 : squareIntegral (fun p ↦ (streamLift ω p * (starRingEnd ℂ)
        (partialX φ p • streamLiftX ω p + partialY φ p • streamLiftY ω p)).re) =
      (⟪mulL2 cx ψ, ψx⟫_ℂ + ⟪mulL2 cy ψ, ψy⟫_ℂ).re := by
    have h12 : Integrable (fun t ↦ cx t * ((starRingEnd ℂ) (ψ t) * ψx t) +
        cy t * ((starRingEnd ℂ) (ψ t) * ψy t)) := (i _ _ _).add (i _ _ _)
    rw [inner_mulL2 (real vcx), inner_mulL2 (real vcy), ← integral_add (i _ _ _) (i _ _ _),
]
    have hre := integral_re h12
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine Eq.trans ?_ (squareIntegral_comp_torusProj h12.1.re)
    congr 1
    funext q
    simp only [streamLift, streamLiftX, streamLiftY, liftL2, vcx, vcy,
      Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [T0, T1, T2]
  simp only [Complex.add_re]
  constructor <;> linarith

open Topology Set in
/-- The first virial identity for an `L²` eigenfunction: `Re⟨fω, ω + ψ⟩ = 2 Re⟨Dψ, ω⟩`.
The proof mollifies across the orbits (`transversalMollifier`), periodizes the outputs
(`boxPeriodize`), applies the `H¹` identity (`virial_eps_identity`) and passes to the limit
(`virial_limit`). -/
theorem virial_l2_first {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₂1 : h₂ < 1)
    (hsupp : ∀ p, (W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0) →
      2 * h₁ ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * h₂)
    {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) :
    (squarePairing (fun p ↦ f p • liftL2 ω p) (fun p ↦ liftL2 ω p + streamLift ω p)).re =
      2 * (squarePairing (fun p ↦ W₁ p • streamLiftX ω p + W₂ p • streamLiftY ω p +
        ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift ω p) (liftL2 ω)).re := by
  /- Coefficients. -/
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hpd : IsPeriodicLift (divergence W₁ W₂) := hpW₁.partialX.add hpW₂.partialY
  have hdc : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real hW₁1).add (continuous_partialY_real hW₂1)
  have hhalf : Continuous fun p ↦ (1 / 2 : ℝ) * divergence W₁ W₂ p := continuous_const.mul hdc
  have hphalf := hpd.const_mul (1 / 2)
  set c₁ := torusFunR hW₁.continuous hpW₁
  set c₂ := torusFunR hW₂.continuous hpW₂
  set ch := torusFunR hhalf hphalf
  set cf := torusFunR hf.continuous hpf
  /- The claim as an identity of torus inner products. -/
  simp only [streamLift, streamLiftX, streamLiftY]
  rw [squarePairing_smul_liftL2_add_right hf.continuous hpf,
    squarePairing_smul_liftL2_add₃ hW₁.continuous hpW₁ hW₂.continuous hpW₂ hhalf hphalf,
    ← inner_add_right, ← inner_add_right, ← inner_add_left]
  set ψ := invLap ω
  suffices H : 2 * lam * (⟪ω, mulL2 c₁ (streamPartial 0 ω) + mulL2 c₂ (streamPartial 1 ω) +
      mulL2 ch ψ⟫_ℂ).re = lam * (⟪ω + ψ, mulL2 cf ω⟫_ℂ).re by
    have h2 := mul_left_cancel₀ hlam (show lam * (⟪ω + ψ, mulL2 cf ω⟫_ℂ).re = lam *
      (2 * (⟪ω, mulL2 c₁ (streamPartial 0 ω) + mulL2 c₂ (streamPartial 1 ω) +
        mulL2 ch ψ⟫_ℂ).re) by linarith)
    exact h2
  /- The cutoff `χ(Ψ/2)`, equal to `1` near the supports of `W`, `f` and `div W`. -/
  obtain ⟨χ, hχ, hχs, hχ0, δ, hδ, hχ1⟩ := exists_levelCutoff h₁0 h₂1
  set cP : ℝ × ℝ → ℝ := fun p ↦ χ (dipoleLift p / 2)
  have hcP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cP :=
    hχ.comp (((Real.contDiff_cos.comp contDiff_fst).add
      (Real.contDiff_cos.comp contDiff_snd)).div_const 2)
  have hcP1 : ContDiff ℝ 1 cP := hcP.of_le (by simp)
  have hpcP : IsPeriodicLift cP := fun q ↦ by simp [cP, dipoleLift, Real.cos_add_two_pi]
  have hcPj (j : Fin 2) : Continuous (coordPartial j cP) := by
    unfold coordPartial
    split_ifs
    · exact continuous_partialX_real hcP1
    · exact continuous_partialY_real hcP1
  have hpcPj (j : Fin 2) : IsPeriodicLift (coordPartial j cP) := by
    unfold coordPartial
    split_ifs
    · exact hpcP.partialX
    · exact hpcP.partialY
  set c := torusFunR hcP.continuous hpcP
  have hh₁ : 0 < h₁ / 2 := by positivity
  have hcell {p : ℝ × ℝ} (hp : p ∈ periodBox) := cellCutoff_eventuallyEq hh₁ hχ0 hp
  have hone {p : ℝ × ℝ} (hp : W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0) :=
    levelCutoff_eventuallyEq_one hsupp hδ hχ1 hp
  /- The eigenfunction equation on the cell. -/
  set u := liftL2 ω
  set v := liftL2 ψ
  set g : Fin 2 → ℝ × ℝ → ℂ := fun j ↦ liftL2 (streamPartial j ω)
  have hBC : volume.restrict cellSquare ≤ volume.restrict periodBox :=
    Measure.restrict_mono cellSquare_subset_periodBox le_rfl
  have huC : MemLp u 2 (volume.restrict cellSquare) := (memLp_liftL2_periodBox ω).mono_measure hBC
  have hvC : MemLp v 2 (volume.restrict cellSquare) := (memLp_liftL2_periodBox ψ).mono_measure hBC
  have hgC (j : Fin 2) : MemLp (g j) 2 (volume.restrict cellSquare) :=
    (memLp_liftL2_periodBox _).mono_measure hBC
  have hT : HasWeakL0On cellSquare (u + v) (fun p ↦ I * (lam * u p)) :=
    (isTransportPair_of_isEigenSolution hlam hω isOrbitUnion_cellNeighbourhood
      isBounded_cellNeighbourhood).hasWeakL0On.mono
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  have hgv (j : Fin 2) : HasWeakPartialOn cellSquare j v (g j) :=
    hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω j) cellSquare
  set kω : ℝ × ℝ → ℂ := fun p ↦ I * (lam * u p) -
    ((Real.sin p.2 : ℂ) * g 0 p - (Real.sin p.1 : ℂ) * g 1 p)
  have hL0u : HasWeakL0On cellSquare u kω :=
    (hT.sub (HasWeakPartialOn.hasWeakL0On isOpen_cellSquare (hgv 0) (hgv 1))).congr_value
      (Eventually.of_forall fun p ↦ by simp)
  have hsin {μ : Measure (ℝ × ℝ)} {a : ℝ × ℝ → ℝ} (ha : Continuous a) {G : ℝ × ℝ → ℂ}
      (hG : MemLp G 2 μ) : MemLp (fun p ↦ (Real.sin (a p) : ℂ) * G p) 2 μ :=
    hG.of_le_mul (c := 1)
      ((continuous_ofReal.comp (Real.continuous_sin.comp ha)).aestronglyMeasurable.mul
        hG.aestronglyMeasurable) (Eventually.of_forall fun p ↦ by
        rw [norm_mul, one_mul, norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _))
  have hkuC : MemLp (fun p ↦ I * (lam * u p)) 2 (volume.restrict cellSquare) :=
    (huC.const_mul (lam : ℂ)).const_mul I
  have hkC : MemLp kω 2 (volume.restrict cellSquare) :=
    hkuC.sub ((hsin continuous_snd (hgC 0)).sub (hsin continuous_fst (hgC 1)))
  /- The mollifier. -/
  obtain ⟨K, hK, hKp, ε₀, hε₀, hJ0⟩ := transversalMollifier_eq_zero hχs
  have hKc : K ⊆ cellSquare := hKp.trans sdiff_subset
  obtain ⟨ε₁, hε₁, C₁, hJ⟩ := memLp_transversalMollifier hχ hχs
  obtain ⟨dψ, hdψev, hdψlim⟩ := tendsto_transversalMollifier_partial hχ hχs hvC hgv hgC
  obtain ⟨dω, hdωev, hdωlim⟩ := transversalMollifier_hasWeakPartialOn hχ hχs huC hkC hL0u
  obtain ⟨ε₂, hε₂, C₂, hcomm⟩ := transversalMollifier_hasWeakL0On hχ hχs
  have hc' : ∀ ε ∈ Ioo 0 ε₂, ∃ kε, HasWeakL0On univ (transversalMollifier χ ε (u + v)) kε ∧
      MemLp kε 2 volume ∧ eLpNorm (kε - transversalMollifier χ ε (fun p ↦ I * (lam * u p))) 2
        volume ≤ ENNReal.ofReal (C₂ * ε) *
          eLpNorm (fun p ↦ I * (lam * u p)) 2 (volume.restrict cellSquare) :=
    fun ε hε ↦ hcomm ε hε (u + v) _ (huC.add hvC) hkuC hT
  choose! kε hkε using hc'
  set ε₃ := min ε₀ (min ε₁ ε₂)
  have hsmall : ∀ᶠ ε in 𝓝[>] 0, ε ∈ Ioo 0 ε₃ := Ioo_mem_nhdsGT (by positivity)
  /- The periodized families. -/
  set ωε : ℝ → L2 := fun ε ↦ boxPeriodize (transversalMollifier χ ε u)
  set ψε : ℝ → L2 := fun ε ↦ boxPeriodize (transversalMollifier χ ε v)
  set ωd : ℝ → Fin 2 → L2 := fun ε j ↦ boxPeriodize (dω j ε)
  set ψd : ℝ → Fin 2 → L2 := fun ε j ↦ boxPeriodize (dψ j ε)
  set rε : ℝ → L2 := fun ε ↦ -I • boxPeriodize
    (kε ε - transversalMollifier χ ε (fun p ↦ I * (lam * u p)))
  have hsy : sinYTorus = torusFun (u := fun p ↦ (Real.sin p.2 : ℂ)) (by fun_prop)
      (fun q ↦ by simp [Real.sin_add_two_pi]) :=
    torusMap_ext fun q ↦ by simp [sinYTorus, torusFunR_torusProj, torusFun_torusProj]
  have hsx : sinXTorus = torusFun (u := fun p ↦ (Real.sin p.1 : ℂ)) (by fun_prop)
      (fun q ↦ by simp [Real.sin_add_two_pi]) :=
    torusMap_ext fun q ↦ by simp [sinXTorus, torusFunR_torusProj, torusFun_torusProj]
  /- The identity at each small scale. -/
  have hstar : ∀ᶠ ε in 𝓝[>] 0,
      2 * lam * (⟪ωε ε, mulL2 c₁ (ψd ε 0) + mulL2 c₂ (ψd ε 1) + mulL2 ch (ψε ε)⟫_ℂ).re =
        lam * (⟪ωε ε + ψε ε, mulL2 cf (ωε ε)⟫_ℂ).re +
          (⟪ωε ε + ψε ε, mulL2 cf (rε ε)⟫_ℂ).re -
          2 * (⟪rε ε, mulL2 c₁ (ωd ε 0 + ψd ε 0) + mulL2 c₂ (ωd ε 1 + ψd ε 1) +
            mulL2 ch (ωε ε + ψε ε)⟫_ℂ).re := by
    filter_upwards [hsmall, hdψev, hdωev] with ε hε hψε hωε
    have hε0 : ε ∈ Ioo 0 ε₀ := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
    have hε1 : ε ∈ Ioo 0 ε₁ := ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hε2 : ε ∈ Ioo 0 ε₂ :=
      ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hJu := (hJ ε hε1 u huC).1
    have hFour {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (volume.restrict cellSquare))
        {d : Fin 2 → ℝ → ℝ × ℝ → ℂ}
        (hd : ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε w) (d j ε) ∧
          MemLp (d j ε) 2 volume) (j : Fin 2) :
        HasFourierPartial j (boxPeriodize (transversalMollifier χ ε w)) (boxPeriodize (d j ε)) :=
      hasFourierPartial_boxPeriodize hK hKc (fun p hp ↦ hJ0 ε hε0 w p hp) (hJ ε hε1 w hw).1
        (hd j).2 (hd j).1
    -- The transport derivative of the mollified `a = ω + ψ`.
    have hsum (j : Fin 2) : HasWeakPartialOn univ j
        (fun p ↦ transversalMollifier χ ε u p + transversalMollifier χ ε v p)
        (fun p ↦ dω j ε p + dψ j ε p) := (hωε j).1.add (hψε j).1
    have hL := HasWeakPartialOn.hasWeakL0On isOpen_univ (hsum 0) (hsum 1)
    have hk := (hkε ε hε2).1.congr_value (transversalMollifier_add hχ hχs hε.1 huC hvC)
    have hae := hk.ae_eq isOpen_univ hL
    have hm (j : Fin 2) : MemLp (fun p ↦ dω j ε p + dψ j ε p) 2 (volume.restrict periodBox) :=
      ((hωε j).2.add (hψε j).2).restrict _
    have hPk : boxPeriodize (kε ε) = mulL2 sinYTorus (ωd ε 0 + ψd ε 0) -
        mulL2 sinXTorus (ωd ε 1 + ψd ε 1) := by
      rw [boxPeriodize_congr (ae_restrict_of_ae (hae.mono fun p hp ↦ hp (mem_univ p)))]
      rw [show (fun p ↦ (Real.sin p.2 : ℂ) * (dω 0 ε p + dψ 0 ε p) -
          (Real.sin p.1 : ℂ) * (dω 1 ε p + dψ 1 ε p)) =
          (fun p ↦ (Real.sin p.2 : ℂ) * (dω 0 ε p + dψ 0 ε p)) -
          (fun p ↦ (Real.sin p.1 : ℂ) * (dω 1 ε p + dψ 1 ε p)) from rfl,
        boxPeriodize_sub (hsin continuous_snd (hm 0)) (hsin continuous_fst (hm 1)),
        boxPeriodize_mul (by fun_prop) (fun q ↦ by simp [Real.sin_add_two_pi]) (hm 0),
        boxPeriodize_mul (by fun_prop) (fun q ↦ by simp [Real.sin_add_two_pi]) (hm 1),
        ← hsy, ← hsx]
      rw [show (fun p ↦ dω 0 ε p + dψ 0 ε p) = dω 0 ε + dψ 0 ε from rfl,
        show (fun p ↦ dω 1 ε p + dψ 1 ε p) = dω 1 ε + dψ 1 ε from rfl,
        boxPeriodize_add ((hωε 0).2.restrict _) ((hψε 0).2.restrict _),
        boxPeriodize_add ((hωε 1).2.restrict _) ((hψε 1).2.restrict _)]
    have hJk : transversalMollifier χ ε (fun p ↦ I * (lam * u p)) =
        fun p ↦ (I * lam) * transversalMollifier χ ε u p := by
      rw [show (fun p ↦ I * (lam * u p)) = fun p ↦ (I * lam) * u p from funext fun p ↦ by ring]
      exact transversalMollifier_const_mul ε (I * lam) u
    have hPJk : boxPeriodize (transversalMollifier χ ε (fun p ↦ I * (lam * u p))) =
        (I * lam) • ωε ε := by
      rw [hJk, boxPeriodize_const_mul (hJu.restrict _)]
    have hrε : rε ε = -I • (boxPeriodize (kε ε) -
        boxPeriodize (transversalMollifier χ ε (fun p ↦ I * (lam * u p)))) := by
      simp only [rε]
      rw [boxPeriodize_sub ((hkε ε hε2).2.1.restrict _) ((hJ ε hε1 _ hkuC).1.restrict _)]
    have hr : -I • (mulL2 sinYTorus (ωd ε 0 + ψd ε 0) - mulL2 sinXTorus (ωd ε 1 + ψd ε 1)) =
        (lam : ℂ) • ωε ε + rε ε := by
      have hII : -I * (I * lam) = lam := by
        rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
      rw [hrε, ← hPk, hPJk, smul_sub, smul_smul, hII]
      abel
    exact virial_eps_identity had hW₁ hW₂ hf hpW₁ hpW₂ hpf hhalf hphalf (hFour huC hωε)
      (hFour hvC hψε) hr
  /- Limits. -/
  have hpm {a : ℝ × ℝ → ℝ} (ha : Continuous a) (hpa : IsPeriodicLift a) {μ : Measure (ℝ × ℝ)}
      {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 μ) : MemLp (fun p ↦ (a p : ℂ) * F p) 2 μ :=
    hF.of_le_mul (c := ‖torusFunR ha hpa‖)
      ((continuous_ofReal.comp ha).aestronglyMeasurable.mul hF.aestronglyMeasurable)
      (Eventually.of_forall fun p ↦ by
        rw [norm_mul, ← torusFunR_torusProj ha hpa p]
        exact mul_le_mul_of_nonneg_right ((torusFunR ha hpa).norm_coe_le_norm _) (norm_nonneg _))
  have huB := memLp_liftL2_periodBox ω
  have hvB := memLp_liftL2_periodBox ψ
  have hJev {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (volume.restrict cellSquare)) :
      ∀ᶠ ε in 𝓝[>] 0, MemLp (transversalMollifier χ ε w) 2 (volume.restrict periodBox) := by
    filter_upwards [hsmall] with ε hε
    have hε1 : ε ∈ Ioo 0 ε₁ :=
      ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    exact ((hJ ε hε1 w hw).1).restrict _
  -- `J_ε w → χ(Ψ/2) w` on the torus, for `w` a lift.
  have hlimJ {x : L2} (hx : MemLp (liftL2 x) 2 (volume.restrict cellSquare)) :
      Tendsto (fun ε ↦ boxPeriodize (transversalMollifier χ ε (liftL2 x))) (𝓝[>] 0)
        (𝓝 (mulL2 c x)) := by
    have hxB := memLp_liftL2_periodBox x
    have hG : boxPeriodize (fun p ↦ (cellCutoff χ p : ℂ) * liftL2 x p) = mulL2 c x := by
      rw [boxPeriodize_congr_box (G := fun p ↦ (cP p : ℂ) * liftL2 x p)
        (fun p hp ↦ by rw [(hcell hp).eq_of_nhds]),
        boxPeriodize_mul (g := fun p ↦ (cP p : ℂ)) (continuous_ofReal.comp hcP.continuous)
          hpcP.ofReal hxB,
        boxPeriodize_liftL2]
      rfl
    rw [← hG]
    refine tendsto_boxPeriodize (hJev hx) ?_ (tendsto_transversalMollifier hχ hχs hx)
    refine MemLp.ae_eq ?_ (hpm hcP.continuous hpcP hxB)
    exact (ae_restrict_iff' measurableSet_periodBox).2 (Eventually.of_forall fun p hp ↦ by
      simp only [(hcell hp).eq_of_nhds]
      rfl)
  have hωlim := hlimJ huC
  have hψlim := hlimJ hvC
  set cj : Fin 2 → C(Torus, ℂ) := fun j ↦ torusFunR (hcPj j) (hpcPj j)
  have hψdlim (j : Fin 2) : Tendsto (fun ε ↦ ψd ε j) (𝓝[>] 0)
      (𝓝 (mulL2 (cj j) ψ + mulL2 c (streamPartial j ω))) := by
    have hgB := memLp_liftL2_periodBox (streamPartial j ω)
    have h1 := hpm (hcPj j) (hpcPj j) hvB
    have h2 := hpm hcP.continuous hpcP hgB
    have hG : boxPeriodize (fun p ↦ ((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * v p +
        (cellCutoff χ p : ℂ) * g j p) = mulL2 (cj j) ψ + mulL2 c (streamPartial j ω) := by
      rw [boxPeriodize_congr_box (G := (fun p ↦ ((coordPartial j cP p : ℝ) : ℂ) * v p) +
        fun p ↦ (cP p : ℂ) * g j p) (fun p hp ↦ by
          simp only [Pi.add_apply, (hcell hp).eq_of_nhds,
            coordPartial_congr_of_eventuallyEq (hcell hp) j]
          rfl),
        boxPeriodize_add h1 h2,
        boxPeriodize_mul (g := fun p ↦ ((coordPartial j cP p : ℝ) : ℂ))
          (continuous_ofReal.comp (hcPj j)) (hpcPj j).ofReal hvB,
        boxPeriodize_mul (g := fun p ↦ (cP p : ℂ)) (continuous_ofReal.comp hcP.continuous)
          hpcP.ofReal hgB,
        boxPeriodize_liftL2, boxPeriodize_liftL2]
      rfl
    rw [← hG]
    refine tendsto_boxPeriodize ?_ ?_ (hdψlim j)
    · filter_upwards [hdψev] with ε hε
      exact (hε j).2.restrict _
    · refine MemLp.ae_eq ?_ (h1.add h2)
      exact (ae_restrict_iff' measurableSet_periodBox).2 (Eventually.of_forall fun p hp ↦ by
        simp only [Pi.add_apply, (hcell hp).eq_of_nhds,
          coordPartial_congr_of_eventuallyEq (hcell hp) j]
        rfl)
  -- `‖r_ε‖ = O(ε)`.
  set N := (eLpNorm (fun p ↦ I * (lam * u p)) 2 (volume.restrict cellSquare)).toReal
  have hrbound : ∀ᶠ ε in 𝓝[>] 0, ‖rε ε‖ ≤ (max C₂ 0 * N) * ε := by
    filter_upwards [hsmall] with ε hε
    have hε1 : ε ∈ Ioo 0 ε₁ :=
      ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hε2 : ε ∈ Ioo 0 ε₂ :=
      ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hd := (hkε ε hε2).2.1.sub (hJ ε hε1 _ hkuC).1
    have hfin : ENNReal.ofReal (max C₂ 0 * ε) *
        eLpNorm (fun p ↦ I * (lam * u p)) 2 (volume.restrict cellSquare) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkuC.eLpNorm_ne_top
    calc ‖rε ε‖ = ‖boxPeriodize (kε ε - transversalMollifier χ ε (fun p ↦ I * (lam * u p)))‖ := by
          simp only [rε, norm_smul, norm_neg, norm_I, one_mul]
      _ ≤ (eLpNorm (kε ε - transversalMollifier χ ε (fun p ↦ I * (lam * u p))) 2 volume).toReal :=
          norm_boxPeriodize_le hd
      _ ≤ (ENNReal.ofReal (max C₂ 0 * ε) *
            eLpNorm (fun p ↦ I * (lam * u p)) 2 (volume.restrict cellSquare)).toReal := by
          refine ENNReal.toReal_mono hfin ((hkε ε hε2).2.2.trans ?_)
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.1.le)) zero_le
      _ = (max C₂ 0 * N) * ε := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) hε.1.le)]
          ring
  -- `ε ‖∇J_ε ω‖ → 0`.
  have hωd (j : Fin 2) : Tendsto (fun ε ↦ ε * ‖ωd ε j‖) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hdωlim j)
    refine squeeze_zero' ?_ ?_ (by simpa using h)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_nonneg (le_of_lt hε) (norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, hdωev] with ε hε hωε
      simp only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hε)]
      exact mul_le_mul_of_nonneg_left (norm_boxPeriodize_le (hωε j).2) (le_of_lt hε)
  have hlim := virial_limit hstar hωlim hψlim hψdlim hrbound hωd
  /- The cutoff disappears: `χ(Ψ/2) = 1` and `∇χ(Ψ/2) = 0` where `W`, `f` and `div W` live. -/
  have hpt {w : ℝ × ℝ → ℝ}
      (hw : ∀ p, w p ≠ 0 → W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0)
      (p : ℝ × ℝ) : cP p * (w p * cP p) = w p ∧ ∀ j, cP p * (w p * coordPartial j cP p) = 0 := by
    by_cases h : w p = 0
    · simp [h]
    · have hev := hone (hw p h)
      have h1 : cP p = 1 := hev.eq_of_nhds
      have h2 (j : Fin 2) : coordPartial j cP p = 0 := by
        refine (coordPartial_congr_of_eventuallyEq hev j).trans ?_
        unfold coordPartial
        split_ifs <;> simp [partialX, partialY]
      exact ⟨by rw [h1]; ring, fun j ↦ by rw [h2]; ring⟩
  have hW₁w : ∀ p, W₁ p ≠ 0 → W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0 :=
    fun p h ↦ Or.inl h
  have hW₂w : ∀ p, W₂ p ≠ 0 → W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0 :=
    fun p h ↦ Or.inr (Or.inl h)
  have hfw : ∀ p, f p ≠ 0 → W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0 :=
    fun p h ↦ Or.inr (Or.inr (Or.inl h))
  have hdw : ∀ p, (1 / 2 : ℝ) * divergence W₁ W₂ p ≠ 0 →
      W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 ∨ divergence W₁ W₂ p ≠ 0 :=
    fun p h ↦ Or.inr (Or.inr (Or.inr (right_ne_zero_of_mul h)))
  have e1 (j : Fin 2) : c * (c₁ * cj j) = 0 := torusMap_ext fun q ↦ by
    simp only [c, c₁, cj, ContinuousMap.mul_apply, ContinuousMap.zero_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hW₁w q).2 j
  have e2 : c * (c₁ * c) = c₁ := torusMap_ext fun q ↦ by
    simp only [c, c₁, ContinuousMap.mul_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hW₁w q).1
  have e3 (j : Fin 2) : c * (c₂ * cj j) = 0 := torusMap_ext fun q ↦ by
    simp only [c, c₂, cj, ContinuousMap.mul_apply, ContinuousMap.zero_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hW₂w q).2 j
  have e4 : c * (c₂ * c) = c₂ := torusMap_ext fun q ↦ by
    simp only [c, c₂, ContinuousMap.mul_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hW₂w q).1
  have e5 : c * (ch * c) = ch := torusMap_ext fun q ↦ by
    simp only [c, ch, ContinuousMap.mul_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hdw q).1
  have e6 : c * (cf * c) = cf := torusMap_ext fun q ↦ by
    simp only [c, cf, ContinuousMap.mul_apply, torusFunR_torusProj]
    exact_mod_cast (hpt hfw q).1
  have hrc : ∀ t, conj (c t) = c t := conj_torusFunR hcP.continuous hpcP
  rw [← inner_mulL2_right hrc, ← mulL2_add_right, ← inner_mulL2_right hrc] at hlim
  simp only [mulL2_add_right, mulL2_mulL2, e1, e2, e3, e4, e5, e6, mulL2_zero_left,
    zero_add] at hlim
  exact hlim

/-- The virial identities for an `L²` eigenfunction (`lem:virial-l2`), for a smooth adapted
    field supported in the annulus `{2h₁ ≤ Ψ ≤ 2h₂}`: `Re⟨fω, ω + ψ⟩ = 2 Re⟨Dψ, ω⟩` with
    `D = W·∇ + ½ div W`, and the quadratic form
    `∫ f|ω|² + ∫ (2 sym DW - f I)∇ψ·∇ψ̄ + ½ ∫ Δ(f - div W)|ψ|² = 0`. -/
theorem virial_l2 {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 3 W₁) (hW₂ : ContDiff ℝ 3 W₂) (hf : ContDiff ℝ 2 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₂1 : h₂ < 1)
    (hsupp : ∀ p, (W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0) →
      2 * h₁ ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * h₂)
    {lam : ℝ} (hlam : lam ≠ 0) {ω : L2} (hω : IsEigenSolution lam ω) :
    (squarePairing (fun p ↦ f p • liftL2 ω p) (fun p ↦ liftL2 ω p + streamLift ω p)).re =
      2 * (squarePairing (fun p ↦ W₁ p • streamLiftX ω p + W₂ p • streamLiftY ω p +
        ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift ω p) (liftL2 ω)).re ∧
    (squarePairing (fun p ↦ f p • liftL2 ω p) (liftL2 ω)).re +
      2 * ((squarePairing (fun p ↦ partialX W₁ p • streamLiftX ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialX W₂ p • streamLiftY ω p) (streamLiftX ω)).re +
        (squarePairing (fun p ↦ partialY W₁ p • streamLiftX ω p) (streamLiftY ω)).re +
        (squarePairing (fun p ↦ partialY W₂ p • streamLiftY ω p) (streamLiftY ω)).re) -
      (squarePairing (fun p ↦ f p • streamLiftX ω p) (streamLiftX ω)).re -
      (squarePairing (fun p ↦ f p • streamLiftY ω p) (streamLiftY ω)).re +
      (1 / 2) * (squarePairing
        (fun p ↦ laplacian (fun q ↦ f q - divergence W₁ W₂ q) p • streamLift ω p)
        (streamLift ω)).re = 0 := by
  have h1 := virial_l2_first had (hW₁.of_le (by norm_num)) (hW₂.of_le (by norm_num))
    (hf.of_le (by norm_num)) hpW₁ hpW₂ hpf h₁0 h₂1 hsupp hlam hω
  refine ⟨h1, ?_⟩
  have h := re_virialForm_eq_quadratic hW₁ hW₂ hf hpW₁ hpW₂ hpf hω.1
  linarith

end NoEmbeddedEigenvalues
