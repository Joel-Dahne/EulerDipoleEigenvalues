module

public import EulerDipoleEigenvalues.Virial.VirialSmooth

/-!
# The quadratic form of the smooth virial identity

Blueprint: `lem:virial-smooth-quadratic`.

Substituting `ω = Δψ` into `Re ⟨f ω, ω + ψ⟩ = 2 Re ⟨D ψ, ω⟩` and integrating by parts
gives `0 = ∫ f |Δψ|² + ∫ (2 sym DW - f I) ∇ψ · ∇ψ̄ + ½ ∫ Δ(f - div W) |ψ|²`.
All integrations by parts come from skew-symmetry: `∂ₓ` and `∂_y` are the
half-density generators of the constant fields `(1, 0)` and `(0, 1)`.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real Complex ComplexConjugate

variable {u v ψ : ℝ × ℝ → ℂ} {W₁ W₂ f g : ℝ × ℝ → ℝ}

/-! ### Skew-symmetry of the partial derivatives -/

theorem halfDensityGen_one_zero (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    halfDensityGen (fun _ ↦ 1) (fun _ ↦ 0) u p = partialX u p := by
  have h1 : partialX (fun _ : ℝ × ℝ ↦ (1 : ℝ)) p = 0 := (hasDerivAt_const p.1 1).deriv
  have h2 : partialY (fun _ : ℝ × ℝ ↦ (0 : ℝ)) p = 0 := (hasDerivAt_const p.2 0).deriv
  simp [halfDensityGen, fieldDeriv, divergence, h1, h2]

theorem halfDensityGen_zero_one (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    halfDensityGen (fun _ ↦ 0) (fun _ ↦ 1) u p = partialY u p := by
  have h1 : partialX (fun _ : ℝ × ℝ ↦ (0 : ℝ)) p = 0 := (hasDerivAt_const p.1 0).deriv
  have h2 : partialY (fun _ : ℝ × ℝ ↦ (1 : ℝ)) p = 0 := (hasDerivAt_const p.2 1).deriv
  simp [halfDensityGen, fieldDeriv, divergence, h1, h2]

theorem isPeriodicLift_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) :
    IsPeriodicLift (fun _ : ℝ × ℝ ↦ c) := fun _ ↦ ⟨rfl, rfl⟩

/-- `∂ₓ` is skew-symmetric for the pairing. -/
theorem squarePairing_partialX (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hpu : IsPeriodicLift u) (hpv : IsPeriodicLift v) :
    squarePairing (partialX u) v = -squarePairing u (partialX v) := by
  have h := squarePairing_halfDensityGen contDiff_const contDiff_const
    (isPeriodicLift_const 1) (isPeriodicLift_const 0) hu hv hpu hpv
  simpa only [show ∀ w : ℝ × ℝ → ℂ, halfDensityGen (fun _ ↦ 1) (fun _ ↦ 0) w = partialX w from
    fun w ↦ funext (halfDensityGen_one_zero w)] using h

/-- `∂_y` is skew-symmetric for the pairing. -/
theorem squarePairing_partialY (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hpu : IsPeriodicLift u) (hpv : IsPeriodicLift v) :
    squarePairing (partialY u) v = -squarePairing u (partialY v) := by
  have h := squarePairing_halfDensityGen contDiff_const contDiff_const
    (isPeriodicLift_const 0) (isPeriodicLift_const 1) hu hv hpu hpv
  simpa only [show ∀ w : ℝ × ℝ → ℂ, halfDensityGen (fun _ ↦ 0) (fun _ ↦ 1) w = partialY w from
    fun w ↦ funext (halfDensityGen_zero_one w)] using h

theorem squarePairing_add_right {w : ℝ × ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    squarePairing u (fun p ↦ v p + w p) = squarePairing u v + squarePairing u w := by
  rw [squarePairing_comm, squarePairing_add_left hv hw hu, map_add, ← squarePairing_comm,
    ← squarePairing_comm]

/-- For real `g`, `Re ⟨g u, ∂ₓu⟩ = -½ ⟨(∂ₓg) u, u⟩`. -/
theorem re_squarePairing_smul_partialX (hg : ContDiff ℝ 1 g) (hpg : IsPeriodicLift g)
    (hu : ContDiff ℝ 1 u) (hpu : IsPeriodicLift u) :
    (squarePairing (fun p ↦ g p • u p) (partialX u)).re =
      -(1 / 2) * (squarePairing (fun p ↦ partialX g p • u p) u).re := by
  have hgu : ContDiff ℝ 1 (fun p ↦ g p • u p) := hg.smul hu
  have hpgu : IsPeriodicLift (fun p ↦ g p • u p) := fun q ↦ by
    simp [(hpg q).1, (hpg q).2, (hpu q).1, (hpu q).2]
  have hgx := (contDiff_partialX (n := 0) (by simpa using hg)).continuous
  have hux := (contDiff_partialX (n := 0) (by simpa using hu)).continuous
  have hskew := squarePairing_partialX hgu hu hpgu hpu
  have hprod : partialX (fun p ↦ g p • u p) = fun p ↦ partialX g p • u p + g p • partialX u p :=
    funext fun p ↦ by
      rw [partialX_smul ((hg.differentiable one_ne_zero) p) ((hu.differentiable one_ne_zero) p),
        add_comm]
  rw [hprod, squarePairing_add_left (u := fun p ↦ partialX g p • u p)
      (v := fun p ↦ g p • partialX u p) (by fun_prop) (by fun_prop) hu.continuous,
    squarePairing_real_smul (u := partialX u) g u,
    squarePairing_comm (fun p ↦ g p • u p) (partialX u)] at hskew
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.conj_re, Complex.neg_re] at this
  linarith

/-- For real `g`, `Re ⟨g u, ∂_yu⟩ = -½ ⟨(∂_yg) u, u⟩`. -/
theorem re_squarePairing_smul_partialY (hg : ContDiff ℝ 1 g) (hpg : IsPeriodicLift g)
    (hu : ContDiff ℝ 1 u) (hpu : IsPeriodicLift u) :
    (squarePairing (fun p ↦ g p • u p) (partialY u)).re =
      -(1 / 2) * (squarePairing (fun p ↦ partialY g p • u p) u).re := by
  have hgu : ContDiff ℝ 1 (fun p ↦ g p • u p) := hg.smul hu
  have hpgu : IsPeriodicLift (fun p ↦ g p • u p) := fun q ↦ by
    simp [(hpg q).1, (hpg q).2, (hpu q).1, (hpu q).2]
  have hgy := (contDiff_partialY (n := 0) (by simpa using hg)).continuous
  have huy := (contDiff_partialY (n := 0) (by simpa using hu)).continuous
  have hskew := squarePairing_partialY hgu hu hpgu hpu
  have hprod : partialY (fun p ↦ g p • u p) = fun p ↦ partialY g p • u p + g p • partialY u p :=
    funext fun p ↦ by
      rw [partialY_smul ((hg.differentiable one_ne_zero) p) ((hu.differentiable one_ne_zero) p),
        add_comm]
  rw [hprod, squarePairing_add_left (u := fun p ↦ partialY g p • u p)
      (v := fun p ↦ g p • partialY u p) (by fun_prop) (by fun_prop) hu.continuous,
    squarePairing_real_smul (u := partialY u) g u,
    squarePairing_comm (fun p ↦ g p • u p) (partialY u)] at hskew
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.conj_re, Complex.neg_re] at this
  linarith

/-- Regularity facts for a periodic `C²` function, used below. -/
theorem contDiff_partialX_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ × ℝ → E} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (partialX h) :=
  contDiff_partialX (n := 1) hh

theorem contDiff_partialY_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ × ℝ → E} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (partialY h) :=
  contDiff_partialY (n := 1) hh

/-- One coordinate of the Laplacian term: with `ψ₁ = ∂ₓψ`,
    `Re ⟨∂ₓψ₁, f ψ⟩ = -Re ⟨f ψ₁, ψ₁⟩ + ½ Re ⟨(∂ₓ² f) ψ, ψ⟩`. -/
theorem re_squarePairing_partialX_partialX (hf : ContDiff ℝ 2 f) (hpf : IsPeriodicLift f)
    (hψ : ContDiff ℝ 2 ψ) (hpψ : IsPeriodicLift ψ) :
    (squarePairing (partialX (partialX ψ)) (fun p ↦ f p • ψ p)).re =
      -(squarePairing (fun p ↦ f p • partialX ψ p) (partialX ψ)).re +
        (1 / 2) * (squarePairing (fun p ↦ partialX (partialX f) p • ψ p) ψ).re := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hψx := contDiff_partialX_one hψ
  have hfx := contDiff_partialX_one hf
  have hfψ : ContDiff ℝ 1 (fun p ↦ f p • ψ p) := hf1.smul hψ1
  have hpfψ : IsPeriodicLift (fun p ↦ f p • ψ p) := fun q ↦ by
    simp [(hpf q).1, (hpf q).2, (hpψ q).1, (hpψ q).2]
  have hskew := squarePairing_partialX hψx hfψ hpψ.partialX hpfψ
  have hprod : partialX (fun p ↦ f p • ψ p) = fun p ↦ partialX f p • ψ p + f p • partialX ψ p :=
    funext fun p ↦ by
      rw [partialX_smul ((hf1.differentiable one_ne_zero) p) ((hψ1.differentiable one_ne_zero) p),
        add_comm]
  have hfc := hf.continuous
  have hψc := hψ.continuous
  have hfxc := hfx.continuous
  have hψxc := hψx.continuous
  rw [hprod, squarePairing_add_right (u := partialX ψ) (v := fun p ↦ partialX f p • ψ p)
    (w := fun p ↦ f p • partialX ψ p) hψxc (by fun_prop) (by fun_prop),
    squarePairing_comm (fun p ↦ partialX f p • ψ p) (partialX ψ),
    ← squarePairing_real_smul (u := partialX ψ) f (partialX ψ)] at hskew
  have hkey := re_squarePairing_smul_partialX hfx hpf.partialX hψ1 hpψ
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.conj_re, Complex.neg_re] at this
  linarith

/-- The `y` coordinate of the Laplacian term. -/
theorem re_squarePairing_partialY_partialY (hf : ContDiff ℝ 2 f) (hpf : IsPeriodicLift f)
    (hψ : ContDiff ℝ 2 ψ) (hpψ : IsPeriodicLift ψ) :
    (squarePairing (partialY (partialY ψ)) (fun p ↦ f p • ψ p)).re =
      -(squarePairing (fun p ↦ f p • partialY ψ p) (partialY ψ)).re +
        (1 / 2) * (squarePairing (fun p ↦ partialY (partialY f) p • ψ p) ψ).re := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hψy := contDiff_partialY_one hψ
  have hfy := contDiff_partialY_one hf
  have hfψ : ContDiff ℝ 1 (fun p ↦ f p • ψ p) := hf1.smul hψ1
  have hpfψ : IsPeriodicLift (fun p ↦ f p • ψ p) := fun q ↦ by
    simp [(hpf q).1, (hpf q).2, (hpψ q).1, (hpψ q).2]
  have hskew := squarePairing_partialY hψy hfψ hpψ.partialY hpfψ
  have hprod : partialY (fun p ↦ f p • ψ p) = fun p ↦ partialY f p • ψ p + f p • partialY ψ p :=
    funext fun p ↦ by
      rw [partialY_smul ((hf1.differentiable one_ne_zero) p) ((hψ1.differentiable one_ne_zero) p),
        add_comm]
  have hfc := hf.continuous
  have hψc := hψ.continuous
  have hfyc := hfy.continuous
  have hψyc := hψy.continuous
  rw [hprod, squarePairing_add_right (u := partialY ψ) (v := fun p ↦ partialY f p • ψ p)
    (w := fun p ↦ f p • partialY ψ p) hψyc (by fun_prop) (by fun_prop),
    squarePairing_comm (fun p ↦ partialY f p • ψ p) (partialY ψ),
    ← squarePairing_real_smul (u := partialY ψ) f (partialY ψ)] at hskew
  have hkey := re_squarePairing_smul_partialY hfy hpf.partialY hψ1 hpψ
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.conj_re, Complex.neg_re] at this
  linarith

/-- `Re ⟨f Δψ, ψ⟩ = -∫ f |∇ψ|² + ½ ∫ Δf |ψ|²`, in pairing form. -/
theorem re_squarePairing_smul_laplacian (hf : ContDiff ℝ 2 f) (hpf : IsPeriodicLift f)
    (hψ : ContDiff ℝ 2 ψ) (hpψ : IsPeriodicLift ψ) :
    (squarePairing (fun p ↦ f p • laplacian ψ p) ψ).re =
      -(squarePairing (fun p ↦ f p • partialX ψ p) (partialX ψ)).re -
        (squarePairing (fun p ↦ f p • partialY ψ p) (partialY ψ)).re +
        (1 / 2) * (squarePairing (fun p ↦ laplacian f p • ψ p) ψ).re := by
  have hxx : Continuous (partialX (partialX ψ)) :=
    (contDiff_partialX (n := 0) (by simpa using contDiff_partialX_one hψ)).continuous
  have hyy : Continuous (partialY (partialY ψ)) :=
    (contDiff_partialY (n := 0) (by simpa using contDiff_partialY_one hψ)).continuous
  have hfxx : Continuous (partialX (partialX f)) :=
    (contDiff_partialX (n := 0) (by simpa using contDiff_partialX_one hf)).continuous
  have hfyy : Continuous (partialY (partialY f)) :=
    (contDiff_partialY (n := 0) (by simpa using contDiff_partialY_one hf)).continuous
  have hfc := hf.continuous
  have hψc := hψ.continuous
  rw [squarePairing_real_smul (u := laplacian ψ) f ψ,
    show laplacian ψ = fun p ↦ partialX (partialX ψ) p + partialY (partialY ψ) p from rfl,
    squarePairing_add_left hxx hyy (by fun_prop),
    show (fun p ↦ laplacian f p • ψ p) =
      fun p ↦ partialX (partialX f) p • ψ p + partialY (partialY f) p • ψ p from
      funext fun p ↦ by simp only [laplacian, add_smul],
    squarePairing_add_left (by fun_prop) (by fun_prop) hψc, Complex.add_re, Complex.add_re,
    re_squarePairing_partialX_partialX hf hpf hψ hpψ,
    re_squarePairing_partialY_partialY hf hpf hψ hpψ]
  ring

/-! ### The `D ψ` term -/

theorem halfDensityGen_eq (W₁ W₂ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → ℂ) :
    halfDensityGen W₁ W₂ u = fun q ↦ W₁ q • partialX u q + W₂ q • partialY u q +
      (1 / 2 : ℝ) • (divergence W₁ W₂ q • u q) := rfl

/-- `∂ₓ (D ψ) = D (∂ₓψ) + (∂ₓW) · ∇ψ + ½ (∂ₓ div W) ψ`. -/
theorem partialX_halfDensityGen (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    (hψ : ContDiff ℝ 2 ψ) (p : ℝ × ℝ) :
    partialX (halfDensityGen W₁ W₂ ψ) p = halfDensityGen W₁ W₂ (partialX ψ) p +
      (partialX W₁ p • partialX ψ p + partialX W₂ p • partialY ψ p) +
      (1 / 2 : ℝ) • (partialX (divergence W₁ W₂) p • ψ p) := by
  have hd₁ : Differentiable ℝ W₁ := hW₁.differentiable two_ne_zero
  have hd₂ : Differentiable ℝ W₂ := hW₂.differentiable two_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable two_ne_zero
  have hψx : Differentiable ℝ (partialX ψ) :=
    (contDiff_partialX_one hψ).differentiable one_ne_zero
  have hψy : Differentiable ℝ (partialY ψ) :=
    (contDiff_partialY_one hψ).differentiable one_ne_zero
  have hdiv : Differentiable ℝ (divergence W₁ W₂) :=
    ((contDiff_partialX_one hW₁).add (contDiff_partialY_one hW₂)).differentiable one_ne_zero
  have hc : partialX (fun _ : ℝ × ℝ ↦ (1 / 2 : ℝ)) p = 0 :=
    (hasDerivAt_const p.1 (1 / 2 : ℝ)).deriv
  rw [halfDensityGen_eq]
  simp (disch := fun_prop) only [partialX_add, partialX_smul, hc,
    zero_smul, add_zero]
  rw [← partialY_partialX hψ p]
  simp only [halfDensityGen, fieldDeriv]
  module

/-- `∂_y (D ψ) = D (∂_yψ) + (∂_yW) · ∇ψ + ½ (∂_y div W) ψ`. -/
theorem partialY_halfDensityGen (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    (hψ : ContDiff ℝ 2 ψ) (p : ℝ × ℝ) :
    partialY (halfDensityGen W₁ W₂ ψ) p = halfDensityGen W₁ W₂ (partialY ψ) p +
      (partialY W₁ p • partialX ψ p + partialY W₂ p • partialY ψ p) +
      (1 / 2 : ℝ) • (partialY (divergence W₁ W₂) p • ψ p) := by
  have hd₁ : Differentiable ℝ W₁ := hW₁.differentiable two_ne_zero
  have hd₂ : Differentiable ℝ W₂ := hW₂.differentiable two_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable two_ne_zero
  have hψx : Differentiable ℝ (partialX ψ) :=
    (contDiff_partialX_one hψ).differentiable one_ne_zero
  have hψy : Differentiable ℝ (partialY ψ) :=
    (contDiff_partialY_one hψ).differentiable one_ne_zero
  have hdiv : Differentiable ℝ (divergence W₁ W₂) :=
    ((contDiff_partialX_one hW₁).add (contDiff_partialY_one hW₂)).differentiable one_ne_zero
  have hc : partialY (fun _ : ℝ × ℝ ↦ (1 / 2 : ℝ)) p = 0 :=
    (hasDerivAt_const p.2 (1 / 2 : ℝ)).deriv
  rw [halfDensityGen_eq]
  simp (disch := fun_prop) only [partialY_add, partialY_smul, hc,
    zero_smul, add_zero]
  rw [partialY_partialX hψ p]
  simp only [halfDensityGen, fieldDeriv]
  module

theorem continuous_halfDensityGen (hW₁ : ContDiff ℝ 1 W₁) (hW₂ : ContDiff ℝ 1 W₂)
    (hu : ContDiff ℝ 1 u) : Continuous (halfDensityGen W₁ W₂ u) := by
  have h1x := (contDiff_partialX (n := 0) (by simpa using hW₁)).continuous
  have h2y := (contDiff_partialY (n := 0) (by simpa using hW₂)).continuous
  have hux := (contDiff_partialX (n := 0) (by simpa using hu)).continuous
  have huy := (contDiff_partialY (n := 0) (by simpa using hu)).continuous
  have := hW₁.continuous
  have := hW₂.continuous
  have := hu.continuous
  unfold halfDensityGen fieldDeriv divergence
  fun_prop

/-- `Re ⟨D u, u⟩ = 0`. -/
theorem re_squarePairing_halfDensityGen_self (hW₁ : ContDiff ℝ 1 W₁) (hW₂ : ContDiff ℝ 1 W₂)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hu : ContDiff ℝ 1 u)
    (hpu : IsPeriodicLift u) : (squarePairing (halfDensityGen W₁ W₂ u) u).re = 0 := by
  have h := squarePairing_halfDensityGen hW₁ hW₂ hpW₁ hpW₂ hu hu hpu hpu
  rw [squarePairing_comm (halfDensityGen W₁ W₂ u) u] at h
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at this
  linarith

theorem squarePairing_real_const_smul_left (c : ℝ) (w : ℝ × ℝ → ℂ) :
    squarePairing (fun p ↦ c • u p) w = c * squarePairing u w := by
  simp only [Complex.real_smul]
  exact squarePairing_const_mul_left (c : ℂ) w

/-- One coordinate of the `D ψ` term:
    `Re ⟨D ψ, ∂ₓ²ψ⟩ = -Re ⟨(∂ₓW) · ∇ψ, ∂ₓψ⟩ + ¼ Re ⟨(∂ₓ² div W) ψ, ψ⟩`. -/
theorem re_squarePairing_halfDensityGen_partialX_partialX (hW₁ : ContDiff ℝ 3 W₁)
    (hW₂ : ContDiff ℝ 3 W₂) (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    (hψ : ContDiff ℝ 2 ψ) (hpψ : IsPeriodicLift ψ) :
    (squarePairing (halfDensityGen W₁ W₂ ψ) (partialX (partialX ψ))).re =
      -(squarePairing (fun p ↦ partialX W₁ p • partialX ψ p) (partialX ψ)).re -
        (squarePairing (fun p ↦ partialX W₂ p • partialY ψ p) (partialX ψ)).re +
        (1 / 4) * (squarePairing (fun p ↦ partialX (partialX (divergence W₁ W₂)) p • ψ p)
          ψ).re := by
  have hW₁2 : ContDiff ℝ 2 W₁ := hW₁.of_le (by norm_num)
  have hW₂2 : ContDiff ℝ 2 W₂ := hW₂.of_le (by norm_num)
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψx := contDiff_partialX_one hψ
  have hψy := contDiff_partialY_one hψ
  have hdiv : ContDiff ℝ 2 (divergence W₁ W₂) :=
    (contDiff_partialX (n := 2) hW₁).add (contDiff_partialY (n := 2) hW₂)
  have hpdiv : IsPeriodicLift (divergence W₁ W₂) := fun q ↦ by
    simp only [divergence, (hpW₁.partialX q).1, (hpW₁.partialX q).2, (hpW₂.partialY q).1,
      (hpW₂.partialY q).2, and_self]
  have hdx := contDiff_partialX_one hdiv
  have hDψ := contDiff_halfDensityGen hW₁2 hW₂2 hψ
  have hpD := IsPeriodicLift.halfDensityGen hpW₁ hpW₂ hpψ
  have hskew := squarePairing_partialX hDψ hψx hpD hpψ.partialX
  rw [show partialX (halfDensityGen W₁ W₂ ψ) = fun p ↦ halfDensityGen W₁ W₂ (partialX ψ) p +
      (partialX W₁ p • partialX ψ p + partialX W₂ p • partialY ψ p) +
      (1 / 2 : ℝ) • (partialX (divergence W₁ W₂) p • ψ p) from
      funext (partialX_halfDensityGen hW₁2 hW₂2 hψ)] at hskew
  have c1 := continuous_halfDensityGen hW₁1 hW₂1 hψx
  have c2 := (contDiff_partialX_one hW₁2).continuous
  have c3 := (contDiff_partialX_one hW₂2).continuous
  have c4 := hdx.continuous
  have c5 := hψx.continuous
  have c6 := hψy.continuous
  have c7 := hψ.continuous
  rw [squarePairing_add_left (by fun_prop) (by fun_prop) c5,
    squarePairing_add_left c1 (by fun_prop) c5,
    squarePairing_add_left (u := fun p ↦ partialX W₁ p • partialX ψ p)
      (v := fun p ↦ partialX W₂ p • partialY ψ p) (by fun_prop) (by fun_prop) c5,
    squarePairing_real_const_smul_left (u := fun p ↦ partialX (divergence W₁ W₂) p • ψ p)] at hskew
  have h0 := re_squarePairing_halfDensityGen_self hW₁1 hW₂1 hpW₁ hpW₂ hψx hpψ.partialX
  have hk := re_squarePairing_smul_partialX hdx hpdiv.partialX hψ1 hpψ
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at this
  linarith

/-- The `y` coordinate of the `D ψ` term. -/
theorem re_squarePairing_halfDensityGen_partialY_partialY (hW₁ : ContDiff ℝ 3 W₁)
    (hW₂ : ContDiff ℝ 3 W₂) (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    (hψ : ContDiff ℝ 2 ψ) (hpψ : IsPeriodicLift ψ) :
    (squarePairing (halfDensityGen W₁ W₂ ψ) (partialY (partialY ψ))).re =
      -(squarePairing (fun p ↦ partialY W₁ p • partialX ψ p) (partialY ψ)).re -
        (squarePairing (fun p ↦ partialY W₂ p • partialY ψ p) (partialY ψ)).re +
        (1 / 4) * (squarePairing (fun p ↦ partialY (partialY (divergence W₁ W₂)) p • ψ p)
          ψ).re := by
  have hW₁2 : ContDiff ℝ 2 W₁ := hW₁.of_le (by norm_num)
  have hW₂2 : ContDiff ℝ 2 W₂ := hW₂.of_le (by norm_num)
  have hW₁1 : ContDiff ℝ 1 W₁ := hW₁.of_le (by norm_num)
  have hW₂1 : ContDiff ℝ 1 W₂ := hW₂.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψx := contDiff_partialX_one hψ
  have hψy := contDiff_partialY_one hψ
  have hdiv : ContDiff ℝ 2 (divergence W₁ W₂) :=
    (contDiff_partialX (n := 2) hW₁).add (contDiff_partialY (n := 2) hW₂)
  have hpdiv : IsPeriodicLift (divergence W₁ W₂) := fun q ↦ by
    simp only [divergence, (hpW₁.partialX q).1, (hpW₁.partialX q).2, (hpW₂.partialY q).1,
      (hpW₂.partialY q).2, and_self]
  have hdy := contDiff_partialY_one hdiv
  have hDψ := contDiff_halfDensityGen hW₁2 hW₂2 hψ
  have hpD := IsPeriodicLift.halfDensityGen hpW₁ hpW₂ hpψ
  have hskew := squarePairing_partialY hDψ hψy hpD hpψ.partialY
  rw [show partialY (halfDensityGen W₁ W₂ ψ) = fun p ↦ halfDensityGen W₁ W₂ (partialY ψ) p +
      (partialY W₁ p • partialX ψ p + partialY W₂ p • partialY ψ p) +
      (1 / 2 : ℝ) • (partialY (divergence W₁ W₂) p • ψ p) from
      funext (partialY_halfDensityGen hW₁2 hW₂2 hψ)] at hskew
  have c1 := continuous_halfDensityGen hW₁1 hW₂1 hψy
  have c2 := (contDiff_partialY_one hW₁2).continuous
  have c3 := (contDiff_partialY_one hW₂2).continuous
  have c4 := hdy.continuous
  have c5 := hψx.continuous
  have c6 := hψy.continuous
  have c7 := hψ.continuous
  rw [squarePairing_add_left (by fun_prop) (by fun_prop) c6,
    squarePairing_add_left c1 (by fun_prop) c6,
    squarePairing_add_left (u := fun p ↦ partialY W₁ p • partialX ψ p)
      (v := fun p ↦ partialY W₂ p • partialY ψ p) (by fun_prop) (by fun_prop) c6,
    squarePairing_real_const_smul_left (u := fun p ↦ partialY (divergence W₁ W₂) p • ψ p)] at hskew
  have h0 := re_squarePairing_halfDensityGen_self hW₁1 hW₂1 hpW₁ hpW₂ hψy hpψ.partialY
  have hk := re_squarePairing_smul_partialY hdy hpdiv.partialY hψ1 hpψ
  have := congrArg Complex.re hskew
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at this
  linarith

/-! ### The quadratic form -/

/-- The quadratic form of the smooth virial identity, with `ω = Δψ`:
    `0 = ∫ f |Δψ|² + ∫ (2 sym DW - f I) ∇ψ · ∇ψ̄ + ½ ∫ Δ(f - div W) |ψ|²`.
    Each integral `∫ g u v̄` with real `g` is written `Re ⟨g u, v⟩`; the second integral
    is expanded over the entries `∂ⱼWᵢ ∂ᵢψ ∂ⱼψ̄` of `DW`. -/
theorem virial_smooth_quadratic (had : IsAdaptedOn W₁ W₂ f Set.univ) (hW₁ : ContDiff ℝ 3 W₁)
    (hW₂ : ContDiff ℝ 3 W₂) (hf : ContDiff ℝ 2 f) (hpW₁ : IsPeriodicLift W₁)
    (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f) (hψ : ContDiff ℝ 4 ψ)
    (hpψ : IsPeriodicLift ψ) {lam : ℝ} (hlam : lam ≠ 0)
    (heq : ∀ p, classicalL0 (fun q ↦ laplacian ψ q + ψ q) p = I * lam * laplacian ψ p) :
    (squarePairing (fun p ↦ f p • laplacian ψ p) (laplacian ψ)).re +
      2 * ((squarePairing (fun p ↦ partialX W₁ p • partialX ψ p) (partialX ψ)).re +
        (squarePairing (fun p ↦ partialX W₂ p • partialY ψ p) (partialX ψ)).re +
        (squarePairing (fun p ↦ partialY W₁ p • partialX ψ p) (partialY ψ)).re +
        (squarePairing (fun p ↦ partialY W₂ p • partialY ψ p) (partialY ψ)).re) -
      (squarePairing (fun p ↦ f p • partialX ψ p) (partialX ψ)).re -
      (squarePairing (fun p ↦ f p • partialY ψ p) (partialY ψ)).re +
      (1 / 2) * (squarePairing
        (fun p ↦ laplacian (fun q ↦ f q - divergence W₁ W₂ q) p • ψ p) ψ).re = 0 := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hW₁2 : ContDiff ℝ 2 W₁ := hW₁.of_le (by norm_num)
  have hW₂2 : ContDiff ℝ 2 W₂ := hW₂.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  -- `ω = Δψ` is periodic and `C²`.
  have hxx : ContDiff ℝ 2 (partialX (partialX ψ)) :=
    contDiff_partialX (n := 2) (contDiff_partialX (n := 3) hψ)
  have hyy : ContDiff ℝ 2 (partialY (partialY ψ)) :=
    contDiff_partialY (n := 2) (contDiff_partialY (n := 3) hψ)
  have hω : ContDiff ℝ 2 (laplacian ψ) := hxx.add hyy
  have hpω : IsPeriodicLift (laplacian ψ) := fun q ↦ by
    simp only [laplacian, (hpψ.partialX.partialX q).1, (hpψ.partialX.partialX q).2,
      (hpψ.partialY.partialY q).1, (hpψ.partialY.partialY q).2, and_self]
  have V := virial_smooth had hW₁2 hW₂2 hf1 hpW₁ hpW₂ hpf hω hψ2 hpω hpψ hlam heq
  -- Left side: `Re ⟨f ω, ω⟩ + Re ⟨f Δψ, ψ⟩`.
  have hfc := hf.continuous
  rw [squarePairing_add_right (by fun_prop) hω.continuous hψ.continuous, Complex.add_re,
    re_squarePairing_smul_laplacian hf hpf hψ2 hpψ] at V
  -- Right side: the two coordinates of the `D ψ` term.
  have hD : (squarePairing (halfDensityGen W₁ W₂ ψ) (laplacian ψ)).re =
      -(squarePairing (fun p ↦ partialX W₁ p • partialX ψ p) (partialX ψ)).re -
        (squarePairing (fun p ↦ partialX W₂ p • partialY ψ p) (partialX ψ)).re +
        (1 / 4) * (squarePairing (fun p ↦ partialX (partialX (divergence W₁ W₂)) p • ψ p)
          ψ).re +
      (-(squarePairing (fun p ↦ partialY W₁ p • partialX ψ p) (partialY ψ)).re -
        (squarePairing (fun p ↦ partialY W₂ p • partialY ψ p) (partialY ψ)).re +
        (1 / 4) * (squarePairing (fun p ↦ partialY (partialY (divergence W₁ W₂)) p • ψ p)
          ψ).re) := by
    rw [show laplacian ψ = fun p ↦ partialX (partialX ψ) p + partialY (partialY ψ) p from rfl,
      squarePairing_add_right (continuous_halfDensityGen (hW₁.of_le (by norm_num))
        (hW₂.of_le (by norm_num)) (hψ.of_le (by norm_num))) hxx.continuous hyy.continuous,
      Complex.add_re,
      re_squarePairing_halfDensityGen_partialX_partialX hW₁ hW₂ hpW₁ hpW₂ hψ2 hpψ,
      re_squarePairing_halfDensityGen_partialY_partialY hW₁ hW₂ hpW₁ hpW₂ hψ2 hpψ]
  rw [hD] at V
  -- `Δ(f - div W) = Δf - ∂ₓ² div W - ∂_y² div W`.
  have hdiv : ContDiff ℝ 2 (divergence W₁ W₂) :=
    (contDiff_partialX (n := 2) hW₁).add (contDiff_partialY (n := 2) hW₂)
  have hfd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hdd : Differentiable ℝ (divergence W₁ W₂) := hdiv.differentiable two_ne_zero
  have hfx : Differentiable ℝ (partialX f) := (contDiff_partialX_one hf).differentiable one_ne_zero
  have hfy : Differentiable ℝ (partialY f) := (contDiff_partialY_one hf).differentiable one_ne_zero
  have hdx : Differentiable ℝ (partialX (divergence W₁ W₂)) :=
    (contDiff_partialX_one hdiv).differentiable one_ne_zero
  have hdy : Differentiable ℝ (partialY (divergence W₁ W₂)) :=
    (contDiff_partialY_one hdiv).differentiable one_ne_zero
  have hlap : laplacian (fun q ↦ f q - divergence W₁ W₂ q) = fun p ↦ laplacian f p -
      partialX (partialX (divergence W₁ W₂)) p - partialY (partialY (divergence W₁ W₂)) p := by
    have h1 : partialX (fun q ↦ f q - divergence W₁ W₂ q) =
        fun q ↦ partialX f q - partialX (divergence W₁ W₂) q :=
      funext fun q ↦ partialX_sub (hfd q) (hdd q)
    have h2 : partialY (fun q ↦ f q - divergence W₁ W₂ q) =
        fun q ↦ partialY f q - partialY (divergence W₁ W₂) q :=
      funext fun q ↦ partialY_sub (hfd q) (hdd q)
    funext p
    simp only [laplacian, h1, h2, partialX_sub (hfx p) (hdx p), partialY_sub (hfy p) (hdy p)]
    ring
  have c1 : Continuous (laplacian f) :=
    ((contDiff_partialX (n := 0) (by simpa using contDiff_partialX_one hf)).add
      (contDiff_partialY (n := 0) (by simpa using contDiff_partialY_one hf))).continuous
  have c2 : Continuous (partialX (partialX (divergence W₁ W₂))) :=
    (contDiff_partialX (n := 0) (by simpa using contDiff_partialX_one hdiv)).continuous
  have c3 : Continuous (partialY (partialY (divergence W₁ W₂))) :=
    (contDiff_partialY (n := 0) (by simpa using contDiff_partialY_one hdiv)).continuous
  have c4 := hψ.continuous
  rw [hlap, show (fun p ↦ (laplacian f p - partialX (partialX (divergence W₁ W₂)) p -
      partialY (partialY (divergence W₁ W₂)) p) • ψ p) = fun p ↦
      (laplacian f p • ψ p - partialX (partialX (divergence W₁ W₂)) p • ψ p) -
        partialY (partialY (divergence W₁ W₂)) p • ψ p from
      funext fun p ↦ by simp only [sub_smul],
    squarePairing_sub_left (by fun_prop) (by fun_prop) c4,
    squarePairing_sub_left (by fun_prop) (by fun_prop) c4, Complex.sub_re, Complex.sub_re]
  linarith

end EulerDipoleEigenvalues
