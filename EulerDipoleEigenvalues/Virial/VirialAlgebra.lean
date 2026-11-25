module

public import EulerDipoleEigenvalues.Geometry.Cells.DipoleCalculus

/-!
# Commutator algebra for adapted vector fields

Blueprint: `def:half-density-generator`, `lem:commutator-pointwise`.

For a vector field `W` adapted with coefficient `f` (`[Y, W] = f Y`), the operator
`W · ∇` commutes with `L₀` up to `f L₀`, `L₀ div W = L₀ f`, and the half-density
generator `D = W · ∇ + ½ div W` satisfies `[L₀, D] = ½ (f L₀ + L₀ f)`. These are
pointwise identities for `C²` functions on the real lift. Skew-symmetry of `D`
(integration by parts) is not treated here.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative `W · ∇u` along a planar vector field `W = (W₁, W₂)`. -/
def fieldDeriv (W₁ W₂ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  W₁ p • partialX u p + W₂ p • partialY u p

/-- The divergence `∂ₓW₁ + ∂_yW₂`. -/
def divergence (W₁ W₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := partialX W₁ p + partialY W₂ p

/-- The half-density generator `D = W · ∇ + ½ div W`. -/
def halfDensityGen (W₁ W₂ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  fieldDeriv W₁ W₂ u p + (1 / 2 : ℝ) • (divergence W₁ W₂ p • u p)

variable {W₁ W₂ f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {p : ℝ × ℝ}

/-- `[L₀, W · ∇] = f L₀` on `C²` functions, at points where `W` is adapted. -/
theorem IsAdaptedOn.classicalL0_fieldDeriv (h : IsAdaptedOn W₁ W₂ f U)
    (hW₁ : Differentiable ℝ W₁) (hW₂ : Differentiable ℝ W₂) {u : ℝ × ℝ → E}
    (hu : ContDiff ℝ 2 u) (hp : p ∈ U) :
    classicalL0 (fieldDeriv W₁ W₂ u) p - fieldDeriv W₁ W₂ (classicalL0 u) p =
      f p • classicalL0 u p := by
  have hux : Differentiable ℝ (partialX u) :=
    (contDiff_partialX (n := 1) hu).differentiable one_ne_zero
  have huy : Differentiable ℝ (partialY u) :=
    (contDiff_partialY (n := 1) hu).differentiable one_ne_zero
  obtain ⟨h1, h2⟩ := h p hp
  simp only [classicalL0, smul_eq_mul] at h1 h2
  rw [show classicalL0 (fieldDeriv W₁ W₂ u) p =
      sin p.2 • partialX (fun q ↦ W₁ q • partialX u q + W₂ q • partialY u q) p -
        sin p.1 • partialY (fun q ↦ W₁ q • partialX u q + W₂ q • partialY u q) p from rfl,
    show fieldDeriv W₁ W₂ (classicalL0 u) p =
      W₁ p • partialX (fun q ↦ sin q.2 • partialX u q - sin q.1 • partialY u q) p +
        W₂ p • partialY (fun q ↦ sin q.2 • partialX u q - sin q.1 • partialY u q) p from rfl]
  simp (disch := fun_prop) only [partialX_add, partialY_add, partialX_sub, partialY_sub,
    partialX_smul, partialY_smul, partialX_sin_fst, partialX_sin_snd, partialY_sin_fst,
    partialY_sin_snd]
  rw [partialY_partialX hu p]
  simp only [classicalL0]
  linear_combination (norm := module) h1 • partialX u p + h2 • partialY u p

/-- `L₀ div W = L₀ f` on an open set where `W` is adapted. -/
theorem IsAdaptedOn.classicalL0_divergence (h : IsAdaptedOn W₁ W₂ f U) (hU : IsOpen U)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : Differentiable ℝ f) (hp : p ∈ U) :
    classicalL0 (divergence W₁ W₂) p = classicalL0 f p := by
  have hd₁ : Differentiable ℝ W₁ := hW₁.differentiable two_ne_zero
  have hd₂ : Differentiable ℝ W₂ := hW₂.differentiable two_ne_zero
  have h1x : Differentiable ℝ (partialX W₁) :=
    (contDiff_partialX (n := 1) hW₁).differentiable one_ne_zero
  have h1y : Differentiable ℝ (partialY W₁) :=
    (contDiff_partialY (n := 1) hW₁).differentiable one_ne_zero
  have h2x : Differentiable ℝ (partialX W₂) :=
    (contDiff_partialX (n := 1) hW₂).differentiable one_ne_zero
  have h2y : Differentiable ℝ (partialY W₂) :=
    (contDiff_partialY (n := 1) hW₂).differentiable one_ne_zero
  -- The two components of `[Y, W] - f Y` vanish near `p`.
  have hA : ∀ᶠ q in nhds p, sin q.2 • partialX W₁ q - sin q.1 • partialY W₁ q -
      cos q.2 • W₂ q - sin q.2 • f q = 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    have := (h q hq).1
    simp only [classicalL0, smul_eq_mul] at this ⊢
    linarith
  have hB : ∀ᶠ q in nhds p, sin q.2 • partialX W₂ q - sin q.1 • partialY W₂ q +
      cos q.1 • W₁ q + sin q.1 • f q = 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    have := (h q hq).2
    simp only [classicalL0, smul_eq_mul] at this ⊢
    linarith
  have eA := partialX_eq_zero_of_eventually hA
  have eB := partialY_eq_zero_of_eventually hB
  simp (disch := fun_prop) only [partialY_add, partialX_sub, partialY_sub, partialX_smul,
    partialY_smul, partialX_sin_fst, partialX_sin_snd, partialY_sin_fst, partialY_sin_snd,
    partialX_cos_snd, partialY_cos_fst] at eA eB
  rw [show divergence W₁ W₂ = fun q ↦ partialX W₁ q + partialY W₂ q from rfl]
  simp (disch := fun_prop) only [classicalL0, partialX_add, partialY_add]
  rw [partialY_partialX hW₁ p, ← partialY_partialX hW₂ p]
  simp only [smul_eq_mul] at eA eB ⊢
  linear_combination eA + eB

/-- `[L₀, D] = ½ (f L₀ + L₀ f)` on `C²` functions, on an open set where `W` is adapted. -/
theorem IsAdaptedOn.classicalL0_halfDensityGen (h : IsAdaptedOn W₁ W₂ f U) (hU : IsOpen U)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : Differentiable ℝ f)
    {u : ℝ × ℝ → E} (hu : ContDiff ℝ 2 u) (hp : p ∈ U) :
    classicalL0 (halfDensityGen W₁ W₂ u) p - halfDensityGen W₁ W₂ (classicalL0 u) p =
      (1 / 2 : ℝ) • (f p • classicalL0 u p + classicalL0 (fun q ↦ f q • u q) p) := by
  have hd₁ : Differentiable ℝ W₁ := hW₁.differentiable two_ne_zero
  have hd₂ : Differentiable ℝ W₂ := hW₂.differentiable two_ne_zero
  have hud : Differentiable ℝ u := hu.differentiable two_ne_zero
  have hux : Differentiable ℝ (partialX u) :=
    (contDiff_partialX (n := 1) hu).differentiable one_ne_zero
  have huy : Differentiable ℝ (partialY u) :=
    (contDiff_partialY (n := 1) hu).differentiable one_ne_zero
  have hdiv : Differentiable ℝ (divergence W₁ W₂) :=
    ((contDiff_partialX (n := 1) hW₁).add (contDiff_partialY (n := 1) hW₂)).differentiable
      one_ne_zero
  have hF : Differentiable ℝ (fieldDeriv W₁ W₂ u) := by
    unfold fieldDeriv
    fun_prop
  have hL := h.classicalL0_fieldDeriv hd₁ hd₂ hu hp
  have hDiv := h.classicalL0_divergence hU hW₁ hW₂ hf hp
  rw [show classicalL0 (halfDensityGen W₁ W₂ u) p =
      sin p.2 • partialX (fun q ↦ fieldDeriv W₁ W₂ u q +
        (1 / 2 : ℝ) • (divergence W₁ W₂ q • u q)) p -
      sin p.1 • partialY (fun q ↦ fieldDeriv W₁ W₂ u q +
        (1 / 2 : ℝ) • (divergence W₁ W₂ q • u q)) p from rfl,
    show halfDensityGen W₁ W₂ (classicalL0 u) p = fieldDeriv W₁ W₂ (classicalL0 u) p +
      (1 / 2 : ℝ) • (divergence W₁ W₂ p • classicalL0 u p) from rfl,
    show classicalL0 (fun q ↦ f q • u q) p = sin p.2 • partialX (fun q ↦ f q • u q) p -
      sin p.1 • partialY (fun q ↦ f q • u q) p from rfl]
  simp (disch := fun_prop) only [partialX_add, partialY_add, partialX_const_smul,
    partialY_const_smul, partialX_smul, partialY_smul]
  simp only [classicalL0] at hL hDiv ⊢
  linear_combination (norm := module) hL + ((1 / 2 : ℝ) * hDiv) • u p

end EulerDipoleEigenvalues
