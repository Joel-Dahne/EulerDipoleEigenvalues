import NoEmbeddedEigenvalues.VirialQuadratic
import NoEmbeddedEigenvalues.LiftTorus

/-!
# The virial identities on the `L²` domain

Blueprint: `lem:virial-exact-identity` and `lem:stream-ibp` (proved),
`lem:virial-h1` and `lem:virial-l2` (stated).

For a smooth adapted field `W` supported in a compact annulus `{2h₁ ≤ Ψ ≤ 2h₂}` of the
cells, `0 < h₁`, `h₂ < 1` (away from the separatrix and the centers), the two smooth virial
identities (`VirialSmooth.lean`, `VirialQuadratic.lean`) hold for every eigenfunction
`ω ∈ L²`, with no further regularity. Derivatives of `ψ = Δ⁻¹ω` are the lifts of the
Fourier-defined ones and `Δψ = ω`.

The planned proof (blueprint proof of `lem:virial-l2`) mollifies in the level variable of
action-angle coordinates (`lem:transversal-mollifier`) and uses the exact identity below with
`V = J_ε† D J_ε`; it needs no flow of `W`.

The `H¹` statements below take Fourier derivative witnesses explicitly (they exist for
every `H¹` input by `MemSobolev.exists_hasFourierPartial`). Their displayed generators
use the lifts of those derivatives, not classical derivatives of arbitrary representatives.
Only first derivatives occur in the conclusions; no assertion that `HDu` or `DHu` is in
`L²` is made. The `H¹` proofs remain admitted.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Complex
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
The functions `du j`, `dv j` are Fourier partial derivatives in `L²`. -/
theorem squarePairing_halfDensityGen_h1 {W₁ W₂ : ℝ × ℝ → ℝ}
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂)
    {u v : L2} (hu : MemSobolev 1 u) (hv : MemSobolev 1 v)
    {du dv : Fin 2 → L2} (hdu : ∀ j, HasFourierPartial j u (du j))
    (hdv : ∀ j, HasFourierPartial j v (dv j)) :
    let Du : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (du 0) p + W₂ p • liftL2 (du 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 u p
    let Dv : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (dv 0) p + W₂ p • liftL2 (dv 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 v p
    squarePairing Du (liftL2 v) = -squarePairing (liftL2 u) Dv := by
  sorry

/-- The commutator identity as a continuous quadratic form on `H¹(𝕋²)`.
`Du` and `Hu = -i L₀u` use the supplied Fourier partial derivatives. -/
theorem virial_h1 {W₁ W₂ f : ℝ × ℝ → ℝ} (had : IsAdaptedOn W₁ W₂ f Set.univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hpW₁ : IsPeriodicLift W₁) (hpW₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {u : L2} (hu : MemSobolev 1 u) {du : Fin 2 → L2}
    (hdu : ∀ j, HasFourierPartial j u (du j)) :
    let Du : ℝ × ℝ → ℂ := fun p ↦ W₁ p • liftL2 (du 0) p + W₂ p • liftL2 (du 1) p +
      ((1 / 2 : ℝ) * divergence W₁ W₂ p) • liftL2 u p
    let Hu : ℝ × ℝ → ℂ := fun p ↦ -I *
      (Real.sin p.2 • liftL2 (du 0) p - Real.sin p.1 • liftL2 (du 1) p)
    2 * (squarePairing Du Hu).re =
      (squarePairing (fun p ↦ f p • Hu p) (liftL2 u)).re := by
  sorry

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
  sorry

end NoEmbeddedEigenvalues
