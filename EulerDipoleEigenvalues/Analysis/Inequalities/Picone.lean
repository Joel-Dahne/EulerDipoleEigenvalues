module

public import EulerDipoleEigenvalues.Virial.VirialAlgebra
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Classical Picone identities for real symmetric planar matrices

Blueprint: `lem:picone`.

The algebraic identity is stated for any finite symmetric real matrix, so it
also covers scalar interval applications. The classical differential and
integrated interfaces below use planar coordinates.

The three real coefficient functions represent `G = [[a,b],[b,c]]`; neither
positive definiteness nor a sign condition on the potential is required.
The pointwise identity requires only first derivatives of the complex function
and positive real comparison function. The divergence form also differentiates
`G∇g`, so it uses C¹ coefficients and C² comparison data on an open set.

The integrated identity takes the divergence formula for the actual current as
an explicit hypothesis, together with absolute integrability of all densities.
The boundary measure and outward normal are supplied by the application. This
is not a divergence theorem for arbitrary domains, a Sobolev approximation
result, or a justification for removing singular points. In particular the
current uses values of the function, not boundary values of its gradient.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set

/-- A finite real matrix's Hermitian quadratic form, written without coordinates. -/
def piconeQuadratic {ι : Type*} [Fintype ι] (G : ι → ι → ℝ) (v : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, G i j * (v i * (starRingEnd ℂ) (v j)).re

/-- Algebraic Picone identity for specified values and gradients in any finite
    dimension. The last factor is the quotient-rule gradient of `|z|²/g`. -/
theorem picone_algebra {ι : Type*} [Fintype ι] (G : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) {g : ℝ} (hpos : 0 < g)
    (dg : ι → ℝ) (z : ℂ) (dz : ι → ℂ) :
    piconeQuadratic G dz =
      g ^ 2 * piconeQuadratic G (fun j ↦ dz j / (g : ℂ) - z * (dg j : ℂ) / (g : ℂ) ^ 2) +
        ∑ i, ∑ j, G i j * dg i *
          (2 * (dz j * (starRingEnd ℂ) z).re / g - ‖z‖ ^ 2 * dg j / g ^ 2) := by
  let q (j : ι) := dz j / (g : ℂ) - z * (dg j : ℂ) / (g : ℂ) ^ 2
  let R (j : ι) := 2 * (dz j * (starRingEnd ℂ) z).re / g - ‖z‖ ^ 2 * dg j / g ^ 2
  have hpair (i j : ι) :
      G i j * (dz i * (starRingEnd ℂ) (dz j)).re =
        g ^ 2 * (G i j * (q i * (starRingEnd ℂ) (q j)).re) +
          (G i j * dg i * R j + G j i * dg j * R i) / 2 := by
    rw [← hG i j]
    dsimp only [q, R]
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.sq_norm, Complex.normSq_apply]
    field_simp [hpos.ne']
    ring
  have hswap : (∑ i, ∑ j, G j i * dg j * R i) = ∑ i, ∑ j, G i j * dg i * R j :=
    Finset.sum_comm
  change (∑ i, ∑ j, G i j * (dz i * (starRingEnd ℂ) (dz j)).re) =
    g ^ 2 * (∑ i, ∑ j, G i j * (q i * (starRingEnd ℂ) (q j)).re) +
      ∑ i, ∑ j, G i j * dg i * R j
  simp_rw [hpair, Finset.sum_add_distrib]
  simp only [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- The real Hermitian quadratic form of the symmetric matrix `[[a,b],[b,c]]`. -/
def piconeMatrixForm (a b c : ℝ) (vx vy : ℂ) : ℝ :=
  a * ‖vx‖ ^ 2 + 2 * b * (vx * (starRingEnd ℂ) vy).re + c * ‖vy‖ ^ 2

/-- Classical gradient energy for three specified real symmetric coefficients. -/
def piconeEnergy (a b c : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeMatrixForm (a p) (b p) (c p) (partialX z p) (partialY z p)

/-- The first component of `G∇g`. -/
def piconeGroundFlux₁ (a b : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p * partialX g p + b p * partialY g p

/-- The second component of `G∇g`. -/
def piconeGroundFlux₂ (b c : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  b p * partialX g p + c p * partialY g p

/-- The residual `-div(G∇g) - Vg` of a real comparison function. -/
def piconeResidual (a b c V g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -divergence (piconeGroundFlux₁ a b g) (piconeGroundFlux₂ b c g) p - V p * g p

/-- The first component of the current `J = |z|² G∇g/g`. -/
def piconeCurrent₁ (a b g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₁ a b g p / g p * ‖z p‖ ^ 2

/-- The second component of the same current. -/
def piconeCurrent₂ (b c g : ℝ × ℝ → ℝ) (z : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  piconeGroundFlux₂ b c g p / g p * ‖z p‖ ^ 2

private theorem hasDerivAt_picone_quotient {g : ℝ → ℝ} {z : ℝ → ℂ}
    {g' t : ℝ} {z' : ℂ} (hg : HasDerivAt g g' t) (hz : HasDerivAt z z' t)
    (hpos : 0 < g t) :
    HasDerivAt (fun s ↦ z s / (g s : ℂ))
      (z' / (g t : ℂ) - z t * (g' : ℂ) / (g t : ℂ) ^ 2) t := by
  have hn : (g t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  convert hz.div hg.ofReal_comp hn using 1
  field_simp

private theorem hasDerivAt_picone_value {g : ℝ → ℝ} {z : ℝ → ℂ}
    {g' t : ℝ} {z' : ℂ} (hg : HasDerivAt g g' t) (hz : HasDerivAt z z' t)
    (hpos : 0 < g t) :
    HasDerivAt (fun s ↦ ‖z s‖ ^ 2 / g s)
      (2 * (z' * (starRingEnd ℂ) (z t)).re / g t - ‖z t‖ ^ 2 * g' / g t ^ 2) t := by
  have hn : HasDerivAt (fun s ↦ ‖z s‖ ^ 2)
      (2 * (z' * (starRingEnd ℂ) (z t)).re) t := by
    convert hz.norm_sq using 1
    simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
    rfl
  convert hn.div hg hpos.ne' using 1
  field_simp

/-- Pointwise Picone identity, for a complex function and a positive real divisor.
    Symmetry is built into the three coefficient representation. -/
theorem picone_identity (a b c : ℝ × ℝ → ℝ) {g : ℝ × ℝ → ℝ}
    {z : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (hg : DifferentiableAt ℝ g p)
    (hz : DifferentiableAt ℝ z p) (hpos : 0 < g p) :
    piconeEnergy a b c z p =
      g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p +
        piconeGroundFlux₁ a b g p * partialX (fun q ↦ ‖z q‖ ^ 2 / g q) p +
        piconeGroundFlux₂ b c g p * partialY (fun q ↦ ‖z q‖ ^ 2 / g q) p := by
  have hqx := (hasDerivAt_picone_quotient (hasDerivAt_partialX hg)
    (hasDerivAt_partialX hz) hpos).deriv
  have hqy := (hasDerivAt_picone_quotient (hasDerivAt_partialY hg)
    (hasDerivAt_partialY hz) hpos).deriv
  have hvx := (hasDerivAt_picone_value (hasDerivAt_partialX hg)
    (hasDerivAt_partialX hz) hpos).deriv
  have hvy := (hasDerivAt_picone_value (hasDerivAt_partialY hg)
    (hasDerivAt_partialY hz) hpos).deriv
  have h := picone_algebra (ι := Fin 2) ![![a p, b p], ![b p, c p]]
    (by intro i j; fin_cases i <;> fin_cases j <;> rfl) hpos
    ![partialX g p, partialY g p] (z p) ![partialX z p, partialY z p]
  simp only [piconeEnergy, partialX, partialY, hqx, hqy, hvx, hvy]
  simp only [piconeQuadratic, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  simp only [piconeMatrixForm, piconeGroundFlux₁, piconeGroundFlux₂]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im] at h ⊢
  simp only [partialX, partialY, Prod.mk.eta] at h ⊢
  linear_combination h

/-- Classical divergence form, with the potential and actual current explicit. -/
theorem picone_divergence {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b c V g : ℝ × ℝ → ℝ} {z : ℝ × ℝ → ℂ}
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U)
    (hc : ContDiffOn ℝ 1 c U) (hg : ContDiffOn ℝ 2 g U)
    (hz : ContDiffOn ℝ 1 z U) (hpos : ∀ p ∈ U, 0 < g p)
    {p : ℝ × ℝ} (hp : p ∈ U) :
    piconeEnergy a b c z p - V p * ‖z p‖ ^ 2 =
      g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p +
        piconeResidual a b c V g p / g p * ‖z p‖ ^ 2 +
        divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p := by
  have hga := hg.contDiffAt (hU.mem_nhds hp)
  have hgd := hga.differentiableAt (by norm_num)
  have hzd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ g) p :=
    (hga.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hxg : DifferentiableAt ℝ (partialX g) p := by
    apply (hfd.clm_apply (differentiableAt_const (1, 0))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partialX_eq_fderiv
      ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num))
  have hyg : DifferentiableAt ℝ (partialY g) p := by
    apply (hfd.clm_apply (differentiableAt_const (0, 1))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partialY_eq_fderiv
      ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num))
  have had := (ha.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hbd := (hb.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hcd := (hc.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hB₁ : DifferentiableAt ℝ (piconeGroundFlux₁ a b g) p :=
    (had.mul hxg).add (hbd.mul hyg)
  have hB₂ : DifferentiableAt ℝ (piconeGroundFlux₂ b c g) p :=
    (hbd.mul hxg).add (hcd.mul hyg)
  have hnorm : DifferentiableAt ℝ (fun q ↦ ‖z q‖ ^ 2) p :=
    ((hz.contDiffAt (hU.mem_nhds hp)).norm_sq ℂ).differentiableAt (by norm_num)
  have hv : DifferentiableAt ℝ (fun q ↦ ‖z q‖ ^ 2 / g q) p :=
    by
      convert hnorm.mul (hgd.inv (hpos p hp).ne') using 1
      ext q
      simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  have hx : partialX (piconeCurrent₁ a b g z) p =
      partialX (piconeGroundFlux₁ a b g) p * (‖z p‖ ^ 2 / g p) +
        piconeGroundFlux₁ a b g p * partialX (fun q ↦ ‖z q‖ ^ 2 / g q) p := by
    rw [show piconeCurrent₁ a b g z = fun q ↦
      piconeGroundFlux₁ a b g q * (‖z q‖ ^ 2 / g q) by
        funext q; unfold piconeCurrent₁; ring]
    exact ((hasDerivAt_partialX hB₁).mul (hasDerivAt_partialX hv)).deriv
  have hy : partialY (piconeCurrent₂ b c g z) p =
      partialY (piconeGroundFlux₂ b c g) p * (‖z p‖ ^ 2 / g p) +
        piconeGroundFlux₂ b c g p * partialY (fun q ↦ ‖z q‖ ^ 2 / g q) p := by
    rw [show piconeCurrent₂ b c g z = fun q ↦
      piconeGroundFlux₂ b c g q * (‖z q‖ ^ 2 / g q) by
        funext q; unfold piconeCurrent₂; ring]
    exact ((hasDerivAt_partialY hB₂).mul (hasDerivAt_partialY hv)).deriv
  rw [picone_identity a b c hgd hzd (hpos p hp)]
  unfold piconeResidual divergence
  rw [hx, hy]
  field_simp [(hpos p hp).ne']
  ring

/-- Integrated Picone identity after a supplied integration-by-parts formula for
    `J`. The boundary measure `σ` and outward normal components `n₁,n₂` enter
    only through that formula. No regularity of the boundary is asserted here. -/
theorem picone_integral {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b c V g : ℝ × ℝ → ℝ} {z : ℝ × ℝ → ℂ}
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U)
    (hc : ContDiffOn ℝ 1 c U) (hg : ContDiffOn ℝ 2 g U)
    (hz : ContDiffOn ℝ 1 z U) (hpos : ∀ p ∈ U, 0 < g p)
    (_hraw : IntegrableOn (fun p ↦ piconeEnergy a b c z p - V p * ‖z p‖ ^ 2) U)
    (hgrad : IntegrableOn (fun p ↦ g p ^ 2 *
      piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p) U)
    (hpot : IntegrableOn (fun p ↦ piconeResidual a b c V g p / g p * ‖z p‖ ^ 2) U)
    (hdiv : IntegrableOn
      (divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z)) U)
    {σ : Measure (ℝ × ℝ)} {n₁ n₂ : ℝ × ℝ → ℝ}
    (_hboundary : Integrable (fun p ↦ n₁ p * piconeCurrent₁ a b g z p +
      n₂ p * piconeCurrent₂ b c g z p) σ)
    (hibp : (∫ p in U, divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p) =
      ∫ p, n₁ p * piconeCurrent₁ a b g z p + n₂ p * piconeCurrent₂ b c g z p ∂σ) :
    (∫ p in U, piconeEnergy a b c z p - V p * ‖z p‖ ^ 2) =
      (∫ p in U, g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p) +
        (∫ p in U, piconeResidual a b c V g p / g p * ‖z p‖ ^ 2) +
        ∫ p, n₁ p * piconeCurrent₁ a b g z p + n₂ p * piconeCurrent₂ b c g z p ∂σ := by
  calc
    _ = ∫ p in U, (g p ^ 2 * piconeEnergy a b c (fun q ↦ z q / (g q : ℂ)) p +
        piconeResidual a b c V g p / g p * ‖z p‖ ^ 2) +
        divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p :=
      setIntegral_congr_fun hU.measurableSet fun p hp ↦
        picone_divergence hU ha hb hc hg hz hpos hp
    _ = _ := by
      simpa only [Pi.add_apply, hibp] using
        (integral_add (hgrad.add hpot) hdiv).trans
          (congrArg (fun x ↦ x + ∫ p in U,
            divergence (piconeCurrent₁ a b g z) (piconeCurrent₂ b c g z) p)
            (integral_add hgrad hpot))

end EulerDipoleEigenvalues
