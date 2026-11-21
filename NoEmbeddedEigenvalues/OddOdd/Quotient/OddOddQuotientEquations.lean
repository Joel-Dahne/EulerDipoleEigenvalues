module

public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddForms
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SobolevMultipliers

/-!
# Weighted quotient Poisson equations

On the open positive cell multiplication by the dipole conjugates the weighted
operator to the negative ordinary Laplacian. Weak identities use specified
Fourier derivatives and compactly supported tests, not classical derivatives of
raw representatives or a global divided transport domain.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology

/-- The original stream quotient on the open positive cell. Values elsewhere are
    totalized, not continuous separatrix traces. -/
def ddStreamQuotient (ω : L2) (p : ℝ × ℝ) : ℂ :=
  contStream ω p / (dipoleLift p : ℂ)

/-- The original vorticity quotient, used only on the open positive cell. -/
def ddVorticityQuotient (ω : L2) (p : ℝ × ℝ) : ℂ :=
  liftL2 ω p / (dipoleLift p : ℂ)

/-- Weighted area on the positive cell, with `μ = Ψ²`. -/
def ddCellMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict cellSquare).withDensity (fun p ↦ ENNReal.ofReal (ddWeight p))

/-- Classical weighted Laplacian `μ⁻¹ div(μ∇)`. -/
def ddWeightedLaplacian (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (partialX (fun q ↦ (ddWeight q : ℂ) * partialX u q) p +
    partialY (fun q ↦ (ddWeight q : ℂ) * partialY u q) p) / (ddWeight p : ℂ)

/-- Classical `E = 1 - μ⁻¹ div(μ∇)`; not an operator on raw Sobolev representatives. -/
def ddOperator (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  u p - ddWeightedLaplacian u p

/-- Weak realization of `Eu = e`, recording the specified first derivatives.
    All tests are supported inside the open cell, away from `Ψ = 0`. -/
def HasDDOperator (u e ux uy : ℝ × ℝ → ℂ) : Prop :=
  HasWeakPartialOn cellSquare 0 u ux ∧ HasWeakPartialOn cellSquare 1 u uy ∧
    LocallyIntegrableOn e cellSquare ∧
    ∀ η, IsTestFunctionOn cellSquare η →
      (∫ p in cellSquare, (ddWeight p : ℂ) * (e p - u p) * η p) =
        ∫ p in cellSquare, (ddWeight p : ℂ) *
          (ux p * partialX η p + uy p * partialY η p)


private theorem weak_mul_on {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {j : Fin 2} {f d c : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U j f d)
    (hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c U) :
    HasWeakPartialOn U j (fun p ↦ c p * f p)
      (fun p ↦ coordPartial j c p * f p + c p * d p) := by
  have hcd (p) (hp : p ∈ U) : DifferentiableAt ℝ c p :=
    (hc.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hcj : ContinuousOn (coordPartial j c) U := by
    have hf := (hc.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      (continuousOn_const (c := (if j = 0 then (1, 0) else (0, 1) : ℝ × ℝ)))
    apply hf.congr
    intro p hp
    unfold coordPartial
    split_ifs
    · exact partialX_eq_fderiv (hcd p hp)
    · exact partialY_eq_fderiv (hcd p hp)
  have iC := hd.1.continuousOn_mul hc.continuousOn hU.isLocallyClosed
  have iD := hd.1.continuousOn_mul hcj hU.isLocallyClosed
  have iE := hd.2.1.continuousOn_mul hc.continuousOn hU.isLocallyClosed
  refine ⟨iC, iD.add iE, fun η hη ↦ ?_⟩
  let ψ := fun p ↦ c p * η p
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨contDiff_iff_contDiffAt.mpr (fun p ↦ ?_), hη.hasCompactSupport.mul_left,
      (tsupport_mul_subset_right (f := c) (g := η)).trans hη.tsupport_subset⟩
    by_cases hp : p ∈ tsupport η
    · exact (hc.contDiffAt (hU.mem_nhds (hη.tsupport_subset hp))).mul hη.contDiff.contDiffAt
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
      simp [ψ, hq]
  have hprod : coordPartial j ψ = fun p ↦
      coordPartial j c p * η p + c p * coordPartial j η p := by
    funext p
    by_cases hp : p ∈ U
    · unfold coordPartial
      split_ifs
      · exact partialX_mul (hcd p hp) (hη.contDiff.differentiable (by simp) p)
      · exact partialY_mul (hcd p hp) (hη.contDiff.differentiable (by simp) p)
    · have h0 : η p = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hη.tsupport_subset h))
      have h1 : coordPartial j η p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hp (hη.tsupport_subset (tsupport_coordPartial_subset j η h)))
      have h2 : coordPartial j ψ p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hp (hψ.tsupport_subset (tsupport_coordPartial_subset j ψ h)))
      simp [h0, h1, h2]
  have hw := hd.2.2 ψ hψ
  rw [hprod] at hw
  have ia := integrable_mul_of_tsupport_subset iD hη.contDiff.continuous
    hη.hasCompactSupport hη.tsupport_subset
  have ib := integrable_mul_of_tsupport_subset iC (hη.continuous_coordPartial j)
    (hη.hasCompactSupport_coordPartial j)
    ((tsupport_coordPartial_subset j η).trans hη.tsupport_subset)
  have ic := integrable_mul_of_tsupport_subset iE hη.contDiff.continuous
    hη.hasCompactSupport hη.tsupport_subset
  have heq : (fun p ↦ f p * (coordPartial j c p * η p + c p * coordPartial j η p)) =
      fun p ↦ (coordPartial j c p * f p) * η p + (c p * f p) * coordPartial j η p := by
    funext p; ring
  have heq' : (fun p ↦ d p * ψ p) = fun p ↦ (c p * d p) * η p := by
    funext p; dsimp [ψ]; ring
  rw [heq, integral_add ia ib, heq'] at hw
  simp only [add_mul]
  rw [integral_add ia ic]
  linear_combination hw

private abbrev scalar (p : ℝ × ℝ) : ℂ := (dipoleLift p : ℂ)

private theorem smooth_scalar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) scalar := by
  exact Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift by unfold dipoleLift; fun_prop)

private theorem weight_scalar (p : ℝ × ℝ) : (ddWeight p : ℂ) = scalar p ^ 2 := by
  simp only [ddWeight, scalar, Complex.ofReal_pow]

private theorem scalar_ne_zero {p : ℝ × ℝ} (hp : p ∈ cellSquare) : scalar p ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp))

private theorem laplacian_scalar (p : ℝ × ℝ) :
    coordPartial 0 (coordPartial 0 scalar) p +
      coordPartial 1 (coordPartial 1 scalar) p = -scalar p := by
  have hs : ContDiff ℝ 2 dipoleLift := by unfold dipoleLift; fun_prop
  have hd := hs.differentiable (by norm_num)
  have hx := (contDiff_partialX hs).differentiable (by norm_num)
  have hy := (contDiff_partialY hs).differentiable (by norm_num)
  simp only [coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  change partialX (partialX (fun p ↦ (dipoleLift p : ℂ))) p +
    partialY (partialY (fun p ↦ (dipoleLift p : ℂ))) p = _
  rw [partialX_ofReal hd, partialY_ofReal hd, partialX_ofReal hx, partialY_ofReal hy]
  simp only [← Complex.ofReal_add, ← Complex.ofReal_neg]
  exact congrArg Complex.ofReal (laplacian_dipoleLift p)

private theorem weak_flux {v vx vxx : ℝ × ℝ → ℂ} {j : Fin 2}
    (hv : HasWeakPartialOn cellSquare j v vx)
    (hxx : HasWeakPartialOn cellSquare j vx vxx) :
    HasWeakPartialOn cellSquare j
      (fun p ↦ scalar p * vx p - coordPartial j scalar p * v p)
      (fun p ↦ scalar p * vxx p - coordPartial j (coordPartial j scalar) p * v p) := by
  have ha := hxx.mul_smooth isOpen_cellSquare smooth_scalar
  have hb := hv.mul_smooth isOpen_cellSquare (contDiff_coordPartial_top j smooth_scalar)
  have ht := ha.add (hb.const_mul (-1))
  apply ht.congr_ae_on isOpen_cellSquare.measurableSet
  · exact Eventually.of_forall fun p _ ↦ by simp only [neg_one_mul]; ring
  · exact Eventually.of_forall fun p _ ↦ by simp only [neg_one_mul]; ring

private theorem conjugate_poisson {v f vx vy vxx vyy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 v vx)
    (hy : HasWeakPartialOn cellSquare 1 v vy)
    (hxx : HasWeakPartialOn cellSquare 0 vx vxx)
    (hyy : HasWeakPartialOn cellSquare 1 vy vyy)
    (hf : LocallyIntegrableOn f cellSquare)
    (heq : ∀ᵐ p, p ∈ cellSquare → vxx p + vyy p = f p) :
    ∃ ux uy, HasDDOperator (fun p ↦ v p / scalar p)
      (fun p ↦ -f p / scalar p) ux uy := by
  let c := fun p ↦ (scalar p)⁻¹
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c cellSquare :=
    smooth_scalar.contDiffOn.inv (fun _ hp ↦ scalar_ne_zero hp)
  let D := fun (j : Fin 2) (d : ℝ × ℝ → ℂ) p ↦
    coordPartial j c p * v p + c p * d p
  have hd (j : Fin 2) (p) (hp : p ∈ cellSquare) :
      coordPartial j c p = -coordPartial j scalar p / scalar p ^ 2 := by
    unfold coordPartial
    split_ifs
    · exact ((hasDerivAt_partialX (smooth_scalar.differentiable (by simp) p)).inv
        (scalar_ne_zero hp)).deriv
    · exact ((hasDerivAt_partialY (smooth_scalar.differentiable (by simp) p)).inv
        (scalar_ne_zero hp)).deriv
  have hx' : HasWeakPartialOn cellSquare 0 (fun p ↦ v p / scalar p) (D 0 vx) := by
    simpa only [D, c, div_eq_mul_inv, mul_comm] using weak_mul_on isOpen_cellSquare hx hc
  have hy' : HasWeakPartialOn cellSquare 1 (fun p ↦ v p / scalar p) (D 1 vy) := by
    simpa only [D, c, div_eq_mul_inv, mul_comm] using weak_mul_on isOpen_cellSquare hy hc
  have hi : LocallyIntegrableOn (fun p ↦ -f p / scalar p) cellSquare := by
    simpa only [c, div_eq_mul_inv, mul_comm, Pi.neg_apply] using
      hf.neg.continuousOn_mul hc.continuousOn isOpen_cellSquare.isLocallyClosed
  refine ⟨D 0 vx, D 1 vy, hx', hy', hi, fun η hη ↦ ?_⟩
  have hFx := weak_flux hx hxx
  have hFy := weak_flux hy hyy
  have iFx := integrable_mul_of_tsupport_subset hFx.1 (hη.continuous_coordPartial 0)
    (hη.hasCompactSupport_coordPartial 0)
    ((tsupport_coordPartial_subset 0 η).trans hη.tsupport_subset)
  have iFy := integrable_mul_of_tsupport_subset hFy.1 (hη.continuous_coordPartial 1)
    (hη.hasCompactSupport_coordPartial 1)
    ((tsupport_coordPartial_subset 1 η).trans hη.tsupport_subset)
  have iDx := integrable_mul_of_tsupport_subset hFx.2.1 hη.contDiff.continuous
    hη.hasCompactSupport hη.tsupport_subset
  have iDy := integrable_mul_of_tsupport_subset hFy.2.1 hη.contDiff.continuous
    hη.hasCompactSupport hη.tsupport_subset
  have hflux (j) (d : ℝ × ℝ → ℂ) (p) (hp : p ∈ cellSquare) :
      (ddWeight p : ℂ) * D j d p = scalar p * d p - coordPartial j scalar p * v p := by
    dsimp only [D]
    rw [hd j p hp, weight_scalar]
    change (scalar p) ^ 2 * (_ * v p + (scalar p)⁻¹ * d p) = _
    field_simp [scalar_ne_zero hp]
    ring
  have hleft : (∫ p in cellSquare,
      (ddWeight p : ℂ) * (-f p / scalar p - v p / scalar p) * η p) =
      -∫ p, ((scalar p * vxx p - coordPartial 0 (coordPartial 0 scalar) p * v p) +
        (scalar p * vyy p - coordPartial 1 (coordPartial 1 scalar) p * v p)) * η p := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
      have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hη.tsupport_subset h))
      simp [hz]), ← integral_neg]
    apply integral_congr_ae
    filter_upwards [heq] with p hp
    by_cases hpU : p ∈ cellSquare
    · have hl := laplacian_scalar p
      have hh := hp hpU
      rw [weight_scalar]
      change scalar p ^ 2 * (-f p / scalar p - v p / scalar p) * η p = _
      field_simp [scalar_ne_zero hpU]
      linear_combination (scalar p * η p) * hh - (v p * η p) * hl
    · have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hpU (hη.tsupport_subset h))
      simp [hz]
  have hright : (∫ p in cellSquare, (ddWeight p : ℂ) *
      (D 0 vx p * partialX η p + D 1 vy p * partialY η p)) =
      ∫ p, (scalar p * vx p - coordPartial 0 scalar p * v p) * coordPartial 0 η p +
        (scalar p * vy p - coordPartial 1 scalar p * v p) * coordPartial 1 η p := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
      have hz (j) : coordPartial j η p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hp (hη.tsupport_subset (tsupport_coordPartial_subset j η h)))
      simpa only [coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
        (show (ddWeight p : ℂ) *
          (D 0 vx p * coordPartial 0 η p + D 1 vy p * coordPartial 1 η p) = 0 by
            rw [hz 0, hz 1]; ring))]
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ cellSquare
      · simp only [mul_add, ← mul_assoc, hflux _ _ p hp, coordPartial,
          show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      · have hz (j) : coordPartial j η p = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hp (hη.tsupport_subset (tsupport_coordPartial_subset j η h)))
        change _ * (_ * coordPartial 0 η p + _ * coordPartial 1 η p) = _
        simp only [hz, mul_zero, add_zero]
  rw [hleft, hright]
  simp only [add_mul]
  rw [integral_add iFx iFy, integral_add iDx iDy, hFx.2.2 η hη, hFy.2.2 η hη]
  ring

private theorem measurable_weight_density :
    Measurable (fun p ↦ ENNReal.ofReal (ddWeight p)) := by
  unfold ddWeight dipoleLift
  fun_prop

private theorem ordinary_ac_weighted : volume.restrict cellSquare ≪ ddCellMeasure := by
  apply withDensity_absolutelyContinuous' measurable_weight_density.aemeasurable
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet] with p hp
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact sq_pos_of_ne_zero (Complex.ofReal_ne_zero.mp (scalar_ne_zero hp))

private theorem weighted_ac_ordinary : ddCellMeasure ≪ volume.restrict cellSquare :=
  withDensity_absolutelyContinuous _ _

private theorem scalar_enorm_sq (p : ℝ × ℝ) :
    ‖scalar p‖ₑ ^ 2 = ENNReal.ofReal (ddWeight p) := by
  rw [pow_two, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [scalar, Complex.norm_real, Real.norm_eq_abs, ← pow_two, sq_abs, ddWeight]

private theorem scalar_mul_eLpNorm {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f ddCellMeasure) :
    eLpNorm (fun p ↦ scalar p * f p) 2 (volume.restrict cellSquare) =
      eLpNorm f 2 ddCellMeasure := by
  have hfm := hf.mono_ac ordinary_ac_weighted
  have hsm : AEStronglyMeasurable (fun p ↦ scalar p * f p)
      (volume.restrict cellSquare) := smooth_scalar.continuous.aestronglyMeasurable.mul hfm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hsm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  congr 1
  rw [ddCellMeasure, lintegral_withDensity_eq_lintegral_mul₀'
    measurable_weight_density.aemeasurable (hf.enorm.pow_const 2)]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun p ↦ by
    simp only [enorm_mul, mul_pow, scalar_enorm_sq, Pi.mul_apply]

private theorem scalar_mul_memLp {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 ddCellMeasure) :
    MemLp (fun p ↦ scalar p * f p) 2 (volume.restrict cellSquare) := by
  change eLpNorm _ _ _ < ⊤
  rw [scalar_mul_eLpNorm hf.aestronglyMeasurable]
  exact hf

private theorem scalar_div_memLp {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict cellSquare)) :
    MemLp (fun p ↦ f p / scalar p) 2 ddCellMeasure := by
  have hfm : AEStronglyMeasurable f ddCellMeasure :=
    hf.aestronglyMeasurable.mono_ac weighted_ac_ordinary
  have hsm : AEStronglyMeasurable scalar ddCellMeasure :=
    smooth_scalar.continuous.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun p ↦ f p / scalar p) ddCellMeasure := hfm.div₀ hsm
  have heq : (fun p ↦ scalar p * (f p / scalar p)) =ᵐ[volume.restrict cellSquare] f := by
    filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet] with p hp
    field_simp [scalar_ne_zero hp]
  change eLpNorm _ _ _ < ⊤
  rw [← scalar_mul_eLpNorm hm, eLpNorm_congr_ae heq]
  exact hf

/-- Multiplication by `s` is unitary from weighted to ordinary cell L². The
    representative identity is asserted only a.e. on the positive cell. -/
theorem dd_cell_unitary :
    ∃ U : Lp ℂ 2 ddCellMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict cellSquare),
      ∀ u, ∀ᵐ p ∂(volume.restrict cellSquare),
        U u p = (dipoleLift p : ℂ) * u p := by
  let F (u : Lp ℂ 2 ddCellMeasure) : Lp ℂ 2 (volume.restrict cellSquare) :=
    (scalar_mul_memLp (Lp.memLp u)).toLp (fun p ↦ scalar p * u p)
  have hF (u : Lp ℂ 2 ddCellMeasure) :
      F u =ᵐ[volume.restrict cellSquare] fun p ↦ scalar p * u p :=
    (scalar_mul_memLp (Lp.memLp u)).coeFn_toLp
  let T : Lp ℂ 2 ddCellMeasure →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict cellSquare) :=
    { toFun := F
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [hF (u + v), hF u, hF v,
          ordinary_ac_weighted.ae_eq (Lp.coeFn_add u v), Lp.coeFn_add (F u) (F v)]
          with p hsum hu hv huv hsum'
        simp only [Pi.add_apply] at huv hsum'
        rw [hsum, hsum', huv, hu, hv]
        ring
      map_smul' := by
        intro a u
        apply Lp.ext
        filter_upwards [hF (a • u), hF u,
          ordinary_ac_weighted.ae_eq (Lp.coeFn_smul a u), Lp.coeFn_smul a (F u)]
          with p hsum hu hsu hsum'
        simp only [Pi.smul_apply, smul_eq_mul] at hsu hsum'
        change F (a • u) p = (a • F u) p
        rw [hsum, hsum', hsu, hu]
        ring
      norm_map' := by
        intro u
        change ‖(scalar_mul_memLp (Lp.memLp u)).toLp (fun p ↦ scalar p * u p)‖ = ‖u‖
        rw [Lp.norm_toLp, Lp.norm_def, scalar_mul_eLpNorm (Lp.aestronglyMeasurable u)] }
  have hsurj : Function.Surjective T := by
    intro f
    let g := fun p ↦ f p / scalar p
    have hg : MemLp g 2 ddCellMeasure := scalar_div_memLp (Lp.memLp f)
    let u := hg.toLp g
    refine ⟨u, ?_⟩
    apply Lp.ext
    filter_upwards [hF u, ordinary_ac_weighted.ae_eq hg.coeFn_toLp,
      ae_restrict_mem isOpen_cellSquare.measurableSet] with p hFu hu hp
    change F u p = f p
    rw [hFu, hu]
    dsimp only [g]
    field_simp [scalar_ne_zero hp]
  exact ⟨LinearIsometryEquiv.ofSurjective T hsurj, hF⟩

private theorem smoothOn_coordPartial {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → ℂ} {n : ℕ} (hu : ContDiffOn ℝ (n + 1) u U) (j : Fin 2) :
    ContDiffOn ℝ n (coordPartial j u) U := by
  have hf := (hu.fderiv_of_isOpen hU (m := n) (by simp)).clm_apply
    (contDiffOn_const (c := (if j = 0 then (1, 0) else (0, 1) : ℝ × ℝ)))
  apply hf.congr
  intro p hp
  have hd := (hu.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  split_ifs
  · exact partialX_eq_fderiv hd
  · exact partialY_eq_fderiv hd

private theorem classical_flux {u : ℝ × ℝ → ℂ} (hu : ContDiffOn ℝ 1 u cellSquare)
    (j : Fin 2) {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    (ddWeight p : ℂ) * coordPartial j (fun q ↦ u q / scalar q) p =
      scalar p * coordPartial j u p - coordPartial j scalar p * u p := by
  have hud := (hu.contDiffAt (isOpen_cellSquare.mem_nhds hp)).differentiableAt (by simp)
  have hsd := smooth_scalar.differentiable (by simp) p
  have hq : coordPartial j (fun q ↦ u q / scalar q) p =
      (coordPartial j u p * scalar p - u p * coordPartial j scalar p) / scalar p ^ 2 := by
    unfold coordPartial
    split_ifs
    · exact ((hasDerivAt_partialX hud).div (hasDerivAt_partialX hsd)
        (scalar_ne_zero hp)).deriv
    · exact ((hasDerivAt_partialY hud).div (hasDerivAt_partialY hsd)
        (scalar_ne_zero hp)).deriv
  rw [hq, weight_scalar]
  field_simp [scalar_ne_zero hp]

/-- Smooth conjugation on the open cell, where division by `s` is smooth. -/
theorem dd_operator_conjugation {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u cellSquare) {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    (dipoleLift p : ℂ) * ddOperator (fun q ↦ u q / (dipoleLift q : ℂ)) p =
      -laplacian u p := by
  have hud := (hu.contDiffAt (isOpen_cellSquare.mem_nhds hp)).differentiableAt (by norm_num)
  have hsd := smooth_scalar.differentiable (by simp) p
  have hflux (j : Fin 2) :
      coordPartial j (fun q ↦ (ddWeight q : ℂ) *
        coordPartial j (fun z ↦ u z / scalar z) q) p =
      scalar p * coordPartial j (coordPartial j u) p -
        coordPartial j (coordPartial j scalar) p * u p := by
    rw [coordPartial_congr_of_eventuallyEq
      (show (fun q ↦ (ddWeight q : ℂ) * coordPartial j (fun z ↦ u z / scalar z) q)
        =ᶠ[𝓝 p] (fun q ↦ scalar q * coordPartial j u q - coordPartial j scalar q * u q) from
        by
          filter_upwards [isOpen_cellSquare.mem_nhds hp] with q hq
          exact classical_flux (hu.of_le (by norm_num)) j hq) j]
    have hdu := ((smoothOn_coordPartial isOpen_cellSquare hu j).contDiffAt
      (isOpen_cellSquare.mem_nhds hp)).differentiableAt (by norm_num)
    have hds := (contDiff_coordPartial_top j smooth_scalar).differentiable (by simp) p
    fin_cases j
    · change DifferentiableAt ℝ (partialX u) p at hdu
      change DifferentiableAt ℝ (partialX scalar) p at hds
      change partialX (fun q ↦ scalar q * partialX u q - partialX scalar q * u q) p =
        scalar p * partialX (partialX u) p - partialX (partialX scalar) p * u p
      have he := (((hasDerivAt_partialX hsd).mul (hasDerivAt_partialX hdu)).sub
        ((hasDerivAt_partialX hds).mul (hasDerivAt_partialX hud))).deriv
      change partialX (fun q ↦ scalar q * partialX u q - partialX scalar q * u q) p = _
        at he
      rw [he]
      ring
    · change DifferentiableAt ℝ (partialY u) p at hdu
      change DifferentiableAt ℝ (partialY scalar) p at hds
      change partialY (fun q ↦ scalar q * partialY u q - partialY scalar q * u q) p =
        scalar p * partialY (partialY u) p - partialY (partialY scalar) p * u p
      have he := (((hasDerivAt_partialY hsd).mul (hasDerivAt_partialY hdu)).sub
        ((hasDerivAt_partialY hds).mul (hasDerivAt_partialY hud))).deriv
      change partialY (fun q ↦ scalar q * partialY u q - partialY scalar q * u q) p = _
        at he
      rw [he]
      ring
  change scalar p * (u p / scalar p -
    (coordPartial 0 (fun q ↦ (ddWeight q : ℂ) *
        coordPartial 0 (fun z ↦ u z / scalar z) q) p +
      coordPartial 1 (fun q ↦ (ddWeight q : ℂ) *
        coordPartial 1 (fun z ↦ u z / scalar z) q) p) / (ddWeight p : ℂ)) = _
  rw [hflux 0, hflux 1, weight_scalar]
  have hl := laplacian_scalar p
  change _ = -(coordPartial 0 (coordPartial 0 u) p + coordPartial 1 (coordPartial 1 u) p)
  field_simp [scalar_ne_zero hp]
  linear_combination u p * hl

/-- The original quotients satisfy the weak Poisson equation on the open cell,
    without any assumption about their global divided regularity. -/
theorem dd_quotient_equations {lam : ℝ} {ω : L2} (hω : IsEigenSolution lam ω) :
    ∃ ux uy, HasDDOperator (ddStreamQuotient ω)
      (fun p ↦ -ddVorticityQuotient ω p) ux uy := by
  have hx := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 0)
    cellSquare).congr_left (streamLift_ae_eq_contStream ω)
  have hy := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω 1)
    cellSquare).congr_left (streamLift_ae_eq_contStream ω)
  have hxx := hasWeakPartialOn_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 0 0) cellSquare
  have hyy := hasWeakPartialOn_liftL2
    (hasFourierPartial_streamPartial_streamSecondPartial ω 1 1) cellSquare
  have hf : LocallyIntegrableOn (liftL2 ω) cellSquare :=
    (locallyIntegrable_liftL2 ω).locallyIntegrableOn cellSquare
  have heq : ∀ᵐ p, p ∈ cellSquare →
      liftL2 (streamSecondPartial 0 0 ω) p + liftL2 (streamSecondPartial 1 1 ω) p =
        liftL2 ω p := by
    have he := ae_torusProj (Lp.coeFn_add
      (streamSecondPartial 0 0 ω) (streamSecondPartial 1 1 ω))
    rw [streamSecondPartial_add hω.1] at he
    filter_upwards [he] with p hp using fun _ ↦ hp.symm
  change ∃ ux uy, HasDDOperator (fun p ↦ contStream ω p / scalar p)
    (fun p ↦ -(liftL2 ω p / scalar p)) ux uy
  simpa only [neg_div] using conjugate_poisson hx hy hxx hyy hf heq

/-- On the positive cell the raw stream quotient is exactly the continuous supplied
    quotient. No assertion is made on the separatrix. -/
theorem DDQuotientData.raw_stream_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {p : ℝ × ℝ} (hp : p ∈ cellSquare) :
    ddStreamQuotient ω p = continuousRep q.phi (torusProj p) := by
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  rw [ddStreamQuotient, q.contStream_eq]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The raw vorticity quotient agrees with supplied data a.e. on the open cell. -/
theorem DDQuotientData.raw_vorticity_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) :
    ∀ᵐ p ∂(volume.restrict cellSquare), ddVorticityQuotient ω p = liftL2 q.nu p := by
  have hm : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  filter_upwards [ae_restrict_of_ae (ae_torusProj q.vorticity_eq),
    ae_restrict_mem hm] with p hp hpc
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hpc
  unfold ddVorticityQuotient liftL2
  rw [hp, Ψ_torusProj]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The quotient Poisson equation for supplied data, without a classical derivative
    of the chosen L² representative or any global transport-domain claim. -/
theorem DDQuotientData.operator_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hω : IsEigenSolution lam ω) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    HasDDOperator (liftL2 q.phi) (fun p ↦ -liftL2 q.nu p) (liftL2 dx) (liftL2 dy) := by
  obtain ⟨ux, uy, hop⟩ := dd_quotient_equations hω
  have hu : ∀ᵐ p, p ∈ cellSquare → ddStreamQuotient ω p = liftL2 q.phi p := by
    filter_upwards [ae_torusProj (coeFn_eq_continuousRep q.regular)] with p hp hpc
    exact (q.raw_stream_eq hpc).trans hp.symm
  have he := (ae_restrict_iff' isOpen_cellSquare.measurableSet).mp q.raw_vorticity_eq
  have hx := hasWeakPartialOn_liftL2 hdx cellSquare
  have hy := hasWeakPartialOn_liftL2 hdy cellSquare
  have hx' := (hop.1.congr_ae_on isOpen_cellSquare.measurableSet hu
    (Eventually.of_forall fun _ _ ↦ rfl)).ae_eq isOpen_cellSquare hx
  have hy' := (hop.2.1.congr_ae_on isOpen_cellSquare.measurableSet hu
    (Eventually.of_forall fun _ _ ↦ rfl)).ae_eq isOpen_cellSquare hy
  refine ⟨hx, hy, (locallyIntegrable_liftL2 q.nu).neg.locallyIntegrableOn cellSquare,
    fun η hη ↦ ?_⟩
  have hl : (∫ p in cellSquare, (ddWeight p : ℂ) *
      (-liftL2 q.nu p - liftL2 q.phi p) * η p) =
      ∫ p in cellSquare, (ddWeight p : ℂ) *
        (-ddVorticityQuotient ω p - ddStreamQuotient ω p) * η p := by
    apply setIntegral_congr_ae isOpen_cellSquare.measurableSet
    filter_upwards [hu, he] with p hup hep hp
    rw [hup hp, hep hp]
  have hr : (∫ p in cellSquare, (ddWeight p : ℂ) *
      (liftL2 dx p * partialX η p + liftL2 dy p * partialY η p)) =
      ∫ p in cellSquare, (ddWeight p : ℂ) *
        (ux p * partialX η p + uy p * partialY η p) := by
    apply setIntegral_congr_ae isOpen_cellSquare.measurableSet
    filter_upwards [hx', hy'] with p hxp hyp hp
    rw [hxp hp, hyp hp]
  exact hl.trans ((hop.2.2.2 η hη).trans hr.symm)


end NoEmbeddedEigenvalues
