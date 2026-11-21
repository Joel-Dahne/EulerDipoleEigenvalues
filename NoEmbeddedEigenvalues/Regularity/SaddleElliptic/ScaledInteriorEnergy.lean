module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.InteriorEnergy
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakLaplacian

/-! # Scaling the interior estimate from a fixed annulus -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Metric
open scoped ContDiff Topology

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Open annulus in the Euclidean chart radius. -/
def ellipticAnnulus (c : ℝ × ℝ) (a b : ℝ) := {p | a < localRadius c p ∧ localRadius c p < b}

theorem continuous_localRadius (c : ℝ × ℝ) : Continuous (localRadius c) := by
  unfold localRadius
  fun_prop

theorem isOpen_ellipticAnnulus (c : ℝ × ℝ) (a b : ℝ) : IsOpen (ellipticAnnulus c a b) :=
  (isOpen_lt continuous_const (continuous_localRadius c)).inter
    (isOpen_lt (continuous_localRadius c) continuous_const)

theorem isCompact_closure_ellipticAnnulus (c : ℝ × ℝ) (a b : ℝ) :
    IsCompact (closure (ellipticAnnulus c a b)) := by
  apply (isCompact_closedBall c b).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  rintro p ⟨-, hp⟩
  change dist p c ≤ b
  apply le_of_lt
  have hh (s t : ℝ) : |s| ≤ Real.sqrt (s ^ 2 + t ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    linarith [sq_nonneg t]
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  refine ⟨(hh _ _).trans_lt hp, (hh (p.2 - c.2) (p.1 - c.1)).trans_lt ?_⟩
  simpa [localRadius, add_comm] using hp

theorem closure_ellipticAnnulus_subset {c : ℝ × ℝ} {a b a' b' : ℝ}
    (ha : a' < a) (hb : b < b') : closure (ellipticAnnulus c a b) ⊆ ellipticAnnulus c a' b' := by
  have hC : IsClosed (localRadius c ⁻¹' Icc a b) := isClosed_Icc.preimage (continuous_localRadius c)
  have h := closure_minimal (s := ellipticAnnulus c a b) (t := localRadius c ⁻¹' Icc a b)
    (fun _ hp ↦ ⟨hp.1.le, hp.2.le⟩) hC
  exact h.trans fun _ hp ↦ ⟨ha.trans_le hp.1, hp.2.trans_lt hb⟩

private def homothety (c : ℝ × ℝ) (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addRight c)

private theorem homothety_apply (c : ℝ × ℝ) (r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    homothety c r hr p = r • p + c := rfl

private theorem radius_homothety (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    localRadius c (homothety c r hr.ne' p) = r * localRadius 0 p := by
  simp only [homothety_apply, localRadius, Prod.fst_add, Prod.snd_add, add_sub_cancel_right,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, sub_zero]
  rw [show (r * p.1) ^ 2 + (r * p.2) ^ 2 = r ^ 2 * (p.1 ^ 2 + p.2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

private theorem preimage_annulus (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    homothety c r hr.ne' ⁻¹' ellipticAnnulus c (r * a) (r * b) = ellipticAnnulus 0 a b := by
  ext p
  change (r * a < localRadius c (homothety c r hr.ne' p) ∧
    localRadius c (homothety c r hr.ne' p) < r * b) ↔ _
  simp only [radius_homothety c hr p, mul_lt_mul_iff_right₀ hr, ellipticAnnulus, mem_ofPred_eq]

private theorem squareEnergy_homothety (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) (f : ℝ × ℝ → ℂ) (n : ℕ) :
    squareEnergy (homothety c r hr.ne' ⁻¹' U)
      (fun p ↦ (r : ℂ) ^ n * f (homothety c r hr.ne' p)) =
        r ^ (2 * n) * (r ^ 2)⁻¹ * squareEnergy U f := by
  let T := homothety c r hr.ne'
  have hmap : Measure.map T volume = ENNReal.ofReal ((r ^ 2)⁻¹) • volume := by
    change Measure.map ((fun p : ℝ × ℝ ↦ p + c) ∘ (fun p ↦ r • p)) volume = _
    have ha : Measurable (fun p : ℝ × ℝ ↦ p + c) :=
      (measurePreserving_add_right volume c).measurable
    rw [← Measure.map_map ha (continuous_const_smul r).measurable,
      Measure.map_addHaar_smul volume hr.ne']
    simp only [Module.finrank_prod, Module.finrank_self, show (1 : ℕ) + 1 = 2 by decide,
      abs_inv]
    rw [Measure.map_smul _ ha.aemeasurable, (measurePreserving_add_right volume c).map_eq,
      abs_of_nonneg (sq_nonneg r)]
  have hrestr : Measure.map T (volume.restrict (T ⁻¹' U)) =
      ENNReal.ofReal ((r ^ 2)⁻¹) • volume.restrict U := by
    rw [← Measure.restrict_map T.continuous.measurable hU, hmap, Measure.restrict_smul]
  unfold squareEnergy
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow,
    ← pow_mul, Nat.mul_comm n 2, integral_const_mul]
  change r ^ (2 * n) * (∫ p in T ⁻¹' U, ‖f (T p)‖ ^ 2) = _
  rw [← T.measurableEmbedding.integral_map (g := fun p ↦ ‖f p‖ ^ 2), hrestr, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ 2)⁻¹), smul_eq_mul]
  ring

private theorem coordPartial_homothety {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f)
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) (j : Fin 2) (z : ℂ) :
    coordPartial j (fun p ↦ z * f (homothety c r hr.ne' p)) =
      fun p ↦ (r : ℂ) * z * coordPartial j f (homothety c r hr.ne' p) := by
  let T := homothety c r hr.ne'
  have hT (p : ℝ × ℝ) : HasFDerivAt T (r • ContinuousLinearMap.id ℝ _) p := by
    exact ((hasFDerivAt_id p).const_smul r).add_const c
  funext p
  have h := (hf (T p)).hasFDerivAt.comp p (hT p)
  have hc := h.const_smul z
  change coordPartial j (z • (f ∘ T)) p = _
  rw [coordPartial_eq_fderiv_plane hc.differentiableAt, hc.fderiv,
    coordPartial_eq_fderiv_plane (hf (T p))]
  simp [smul_eq_mul, Complex.real_smul, ← mul_assoc, mul_comm z (r : ℂ)]

/-- The smooth interior estimate on the dyadic annuli, with the scaling factors explicit. -/
theorem smooth_dyadic_third_estimate : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℝ × ℝ) (r : ℝ), 0 < r → ∀ {v : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ v →
      ∀ i j k : Fin 2,
        squareEnergy (ellipticAnnulus c r (2 * r))
          (coordPartial i (coordPartial j (coordPartial k v))) ≤ C *
        (squareEnergy (ellipticAnnulus c (r * (3 / 4)) (r * 3))
            (coordPartial k (energyLaplacian v)) +
          r⁻¹ ^ 2 * squareEnergy (ellipticAnnulus c (r * (3 / 4)) (r * 3)) (energyLaplacian v) +
          r⁻¹ ^ 6 * squareEnergy (ellipticAnnulus c (r * (3 / 4)) (r * 3)) v) := by
  let A := ellipticAnnulus 0 1 2
  let B := ellipticAnnulus 0 (3 / 4) 3
  obtain ⟨C, hC, h⟩ := smooth_interior_third_estimate (A := A) (B := B)
    (isOpen_ellipticAnnulus ..) (isOpen_ellipticAnnulus ..)
    (isCompact_closure_ellipticAnnulus ..) (isCompact_closure_ellipticAnnulus ..)
    (closure_ellipticAnnulus_subset (by norm_num) (by norm_num))
  refine ⟨C, hC, fun c r hr v hv i j k ↦ ?_⟩
  let T := homothety c r hr.ne'
  let w := v ∘ T
  have hw : ContDiff ℝ ∞ w := hv.comp (show ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ r • p + c) by fun_prop)
  have hd (j : Fin 2) := contDiff_coordPartial_top j hv
  have hdd (i j : Fin 2) := contDiff_coordPartial_top i (hd j)
  have h₁ (j : Fin 2) : coordPartial j w = fun p ↦ (r : ℂ) * coordPartial j v (T p) := by
    change coordPartial j (fun p ↦ v (homothety c r hr.ne' p)) = _
    simpa only [one_mul, mul_one] using
      coordPartial_homothety (hv.differentiable (by simp)) c hr j 1
  have h₂ (i j : Fin 2) : coordPartial i (coordPartial j w) =
      fun p ↦ (r : ℂ) ^ 2 * coordPartial i (coordPartial j v) (T p) := by
    rw [h₁, coordPartial_homothety ((hd j).differentiable (by simp)) c hr, pow_two]
  have h₃ : coordPartial i (coordPartial j (coordPartial k w)) =
      fun p ↦ (r : ℂ) ^ 3 * coordPartial i (coordPartial j (coordPartial k v)) (T p) := by
    rw [h₂, coordPartial_homothety ((hdd j k).differentiable (by simp)) c hr]
    funext p
    ring
  have hL : energyLaplacian w = fun p ↦ (r : ℂ) ^ 2 * energyLaplacian v (T p) := by
    funext p
    unfold energyLaplacian
    rw [h₂ 0 0, h₂ 1 1, mul_add]
  have hLd : coordPartial k (energyLaplacian w) =
      fun p ↦ (r : ℂ) ^ 3 * coordPartial k (energyLaplacian v) (T p) := by
    have he : ContDiff ℝ ∞ (energyLaplacian v) := (hdd 0 0).add (hdd 1 1)
    rw [hL, coordPartial_homothety (he.differentiable (by simp)) c hr]
    funext p
    ring
  have hAE : T ⁻¹' ellipticAnnulus c r (2 * r) = A := by
    simpa only [mul_one, mul_comm r 2] using preimage_annulus c hr 1 2
  have hBE : T ⁻¹' ellipticAnnulus c (r * (3 / 4)) (r * 3) = B :=
    preimage_annulus c hr _ _
  have hAeq := squareEnergy_homothety c hr (isOpen_ellipticAnnulus c r (2 * r)).measurableSet
    (coordPartial i (coordPartial j (coordPartial k v))) 3
  rw [hAE, ← h₃] at hAeq
  have hm := (isOpen_ellipticAnnulus c (r * (3 / 4)) (r * 3)).measurableSet
  have hB₀ := squareEnergy_homothety c hr hm v 0
  have hB₁ := squareEnergy_homothety c hr hm (energyLaplacian v) 2
  have hB₂ := squareEnergy_homothety c hr hm (coordPartial k (energyLaplacian v)) 3
  change squareEnergy (T ⁻¹' ellipticAnnulus c (r * (3 / 4)) (r * 3)) _ = _ at hB₀ hB₁ hB₂
  rw [hBE] at hB₀ hB₁ hB₂
  simp only [pow_zero, one_mul, Nat.mul_zero] at hB₀
  change squareEnergy B w = _ at hB₀
  rw [← hL] at hB₁
  rw [← hLd] at hB₂
  have hp := h hw i j k
  rw [hAeq, hB₀, hB₁, hB₂] at hp
  apply (mul_le_mul_iff_right₀ (show 0 < r ^ 4 by positivity)).mp
  have hr₀ := hr.ne'
  simp only [show (2 : ℕ) * 3 = 6 by decide, show (2 : ℕ) * 2 = 4 by decide] at hp
  rw [show r ^ 6 * (r ^ 2)⁻¹ = r ^ 4 by field_simp,
    show r ^ 4 * (r ^ 2)⁻¹ = r ^ 2 by field_simp] at hp
  convert hp using 1
  field_simp
  ring

end NoEmbeddedEigenvalues
