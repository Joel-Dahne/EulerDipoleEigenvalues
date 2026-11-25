module

public import EulerDipoleEigenvalues.OddOdd.Picone.OddOddPiconeIntegrability

/-!
# Cancellation in the differentiated ground-state residual

Blueprint: `lem:dd-ground-residual-factorization`, `lem:dd-ground-residual-bounded`,
`lem:dd-picone-potential-integrable`.

The ratio `s * (2 - s) / r` and the logarithmic factor `r * log (r / 2)`
remain bounded on the positive cell. Factoring the actual differentiated
residual in these coordinates removes its apparent poles. This calculation
is independent of the residual sign certificate.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology

private def radial (r : ℝ) : ℝ :=
  1 / 16 - r * (2 * Real.log (r / 2) + 1) / 256

private def radial' (r : ℝ) : ℝ := -(2 * Real.log (r / 2) + 3) / 256

private def coeffC (s r : ℝ) : ℝ := s * (8 - s ^ 3) / r / 3
private def coeffCs (s r : ℝ) : ℝ := (8 - 4 * s ^ 3) / r / 3
private def coeffCr (s r : ℝ) : ℝ := -s * (8 - s ^ 3) / r ^ 2 / 3
private def polyP (s : ℝ) : ℝ := 2 * s ^ 3 + 32
private def polyU (s : ℝ) : ℝ := s ^ 2 * (8 - s ^ 3)
private def polyPs (s : ℝ) : ℝ := 6 * s ^ 2
private def polyUs (s : ℝ) : ℝ := 16 * s - 5 * s ^ 4
private def polyD (s r : ℝ) : ℝ := 4 - s ^ 2 - 3 * r
private def coeffT (s r : ℝ) : ℝ := (polyP s - 2 * polyU s / r) / 3
private def coeffE (s r : ℝ) : ℝ :=
  (polyP s - polyU s / r) / 24 + coeffT s r * radial r * polyD s r / r
private def coeffEs (s r : ℝ) : ℝ :=
  (polyPs s - polyUs s / r) / 24 +
    (polyPs s - 2 * polyUs s / r) / 3 * radial r * polyD s r / r -
    coeffT s r * radial r * 2 * s / r
private def coeffEr (s r : ℝ) : ℝ :=
  polyU s / r ^ 2 / 24 +
    (2 * polyU s / r ^ 2 / 3 * radial r * polyD s r +
      coeffT s r * radial' r * polyD s r - 3 * coeffT s r * radial r) / r -
    coeffT s r * radial r * polyD s r / r ^ 2

private theorem radial_path {R : ℝ → ℝ} {t dr : ℝ}
    (hR : HasDerivAt R dr t) (hr : R t ≠ 0) :
    HasDerivAt (fun x ↦ radial (R x)) (radial' (R t) * dr) t := by
  have hl := (hR.div_const 2).log (div_ne_zero hr (by norm_num))
  convert (hasDerivAt_const t (1 / 16 : ℝ)).sub
    ((hR.mul ((hl.const_mul 2).add_const 1)).div_const 256) using 1
  · rfl
  · dsimp [radial']
    field_simp [hr]
    ring

private theorem coeffC_path {S R : ℝ → ℝ} {t ds dr : ℝ}
    (hS : HasDerivAt S ds t) (hR : HasDerivAt R dr t) (hr : R t ≠ 0) :
    HasDerivAt (fun x ↦ coeffC (S x) (R x))
      (coeffCs (S t) (R t) * ds + coeffCr (S t) (R t) * dr) t := by
  convert ((hS.mul ((hS.pow 3).const_sub 8)).div hR hr).div_const 3 using 1
  · rfl
  · dsimp [coeffCs, coeffCr]
    field_simp [hr]
    ring

private theorem coeffE_path {S R : ℝ → ℝ} {t ds dr : ℝ}
    (hS : HasDerivAt S ds t) (hR : HasDerivAt R dr t) (hr : R t ≠ 0) :
    HasDerivAt (fun x ↦ coeffE (S x) (R x))
      (coeffEs (S t) (R t) * ds + coeffEr (S t) (R t) * dr) t := by
  have hP : HasDerivAt (fun x ↦ polyP (S x)) (polyPs (S t) * ds) t := by
    convert ((hS.pow 3).const_mul 2).add_const 32 using 1
    · rfl
    · dsimp [polyPs]; ring
  have hU : HasDerivAt (fun x ↦ polyU (S x)) (polyUs (S t) * ds) t := by
    convert (hS.pow 2).mul ((hS.pow 3).const_sub 8) using 1
    · rfl
    · dsimp [polyUs]; ring
  have hD := ((hS.pow 2).const_sub 4).sub (hR.const_mul 3)
  have hT := (hP.sub (((hU.const_mul 2).div hR hr))).div_const 3
  have hB := radial_path hR hr
  convert ((hP.sub (hU.div hR hr)).div_const 24).add
    (((hT.mul hB).mul hD).div hR hr) using 1
  · rfl
  · dsimp [coeffEs, coeffEr, coeffT, polyD]
    field_simp [hr]
    ring

private def fluxModel (x y : ℝ) : ℝ :=
  Real.sin x * (2 * Real.cos x * coeffC (dipoleLift (x, y)) (gradSq dipoleLift (x, y)) *
    radial (gradSq dipoleLift (x, y)) - coeffE (dipoleLift (x, y)) (gradSq dipoleLift (x, y)))

private def fluxDerivative (s r a : ℝ) : ℝ :=
  a * (2 * a * coeffC s r * radial r - coeffE s r) +
    (1 - a ^ 2) * (-2 * coeffC s r * radial r +
      2 * a * (-coeffCs s r + 2 * a * coeffCr s r) * radial r +
      4 * a ^ 2 * coeffC s r * radial' r + coeffEs s r - 2 * a * coeffEr s r)

private theorem fluxModel_deriv (x y : ℝ) (hr : gradSq dipoleLift (x, y) ≠ 0) :
    HasDerivAt (fun t ↦ fluxModel t y)
      (fluxDerivative (dipoleLift (x, y)) (gradSq dipoleLift (x, y)) (Real.cos x)) x := by
  have hS := hasDerivAt_partialX
    (show DifferentiableAt ℝ dipoleLift (x, y) by unfold dipoleLift; fun_prop)
  have hR := hasDerivAt_partialX
    (show DifferentiableAt ℝ (gradSq dipoleLift) (x, y) by rw [gradSq_dipoleLift]; fun_prop)
  simp only [partialX_dipoleLift] at hS
  simp only [partialX_gradSq_dipoleLift] at hR
  have hB := radial_path hR hr
  have hC := coeffC_path hS hR hr
  have hE := coeffE_path hS hR hr
  convert (Real.hasDerivAt_sin x).mul
    (((((Real.hasDerivAt_cos x).const_mul 2).mul hC).mul hB).sub hE) using 1
  · rfl
  · dsimp [fluxDerivative]
    rw [← Real.sin_sq_add_cos_sq x]
    ring

private theorem ground_partialX_model {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddGround p = Real.sin p.1 *
      (-Real.cos p.2 / 8 - Real.cos p.1 * gradSq dipoleLift p *
        (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128) := by
  rw [partialX_ddGround hr]
  change -Real.sin p.1 * Real.cos p.2 / 8 -
    (gradSq dipoleLift p * (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128) *
      Real.sin p.1 * Real.cos p.1 = _
  ring

private theorem ground_partialY_model {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddGround p = Real.sin p.2 *
      (-Real.cos p.1 / 8 - Real.cos p.2 * gradSq dipoleLift p *
        (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128) := by
  rw [partialY_ddGround hr]
  change -Real.sin p.2 * Real.cos p.1 / 8 -
    (gradSq dipoleLift p * (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128) *
      Real.sin p.2 * Real.cos p.2 = _
  ring

private theorem sin_sq (x : ℝ) : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
  linarith [Real.sin_sq_add_cos_sq x]

set_option maxRecDepth 4096 in
private theorem ground_fluxX_model {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddMxx p * partialX ddGround p + ddMxy p * partialY ddGround p =
      fluxModel p.1 p.2 := by
  rw [ground_partialX_model hr, ground_partialY_model hr]
  let gx := -Real.cos p.2 / 8 - Real.cos p.1 * gradSq dipoleLift p *
    (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128
  let gy := -Real.cos p.1 / 8 - Real.cos p.2 * gradSq dipoleLift p *
    (2 * Real.log (gradSq dipoleLift p / 2) + 1) / 128
  change ddMxx p * (Real.sin p.1 * gx) + ddMxy p * (Real.sin p.2 * gy) = _
  calc
    _ = Real.sin p.1 * (ddC p * gx + (ddA p - ddC p) / gradSq dipoleLift p *
        (Real.sin p.1 ^ 2 * gx + Real.sin p.2 ^ 2 * gy)) := by
      unfold ddMxx ddMxy
      ring
    _ = _ := by
      unfold fluxModel
      congr 1
      dsimp [gx, gy, ddA, ddC, coeffC, coeffE, coeffT, radial, polyD, polyP, polyU]
      simp only [dipoleLift, gradSq_dipoleLift, sin_sq] at *
      field_simp [hs, hr]
      ring

private theorem ground_fluxY_model {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddMxy p * partialX ddGround p + ddMyy p * partialY ddGround p =
      fluxModel p.2 p.1 := by
  have hs' : dipoleLift (p.2, p.1) ≠ 0 := by simpa [dipoleLift, add_comm] using hs
  have hr' : gradSq dipoleLift (p.2, p.1) ≠ 0 := by
    simpa [gradSq_dipoleLift, add_comm] using hr
  have h := ground_fluxX_model hs' hr'
  have hX : partialX ddGround (p.2, p.1) = partialY ddGround p := by
    rw [ground_partialX_model hr', ground_partialY_model hr]
    simp only [gradSq_dipoleLift, add_comm]
  have hY : partialY ddGround (p.2, p.1) = partialX ddGround p := by
    rw [ground_partialY_model hr', ground_partialX_model hr]
    simp only [gradSq_dipoleLift, add_comm]
  have hC : ddC (p.2, p.1) = ddC p := by
    simp only [ddC, dipoleLift, gradSq_dipoleLift, add_comm]
  have hA : ddA (p.2, p.1) = ddA p := by
    simp only [ddA, hC, dipoleLift, add_comm]
  have hMxx : ddMxx (p.2, p.1) = ddMyy p := by
    simp only [ddMxx, ddMyy, hC, hA, gradSq_dipoleLift, add_comm]
  have hMxy : ddMxy (p.2, p.1) = ddMxy p := by
    simp only [ddMxy, hC, hA, gradSq_dipoleLift, add_comm]
    ring
  rw [hX, hY, hMxx, hMxy] at h
  exact (add_comm _ _).trans h

private theorem ground_fluxX_partial {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialX (fun q ↦ ddMxx q * partialX ddGround q + ddMxy q * partialY ddGround q) p =
      fluxDerivative (dipoleLift p) (gradSq dipoleLift p) (Real.cos p.1) := by
  have hS : Continuous (fun t ↦ dipoleLift (t, p.2)) := by unfold dipoleLift; fun_prop
  have hR : Continuous (fun t ↦ gradSq dipoleLift (t, p.2)) := by
    simp only [gradSq_dipoleLift]; fun_prop
  have heq : (fun t ↦ ddMxx (t, p.2) * partialX ddGround (t, p.2) +
      ddMxy (t, p.2) * partialY ddGround (t, p.2)) =ᶠ[𝓝 p.1] (fun t ↦ fluxModel t p.2) := by
    filter_upwards [hS.continuousAt.eventually_ne hs, hR.continuousAt.eventually_ne hr]
      with t htS htR
    exact ground_fluxX_model htS htR
  exact ((fluxModel_deriv p.1 p.2 hr).congr_of_eventuallyEq heq).deriv

private theorem ground_fluxY_partial {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialY (fun q ↦ ddMxy q * partialX ddGround q + ddMyy q * partialY ddGround q) p =
      fluxDerivative (dipoleLift p) (gradSq dipoleLift p) (Real.cos p.2) := by
  have hS : Continuous (fun t ↦ dipoleLift (p.1, t)) := by unfold dipoleLift; fun_prop
  have hR : Continuous (fun t ↦ gradSq dipoleLift (p.1, t)) := by
    simp only [gradSq_dipoleLift]; fun_prop
  have heq : (fun t ↦ ddMxy (p.1, t) * partialX ddGround (p.1, t) +
      ddMyy (p.1, t) * partialY ddGround (p.1, t)) =ᶠ[𝓝 p.2] (fun t ↦ fluxModel t p.1) := by
    filter_upwards [hS.continuousAt.eventually_ne hs, hR.continuousAt.eventually_ne hr]
      with t htS htR
    exact ground_fluxY_model htS htR
  have hr' : gradSq dipoleLift (p.2, p.1) ≠ 0 := by
    simpa [gradSq_dipoleLift, add_comm] using hr
  have h := ((fluxModel_deriv p.2 p.1 hr').congr_of_eventuallyEq heq).deriv
  simpa only [partialY, dipoleLift, gradSq_dipoleLift, add_comm] using h

/-- A polynomial representation of the actual ground-state residual in bounded coordinates. -/
def ddGroundResidualPolynomial (s r z l : ℝ) : ℝ :=
  -z ^ 3 * (s + 2) ^ 2 * (s ^ 2 + 2 * s + 4) / 12 +
    s * z ^ 2 * (s + 2) * (s ^ 4 + 2 * s ^ 3 + 104 * s ^ 2 + 200 * s + 208) / 384 -
    z * (5 * s ^ 6 + 10 * s ^ 5 + 56 * s ^ 4 + 96 * s ^ 3 -
      64 * s ^ 2 - 128 * s - 256) / 192 +
    s * (14 * s ^ 5 + 19 * s ^ 3 + 74 * s ^ 2 - 96 * s - 416) / 192 +
    r * s * (5 * s ^ 3 + 15 * s + 113) / 96 - 3 * r ^ 2 * s ^ 2 / 128 +
    l * (z ^ 3 * (s + 2) ^ 2 * (s ^ 2 + 2 * s + 4) / 192 -
      s * z ^ 2 * (s + 2) * (s ^ 2 + 2 * s + 4) / 96 -
      z * (9 * s ^ 4 + 18 * s ^ 3 + 8 * s ^ 2 + 280 * s + 560) / 768 +
      s * (s ^ 3 + 24 * s + 352) / 384 - 3 * r * s ^ 2 / 64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Clear the rational denominators before normalizing the polynomial identity.
/-- Exact factorization of the differentiated residual, without a sign certificate. -/
theorem ddGroundResidual_eq_polynomial {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddGroundResidual p = ddGroundResidualPolynomial (dipoleLift p) (gradSq dipoleLift p)
      (dipoleLift p * (2 - dipoleLift p) / gradSq dipoleLift p)
      (gradSq dipoleLift p * Real.log (gradSq dipoleLift p / 2)) := by
  unfold ddGroundResidual
  rw [ground_fluxX_partial hs hr, ground_fluxY_partial hs hr]
  dsimp [fluxDerivative, coeffC, coeffCs, coeffCr, radial, radial', coeffE, coeffEs,
    coeffEr, coeffT, polyP, polyU, polyD, polyPs, polyUs, ddGroundResidualPolynomial,
    ddF, ddGround]
  simp only [dipoleLift, gradSq_dipoleLift, sin_sq] at *
  field_simp [hr]
  ring

/-- The apparent poles of the residual cancel uniformly, including near saddles. -/
theorem exists_bound_ddGroundResidual : ∃ C : ℝ, 0 ≤ C ∧
    ∀ p : ℝ × ℝ, 0 < dipoleLift p → dipoleLift p < 2 → |ddGroundResidual p| ≤ C := by
  let K : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (Icc 0 2 ×ˢ Icc 0 2) ×ˢ (Icc 0 1 ×ˢ Icc (-2) 2)
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hP : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) ↦
      ddGroundResidualPolynomial q.1.1 q.1.2 q.2.1 q.2.2) := by
    unfold ddGroundResidualPolynomial
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hP.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hs hs2 ↦ ?_⟩
  have hr := gradSq_dipoleLift_pos hs hs2
  have hr2 : gradSq dipoleLift p ≤ 2 := by
    rw [gradSq_dipoleLift]
    nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
  have hz : dipoleLift p * (2 - dipoleLift p) / gradSq dipoleLift p ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hr).mpr (dipoleLift_mul_le_gradSq p)⟩
  have hl : |gradSq dipoleLift p * Real.log (gradSq dipoleLift p / 2)| ≤ 2 := by
    have h := (Real.abs_log_mul_self_lt (gradSq dipoleLift p / 2)
      (by positivity) (by linarith)).le
    have he : gradSq dipoleLift p * Real.log (gradSq dipoleLift p / 2) =
        2 * (Real.log (gradSq dipoleLift p / 2) * (gradSq dipoleLift p / 2)) := by ring
    rw [he, abs_mul]
    norm_num only at *
    linarith
  rw [ddGroundResidual_eq_polynomial hs.ne' hr.ne']
  exact (hC ((dipoleLift p, gradSq dipoleLift p),
    (dipoleLift p * (2 - dipoleLift p) / gradSq dipoleLift p,
      gradSq dipoleLift p * Real.log (gradSq dipoleLift p / 2)))
    ⟨⟨⟨hs.le, hs2.le⟩, ⟨hr.le, hr2⟩⟩, ⟨hz, abs_le.mp hl⟩⟩).trans (le_max_left _ _)

private theorem ae_regular_cellSquare :
    ∀ᵐ p ∂volume.restrict cellSquare, 0 < dipoleLift p ∧ dipoleLift p < 2 := by
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet,
    ae_restrict_of_ae ae_cos_fst_ne_cos_snd] with p hp hn
  have hs := torusProj_mem_positiveCell hp
  change 0 < Ψ (torusProj p) at hs
  rw [Ψ_torusProj] at hs
  refine ⟨hs, ?_⟩
  by_contra hge
  apply hn
  unfold dipoleLift at hge
  linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]

/-- The potential is integrable for arbitrary L² data; no derivative or parity is needed. -/
theorem ddPiconePotential_integrable (φ : L2) :
    IntegrableOn (ddPiconePotential φ) cellSquare := by
  let R := fun p ↦ ddGroundResidualPolynomial (dipoleLift p) (gradSq dipoleLift p)
    (dipoleLift p * (2 - dipoleLift p) / gradSq dipoleLift p)
    (gradSq dipoleLift p * Real.log (gradSq dipoleLift p / 2))
  have hm : Measurable R := by
    dsimp [R, ddGroundResidualPolynomial, dipoleLift]
    simp only [gradSq_dipoleLift]
    fun_prop
  have hw : Measurable ddGround := by
    unfold ddGround
    simp only [gradSq_dipoleLift, dipoleLift]
    fun_prop
  have hb : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  have hL := memLp_liftL2 φ hb
  have hmeas : AEStronglyMeasurable (ddPiconePotential φ) (volume.restrict cellSquare) := by
    apply ((hm.div hw).aestronglyMeasurable.mul (hL.aestronglyMeasurable.norm.pow 2)).congr
    filter_upwards [ae_regular_cellSquare] with p hp
    simp only [ddPiconePotential, R,
      ddGroundResidual_eq_polynomial hp.1.ne' (gradSq_dipoleLift_pos hp.1 hp.2).ne']
    rfl
  obtain ⟨C, hC, hbound⟩ := exists_bound_ddGroundResidual
  apply ((hL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul C).mono' hmeas
  filter_upwards [ae_regular_cellSquare] with p hp
  have hwpos : 0 < ddGround p := lt_of_lt_of_le zero_lt_one (one_le_ddGround p)
  have hcoeff : |ddGroundResidual p| / ddGround p ≤ C := by
    apply (div_le_iff₀ hwpos).mpr
    exact (hbound p hp.1 hp.2).trans (le_mul_of_one_le_right hC (one_le_ddGround p))
  simpa only [ddPiconePotential, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos hwpos, abs_of_nonneg (sq_nonneg ‖liftL2 φ p‖)] using
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖liftL2 φ p‖)

/-- Integrability of the actual differentiated residual, not a sign certificate for it. -/
theorem dd_piconePotential_integrable {φ : L2} (_hφ : MemSobolev 2 φ) :
    IntegrableOn (ddPiconePotential φ) cellSquare :=
  ddPiconePotential_integrable φ

/-- All four integrability assertions on a positive Picone truncation. No
    Fourier derivative relations are needed for these assertions. -/
theorem dd_truncated_picone_integrability {φ : L2} (hφ : MemSobolev 2 φ) (dx dy : L2)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconePotential φ) (ddTruncatedCell ε) ∧
      IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
        ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
        volume 0 (orbitPeriod (ε / 2)) := by
  exact ⟨ddRawEnergy_integrable φ dx dy hε.1,
    ddPiconeGradient_integrable φ dx dy hε.1,
    (dd_piconePotential_integrable hφ).mono_set (fun _ hp ↦ hp.1),
    ddGroundCurrent_intervalIntegrable φ hε⟩

end EulerDipoleEigenvalues
