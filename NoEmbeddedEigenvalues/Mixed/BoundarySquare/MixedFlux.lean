module

public import NoEmbeddedEigenvalues.Mixed.BoundarySquare.MixedTraceMass
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedTangentialLimit
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedPairing
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedEdgeDefect
public import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedLevelGradient
public import NoEmbeddedEigenvalues.Mixed.BoundarySquare.MixedBoundarySquare
public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.CanonicalBoundaryForm
public import NoEmbeddedEigenvalues.EvenEven.GradientTraces.EvenEvenBoundary
public import NoEmbeddedEigenvalues.Mixed.BoundarySquare.MixedVorticityTrace
public import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix.MixedSeparatrix
public import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix.MixedQuotient
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.EdgeWindowTransport
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.BoundaryTraceCompare
public import NoEmbeddedEigenvalues.Transport.CanonicalProfile.Melnikov
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.BoundedVariation

/-! # Paired mixed-sector flux and its Neumann trace -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology ENNReal

local notation "Plane" => ℝ × ℝ

/-- An absolute-level collar in the Cartesian lift. -/
def mixedSeparatrixCollar (ε : ℝ) : Set Plane := {p | |dipoleLift p| < ε}

private theorem mixed_cell_eq_strip (ε : ℝ) :
    cellSquare ∩ mixedSeparatrixCollar ε = cellSeparatrixStrip ε := by
  ext p
  have hp (h : p ∈ cellSquare) : 0 < dipoleLift p := by
    rw [dipoleLift_eq_diag]
    exact mul_pos (mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo (abs_lt.mp h.1)))
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp h.2))
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, hp h, (abs_of_pos (hp h)) ▸ h'⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨h, by change |dipoleLift p| < ε; rwa [abs_of_pos h₁]⟩

/-- Regularity across the separatrix and the one-factor cell quotient. -/
theorem mixed_quotient_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) :
    Nonempty (MixedQuotientData ω) ∧
      ∃ ε : ℝ, 0 < ε ∧
        MemSobolevLocOn 1 (mixedSeparatrixCollar ε) (liftL2 ω) ∧
        MemSobolevLocOn 3 (mixedSeparatrixCollar ε) (liftL2 (invLap ω)) ∧
        ∀ σ : Bool, HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 0 σ
          (liftL2 ω) (fun _ ↦ 0) := by
  obtain ⟨ε, hε, _, hv, hψ, hodd⟩ := mixed_separatrix_h1 hlam hω hs
  have hψ' : MemSobolevLocOn 3 (mixedSeparatrixCollar ε) (liftL2 (invLap ω)) :=
    hψ.congr_ae_on ((streamLift_ae_eq_contStream ω).symm.mono fun _ hp _ ↦ hp)
  refine ⟨mixed_quotient_data_of_collar hω.1 hs hε hv hψ, ε, hε, hv, hψ', ?_⟩
  rw [mixed_cell_eq_strip]
  exact hodd

/-- The two Neumann arcs, with their inherited orientations. -/
def mixedNeumannArc (positive : Bool) (t : ℝ) : Plane :=
  cellArc (if positive then 0 else 2) t

/-- Inverse flow time on a Neumann side, in tangential coordinate `a`.
On the positive side `sin a = -tanh t`; on the negative side the sign reverses. -/
def mixedNeumannTime (positive : Bool) (a : ℝ) : ℝ :=
  Real.artanh ((if positive then -1 else 1) * Real.sin a)

/-- The physical stream trace, using the continuous quotient on the Neumann arc. -/
def mixedNeumannStream (φ : Plane → ℂ) (positive : Bool) (t : ℝ) : ℂ :=
  let q := diagCoord (mixedNeumannArc positive t)
  (Real.cos q.1 : ℂ) * φ q

/-- The transformed stream trace `G = ψ/sech t` in `x = tanh t`. -/
def mixedNeumannG (φ : Plane → ℂ) (positive : Bool) (x : ℝ) : ℂ :=
  φ (diagCoord (mixedNeumannArc positive (Real.artanh x)))

/-- The transformed canonical unknown `F = z/sech t`. -/
def mixedNeumannF (lam : ℝ) (φ : Plane → ℂ) (positive : Bool) (x : ℝ) : ℂ :=
  canonicalUnknown lam (mixedNeumannStream φ positive) (Real.artanh x) /
    (Real.sqrt (boundaryWeight x) : ℂ)

/-- Neumann contribution to the cutoff flux, before renormalizing the gradient term. -/
def mixedNeumannFluxCutoff (lam : ℝ) (φ : Plane → ℂ) (σ : Bool) (T : ℝ) : ℝ :=
  let g := mixedNeumannStream φ σ
  ∫ t in Ioo (-T) T, ‖deriv g t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 +
    (canonicalProfile lam g t * conj (g t)).re

/-- The paired edge expression before taking the limit. On a Dirichlet side,
the squared physical normal derivative is `|φ|²/2`. On a Neumann side the
physical tangential derivative is the time derivative divided by the flow speed. -/
def mixedPairedFluxCutoff (lam : ℝ) (φ : Plane → ℂ) (T : ℝ) : ℝ :=
  let dir := fun k : ℕ ↦ ∫ t in Ioo (-T) T, ‖φ (diagCoord (cellArc k t))‖ ^ 2 / 2
  dir 1 + dir 3 - ∑ σ : Bool, mixedNeumannFluxCutoff lam φ σ T

/-- Signed gradient contribution to the cutoff flux, with no vorticity pairing. -/
def mixedGradientFluxCutoff (φ : Plane → ℂ) (T : ℝ) : ℝ :=
  let dir := fun k : ℕ ↦ ∫ t in Ioo (-T) T, ‖φ (diagCoord (cellArc k t))‖ ^ 2 / 2
  dir 1 + dir 3 - ∑ σ : Bool, ∫ t in Ioo (-T) T,
    ‖deriv (mixedNeumannStream φ σ) t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2

/-- The geometric part of the normal-field level term, before pairing with vorticity. -/
def mixedGeometricLevelTerm (ω : L2) (h : ℝ) : ℝ :=
  levelIntegral h (fun p ↦ gradNorm p * (streamLift ω p * conj (streamNormal ω p)).re) +
    (2 - 2 * h) * (levelIntegral h (fun p ↦ ‖streamNormal ω p‖ ^ 2) -
      levelIntegral h (fun p ↦ ‖streamTangent ω p‖ ^ 2))

/-- Integrated tangential comparison for the adapted and normal fields.
The two integrals are separately absolutely convergent; this comparison
requires removing the boundary current of their tangential difference. -/
theorem mixed_tangential_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (_hs : InSector false true ω) (d : MixedQuotientData ω) :
    (∫ q in mixedOpenCell, mixedVirialDensity d q) =
      ∫ q in mixedOpenCell, mixedNormalVirialDensity d q :=
  mixed_tangential_compare hlam hω d

private theorem mixed_tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun t ↦ by
    rw [(hasDerivAt_tanh t).deriv, one_sub_tanh_sq]
    positivity

private theorem mixed_tanh_mem (t : ℝ) : Real.tanh t ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩

private theorem mixed_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  apply tendsto_order.2
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ Eventually.of_forall fun t ↦ (Real.tanh_lt_one t).trans hx⟩
  obtain ⟨y, hxy, hy⟩ := exists_between (max_lt (show (-1 : ℝ) < 1 by norm_num) hx)
  filter_upwards [eventually_ge_atTop (Real.artanh y)] with t ht
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨(le_max_left _ _).trans_lt hxy, hy⟩
  calc
    x < y := (le_max_right _ _).trans_lt hxy
    _ = Real.tanh (Real.artanh y) := (Real.tanh_artanh hy').symm
    _ ≤ Real.tanh t := mixed_tanh_strictMono.monotone ht

private theorem mixedNeumannArc_cos (σ : Bool) (t : ℝ) :
    Real.cos (diagCoord (mixedNeumannArc σ t)).1 = (Real.cosh t)⁻¹ := by
  cases σ <;>
    simp [mixedNeumannArc, cellArc, Function.iterate_succ_apply', rotLift,
      separatrixArc, diagCoord, show ∀ a : ℝ, (a + (a - Real.pi)) / 2 = a - Real.pi / 2
        from fun a ↦ by ring,
      show ∀ a : ℝ, (-a + (Real.pi - a)) / 2 = -(a - Real.pi / 2)
        from fun a ↦ by ring, Real.cos_sub, sin_arcAngle, one_div]

private theorem mixedNeumannArc_mem (σ : Bool) (t : ℝ) :
    diagCoord (mixedNeumannArc σ t) ∈ closure mixedOpenCell := by
  rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos])]
  have ha : 0 < arcAngle t ∧ arcAngle t < Real.pi := by
    unfold arcAngle
    constructor
    · exact mul_pos (by norm_num) (Real.arctan_pos.mpr (Real.exp_pos _))
    · linarith [Real.arctan_lt_pi_div_two (Real.exp (-t))]
  cases σ <;>
    simp only [mixedNeumannArc, Bool.false_eq_true, ↓reduceIte, cellArc,
      Function.iterate_succ_apply', Function.iterate_zero_apply, rotLift, separatrixArc,
      diagCoord, mem_prod, mem_Icc] <;> constructor <;> constructor <;>
      linarith [ha.1, ha.2, Real.pi_pos]

private theorem mixed_sech_deriv (t : ℝ) :
    HasDerivAt (fun s ↦ (Real.cosh s)⁻¹) (-(Real.cosh t)⁻¹ * Real.tanh t) t := by
  convert (Real.hasDerivAt_cosh t).inv (Real.cosh_pos t).ne' using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

private def mixedNeumannA (σ : Bool) (t : ℝ) : ℝ :=
  if σ then arcAngle t - Real.pi / 2 else -(arcAngle t - Real.pi / 2)

private theorem mixedNeumann_coord (σ : Bool) (t : ℝ) :
    diagCoord (mixedNeumannArc σ t) = (mixedNeumannA σ t, cellEdgeNormal σ) := by
  cases σ <;> simp only [mixedNeumannArc, cellArc, Function.iterate_succ_apply',
    Function.iterate_zero_apply, rotLift, Bool.false_eq_true, ↓reduceIte, separatrixArc,
    diagCoord, mixedNeumannA, cellEdgeNormal, Prod.mk.injEq] <;> constructor <;> ring

private theorem mixedNeumannA_mem (σ : Bool) (t : ℝ) :
    mixedNeumannA σ t ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
  have ht := arcAngle_mem_Ioo t
  cases σ <;> simp only [mixedNeumannA, Bool.false_eq_true, ↓reduceIte] <;> constructor <;>
    linarith [ht.1, ht.2]

private theorem mixedNeumannA_deriv (σ : Bool) (t : ℝ) :
    HasDerivAt (mixedNeumannA σ)
      ((if σ then -1 else 1) * (Real.cosh t)⁻¹) t := by
  have h := (hasDerivAt_arcAngle t).sub_const (Real.pi / 2)
  cases σ
  · exact h.neg.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl) |>.congr_deriv
      (by simp [one_div])
  · exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl) |>.congr_deriv
      (by simp [one_div])

private theorem mixedNeumannA_image (σ : Bool) :
    range (mixedNeumannA σ) = Ioo (-Real.pi / 2) (Real.pi / 2) := by
  refine Subset.antisymm (range_subset_iff.2 (mixedNeumannA_mem σ)) ?_
  intro a ha
  have hpos : a + Real.pi / 2 ∈ Ioo 0 Real.pi :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hneg : -a + Real.pi / 2 ∈ Ioo 0 Real.pi :=
    ⟨by linarith [ha.2], by linarith [ha.1]⟩
  cases σ
  · refine ⟨-Real.log (Real.tan ((-a + Real.pi / 2) / 2)), ?_⟩
    simp [mixedNeumannA, arcAngle_surjOn hneg]
  · refine ⟨-Real.log (Real.tan ((a + Real.pi / 2) / 2)), ?_⟩
    simp [mixedNeumannA, arcAngle_surjOn hpos]

private theorem mixedNeumannA_injective (σ : Bool) : Function.Injective (mixedNeumannA σ) := by
  cases σ
  · exact (fun _ _ h ↦ strictAnti_arcAngle.injective (by simpa [mixedNeumannA] using h))
  · exact (fun _ _ h ↦ strictAnti_arcAngle.injective (by simpa [mixedNeumannA] using h))

private theorem mixedNeumannA_integrable (σ : Bool) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo (-Real.pi / 2) (Real.pi / 2))) :
    Integrable (fun t ↦ (Real.cosh t)⁻¹ * f (mixedNeumannA σ t)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := mixedNeumannA σ)
    MeasurableSet.univ (fun t _ ↦ (mixedNeumannA_deriv σ t).hasDerivWithinAt)
    (mixedNeumannA_injective σ).injOn f
  rw [image_univ, mixedNeumannA_image, integrableOn_univ] at h
  refine (h.mp hf).congr (Eventually.of_forall fun t ↦ ?_)
  have hp := inv_pos.mpr (Real.cosh_pos t)
  cases σ <;> simp [abs_of_pos hp, smul_eq_mul]

private theorem mixedNeumannA_integral (σ : Bool) (f : ℝ → ℝ) :
    (∫ t, (Real.cosh t)⁻¹ * f (mixedNeumannA σ t)) =
      ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), f a := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := mixedNeumannA σ)
    MeasurableSet.univ (fun t _ ↦ (mixedNeumannA_deriv σ t).hasDerivWithinAt)
    (mixedNeumannA_injective σ).injOn f
  rw [image_univ, mixedNeumannA_image, Measure.restrict_univ] at h
  rw [h]
  apply integral_congr_ae
  refine Eventually.of_forall fun t ↦ ?_
  have hp := inv_pos.mpr (Real.cosh_pos t)
  cases σ <;> simp [abs_of_pos hp, smul_eq_mul]

private theorem mixedNeumannA_true_neg (t : ℝ) :
    mixedNeumannA true (-t) = -(mixedNeumannA true t) := by
  simp only [mixedNeumannA, ite_true, arcAngle, neg_neg, Real.exp_neg]
  rw [Real.arctan_inv_of_pos (Real.exp_pos t)]
  ring

/-- Pair the singular edge masses before taking the time cutoff. This does
not require the bulk divergence theorem for the trace-mass current. -/
theorem mixed_trace_mass_cutoff_limit {ω : L2} (d : MixedQuotientData ω) :
    Tendsto (mixedTraceMassCutoff d.phi) atTop
      (𝓝 (∫ x in Ioo (-Real.pi / 2) (Real.pi / 2), mixedEdgeMassDefect d.phi x / Real.cos x)) := by
  let a := mixedNeumannA true
  let D (σ : Bool) (t : ℝ) := ‖d.phi (cellEdgeNormal σ, a t)‖ ^ 2
  let N (σ : Bool) (t : ℝ) := ‖d.phi (a t, cellEdgeNormal σ)‖ ^ 2
  let F := fun t ↦ mixedEdgeMassDefect d.phi (a t)
  let f := fun x ↦ mixedEdgeMassDefect d.phi x / Real.cos x
  have hfi : IntegrableOn f (Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    simpa only [neg_div] using mixed_edge_mass_defect_integrable d
  have hcos (t : ℝ) : Real.cos (a t) = (Real.cosh t)⁻¹ := by
    have h := mixedNeumannArc_cos true t
    rw [mixedNeumann_coord] at h
    exact h
  have hF (t : ℝ) : (Real.cosh t)⁻¹ * f (a t) = F t := by
    dsimp only [F, f]
    rw [hcos, mul_div_cancel₀ _ (inv_ne_zero (Real.cosh_pos t).ne')]
  have hi : Integrable F := (mixedNeumannA_integrable true hfi).congr (.of_forall hF)
  have hI : (∫ t, F t) = ∫ x in Ioo (-Real.pi / 2) (Real.pi / 2), f x := by
    have hs := integral_image_eq_integral_abs_deriv_smul (f := a) (g := f)
      MeasurableSet.univ (fun t _ ↦ (mixedNeumannA_deriv true t).hasDerivWithinAt)
      (mixedNeumannA_injective true).injOn
    rw [image_univ, mixedNeumannA_image, setIntegral_univ] at hs
    rw [hs]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hF t]
    simp only [ite_true, neg_one_mul, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr (Real.cosh_pos t).le), smul_eq_mul]
  have hac : Continuous a := continuous_iff_continuousAt.2
    fun t ↦ (mixedNeumannA_deriv true t).continuousAt
  have hden (x : ℝ) (hx : x ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) (σ : Bool) :
      (cellEdgeNormal σ, x) ∈ closure mixedOpenCell ∧
      (x, cellEdgeNormal σ) ∈ closure mixedOpenCell := by
    rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos])]
    have h : cellEdgeNormal σ ∈ Icc (-Real.pi / 2) (Real.pi / 2) := by
      cases σ <;> simp [cellEdgeNormal] <;> linarith [Real.pi_pos]
    exact ⟨⟨h, Ioo_subset_Icc_self hx⟩, ⟨Ioo_subset_Icc_self hx, h⟩⟩
  have hcD (σ : Bool) : Continuous (D σ) :=
    (d.continuous.comp_continuous (continuous_const.prodMk hac)
      (fun t ↦ (hden _ (mixedNeumannA_mem true t) σ).1)).norm.pow _
  have hcN (σ : Bool) : Continuous (N σ) :=
    (d.continuous.comp_continuous (hac.prodMk continuous_const)
      (fun t ↦ (hden _ (mixedNeumannA_mem true t) σ).2)).norm.pow _
  have hneg (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℝ) :
      (∫ t in Ioo (-T) T, g (-t)) = ∫ t in Ioo (-T) T, g t := by
    have h : -T ≤ T := by linarith
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_comp_neg, neg_neg, intervalIntegral.integral_of_le h,
      integral_Ioc_eq_integral_Ioo]
  have hArc₁ (t : ℝ) : diagCoord (cellArc 1 t) = (cellEdgeNormal false, a t) := by
    simp only [cellArc, Function.iterate_one, rotLift, diagCoord, separatrixArc, a, mixedNeumannA,
      ite_true, cellEdgeNormal, Bool.false_eq_true, ite_false, Prod.mk.injEq]
    constructor <;> ring
  have hArc₃ (t : ℝ) : diagCoord (cellArc 3 t) = (cellEdgeNormal true, a (-t)) := by
    dsimp only [a]
    rw [mixedNeumannA_true_neg]
    simp only [cellArc, Function.iterate_succ_apply', Function.iterate_zero_apply, rotLift, neg_neg,
      diagCoord, separatrixArc, mixedNeumannA, ite_true, cellEdgeNormal, Prod.mk.injEq]
    constructor <;> ring
  have hArc₂ (t : ℝ) : diagCoord (cellArc 2 t) = (a (-t), cellEdgeNormal false) := by
    change diagCoord (mixedNeumannArc false t) = _
    rw [mixedNeumann_coord]
    exact congrArg (fun s ↦ (s, cellEdgeNormal false)) (mixedNeumannA_true_neg t).symm
  rw [← hI]
  apply (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [id_eq, intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Ioc_eq_integral_Ioo]
  have hD (σ : Bool) : IntegrableOn (D σ) (Ioo (-T) T) :=
    ((hcD σ).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hN (σ : Bool) : IntegrableOn (N σ) (Ioo (-T) T) :=
    ((hcN σ).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hsplit : (∫ t in Ioo (-T) T, F t) =
      (∫ t in Ioo (-T) T, D true t) + (∫ t in Ioo (-T) T, D false t) -
        ((∫ t in Ioo (-T) T, N true t) + (∫ t in Ioo (-T) T, N false t)) := by
    change (∫ t in Ioo (-T) T, (D true + D false) t - (N true + N false) t) = _
    rw [integral_sub ((hD true).add (hD false)) ((hN true).add (hN false))]
    simp only [Pi.add_apply, integral_add (hD true) (hD false), integral_add (hN true) (hN false)]
  rw [hsplit]
  simp only [mixedTraceMassCutoff, hArc₁, hArc₂, hArc₃,
    show ∀ t, diagCoord (cellArc 0 t) = (a t, cellEdgeNormal true) from mixedNeumann_coord true]
  change _ = (∫ t in Ioo (-T) T, D false t) + (∫ t in Ioo (-T) T, D true (-t)) -
    ((∫ t in Ioo (-T) T, N true t) + (∫ t in Ioo (-T) T, N false (-t)))
  rw [hneg T hT (D true), hneg T hT (N false), add_comm (∫ t in Ioo (-T) T, D true t)]

/-- The paired time cutoff equals the absolutely convergent volume trace mass. -/
theorem mixed_trace_mass {ω : L2} (d : MixedQuotientData ω) :
    (∀ q ∈ mixedOpenCell, divergence mixedFieldA (fun r ↦ -mixedFieldB r) q = 0) ∧
    (∀ x ∈ Ioo (-Real.pi / 2) (Real.pi / 2), ∀ σ : Bool,
      let sign : ℝ := if σ then 1 else -1
      sign * mixedFieldA (cellEdgeNormal σ, x) = 1 / Real.cos x ∧
      -sign * mixedFieldB (x, cellEdgeNormal σ) = -1 / Real.cos x) ∧
    IntegrableOn (mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1])) mixedOpenCell ∧
    Tendsto (mixedTraceMassCutoff d.phi) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q)) := by
  refine ⟨fun _ hq ↦ (mixed_trace_mass_field hq).1, fun _ hx ↦ mixed_trace_mass_edge_flux hx, ?_⟩
  refine ⟨(mixed_rellich_volume_integrable d).2.2, ?_⟩
  rw [mixed_trace_mass_volume_eq d, ← neg_div]
  exact mixed_trace_mass_cutoff_limit d

private theorem mixedNeumannA_ae (σ : Bool) {P : ℝ → Prop}
    (h : ∀ᵐ a ∂volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2)), P a) :
    ∀ᵐ t, P (mixedNeumannA σ t) := by
  have h' : ∀ᵐ a, a ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) → P a := by
    rw [← neg_div, ← ae_restrict_iff' measurableSet_Ioo]
    exact h
  cases σ
  · have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h'
    have hP : ∀ᵐ a ∂volume.restrict (Ioo (-(Real.pi / 2)) (Real.pi / 2)), P (-a) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hn] with a ha hm
      exact ha ⟨by linarith [hm.2], by linarith [hm.1]⟩
    simpa only [mixedNeumannA, Bool.false_eq_true, ↓reduceIte] using ae_comp_arcAngle hP
  · simpa only [mixedNeumannA, Bool.true_eq, ↓reduceIte] using
      ae_comp_arcAngle ((ae_restrict_iff' measurableSet_Ioo).2 h')

/-- The critical edge weight `1 / cos a` is exactly flow-time measure on either
mixed Neumann edge. -/
theorem mixed_neumann_trace_memLp_flow {T : ℝ → ℂ} (σ : Bool)
    (hT : MemLp (fun a ↦ T a / (Real.sqrt (Real.cos a) : ℂ)) 2
      (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2)))) :
    MemLp (fun t ↦ T ((diagCoord (mixedNeumannArc σ t)).1)) 2 volume := by
  have hi := mixedNeumannA_integrable σ
    (hT.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have he : (fun t ↦ (Real.cosh t)⁻¹ *
      ‖T (mixedNeumannA σ t) / (Real.sqrt (Real.cos (mixedNeumannA σ t)) : ℂ)‖ ^ 2) =
      (fun t ↦ ‖T (mixedNeumannA σ t)‖ ^ 2) := by
    funext t
    have hcos := mixedNeumannArc_cos σ t
    rw [mixedNeumann_coord] at hcos
    change Real.cos (mixedNeumannA σ t) = _ at hcos
    have hpos := inv_pos.mpr (Real.cosh_pos t)
    rw [hcos, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hpos.le]
    field_simp [hpos.ne']
  rw [he] at hi
  have hT0 : AEStronglyMeasurable T (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2))) := by
    apply (hT.aestronglyMeasurable.mul (by fun_prop : Continuous fun a : ℝ ↦
      (Real.sqrt (Real.cos a) : ℂ)).aestronglyMeasurable).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    have hc := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using ha)
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne')
  have hM : QuasiMeasurePreserving (mixedNeumannA σ) volume
      (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2))) := by
    have hc : Continuous (mixedNeumannA σ) := continuous_iff_continuousAt.2
      fun t ↦ (mixedNeumannA_deriv σ t).continuousAt
    refine ⟨hc.measurable.aemeasurable, Measure.AbsolutelyContinuous.mk ?_⟩
    intro s hs hm
    rw [Measure.map_apply hc.measurable hs]
    have hm' : ∀ᵐ a ∂volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2)),
        a ∉ s := by rwa [ae_iff, show {a | ¬a ∉ s} = s by ext a; simp]
    have he := mixedNeumannA_ae σ hm'
    rwa [ae_iff, show {t | ¬mixedNeumannA σ t ∉ s} = mixedNeumannA σ ⁻¹' s by
      ext t; simp] at he
  have hmem := (memLp_two_iff_integrable_sq_norm (hT0.comp_quasiMeasurePreserving hM)).2 hi
  simpa only [mixedNeumann_coord, Function.comp_def] using hmem

/-- A canonical trace on a full inward strip is square integrable in the
Neumann flow time when its bulk representative divided by `cos a` is in `L²`. -/
theorem mixed_neumann_strip_memLp_flow {w : ℝ} {F D : Plane → ℂ} {T : ℝ → ℂ}
    {chart : Plane → Plane} (σ : Bool)
    (hT : HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) 0 w 0 chart F T)
    (hD : HasWeakPartialOn (Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo 0 w) 1 (F ∘ chart) D)
    (hDL : MemLp D 2 (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo 0 w)))
    (hFL : MemLp (fun q ↦ F (chart q) / (Real.cos q.1 : ℂ)) 2
      (volume.restrict (Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo 0 w))) :
    MemLp (fun t ↦ T ((diagCoord (mixedNeumannArc σ t)).1)) 2 volume := by
  apply mixed_neumann_trace_memLp_flow σ
  exact hT.left_memLp_div_sqrt hD hDL hFL hT.2.1 Real.continuous_cos.measurable
    (fun _ ha ↦ Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using ha))
    (fun a _ ↦ mul_le_of_le_one_right hT.2.1.le (Real.cos_le_one a))

/-- Shrinking the absolute-level open collar gives an H¹ cell collar. -/
theorem mixed_cell_collar_h1 {ω : L2} {ε : ℝ} (hε : 0 < ε)
    (hω : MemSobolevLocOn 1 (mixedSeparatrixCollar ε) (liftL2 ω)) :
    MemSobolevOn 1 (cellSeparatrixStrip (ε / 2)) (liftL2 ω) := by
  let P := cellSeparatrixStrip (ε / 2)
  have hc : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hPc : closure P ⊆ {p | |dipoleLift p| ≤ ε / 2} :=
    closure_minimal (fun p hp ↦ by
      change |dipoleLift p| ≤ ε / 2
      rw [abs_of_pos hp.2.1]
      exact hp.2.2.le) (isClosed_le hc.abs continuous_const)
  have hPB : Bornology.IsBounded P :=
    isBounded_cellNeighbourhood.subset (fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1))
  exact hω P (isOpen_cellSeparatrixStrip _) (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closure, hPB.closure⟩) (fun p hp ↦
      (show |dipoleLift p| ≤ ε / 2 from hPc hp).trans_lt (half_lt_self hε))

private theorem mixed_trace_restrict_tangent {l r a b w : ℝ} {V : Plane → ℂ} {S : ℝ → ℂ}
    (hS : HasTransverseH1Trace l r 0 w 0 id V S)
    (hab : a < b) (hsub : Ioo a b ⊆ Ioo l r) :
    HasTransverseH1Trace a b 0 w 0 id V S := by
  obtain ⟨_, hw, h0, G, D, hGm, hG, hGL, hDL, hACL, hT⟩ := hS
  have hP := prod_mono hsub (Subset.rfl : Ioo 0 w ⊆ Ioo 0 w)
  have hμ := Measure.restrict_mono_set volume hP
  have hν := Measure.restrict_mono_set volume hsub
  exact ⟨hab, hw, h0, G, D, hGm, ae_mono hμ hG, hGL.mono_measure hμ,
    hDL.mono_measure hμ, ae_mono hν hACL, ae_mono hν hT⟩

/-- The full inward trace agrees with the trace on every regular physical
window contained in the Sobolev collar, even if that window is wider. -/
theorem mixed_neumann_inward_hasCellEdgeTrace {ω : L2} {ε w : ℝ} {S : ℝ → ℂ}
    (σ : Bool) (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω))
    (hS : HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) 0 w 0 id
      (liftL2 ω ∘ inwardEdgeChart 1 σ) S) :
    HasCellEdgeTrace (cellSeparatrixStrip ε) 1 σ (liftL2 ω) S := by
  intro l r a b hlr hab hreg hedge hrect
  let C := diagonalTraceChart 1
  let V := liftL2 ω ∘ C
  let t := cellEdgeNormal σ
  have hV := (hv.comp_diagonalTraceChart (isOpen_cellSeparatrixStrip ε) 1).mono
    (image_subset_iff.mp hrect)
  obtain ⟨D, hd, hD⟩ := hV.2 1
  have ht : t ∈ Icc a b := by
    cases σ
    · change a = cellEdgeNormal false at hedge
      exact ⟨hedge.le, hedge.symm.le.trans hab.le⟩
    · change b = cellEdgeNormal true at hedge
      exact ⟨hab.le.trans hedge.le, hedge.symm.le⟩
  obtain ⟨T, hT⟩ := hd.exists_transverse_trace hlr hab ht hV.1 hD
  let δ := min w (b - a)
  have hδ : 0 < δ := lt_min hS.2.1 (sub_pos.mpr hab)
  have hδw : δ ≤ w := min_le_left _ _
  have hδab : δ ≤ b - a := min_le_right _ _
  let φ := fun u ↦ edgeSideSign σ * (Real.pi / 2 - u)
  have hφ : MapsTo φ (Ioo 0 δ) (Ioo a b) := by
    intro u hu
    cases σ
    · change a = -Real.pi / 2 at hedge
      change -1 * (Real.pi / 2 - u) ∈ Ioo a b
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · change b = Real.pi / 2 at hedge
      change 1 * (Real.pi / 2 - u) ∈ Ioo a b
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hm : MeasurePreserving φ volume volume := by
    cases σ
    · convert measurePreserving_add_right volume (-(Real.pi / 2)) using 1
      funext u
      simp [φ, edgeSideSign]
      ring
    · simpa [φ, edgeSideSign] using Measure.measurePreserving_sub_left volume (Real.pi / 2)
  have hφc : Continuous φ := by fun_prop
  have hφ0 : φ 0 = t := by
    cases σ <;> simp [φ, t, edgeSideSign, cellEdgeNormal, neg_div]
  have hS' := mixed_trace_restrict_tangent hS hlr (Ioo_subset_Icc_self.trans hreg)
  have he := hS'.ae_eq_inward hT hδ hδw (k := id) (fun _ hs ↦ hs)
    hφ (MeasurePreserving.id volume) hm hφc hφ0 (fun s _ u _ ↦ by
      change liftL2 ω (C (edgeInward σ (s, u))) = liftL2 ω (C (s, φ u))
      rw [edgeInward_apply])
  exact hT.congr_trace he

/-- The mixed bulk weight and a Sobolev cell collar give the canonical
physical vorticity trace in `L²(dt)` on a full inward rectangle. -/
theorem mixed_neumann_inward_trace_memLp {ω : L2} (d : MixedQuotientData ω)
    {ε : ℝ} (hε : 0 < ε) (hω : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω))
    (σ : Bool) :
    ∃ w : ℝ, 0 < w ∧
      Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo 0 w ⊆
        inwardEdgeChart 1 σ ⁻¹' cellSeparatrixStrip ε ∧
      ∃ S : ℝ → ℂ,
        HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) 0 w 0 id
          (liftL2 ω ∘ inwardEdgeChart 1 σ) S ∧
        MemLp (fun t ↦ S ((diagCoord (mixedNeumannArc σ t)).1)) 2 volume ∧
        HasCellEdgeTrace (cellSeparatrixStrip ε) 1 σ (liftL2 ω) S := by
  let w := min (ε / 4) (Real.pi / 2)
  let Q := Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (0 : ℝ) w
  let C := inwardEdgeChart 1 σ
  have hw : 0 < w := lt_min (by positivity) (by positivity)
  have hwε : 2 * w ≤ ε := by dsimp [w]; linarith [min_le_left (ε / 4) (Real.pi / 2)]
  have hwπ : w < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hW : Q ⊆ C ⁻¹' cellSeparatrixStrip ε := by
    intro q hq
    exact inwardEdgeChart_mem_collar ⟨hq.2.1, hq.2.2.trans hwπ⟩
      ((mul_lt_mul_of_pos_left hq.2.2 (by norm_num)).trans_le hwε) hq.1 1 σ
  have hV := (hω.comp_inwardEdgeChart (isOpen_cellSeparatrixStrip ε) 1 σ).mono hW
  obtain ⟨D, hD, hDL⟩ := hV.2 1
  obtain ⟨S, hS⟩ := hD.exists_left_trace (by linarith [Real.pi_pos]) hw hV.1 hDL
  refine ⟨w, hw, hW, S, hS, mixed_neumann_strip_memLp_flow σ hS hD hDL ?_,
    mixed_neumann_inward_hasCellEdgeTrace σ hω hS⟩
  have hsub : Q ⊆ edgeInward σ ⁻¹' mixedOpenCell := by
    intro q hq
    have hp := (hW hq).1
    change diagInv (edgeInward σ q) ∈ cellSquare at hp
    simpa only [cellSquare, mem_ofPred_eq, diagCoord_diagInv, abs_lt, neg_div,
      mem_preimage, mixedOpenCell, mem_prod, mem_Ioo] using hp
  have hL := (memLp_comp_planeAffine _ _ (measurePreserving_edgeInward σ)
    (measurableSet_Ioo.prod measurableSet_Ioo) d.vorticity_divided).mono_measure
      (Measure.restrict_mono_set volume hsub)
  refine hL.ae_eq (Eventually.of_forall fun q ↦ ?_)
  change liftL2 ω (diagInv (edgeInward σ q)) / (Real.cos (edgeInward σ q).1 : ℂ) =
    liftL2 ω (diagInv (edgeInward σ q)) / (Real.cos q.1 : ℂ)
  rw [edgeInward_apply]

private theorem mixed_glue_interval_h1 {a b : ℝ} {F D : ℝ → ℂ}
    (h : ∀ c e, c < e → Icc c e ⊆ Ioo a b →
      ∃ T, T =ᵐ[volume.restrict (Ioo c e)] F ∧ HasIntervalH1 c e T D) :
    ∃ T, (T =ᵐ[volume.restrict (Ioo a b)] F) ∧
      (∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt T (D x) x) ∧
      ∀ c e, c < e → Icc c e ⊆ Ioo a b → HasIntervalH1 c e T D := by
  classical
  let I := Ioo a b
  have hloc (x : ℝ) (hx : x ∈ I) :
      ∃ c e, x ∈ Ioo c e ∧
        ∃ R, R =ᵐ[volume.restrict (Ioo c e)] F ∧ HasIntervalH1 c e R D := by
    obtain ⟨c, hc, hcx⟩ := exists_between hx.1
    obtain ⟨e, hxe, he⟩ := exists_between hx.2
    exact ⟨c, e, ⟨hcx, hxe⟩, h c e (hcx.trans hxe) (Icc_subset_Ioo hc he)⟩
  choose c e hmem R hR hRd using hloc
  let T (x : ℝ) := if hx : x ∈ I then R x hx x else 0
  have hagree {l r : ℝ} {S : ℝ → ℂ} (hW : Ioo l r ⊆ I)
      (hS : S =ᵐ[volume.restrict (Ioo l r)] F) (hSd : HasIntervalH1 l r S D) :
      EqOn T S (Ioo l r) := by
    intro x hx
    have hxI := hW hx
    let J := Ioo (c x hxI) (e x hxI) ∩ Ioo l r
    have he₁ : R x hxI =ᵐ[volume.restrict J] F :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hR x hxI)
    have he₂ : S =ᵐ[volume.restrict J] F :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hS
    have hcont {l r : ℝ} {G : ℝ → ℂ} (hlr : l < r) (hG : HasIntervalH1 l r G D) :
        ContinuousOn G (Ioo l r) :=
      ((hG.continuousOn_extension hlr).mono Ioo_subset_Icc_self).congr (hG.extension_eq hlr).symm
    have he := Measure.eqOn_open_of_ae_eq (he₁.trans he₂.symm) (isOpen_Ioo.inter isOpen_Ioo)
      ((hcont ((hmem x hxI).1.trans (hmem x hxI).2) (hRd x hxI)).mono inter_subset_left)
      ((hcont (hx.1.trans hx.2) hSd).mono inter_subset_right) ⟨hmem x hxI, hx⟩
    simpa only [T, dite_eq_left hxI] using he
  have hT (l r : ℝ) (hlr : l < r) (hW : Icc l r ⊆ I) :
      (T =ᵐ[volume.restrict (Ioo l r)] F) ∧ HasIntervalH1 l r T D := by
    obtain ⟨S, hS, hSd⟩ := h l r hlr hW
    have he := hagree (Ioo_subset_Icc_self.trans hW) hS hSd
    have he' : T =ᵐ[volume.restrict (Ioo l r)] S :=
      ae_restrict_of_forall_mem measurableSet_Ioo he
    exact ⟨he'.trans hS, hSd.congr_Ioo he.symm⟩
  have hae (l r : ℚ) : ∀ᵐ x, x ∈ Ioo (l : ℝ) (r : ℝ) →
      Icc (l : ℝ) (r : ℝ) ⊆ I → T x = F x ∧ HasDerivAt T (D x) x := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    by_cases hW : Icc (l : ℝ) (r : ℝ) ⊆ I
    · by_cases hlr : (l : ℝ) < (r : ℝ)
      · obtain ⟨he, hD⟩ := hT l r hlr hW
        filter_upwards [he, ae_restrict_of_ae hD.hasDerivAt_ae,
          ae_restrict_mem measurableSet_Ioo] with x hx hd hxW
        exact fun _ ↦ ⟨hx, hd hxW⟩
      · simp [Ioo_eq_empty hlr]
    · exact Eventually.of_forall fun _ hx ↦ (hW hx).elim
  have hall : ∀ᵐ x ∂volume.restrict I, T x = F x ∧ HasDerivAt T (D x) x := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.2 fun l ↦ ae_all_iff.2 (hae l)),
      ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with x hx hxI
    obtain ⟨l, hl, hlx⟩ := exists_rat_btwn hxI.1
    obtain ⟨r, hxr, hr⟩ := exists_rat_btwn hxI.2
    exact hx l r ⟨hlx, hxr⟩ (Icc_subset_Ioo hl hr)
  exact ⟨T, hall.mono fun _ hx ↦ hx.1, hall.mono fun _ hx ↦ hx.2,
    fun l r hlr hW ↦ (hT l r hlr hW).2⟩

private theorem mixed_hasDerivAt_weightedFlow {U : ℝ → ℂ} {t : ℝ}
    (h : DifferentiableAt ℝ U (Real.tanh t)) :
    HasDerivAt (fun s ↦ ((Real.cosh s)⁻¹ : ℝ) * U (Real.tanh s))
      (((Real.cosh t)⁻¹ : ℝ) *
        ((boundaryWeight (Real.tanh t) : ℂ) * deriv U (Real.tanh t) -
          (Real.tanh t : ℂ) * U (Real.tanh t))) t := by
  convert ((mixed_sech_deriv t).ofReal_comp).mul
    (hasDerivAt_flowValue h.hasDerivAt) using 1 <;>
    simp [flowValue, flowFirst, Pi.mul_def]
  ring

private theorem mixedNeumann_weighted_stream (φ : Plane → ℂ) (σ : Bool) :
    mixedNeumannStream φ σ = fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * mixedNeumannG φ σ (Real.tanh t) := by
  funext t
  simp only [mixedNeumannStream, mixedNeumannG, Real.artanh_tanh, mixedNeumannArc_cos]

private theorem mixedNeumann_weighted_unknown (lam : ℝ) (φ : Plane → ℂ) (σ : Bool) :
    canonicalUnknown lam (mixedNeumannStream φ σ) =
      fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * mixedNeumannF lam φ σ (Real.tanh t) := by
  funext t
  simp only [mixedNeumannF, Real.artanh_tanh, boundaryWeight_tanh, one_div, Real.sqrt_inv,
    Real.sqrt_sq (Real.cosh_pos t).le, Complex.ofReal_inv]
  have hcosh : (↑(Real.cosh t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  rw [mul_comm, div_mul_cancel₀ _ (inv_ne_zero hcosh)]

private theorem mixedNeumannF_eq {lam : ℝ} (φ : Plane → ℂ) (σ : Bool) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    mixedNeumannF lam φ σ x = (Real.cosh (Real.artanh x) : ℂ) *
      canonicalUnknown lam (mixedNeumannStream φ σ) (Real.artanh x) := by
  have h := congrFun (mixedNeumann_weighted_unknown lam φ σ) (Real.artanh x)
  rw [Real.tanh_artanh hx, Complex.ofReal_inv] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'), one_mul]

private theorem mixed_cosh_exp_abs (t : ℝ) :
    Real.exp |t| / 2 ≤ Real.cosh t ∧ Real.cosh t ≤ Real.exp |t| := by
  rw [← Real.cosh_abs t, Real.cosh_eq]
  constructor
  · linarith [Real.exp_pos (-|t|)]
  · linarith [Real.exp_le_exp.mpr (show -|t| ≤ |t| by linarith [abs_nonneg t])]

private theorem mixed_integrating_factor_limit {q : ℝ → ℂ} (hq : MemLp q 2 volume)
    {b : ℂ} {f : ℝ → ℂ} (hn : ∀ t, ‖f t‖ = ‖q t‖)
    (h : Tendsto f atTop (𝓝 b) ∨ Tendsto f atBot (𝓝 b)) : b = 0 := by
  by_contra hb
  have hpos : 0 < ‖b‖ / 2 := half_pos (norm_pos_iff.mpr hb)
  have hm : volume {t | ‖b‖ / 2 ≤ ‖q t‖} < ⊤ := by
    simpa only [Real.coe_toNNReal _ hpos.le, coe_nnNorm, ← NNReal.coe_le_coe] using
      hq.meas_ge_lt_top (by norm_num) (by norm_num)
        (ne_of_gt (show 0 < Real.toNNReal (‖b‖ / 2) from Real.toNNReal_pos.2 hpos))
  have hnorm {l : Filter ℝ} (hl : Tendsto f l (𝓝 b)) :
      ∀ᶠ t in l, ‖b‖ / 2 ≤ ‖q t‖ := by
    filter_upwards [hl.norm.eventually_const_lt (show ‖b‖ / 2 < ‖b‖ by linarith)] with t ht
    exact (hn t ▸ ht).le
  rcases h with ht | ht
  · obtain ⟨a, ha⟩ := eventually_atTop.1 (hnorm ht)
    have hmono := measure_mono (μ := volume) (show Ioi a ⊆ {t | ‖b‖ / 2 ≤ ‖q t‖} from
      fun t ht ↦ ha t ht.le)
    rw [Real.volume_Ioi] at hmono
    exact (not_lt_of_ge hmono) hm
  · obtain ⟨a, ha⟩ := eventually_atBot.1 (hnorm ht)
    have hmono := measure_mono (μ := volume) (show Iio a ⊆ {t | ‖b‖ / 2 ≤ ‖q t‖} from
      fun t ht ↦ ha t ht.le)
    rw [Real.volume_Iio] at hmono
    exact (not_lt_of_ge hmono) hm

/-- An `L²(dt)` trace satisfying the profile ODE decays at both ends. The
integrating factor has limits because the forcing is in `L¹(dt)`, and any
nonzero limit would give a positive lower bound on a half-line. -/
theorem mixed_vorticity_profile_decay {lam : ℝ} {g q : ℝ → ℂ}
    (hg : Integrable (deriv g)) (hqAC : ∀ c e, AbsolutelyContinuousOnInterval q c e)
    (hqODE : ∀ᵐ t, HasDerivAt q (Complex.I * lam * q t - deriv g t) t)
    (hq : MemLp q 2 volume) :
    Tendsto q atTop (𝓝 0) ∧ Tendsto q atBot (𝓝 0) := by
  let E : ℝ → ℂ := fun t ↦ Complex.exp (-(Complex.I * lam * t))
  let Q : ℝ → ℂ := fun t ↦ E t * q t
  have hNorm (t : ℝ) : ‖Q t‖ = ‖q t‖ := by
    simp only [Q, E, norm_mul, norm_exp_neg_I_mul, one_mul]
  have hE : ContDiff ℝ 1 E :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp
  have hQAC (c e : ℝ) : AbsolutelyContinuousOnInterval Q c e :=
    hE.contDiffOn.absolutelyContinuousOnInterval.smul (hqAC c e)
  have hQD : ∀ᵐ t, HasDerivAt Q (-profileIntegrand lam g t) t := by
    filter_upwards [hqODE] with t ht
    have hEd : HasDerivAt E (E t * -(Complex.I * lam)) t := by
      simpa [E] using
        (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * lam)).neg.cexp).comp_ofReal
    convert hEd.mul ht using 1
    simp only [profileIntegrand, E]
    ring
  have hI := integrable_profileIntegrand (lam := lam) hg
  have hQ (t : ℝ) : Q t = Q 0 - ∫ s in (0 : ℝ)..t, profileIntegrand lam g s := by
    have h := complex_integral_eq_sub_of_ac (hQAC 0 t) hI.neg.intervalIntegrable
      (hQD.mono fun _ ht _ ↦ ht)
    simp only [Pi.neg_apply, intervalIntegral.integral_neg] at h
    linear_combination -h
  have hTop : Tendsto Q atTop (𝓝 (Q 0 - ∫ t in Ioi 0, profileIntegrand lam g t)) :=
    ((intervalIntegral_tendsto_integral_Ioi 0 hI.integrableOn tendsto_id).const_sub (Q 0)).congr
      (fun t ↦ (hQ t).symm)
  have hBot : Tendsto Q atBot (𝓝 (Q 0 + ∫ t in Iic 0, profileIntegrand lam g t)) := by
    refine ((intervalIntegral_tendsto_integral_Iic 0 hI.integrableOn tendsto_id).const_add
      (Q 0)).congr fun t ↦ ?_
    simp only [id_eq, hQ t, intervalIntegral.integral_symm t 0, sub_eq_add_neg, neg_neg]
  have hT := mixed_integrating_factor_limit hq hNorm (Or.inl hTop)
  have hB := mixed_integrating_factor_limit hq hNorm (Or.inr hBot)
  rw [hT] at hTop
  rw [hB] at hBot
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hNorm, norm_zero] using hTop.norm
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hNorm, norm_zero] using hBot.norm

/-- The Melnikov condition and the bounded stream quotient give a bounded
transformed canonical unknown and its first-order transport equation. -/
theorem mixed_neumann_canonical_transport {lam : ℝ} (hlam : lam ≠ 0) {φ : Plane → ℂ}
    (σ : Bool) (hgac : ∀ c e, AbsolutelyContinuousOnInterval (mixedNeumannStream φ σ) c e)
    (hg : Integrable (deriv (mixedNeumannStream φ σ)))
    (hbG : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖mixedNeumannG φ σ x‖ ≤ C)
    (hM : ∫ t, profileIntegrand lam (mixedNeumannStream φ σ) t = 0) :
    let F := mixedNeumannF lam φ σ
    let G := mixedNeumannG φ σ
    MixedBoundaryLocAC F ∧
    (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖F x‖ ≤ C) ∧
    G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F := by
  let g := mixedNeumannStream φ σ
  let G := mixedNeumannG φ σ
  let F := mixedNeumannF lam φ σ
  let z := canonicalUnknown lam g
  have hzAC (c e : ℝ) : AbsolutelyContinuousOnInterval z c e := by
    refine (((absolutelyContinuousOnInterval_canonicalProfile (lam := lam) hg c e).add
      (hgac c e)).neg.const_smul (lam : ℂ)⁻¹).congr fun t _ ↦ ?_
    simp only [z, g, canonicalUnknown, Pi.neg_apply, Pi.add_apply, smul_eq_mul,
      div_eq_mul_inv]
    exact mul_comm _ _
  have hzCos (c e : ℝ) :
      AbsolutelyContinuousOnInterval (fun t ↦ (Real.cosh t : ℂ) * z t) c e := by
    have hcos : ContDiff ℝ 1 (fun t ↦ (Real.cosh t : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp Real.contDiff_cosh
    exact hcos.contDiffOn.absolutelyContinuousOnInterval.smul (hzAC c e)
  have hF : MixedBoundaryLocAC F := by
    intro c e hc hce he
    refine (absolutelyContinuousOnInterval_comp_artanh hzCos hc hce.le he).congr ?_
    intro x hx
    rw [uIcc_of_le hce.le] at hx
    exact (mixedNeumannF_eq φ σ ⟨hc.trans_le hx.1, hx.2.trans_lt he⟩).symm
  obtain ⟨C, hC⟩ := hbG
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  have hgb (t : ℝ) : ‖g t‖ ≤ 2 * C * Real.exp (-|t|) := by
    change ‖mixedNeumannStream φ σ t‖ ≤ _
    rw [congrFun (mixedNeumann_weighted_stream φ σ) t, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.cosh_pos t))]
    calc
      _ ≤ (Real.cosh t)⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hC _ (mixed_tanh_mem t)) (by positivity)
      _ ≤ (Real.exp |t| / 2)⁻¹ * C :=
        mul_le_mul_of_nonneg_right ((inv_le_inv₀ (Real.cosh_pos t)
          (half_pos (Real.exp_pos _))).2 (mixed_cosh_exp_abs t).1) hC0
      _ = _ := by rw [Real.exp_neg]; ring
  obtain ⟨D, hD⟩ := norm_canonicalProfile_le_exp hgac hg hM (α := 1) (C := 2 * C)
    (cp := 0) (cm := 0) one_pos
    (fun t ht ↦ by simpa [abs_of_nonneg ht] using hgb t)
    (fun t ht ↦ by simpa [abs_of_nonpos ht] using hgb t)
  have hbF : ∃ A : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖F x‖ ≤ A := by
    refine ⟨(D + 2 * C) / |lam|, fun x hx ↦ ?_⟩
    let t := Real.artanh x
    change ‖mixedNeumannF lam φ σ x‖ ≤ _
    rw [mixedNeumannF_eq φ σ hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
    change Real.cosh t * ‖z t‖ ≤ _
    have hzb : ‖z t‖ ≤ (D + 2 * C) / |lam| * Real.exp (-|t|) := by
      change ‖canonicalUnknown lam g t‖ ≤ _
      rw [canonicalUnknown, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (‖canonicalProfile lam g t‖ + ‖g t‖) / |lam| :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (abs_nonneg _)
        _ ≤ (D * Real.exp (-|t|) + 2 * C * Real.exp (-|t|)) / |lam| :=
          div_le_div_of_nonneg_right (add_le_add (by simpa using hD t) (hgb t)) (abs_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ Real.exp |t| * ‖z t‖ :=
        mul_le_mul_of_nonneg_right (mixed_cosh_exp_abs t).2 (norm_nonneg _)
      _ ≤ Real.exp |t| * ((D + 2 * C) / |lam| * Real.exp (-|t|)) :=
        mul_le_mul_of_nonneg_left hzb (Real.exp_nonneg _)
      _ = _ := by
        rw [Real.exp_neg, mul_left_comm, mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
  have hgd : ∀ᵐ t, DifferentiableAt ℝ g t := by
    have h (n : ℕ) : ∀ᵐ t, t ∈ uIcc (-(n : ℝ)) n → DifferentiableAt ℝ g t :=
      (hgac _ _).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    filter_upwards [ae_all_iff.2 h] with t ht
    obtain ⟨n, hn⟩ := exists_nat_ge |t|
    exact ht n (Icc_subset_uIcc ⟨(neg_le_neg hn).trans (neg_abs_le _), (le_abs_self _).trans hn⟩)
  have hflow : ∀ᵐ t, G (Real.tanh t) = mixedBoundaryTransport lam F (Real.tanh t) := by
    filter_upwards [ae_comp_tanh hF.ae_differentiableAt,
      ae_hasDerivAt_canonicalUnknown_sub hlam hg hgd] with t ht hz
    have h := hz.unique
      ((mixedNeumann_weighted_unknown lam φ σ).symm ▸
        mixed_hasDerivAt_weightedFlow (ht (mixed_tanh_mem t)))
    rw [congrFun (mixedNeumann_weighted_unknown lam φ σ) t,
      congrFun (mixedNeumann_weighted_stream φ σ) t] at h
    have hc : ((↑(Real.cosh t)⁻¹ : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.cosh_pos t).ne')
    have he := mul_left_cancel₀ hc (show
        (↑(Real.cosh t)⁻¹ : ℂ) * (Complex.I * ((lam : ℂ) * F (Real.tanh t) + G (Real.tanh t))) =
        (↑(Real.cosh t)⁻¹ : ℂ) * ((boundaryWeight (Real.tanh t) : ℂ) * deriv F (Real.tanh t) -
          (Real.tanh t : ℂ) * F (Real.tanh t)) from by rw [← h]; ring)
    unfold mixedBoundaryTransport
    linear_combination -Complex.I * he + (Complex.I_sq) *
      ((lam : ℂ) * F (Real.tanh t) + G (Real.tanh t))
  refine ⟨hF, hbF, (ae_restrict_iff' measurableSet_Ioo).2 ?_⟩
  filter_upwards [ae_comp_artanh hflow] with x hx hmem
  simpa only [Real.tanh_artanh hmem] using hx hmem

/-- The Neumann stream trace and its weighted tangential energy. -/
theorem mixed_neumann_stream_trace {ω : L2} (d : MixedQuotientData ω) (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    let G := mixedNeumannG d.phi σ
    (∀ c e, AbsolutelyContinuousOnInterval g c e) ∧ Integrable (deriv g) ∧
    MixedBoundaryLocAC G ∧ (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖G x‖ ≤ C) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) (Ioo (-1) 1) := by
  let I := Ioo (-Real.pi / 2) (Real.pi / 2)
  let a := mixedNeumannA σ
  let T := fun x ↦ d.phi (x, cellEdgeNormal σ)
  let U := T ∘ a
  let g := mixedNeumannStream d.phi σ
  let G := mixedNeumannG d.phi σ
  let h := fun t ↦ (Real.cosh t)⁻¹
  obtain ⟨hTac, hT2⟩ : AbsolutelyContinuousOnInterval T (-Real.pi / 2) (Real.pi / 2) ∧
      MemLp (deriv T) 2 (volume.restrict I) := mixed_quotient_edge_h1 d σ
  have haMem := mixedNeumannA_mem σ
  have haL : LipschitzWith 1 a := by
    have he : LipschitzWith 1 (fun t ↦ arcAngle t - Real.pi / 2) :=
      LipschitzWith.of_dist_le_mul fun s t ↦ by
        simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using
          lipschitzWith_arcAngle.dist_le_mul s t
    cases σ
    · exact he.neg
    · exact he
  have haMaps (c e : ℝ) : MapsTo a (uIcc c e) (uIcc (-Real.pi / 2) (Real.pi / 2)) :=
    fun t _ ↦ Icc_subset_uIcc (Ioo_subset_Icc_self (haMem t))
  have hUac (c e : ℝ) : AbsolutelyContinuousOnInterval U c e := by
    cases σ
    · refine AbsolutelyContinuousOnInterval.comp_monotoneOn hTac haL.lipschitzOnWith ?_ (haMaps c e)
      exact (show Monotone a from fun s t hst ↦ by
        change -(arcAngle s - Real.pi / 2) ≤ -(arcAngle t - Real.pi / 2)
        linarith [antitone_arcAngle hst]).monotoneOn _
    · refine AbsolutelyContinuousOnInterval.comp_antitoneOn hTac haL.lipschitzOnWith ?_ (haMaps c e)
      exact (show Antitone a from fun s t hst ↦ by
        simpa [a, mixedNeumannA] using antitone_arcAngle hst).antitoneOn _
  have hcomp (t : ℝ) : G (Real.tanh t) = U t := by
    simp only [G, mixedNeumannG, Real.artanh_tanh, mixedNeumann_coord, U, Function.comp_apply, T, a]
  have hg_eq : g = fun t ↦ (h t : ℂ) * U t := by
    rw [show g = _ from mixedNeumann_weighted_stream d.phi σ]
    funext t
    change (h t : ℂ) * G (Real.tanh t) = _
    rw [hcomp]
  have hGac : MixedBoundaryLocAC G := by
    intro c e hc hce he
    refine (absolutelyContinuousOnInterval_comp_artanh hUac hc hce.le he).congr fun x hx ↦ ?_
    rw [uIcc_of_le hce.le] at hx
    have hxm := Real.tanh_artanh ⟨hc.trans_le hx.1, hx.2.trans_lt he⟩
    simpa only [Function.comp_apply, hxm] using (hcomp (Real.artanh x)).symm
  obtain ⟨C, hC⟩ := hTac.exists_bound
  have hC' (x : ℝ) (hx : x ∈ I) : ‖T x‖ ≤ C :=
    hC x (Icc_subset_uIcc (Ioo_subset_Icc_self hx))
  have hgac (c e : ℝ) : AbsolutelyContinuousOnInterval g c e := by
    rw [hg_eq]
    have hCosh : ContDiff ℝ 1 (fun t ↦ (h t : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Real.contDiff_cosh.inv (fun t ↦ (Real.cosh_pos t).ne'))
    exact hCosh.contDiffOn.absolutelyContinuousOnInterval.smul (hUac c e)
  have hGbound : ∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, ‖G x‖ ≤ C := by
    refine ⟨C, fun x hx ↦ ?_⟩
    have he := hcomp (Real.artanh x)
    rw [Real.tanh_artanh hx] at he
    rw [he]
    exact hC' _ (haMem _)
  have hTae : ∀ᵐ x ∂volume.restrict I, DifferentiableAt ℝ T x := by
    filter_upwards [ae_restrict_of_ae hTac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with x hx hxI
    exact hx (Icc_subset_uIcc (Ioo_subset_Icc_self hxI))
  have hUdiff : ∀ᵐ t, HasDerivAt U (((if σ then -1 else 1 : ℝ) * h t) • deriv T (a t)) t := by
    filter_upwards [mixedNeumannA_ae σ hTae] with t ht
    exact ht.hasDerivAt.scomp t (mixedNeumannA_deriv σ t)
  have hhI : Integrable h := by
    simpa only [mul_one] using mixedNeumannA_integrable σ (f := fun _ ↦ 1) (integrable_const _)
  have hTl := hT2.integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hD1 := mixedNeumannA_integrable σ hTl.norm
  have hD2 := mixedNeumannA_integrable σ ((memLp_two_iff_integrable_sq_norm
    hT2.aestronglyMeasurable).mp hT2)
  have hpos (t : ℝ) : 0 < h t := inv_pos.mpr (Real.cosh_pos _)
  have hle (t : ℝ) : h t ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh _)
  have hgI : Integrable (deriv g) := by
    refine ((hhI.const_mul C).add hD1).mono' (measurable_deriv g).aestronglyMeasurable ?_
    filter_upwards [hUdiff] with t ht
    have hgD : deriv (fun t ↦ (h t : ℂ) * U t) t =
        ((-(h t) * Real.tanh t : ℝ) : ℂ) * U t +
          (h t : ℂ) * (((if σ then -1 else 1 : ℝ) * h t) • deriv T (a t)) :=
      ((mixed_sech_deriv t).ofReal_comp.mul ht).deriv
    rw [hg_eq, hgD]
    refine (norm_add_le _ _).trans ?_
    have htanh : |Real.tanh t| ≤ 1 := abs_le.mpr
      ⟨(Real.neg_one_lt_tanh t).le, (Real.tanh_lt_one t).le⟩
    have h₁ : ‖((-(h t) * Real.tanh t : ℝ) : ℂ) * U t‖ ≤ C * h t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (hpos t)]
      calc
        _ ≤ (h t * 1) * C :=
          mul_le_mul (mul_le_mul_of_nonneg_left htanh (hpos t).le)
            (hC' _ (haMem t)) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h₂ : ‖(h t : ℂ) * (((if σ then -1 else 1 : ℝ) * h t) • deriv T (a t))‖ ≤
        h t * ‖deriv T (a t)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos t), norm_smul,
        Real.norm_eq_abs, abs_mul, abs_of_pos (hpos t)]
      have he : |(if σ then -1 else 1 : ℝ)| = 1 := by cases σ <;> norm_num
      rw [he, one_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hle t)
          (norm_nonneg (deriv T (a t)))) (hpos t).le
    exact add_le_add h₁ h₂
  have henergy : IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2)
      (Ioo (-1) 1) := by
    apply (integrableOn_Ioo_iff_tanh _).2
    refine hD2.mono' (by
      change AEStronglyMeasurable (fun t ↦ (1 / Real.cosh t ^ 2) *
        (boundaryWeight (Real.tanh t) * ‖deriv G (Real.tanh t)‖ ^ 2)) volume
      have ht : Continuous Real.tanh := continuous_iff_continuousAt.2
        fun t ↦ (hasDerivAt_tanh t).continuousAt
      have h₁ : Continuous (fun t : ℝ ↦ 1 / Real.cosh t ^ 2) :=
        continuous_const.div (Real.continuous_cosh.pow _)
          (fun t ↦ pow_ne_zero _ (Real.cosh_pos t).ne')
      have h₂ : Continuous (fun t : ℝ ↦ boundaryWeight (Real.tanh t)) :=
        continuous_const.sub (ht.pow 2)
      exact h₁.aestronglyMeasurable.mul (h₂.aestronglyMeasurable.mul
        (((measurable_deriv G).comp ht.measurable).aestronglyMeasurable.norm.pow 2))) ?_
    filter_upwards [hUdiff, ae_comp_tanh hGac.ae_differentiableAt] with t ht htG
    have heq : G ∘ Real.tanh = U := funext hcomp
    have hd := ((htG (mixed_tanh_mem t)).hasDerivAt.scomp t (hasDerivAt_tanh t)).unique
      (heq.symm ▸ ht)
    have hdN := congrArg norm hd
    have hsign : |(if σ then -1 else 1 : ℝ)| = 1 := by cases σ <;> norm_num
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, hsign, one_mul,
      one_sub_tanh_sq, abs_of_pos (hpos t)] at hdN
    have hw : 0 < 1 / Real.cosh t ^ 2 := by positivity
    rw [abs_of_pos hw] at hdN
    simp only [smul_eq_mul, boundaryWeight_tanh, Real.norm_of_nonneg
      (mul_nonneg hw.le (mul_nonneg hw.le (sq_nonneg _)))]
    calc
      _ = ((1 / Real.cosh t ^ 2) * ‖deriv G (Real.tanh t)‖) ^ 2 := by ring
      _ = h t ^ 2 * ‖deriv T (a t)‖ ^ 2 := by rw [hdN, mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by nlinarith [mul_le_mul_of_nonneg_left (hle t) (hpos t).le]) (sq_nonneg _)
  exact ⟨hgac, hgI, hGac, hGbound, henergy⟩

/-- The finite Neumann energy in centered time coordinates is the
cosine-weighted tangential trace energy in the straight side coordinate. -/
theorem mixed_neumann_weighted_energy_eq {ω : L2} (d : MixedQuotientData ω) (σ : Bool) :
    (∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2) =
      ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
        Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2 := by
  let I := Ioo (-Real.pi / 2) (Real.pi / 2)
  let a := mixedNeumannA σ
  let T := fun x ↦ d.phi (x, cellEdgeNormal σ)
  let G := mixedNeumannG d.phi σ
  have hTac : AbsolutelyContinuousOnInterval T (-Real.pi / 2) (Real.pi / 2) :=
    (mixed_quotient_edge_h1 d σ).1
  have hGac : MixedBoundaryLocAC G := (mixed_neumann_stream_trace d σ).2.2.1
  have hcomp : G ∘ Real.tanh = T ∘ a := by
    funext t
    simp only [G, mixedNeumannG, Real.artanh_tanh, mixedNeumann_coord, T, a, Function.comp_apply]
  have hTae : ∀ᵐ x ∂volume.restrict I, DifferentiableAt ℝ T x := by
    filter_upwards [ae_restrict_of_ae hTac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo] with x hx hxI
    exact hx (Icc_subset_uIcc (Ioo_subset_Icc_self hxI))
  rw [← integral_tanh_subst, ← mixedNeumannA_integral σ]
  apply integral_congr_ae
  filter_upwards [mixedNeumannA_ae σ hTae, ae_comp_tanh hGac.ae_differentiableAt] with t ht htG
  have hU := ht.hasDerivAt.scomp t (mixedNeumannA_deriv σ t)
  have hd := ((htG (mixed_tanh_mem t)).hasDerivAt.scomp t (hasDerivAt_tanh t)).unique
    (hcomp.symm ▸ hU)
  have hdN := congrArg norm hd
  have hsign : |(if σ then -1 else 1 : ℝ)| = 1 := by cases σ <;> norm_num
  have hp : 0 < Real.cosh t := Real.cosh_pos t
  have hw : 0 < 1 / Real.cosh t ^ 2 := by positivity
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, hsign, one_mul,
    one_sub_tanh_sq, abs_of_pos (inv_pos.mpr hp), abs_of_pos hw] at hdN
  change (1 / Real.cosh t ^ 2) • (boundaryWeight (Real.tanh t) * ‖deriv G (Real.tanh t)‖ ^ 2) =
    (Real.cosh t)⁻¹ * (Real.cos (a t) * ‖deriv T (a t)‖ ^ 2)
  have hcos : Real.cos (a t) = (Real.cosh t)⁻¹ := by
    have hh := mixedNeumannArc_cos σ t
    rw [mixedNeumann_coord] at hh
    simpa only [a] using hh
  rw [boundaryWeight_tanh, smul_eq_mul, hcos]
  calc
    _ = ((1 / Real.cosh t ^ 2) * ‖deriv G (Real.tanh t)‖) ^ 2 := by ring
    _ = _ := by rw [hdN]; ring

private theorem mixed_stream_eq_on_closed_cell {ω : L2} (d : MixedQuotientData ω) :
    EqOn (contStream ω ∘ diagInv) (fun q ↦ (Real.cos q.1 : ℂ) * d.phi q)
      (closure mixedOpenCell) := by
  have hO : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hleft : ContinuousOn (contStream ω ∘ diagInv) (closure mixedOpenCell) :=
    ((continuous_contStream ω).comp diagInv.continuous).continuousOn
  have hright : ContinuousOn (fun q ↦ (Real.cos q.1 : ℂ) * d.phi q)
      (closure mixedOpenCell) :=
    ((by fun_prop : Continuous fun q : Plane ↦ (Real.cos q.1 : ℂ)).continuousOn.mul d.continuous)
  have hrep := (quasiMeasurePreserving_diagonalTraceChart 1).ae (streamLift_ae_eq_contStream ω)
  have hae : contStream ω ∘ diagInv =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ (Real.cos q.1 : ℂ) * d.phi q := by
    filter_upwards [ae_restrict_of_ae hrep, d.stream_eq] with q hr hd
    exact hr.symm.trans hd
  exact (Measure.eqOn_open_of_ae_eq hae hO (hleft.mono subset_closure)
    (hright.mono subset_closure)).of_subset_closure hleft hright subset_closure Subset.rfl

/-- The canonical pairing density on a Neumann edge. -/
def mixedNeumannPairing (lam : ℝ) (φ : Plane → ℂ) (σ : Bool) (t : ℝ) : ℝ :=
  let g := mixedNeumannStream φ σ
  (canonicalProfile lam g t * conj (g t)).re

/-- The four canonical arc pairings are precisely the full-line limits of
the two Neumann cutoff pairings. Both Dirichlet stream traces vanish. -/
theorem mixed_canonical_pairing_cutoff_limit {lam : ℝ} {ω : L2} (d : MixedQuotientData ω) :
    (∀ σ, Integrable (mixedNeumannPairing lam d.phi σ)) ∧
    Tendsto (fun T ↦ ∑ σ : Bool, ∫ t in Ioo (-T) T, mixedNeumannPairing lam d.phi σ t) atTop
      (𝓝 (∑ k ∈ Finset.range 4, ∫ t,
        (canonicalProfile lam (contStream ω ∘ cellArc k) t *
          conj (contStream ω (cellArc k t))).re)) := by
  let g := mixedNeumannStream d.phi
  have gi (σ : Bool) : Integrable (g σ) := by
    obtain ⟨hac, _, _, ⟨C, hC⟩, _⟩ := mixed_neumann_stream_trace d σ
    have hc := continuous_of_absolutelyContinuous hac
    have hh : Integrable (fun t : ℝ ↦ (Real.cosh t)⁻¹) := by
      simpa only [mul_one] using mixedNeumannA_integrable σ (f := fun _ ↦ 1) (integrable_const _)
    refine (hh.const_mul C).mono' hc.aestronglyMeasurable (.of_forall fun t ↦ ?_)
    change ‖mixedNeumannStream d.phi σ t‖ ≤ _
    rw [congrFun (mixedNeumann_weighted_stream d.phi σ) t, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.cosh_pos t).le), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _ (mixed_tanh_mem t)) (by positivity)
  have hi (σ : Bool) : Integrable (mixedNeumannPairing lam d.phi σ) := by
    have hgi := (mixed_neumann_stream_trace d σ).2.1
    have hc := continuous_of_absolutelyContinuous
      (absolutelyContinuousOnInterval_canonicalProfile (lam := lam) hgi)
    let B := ∫ t, ‖profileIntegrand lam (g σ) t‖
    have hbound (t : ℝ) : ‖canonicalProfile lam (g σ) t‖ ≤ B := by
      rw [norm_canonicalProfile]
      refine (norm_integral_le_integral_norm _).trans ?_
      exact setIntegral_le_integral (integrable_profileIntegrand hgi).norm
        (.of_forall fun _ ↦ norm_nonneg _)
    have hj := (gi σ).norm.const_mul B
    refine hj.mono' (Complex.continuous_re.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.mul
        (Complex.continuous_conj.comp_aestronglyMeasurable (gi σ).aestronglyMeasurable)))
      (.of_forall fun t ↦ ?_)
    change |(canonicalProfile lam (g σ) t * conj (g σ t)).re| ≤ _
    exact (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))
  have hNeumann (σ : Bool) : contStream ω ∘ mixedNeumannArc σ = g σ := by
    funext t
    have he := mixed_stream_eq_on_closed_cell d (mixedNeumannArc_mem σ t)
    simp only [Function.comp_apply, diagInv_diagCoord] at he
    exact he
  have hDirichlet (k : ℕ) (hk : k = 1 ∨ k = 3) :
      contStream ω ∘ cellArc k = 0 := by
    funext t
    have hmem := rotLift_iterate_mem (U := closure cellSquare)
      (fun _ h ↦ rotLift_mem_closure_cellSquare h)
      (arcSegment_subset_closure_cellSquare (separatrixArc_mem_arcSegment t)) k
    have hq : diagCoord (cellArc k t) ∈ closure mixedOpenCell := by
      have hmap : MapsTo diagCoord cellSquare mixedOpenCell := fun p hp ↦ by
        exact ⟨by simpa only [mem_Ioo, neg_div] using abs_lt.mp hp.1,
          by simpa only [mem_Ioo, neg_div] using abs_lt.mp hp.2⟩
      exact hmap.closure_of_continuousOn continuous_diagCoord.continuousOn hmem
    have he := mixed_stream_eq_on_closed_cell d hq
    simp only [Function.comp_apply, diagInv_diagCoord] at he
    have hzero : Real.cos (diagCoord (cellArc k t)).1 = 0 := by
      rcases hk with rfl | rfl <;>
        simp only [cellArc, Function.iterate_succ_apply', Function.iterate_zero_apply,
          rotLift, neg_neg, separatrixArc, diagCoord]
      · rw [show (arcAngle t - Real.pi + -arcAngle t) / 2 = -(Real.pi / 2) by ring,
          Real.cos_neg, Real.cos_pi_div_two]
      · rw [show (-(arcAngle t - Real.pi) + arcAngle t) / 2 = Real.pi / 2 by ring,
          Real.cos_pi_div_two]
    rw [hzero, Complex.ofReal_zero, zero_mul] at he
    exact he
  have hEq : (∑ k ∈ Finset.range 4, ∫ t,
      (canonicalProfile lam (contStream ω ∘ cellArc k) t * conj (contStream ω (cellArc k t))).re) =
      ∑ σ : Bool, ∫ t, mixedNeumannPairing lam d.phi σ t := by
    have hD (k : ℕ) (hk : k = 1 ∨ k = 3) :
        (∫ t, (canonicalProfile lam (contStream ω ∘ cellArc k) t *
          conj (contStream ω (cellArc k t))).re) = 0 := by
      have h := hDirichlet k hk
      change (∫ t, (canonicalProfile lam (contStream ω ∘ cellArc k) t *
        conj ((contStream ω ∘ cellArc k) t)).re) = 0
      rw [h]
      simp only [Pi.zero_apply, map_zero, mul_zero, Complex.zero_re, integral_zero]
    have hN (σ : Bool) :
        (∫ t, (canonicalProfile lam (contStream ω ∘ mixedNeumannArc σ) t *
          conj (contStream ω (mixedNeumannArc σ t))).re) =
          ∫ t, mixedNeumannPairing lam d.phi σ t := by
      change (∫ t, (canonicalProfile lam (contStream ω ∘ mixedNeumannArc σ) t *
        conj ((contStream ω ∘ mixedNeumannArc σ) t)).re) = _
      rw [hNeumann]
      rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, hD 1 (Or.inl rfl), hD 3 (Or.inr rfl),
      zero_add, add_zero, add_zero, Fintype.sum_bool]
    exact congrArg₂ (· + ·) (hN true) (hN false)
  refine ⟨hi, ?_⟩
  rw [hEq]
  have hlim (σ : Bool) : Tendsto (fun T ↦ ∫ t in Ioo (-T) T, mixedNeumannPairing lam d.phi σ t)
      atTop (𝓝 (∫ t, mixedNeumannPairing lam d.phi σ t)) := by
    apply (intervalIntegral_tendsto_integral (hi σ) tendsto_neg_atTop_atBot tendsto_id).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [id_eq, intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Ioc_eq_integral_Ioo]
  simp only [Fintype.sum_bool]
  exact (hlim true).add (hlim false)

private theorem mixedNeumannTime_left_inv (σ : Bool) (t : ℝ) :
    mixedNeumannTime σ (mixedNeumannA σ t) = t := by
  have hcos : Real.cos (arcAngle t) = Real.tanh t := by
    rw [arcAngle, Real.cos_two_mul, Real.cos_arctan, Real.tanh_eq_sinh_div_cosh,
      Real.sinh_eq, Real.cosh_eq]
    have he := Real.exp_pos (-t)
    have he' := Real.exp_pos t
    have hm : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hs : 0 ≤ 1 + Real.exp (-t) ^ 2 := by positivity
    rw [div_pow, Real.sq_sqrt hs]
    field_simp
    linear_combination -2 * Real.exp (-t) * hm
  unfold mixedNeumannTime
  rw [show (if σ then -1 else 1) * Real.sin (mixedNeumannA σ t) = Real.tanh t by
    cases σ <;> simp [mixedNeumannA, Real.sin_sub_pi_div_two, Real.sin_pi_div_two_sub, hcos]]
  exact Real.artanh_tanh t

private theorem mixedNeumannA_right_inv (σ : Bool) {a : ℝ}
    (ha : a ∈ Ioo (-Real.pi / 2) (Real.pi / 2)) :
    mixedNeumannA σ (mixedNeumannTime σ a) = a := by
  rw [← mixedNeumannA_image σ] at ha
  obtain ⟨t, rfl⟩ := ha
  rw [mixedNeumannTime_left_inv]

private theorem mixed_neumann_comp_local_h1 (σ : Bool) {F D : ℝ → ℂ}
    (h : ∀ l r, l < r → Icc l r ⊆ Ioo (-Real.pi / 2) (Real.pi / 2) →
      HasIntervalH1 l r F D) (c e : ℝ) :
    AbsolutelyContinuousOnInterval (F ∘ mixedNeumannA σ) c e := by
  let A := mixedNeumannA σ
  have hL0 : LipschitzWith 1 (fun t ↦ arcAngle t - Real.pi / 2) :=
    LipschitzWith.of_dist_le_mul fun s t ↦ by
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using
        lipschitzWith_arcAngle.dist_le_mul s t
  have hL : LipschitzWith 1 A := by
    cases σ
    · exact hL0.neg
    · exact hL0
  have hac := mixedNeumannA_mem σ c
  have hae := mixedNeumannA_mem σ e
  obtain ⟨l, hl, hl'⟩ := exists_between (lt_min hac.1 hae.1)
  obtain ⟨r, hr', hr⟩ := exists_between (max_lt hac.2 hae.2)
  have hc : A c ∈ Ioo l r := ⟨hl'.trans_le (min_le_left _ _),
    (le_max_left _ _).trans_lt hr'⟩
  have he : A e ∈ Ioo l r := ⟨hl'.trans_le (min_le_right _ _),
    (le_max_right _ _).trans_lt hr'⟩
  have hF := (h l r (hc.1.trans hc.2) (Icc_subset_Ioo hl hr)).absolutelyContinuous hc he
  cases σ
  · have hm : Monotone A := fun s t hst ↦ by
      change -(arcAngle s - Real.pi / 2) ≤ -(arcAngle t - Real.pi / 2)
      linarith [antitone_arcAngle hst]
    exact AbsolutelyContinuousOnInterval.comp_monotoneOn hF hL.lipschitzOnWith
      (hm.monotoneOn _) hm.mapsTo_uIcc
  · have hm : Antitone A := fun s t hst ↦ by
      change arcAngle t - Real.pi / 2 ≤ arcAngle s - Real.pi / 2
      linarith [antitone_arcAngle hst]
    exact AbsolutelyContinuousOnInterval.comp_antitoneOn hF hL.lipschitzOnWith
      (hm.antitoneOn _) hm.mapsTo_uIcc

/-- The physical vorticity trace obeys the transport equation on the regular arc and
is square integrable in flow time, assuming an inward H¹ vorticity collar. -/
theorem mixed_neumann_vorticity_trace_of_cell_collar {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (d : MixedQuotientData ω)
    {ε : ℝ} (hε : 0 < ε) (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 ω))
    (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    ∃ q : ℝ → ℂ, (∀ c e, AbsolutelyContinuousOnInterval q c e) ∧
      (∀ᵐ t, HasDerivAt q (Complex.I * lam * q t - deriv g t) t) ∧
      MemLp q 2 volume ∧
      ∃ ε : ℝ, 0 < ε ∧ HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 1 σ
        (liftL2 ω) (fun a ↦ q (mixedNeumannTime σ a)) := by
  let I := Ioo (-Real.pi / 2) (Real.pi / 2)
  let A := mixedNeumannA σ
  let g := mixedNeumannStream d.phi σ
  let f := fun a ↦ contStream ω (diagonalTraceChart 1 (a, cellEdgeNormal σ))
  obtain ⟨w, hw, hW, S, hS, hS2, hScell⟩ :=
    mixed_neumann_inward_trace_memLp d hε hv σ
  let k : ℝ := -edgeSideSign σ
  let D := fun a ↦ Complex.I * ((k * lam / Real.cos a : ℝ) : ℂ) * S a
  have hpair := isTransportPair_contStream hlam hω isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hloc (l r : ℝ) (hlr : l < r) (hr : Icc l r ⊆ I) :
      ∃ T, T =ᵐ[volume.restrict (Ioo l r)] (S + f) ∧ HasIntervalH1 l r T D := by
    have hsub := Ioo_subset_Icc_self.trans hr
    obtain ⟨V, T, hV, he, hT⟩ := hpair.inward_edge_window_transport
      closure_cellSquare_subset_cellNeighbourhood hv (continuous_contStream ω).continuousOn
      EventuallyEq.rfl 1 σ hlr hw hr (fun q hq ↦ hW ⟨hsub hq.1, hq.2⟩)
    have hVS := hV.ae_eq_inward hS hw le_rfl (k := id) hsub (fun _ hu ↦ hu)
      (MeasurePreserving.id volume) (MeasurePreserving.id volume) continuous_id rfl
      (fun _ _ _ _ ↦ rfl)
    have hF : T =ᵐ[volume.restrict (Ioo l r)] (S + f) := by
      filter_upwards [he, hVS] with a ha hsa
      change V a = S a at hsa
      simpa only [Pi.add_apply, f, hsa] using ha
    have hD : (fun a ↦ Complex.I *
        (↑((if (1 : Fin 2) = 0 then 1 else -1) * edgeSideSign σ * lam / Real.cos a) : ℂ) * V a)
        =ᵐ[volume.restrict (Ioo l r)] D := by
      filter_upwards [hVS] with a ha
      change V a = S a at ha
      simp only [D, k, one_ne_zero, ite_false, neg_one_mul, ha]
    refine ⟨T, hF, hT.memLp_value, hT.memLp_derivative.ae_eq hD,
      hT.locally_absolutelyContinuous, ?_⟩
    filter_upwards [hT.hasDerivAt_ae, (ae_restrict_iff' measurableSet_Ioo).1 hD] with a ha hda hmem
    rw [← hda hmem]
    exact ha hmem
  obtain ⟨T, heT, hTd, hT⟩ := mixed_glue_interval_h1 hloc
  let q := T ∘ A - g
  have hgac : ∀ c e, AbsolutelyContinuousOnInterval g c e :=
    (mixed_neumann_stream_trace d σ).1
  have hgval (t : ℝ) : f (A t) = g t := by
    have hm := mixedNeumannArc_mem σ t
    rw [mixedNeumann_coord] at hm
    change contStream ω (diagInv (mixedNeumannA σ t, cellEdgeNormal σ)) =
      mixedNeumannStream d.phi σ t
    simpa only [Function.comp_apply, mixedNeumannStream, mixedNeumann_coord] using
      mixed_stream_eq_on_closed_cell d hm
  have hqS : ∀ᵐ a ∂volume.restrict I, q (mixedNeumannTime σ a) = S a := by
    filter_upwards [heT, ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo]
      with a ha haI
    have hinv : A (mixedNeumannTime σ a) = a := mixedNeumannA_right_inv σ haI
    change T (A (mixedNeumannTime σ a)) - g (mixedNeumannTime σ a) = S a
    rw [← hgval, hinv, ha, Pi.add_apply, add_sub_cancel_right]
  have hqflow : q =ᵐ[volume] S ∘ A := by
    filter_upwards [mixedNeumannA_ae σ heT] with t ht
    change T (A t) - g t = S (A t)
    rw [← hgval, ht, Pi.add_apply, add_sub_cancel_right]
  refine ⟨q, fun c e ↦ (mixed_neumann_comp_local_h1 σ hT c e).sub (hgac c e), ?_,
    ((show MemLp (S ∘ A) 2 volume by simpa only [A, Function.comp_def, mixedNeumann_coord]
      using hS2).ae_eq hqflow.symm), ε, hε, ?_⟩
  · have hgd : ∀ᵐ t, DifferentiableAt ℝ g t := by
      have hn (n : ℕ) := (hgac (-(n : ℝ)) n).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      filter_upwards [ae_all_iff.2 hn] with t ht
      obtain ⟨n, hn'⟩ := exists_nat_gt |t|
      exact ht n (Icc_subset_uIcc ⟨by linarith [(abs_lt.mp hn').1], (abs_lt.mp hn').2.le⟩)
    filter_upwards [mixedNeumannA_ae σ hTd, hgd, hqflow] with t ht hgt hq
    have hc : Real.cos (A t) = (Real.cosh t)⁻¹ := by
      simpa only [A, mixedNeumann_coord] using mixedNeumannArc_cos σ t
    have hk : (if σ then -1 else 1 : ℝ) = k := by cases σ <;> norm_num [k, edgeSideSign]
    have hh := (ht.scomp t (mixedNeumannA_deriv σ t)).sub hgt.hasDerivAt
    refine hh.congr_deriv ?_
    change ((if σ then -1 else 1 : ℝ) * (Real.cosh t)⁻¹) • D (A t) - deriv g t =
      Complex.I * (lam : ℂ) * q t - deriv g t
    rw [hq, hk]
    simp only [D, hc, Function.comp_apply, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_div]
    have hk2 : (k : ℂ) ^ 2 = 1 := by cases σ <;> norm_num [k, edgeSideSign]
    have hcz : (↑((Real.cosh t)⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.cosh_pos t).ne')
    rw [show (k : ℂ) * (↑((Real.cosh t)⁻¹ : ℝ) : ℂ) *
        (Complex.I * ((k : ℂ) * (lam : ℂ) / ↑((Real.cosh t)⁻¹ : ℝ)) * S (A t)) =
        (k : ℂ) ^ 2 * (Complex.I * (lam : ℂ) * S (A t)) by
          rw [div_eq_mul_inv]
          linear_combination (k : ℂ) ^ 2 * Complex.I * (lam : ℂ) * S (A t) *
            (mul_inv_cancel₀ hcz), hk2, one_mul]
  · intro l r a b hlr hab hreg hedge hrect
    have h' := hScell l r a b hlr hab hreg hedge (hrect.trans
      (mixed_cell_eq_strip ε).subset)
    exact h'.congr_trace (ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Icc_self.trans hreg) hqS)

/-- The full-collar variant follows by shrinking to an inward strip. -/
theorem mixed_neumann_vorticity_trace_of_collar {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (d : MixedQuotientData ω)
    {ε : ℝ} (hε : 0 < ε) (hv : MemSobolevLocOn 1 (mixedSeparatrixCollar ε) (liftL2 ω))
    (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    ∃ q : ℝ → ℂ, (∀ c e, AbsolutelyContinuousOnInterval q c e) ∧
      (∀ᵐ t, HasDerivAt q (Complex.I * lam * q t - deriv g t) t) ∧
      MemLp q 2 volume ∧
      ∃ ε : ℝ, 0 < ε ∧ HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 1 σ
        (liftL2 ω) (fun a ↦ q (mixedNeumannTime σ a)) := by
  exact mixed_neumann_vorticity_trace_of_cell_collar hlam hω d (half_pos hε)
    (mixed_cell_collar_h1 hε hv) σ

/-- The physical vorticity trace obeys the transport equation on the regular arc and
is square integrable in flow time. It is not yet identified with the canonical profile. -/
theorem mixed_neumann_vorticity_trace {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    ∃ q : ℝ → ℂ, (∀ c e, AbsolutelyContinuousOnInterval q c e) ∧
      (∀ᵐ t, HasDerivAt q (Complex.I * lam * q t - deriv g t) t) ∧
      MemLp q 2 volume ∧
      ∃ ε : ℝ, 0 < ε ∧ HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 1 σ
        (liftL2 ω) (fun a ↦ q (mixedNeumannTime σ a)) := by
  obtain ⟨ε, hε, _, hv, _⟩ := mixed_cell_separatrix_h1 hlam hω hs
  exact mixed_neumann_vorticity_trace_of_cell_collar hlam hω d hε hv σ

/-- Boundary square and physical trace for the actual mixed Neumann profile. -/
theorem mixed_boundary_square_traces {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    (σ : Bool) :
    let g := mixedNeumannStream d.phi σ
    let F := mixedNeumannF lam d.phi σ
    let G := mixedNeumannG d.phi σ
    Integrable (deriv g) ∧ MixedBoundaryLocAC F ∧ MixedBoundaryLocAC G ∧
    MixedBoundaryLocAC (deriv F) ∧
    G =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] mixedBoundaryTransport lam F ∧
    (∃ C : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      ‖F x‖ ≤ C ∧ ‖G x‖ ≤ C ∧ ‖(boundaryWeight x : ℂ) * deriv F x‖ ≤ C) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re) (Ioo (-1) 1) ∧
    IntegrableOn (fun x ↦ boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) (Ioo (-1) 1) ∧
    ((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
      2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re) =
        ∫ x in Ioo (-1) 1, boundaryWeight x * ‖mixedBoundarySquare lam F x‖ ^ 2) ∧
    ∃ ε : ℝ, 0 < ε ∧ HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 1 σ (liftL2 ω)
      (fun a ↦ canonicalProfile lam g (mixedNeumannTime σ a)) := by
  obtain ⟨hgac, hg, hG, hbG, he⟩ := mixed_neumann_stream_trace d σ
  obtain ⟨q, hqAC, hqODE, hqL2, ε, hε, hqTrace⟩ :=
    mixed_neumann_vorticity_trace hlam hω hs d σ
  obtain ⟨hqTop, hqBot⟩ := mixed_vorticity_profile_decay hg hqAC hqODE hqL2
  obtain rfl := canonicalProfile_unique hg hqAC hqODE hqTop
  have hM := (tendsto_canonicalProfile_atBot_iff hg).mp hqBot
  obtain ⟨hF, hbF, htr⟩ := mixed_neumann_canonical_transport hlam σ hgac hg hbG hM
  obtain ⟨hdF, hbdF, hc, hsquare, heq⟩ :=
    mixed_boundary_square_weighted lam hF hG htr hbF hbG he
  obtain ⟨CF, hCF⟩ := hbF
  obtain ⟨CG, hCG⟩ := hbG
  obtain ⟨CD, hCD⟩ := hbdF
  exact ⟨hg, hF, hG, hdF, htr, ⟨max CF (max CG CD), fun x hx ↦
    ⟨(hCF x hx).trans (le_max_left _ _),
      (hCG x hx).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hCD x hx).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩,
    he, hc, hsquare, heq, ε, hε, hqTrace⟩

private theorem mixed_tanh_integral {f : ℝ → ℝ} {a b : ℝ} :
    (∫ t in Ioo a b, boundaryWeight (Real.tanh t) * f (Real.tanh t)) =
      ∫ x in Ioo (Real.tanh a) (Real.tanh b), f x := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t (_ : t ∈ Ioo a b) ↦ (hasDerivAt_tanh t).hasDerivWithinAt)
    Real.tanh_injective.injOn f
  have hc : Continuous Real.tanh := continuous_iff_continuousAt.2
    fun t ↦ (hasDerivAt_tanh t).continuousAt
  rw [hc.image_Ioo_of_strictMono mixed_tanh_strictMono] at h
  rw [h]
  congr 1
  funext t
  rw [abs_of_pos (by rw [one_sub_tanh_sq]; positivity), boundaryWeight, smul_eq_mul]

private theorem mixed_tanh_integrable {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : IntegrableOn f (Real.tanh '' s)) :
    IntegrableOn (fun t ↦ boundaryWeight (Real.tanh t) * f (Real.tanh t)) s := by
  apply ((integrableOn_image_iff_integrableOn_abs_deriv_smul hs
    (fun t _ ↦ (hasDerivAt_tanh t).hasDerivWithinAt) Real.tanh_injective.injOn f).mp h).congr
  exact Eventually.of_forall fun t ↦ by
    dsimp only
    rw [abs_of_pos (by rw [one_sub_tanh_sq]; positivity), boundaryWeight, smul_eq_mul]

private theorem mixed_norm_boundary_ac {G : ℝ → ℂ} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ x * ‖G x‖ ^ 2) a b := by
  have hn := (lipschitzWith_one_norm (E := ℂ)).comp_absolutelyContinuousOnInterval h
  have hi : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x) a b :=
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  simpa only [Function.comp_apply, pow_two] using hi.fun_mul (hn.fun_mul hn)

private theorem mixed_norm_boundary_deriv {G : ℝ → ℂ} {x : ℝ}
    (h : DifferentiableAt ℝ G x) :
    deriv (fun y ↦ y * ‖G y‖ ^ 2) x =
      ‖G x‖ ^ 2 + 2 * x * (deriv G x * conj (G x)).re := by
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h.hasDerivAt
  have hI := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h.hasDerivAt
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_def] at hR hI
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hd := ((hasDerivAt_id x).mul ((hR.mul hR).add (hI.mul hI))).deriv
  simp only [id_eq, Pi.add_apply, Pi.mul_def, Pi.add_def] at hd
  rw [hd]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem mixed_flux_gradient_pointwise (t : ℝ) (U V : ℂ) :
    2 * ‖((Real.cosh t)⁻¹ : ℝ) *
        ((boundaryWeight (Real.tanh t) : ℂ) * V - (Real.tanh t : ℂ) * U) /
        (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 - ‖U‖ ^ 2 =
      boundaryWeight (Real.tanh t) *
        (boundaryWeight (Real.tanh t) * ‖V‖ ^ 2 -
          (‖U‖ ^ 2 + 2 * Real.tanh t * (V * conj U).re)) := by
  have he (z : ℂ) :
      ((Real.cosh t)⁻¹ : ℝ) * z / (Real.sqrt 2 / Real.cosh t : ℝ) =
        z / (Real.sqrt 2 : ℝ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
    rw [← Complex.ofReal_cosh, mul_div_cancel_left₀ _
      (Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne')]
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (by norm_num)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, boundaryWeight]
  ring

private theorem mixed_neumann_corner_limit {ω : L2} (d : MixedQuotientData ω) (σ : Bool) :
    let H := fun x : ℝ ↦ x * ‖mixedNeumannG d.phi σ x‖ ^ 2
    Tendsto (fun T ↦ H (Real.tanh T) - H (Real.tanh (-T))) atTop
      (𝓝 (∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2)) := by
  let H := fun x : ℝ ↦ x * ‖mixedNeumannG d.phi σ x‖ ^ 2
  have hmass (t : ℝ) :
      mixedNeumannG d.phi σ (Real.tanh t) = d.phi (diagCoord (mixedNeumannArc σ t)) := by
    simp [mixedNeumannG, Real.artanh_tanh]
  change Tendsto (fun T ↦ H (Real.tanh T) - H (Real.tanh (-T))) atTop _
  have hminus : Tendsto (fun T : ℝ ↦ Real.tanh (-T)) atTop (𝓝 (-1)) := by
    simpa only [Real.tanh_neg] using mixed_tanh_atTop.neg
  let R (p : Plane) : Plane := if σ then p else (-p.1, -p.2)
  have hR : Continuous R := by
    cases σ <;> dsimp [R] <;> fun_prop
  have hArc (t : ℝ) : mixedNeumannArc σ t = R (separatrixArc t) := by
    cases σ <;> simp [R, mixedNeumannArc, cellArc, Function.iterate_succ_apply', rotLift]
  have hp : Tendsto (fun t ↦ diagCoord (mixedNeumannArc σ t)) atTop
      (𝓝 (diagCoord (R (0, -Real.pi)))) := by
    simpa only [hArc, Function.comp_def] using ((continuous_diagCoord.comp hR).tendsto _).comp
      tendsto_separatrixArc_atTop
  have hn : Tendsto (fun t ↦ diagCoord (mixedNeumannArc σ (-t))) atTop
      (𝓝 (diagCoord (R (Real.pi, 0)))) := by
    simpa only [hArc, Function.comp_def] using ((continuous_diagCoord.comp hR).tendsto _).comp
      (tendsto_separatrixArc_atBot.comp tendsto_neg_atTop_atBot)
  have hClosed : IsClosed (closure mixedOpenCell) := isClosed_closure
  have hpMem := hClosed.mem_of_tendsto hp (Eventually.of_forall (mixedNeumannArc_mem σ))
  have hnMem := hClosed.mem_of_tendsto hn
    (Eventually.of_forall fun t ↦ mixedNeumannArc_mem σ (-t))
  have hpG := (d.continuous _ hpMem).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hp, Eventually.of_forall (mixedNeumannArc_mem σ)⟩)
  have hnG := (d.continuous _ hnMem).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hn, Eventually.of_forall fun t ↦ mixedNeumannArc_mem σ (-t)⟩)
  have h := (mixed_tanh_atTop.mul (hpG.norm.pow 2)).sub (hminus.mul (hnG.norm.pow 2))
  have hP : diagCoord (R (0, -Real.pi)) = (cellEdgeNormal (!σ), cellEdgeNormal σ) := by
    cases σ <;> simp [R, diagCoord, cellEdgeNormal]
  have hN : diagCoord (R (Real.pi, 0)) = (cellEdgeNormal σ, cellEdgeNormal σ) := by
    cases σ <;> simp [R, diagCoord, cellEdgeNormal]
  rw [hP, hN] at h
  simp only [H, hmass]
  cases σ <;> simpa [Fintype.sum_bool, add_comm] using h

private theorem mixed_neumann_energy_cutoff {ω : L2} (d : MixedQuotientData ω)
    (σ : Bool) (T : ℝ) (hT : 0 < T) :
    let e := fun t ↦ ‖deriv (mixedNeumannStream d.phi σ) t /
      (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2
    let G := mixedNeumannG d.phi σ
    let H := fun x ↦ x * ‖G x‖ ^ 2
    IntegrableOn e (Ioo (-T) T) ∧
      2 * (∫ t in Ioo (-T) T, e t) -
          (∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2) =
        (∫ x in Ioo (Real.tanh (-T)) (Real.tanh T), boundaryWeight x * ‖deriv G x‖ ^ 2) -
          (H (Real.tanh T) - H (Real.tanh (-T))) := by
  let g := mixedNeumannStream d.phi σ
  let G := mixedNeumannG d.phi σ
  let w := fun t ↦ boundaryWeight (Real.tanh t)
  let H := fun x : ℝ ↦ x * ‖G x‖ ^ 2
  let e := fun t ↦ ‖deriv g t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2
  obtain ⟨hac, _, hG, _, hge⟩ := mixed_neumann_stream_trace d σ
  have ht : -T < T := by linarith
  have hab := mixed_tanh_strictMono ht
  have hE : Integrable (fun t ↦ w t * (boundaryWeight (Real.tanh t) *
      ‖deriv G (Real.tanh t)‖ ^ 2)) := by
    rw [← integrableOn_univ]
    apply mixed_tanh_integrable (f := fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2)
      MeasurableSet.univ
    rwa [Real.tanh_bijOn.image_eq]
  have hH := mixed_norm_boundary_ac (hG _ _ (mixed_tanh_mem (-T)).1 hab (mixed_tanh_mem T).2)
  have hDi : IntegrableOn (fun t ↦ w t * deriv H (Real.tanh t)) (Ioo (-T) T) := by
    apply mixed_tanh_integrable measurableSet_Ioo
    have htc : Continuous Real.tanh := continuous_iff_continuousAt.2
      fun t ↦ (hasDerivAt_tanh t).continuousAt
    rw [htc.image_Ioo_of_strictMono mixed_tanh_strictMono]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hH.intervalIntegrable_deriv
  have hm : IntegrableOn (fun t ↦ ‖G (Real.tanh t)‖ ^ 2) (Ioo (-T) T) := by
    have he (t : ℝ) : G (Real.tanh t) = (Real.cosh t : ℂ) * g t := by
      change _ = _ * mixedNeumannStream d.phi σ t
      rw [congrFun (mixedNeumann_weighted_stream d.phi σ) t, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.cosh_pos t).ne',
        Complex.ofReal_one, one_mul]
    simp_rw [he]
    have hgc : Continuous g := continuous_of_absolutelyContinuous hac
    have hc : Continuous fun t : ℝ ↦ (Real.cosh t : ℂ) * g t := by fun_prop
    exact (hc.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hgd := ae_comp_tanh hG.ae_differentiableAt
  have hg_eq := mixedNeumann_weighted_stream d.phi σ
  have he : (fun t ↦ (1 / 2 : ℝ) *
      (w t * (boundaryWeight (Real.tanh t) * ‖deriv G (Real.tanh t)‖ ^ 2) -
        w t * deriv H (Real.tanh t) + ‖G (Real.tanh t)‖ ^ 2)) =ᵐ[volume.restrict (Ioo (-T) T)]
        e := by
    filter_upwards [ae_restrict_of_ae hgd] with t htG
    have hd := htG (mixed_tanh_mem t)
    change (1 / 2 : ℝ) * (w t * (boundaryWeight (Real.tanh t) * ‖deriv G (Real.tanh t)‖ ^ 2) -
      w t * deriv H (Real.tanh t) + ‖G (Real.tanh t)‖ ^ 2) = e t
    dsimp only [e, g, w, H]
    rw [congrArg (fun f : ℝ → ℂ ↦ deriv f t) hg_eq,
      (mixed_hasDerivAt_weightedFlow hd).deriv, mixed_norm_boundary_deriv hd]
    have hx := mixed_flux_gradient_pointwise t (G (Real.tanh t)) (deriv G (Real.tanh t))
    linarith only [hx]
  have hi : IntegrableOn e (Ioo (-T) T) :=
    (((hE.integrableOn.sub hDi).add hm).const_mul (1 / 2 : ℝ)).congr he
  refine ⟨hi, ?_⟩
  have hmass (t : ℝ) : G (Real.tanh t) = d.phi (diagCoord (mixedNeumannArc σ t)) := by
    simp [G, mixedNeumannG, Real.artanh_tanh]
  simp only [← hmass]
  change 2 * (∫ t in Ioo (-T) T, e t) - (∫ t in Ioo (-T) T, ‖G (Real.tanh t)‖ ^ 2) = _
  rw [← integral_congr_ae he, integral_const_mul]
  have hsplit := integral_add (hE.integrableOn.sub hDi) hm
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_sub hE.integrableOn hDi]
  have hD : (∫ x in Ioo (Real.tanh (-T)) (Real.tanh T), deriv H x) =
      H (Real.tanh T) - H (Real.tanh (-T)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact hH.integral_deriv_eq_sub
  have hE' := mixed_tanh_integral (f := fun x ↦ boundaryWeight x * ‖deriv G x‖ ^ 2)
    (a := -T) (b := T)
  have hD' := mixed_tanh_integral (f := deriv H) (a := -T) (b := T)
  change (∫ t in Ioo (-T) T, w t * (boundaryWeight (Real.tanh t) *
    ‖deriv G (Real.tanh t)‖ ^ 2)) = _ at hE'
  change (∫ t in Ioo (-T) T, w t * deriv H (Real.tanh t)) = _ at hD'
  rw [hE', hD', hD]
  change 2 * (1 / 2 * (_ + _)) - _ = _ - (H _ - H _)
  ring

private theorem mixed_neumann_energy_cutoff_integrable {ω : L2} (d : MixedQuotientData ω)
    (σ : Bool) (T : ℝ) :
    IntegrableOn (fun t ↦ ‖deriv (mixedNeumannStream d.phi σ) t /
      (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2) (Ioo (-T) T) := by
  by_cases hT : 0 < T
  · exact (mixed_neumann_energy_cutoff d σ T hT).1
  · rw [Ioo_eq_empty (by linarith)]
    exact integrableOn_empty

/-- On a single Neumann edge, subtract the trace mass before taking the cutoff
limit. In `x = tanh t` the leftover gradient term is the weighted energy
minus the derivative of `x |G|²`; the latter gives the two corner values. -/
theorem mixed_neumann_flux_renormalized {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω)
    (σ : Bool) :
    let F := mixedNeumannF lam d.phi σ
    let G := mixedNeumannG d.phi σ
    Tendsto (fun T ↦ 2 * mixedNeumannFluxCutoff lam d.phi σ T -
      ∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2) atTop
      (𝓝 (((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv G x‖ ^ 2) -
        2 * (∫ x in Ioo (-1) 1, (mixedBoundaryTransport 0 F x * conj (G x)).re)) -
        ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2)) := by
  let g := mixedNeumannStream d.phi σ
  let F := mixedNeumannF lam d.phi σ
  let G := mixedNeumannG d.phi σ
  let H := fun x : ℝ ↦ x * ‖G x‖ ^ 2
  let e := fun x : ℝ ↦ boundaryWeight x * ‖deriv G x‖ ^ 2
  let c := fun x : ℝ ↦ (mixedBoundaryTransport 0 F x * conj (G x)).re
  let w := fun t : ℝ ↦ boundaryWeight (Real.tanh t)
  let m := fun t : ℝ ↦ ‖G (Real.tanh t)‖ ^ 2
  let j := fun t : ℝ ↦ ‖deriv g t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2 +
    (canonicalProfile lam g t * conj (g t)).re
  obtain ⟨hg, hF, hG, _, _, _, he, hc, _⟩ := mixed_boundary_square_traces hlam hω hs d σ
  have hmass (t : ℝ) : G (Real.tanh t) = d.phi (diagCoord (mixedNeumannArc σ t)) := by
    simp [G, mixedNeumannG, Real.artanh_tanh]
  have hg_eq : g = fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * G (Real.tanh t) :=
    mixedNeumann_weighted_stream d.phi σ
  have hz_eq : canonicalUnknown lam g = fun t ↦ ((Real.cosh t)⁻¹ : ℝ) * F (Real.tanh t) :=
    mixedNeumann_weighted_unknown lam d.phi σ
  have hgd := ae_comp_tanh hG.ae_differentiableAt
  have hfd := ae_comp_tanh hF.ae_differentiableAt
  have hgd' : ∀ᵐ t, DifferentiableAt ℝ g t := by
    filter_upwards [hgd] with t ht
    rw [hg_eq]
    exact (mixed_hasDerivAt_weightedFlow (ht (mixed_tanh_mem t))).differentiableAt
  have hprofile := ae_hasDerivAt_canonicalUnknown hlam hg hgd'
  have hpoint : ∀ᵐ t, 2 * j t - m t =
      w t * ((e (Real.tanh t) - 2 * c (Real.tanh t)) - deriv H (Real.tanh t)) := by
    filter_upwards [hgd, hfd, hprofile] with t hgt hft hz
    have hgt := hgt (mixed_tanh_mem t)
    have hft := hft (mixed_tanh_mem t)
    have hderiv := (mixed_hasDerivAt_weightedFlow hgt).deriv
    have hdz := hz.unique (hz_eq.symm ▸ mixed_hasDerivAt_weightedFlow hft)
    have hΩ : canonicalProfile lam g t =
        -(((Real.cosh t)⁻¹ : ℝ) : ℂ) * mixedBoundaryTransport 0 F (Real.tanh t) := by
      unfold mixedBoundaryTransport
      simp only [Complex.ofReal_zero, zero_mul, sub_zero]
      linear_combination Complex.I * hdz + (Complex.I_sq) * canonicalProfile lam g t
    have hp : (canonicalProfile lam g t * conj (g t)).re = -(w t * c (Real.tanh t)) := by
      rw [hΩ, congrFun hg_eq t]
      simp only [c, w, boundaryWeight_tanh, map_mul, Complex.conj_ofReal,
        neg_mul, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, one_div]
      ring
    dsimp only [j, m, H, e]
    rw [congrArg (fun f : ℝ → ℂ ↦ deriv f t) hg_eq, hderiv, hp, mixed_norm_boundary_deriv hgt]
    linarith only [mixed_flux_gradient_pointwise t (G (Real.tanh t)) (deriv G (Real.tanh t))]
  have hE : IntegrableOn (fun x ↦ e x - 2 * c x) (Ioo (-1 : ℝ) 1) :=
    he.sub (hc.const_mul 2)
  have htime : Integrable (fun t ↦ w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) := by
    rw [← integrableOn_univ]
    apply mixed_tanh_integrable (f := fun x ↦ e x - 2 * c x) MeasurableSet.univ
    rwa [Real.tanh_bijOn.image_eq]
  have hcut (T : ℝ) (hT : 0 < T) :
      2 * mixedNeumannFluxCutoff lam d.phi σ T -
        (∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2) =
      (∫ t in Ioo (-T) T, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) -
        (H (Real.tanh T) - H (Real.tanh (-T))) := by
    have ht : -T < T := by linarith
    have hab := mixed_tanh_strictMono ht
    have hH := mixed_norm_boundary_ac (hG _ _ (mixed_tanh_mem (-T)).1 hab (mixed_tanh_mem T).2)
    have hHi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hH.intervalIntegrable_deriv
    have hDi : IntegrableOn (fun t ↦ w t * deriv H (Real.tanh t)) (Ioo (-T) T) := by
      apply mixed_tanh_integrable measurableSet_Ioo
      have htc : Continuous Real.tanh := continuous_iff_continuousAt.2
        fun t ↦ (hasDerivAt_tanh t).continuousAt
      rwa [htc.image_Ioo_of_strictMono mixed_tanh_strictMono]
    have hm : Continuous m := by
      have ha : Continuous (fun t ↦ diagCoord (mixedNeumannArc σ t)) := by
        cases σ <;> simp only [mixedNeumannArc, Bool.false_eq_true, ↓reduceIte, cellArc,
          Function.iterate_succ_apply', Function.iterate_zero_apply, rotLift,
          separatrixArc, diagCoord]
        all_goals
          have hac : Continuous arcAngle := continuous_iff_continuousAt.2
            fun t ↦ (hasDerivAt_arcAngle t).continuousAt
          fun_prop
      rw [show m = fun t ↦ ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2 by
        funext t; simp only [m, hmass]]
      exact (d.continuous.comp_continuous ha (mixedNeumannArc_mem σ)).norm.pow _
    have hmi : IntegrableOn m (Ioo (-T) T) :=
      (hm.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hp' : IntegrableOn (fun t ↦ 2 * j t - m t) (Ioo (-T) T) := by
      apply ((htime.integrableOn (s := Ioo (-T) T)).sub hDi).congr
      filter_upwards [ae_restrict_of_ae hpoint] with t h
      simpa only [Pi.sub_apply, mul_sub] using h.symm
    have hji : IntegrableOn j (Ioo (-T) T) := by
      apply ((hp'.add hmi).const_mul (1 / 2 : ℝ)).congr
      exact Eventually.of_forall fun t ↦ by dsimp; ring
    simp only [mixedNeumannFluxCutoff, ← hmass]
    change 2 * (∫ t in Ioo (-T) T, j t) - (∫ t in Ioo (-T) T, m t) = _
    rw [← integral_const_mul, ← integral_sub (hji.const_mul 2) hmi]
    calc
      _ = ∫ t in Ioo (-T) T, w t * (e (Real.tanh t) - 2 * c (Real.tanh t)) -
          w t * deriv H (Real.tanh t) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hpoint] with t h
          rw [h, mul_sub]
      _ = _ := by
        have hd : (∫ x in Ioo (Real.tanh (-T)) (Real.tanh T), deriv H x) =
            H (Real.tanh T) - H (Real.tanh (-T)) := by
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
          exact hH.integral_deriv_eq_sub
        rw [integral_sub htime.integrableOn hDi, mixed_tanh_integral, hd]
  have htimeLim := intervalIntegral_tendsto_integral htime tendsto_neg_atTop_atBot tendsto_id
  rw [show (∫ t, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) =
      (∫ x in Ioo (-1) 1, e x) - 2 * (∫ x in Ioo (-1) 1, c x) by
    rw [show (∫ t, w t * (e (Real.tanh t) - 2 * c (Real.tanh t))) =
      ∫ x in Ioo (-1) 1, e x - 2 * c x by
      simpa only [w, boundaryWeight_tanh, smul_eq_mul] using
        integral_tanh_subst (fun x ↦ e x - 2 * c x)]
    rw [integral_sub he (hc.const_mul 2), integral_const_mul]] at htimeLim
  have hEnds := mixed_neumann_corner_limit d σ
  apply (htimeLim.sub hEnds).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [id_eq]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Ioc_eq_integral_Ioo]
  exact (hcut T hT).symm

/-- Explicit finite part of twice the centered signed gradient cutoff. -/
def mixedGradientFluxFinitePart {ω : L2} (d : MixedQuotientData ω) : ℝ :=
  (∫ x in Ioo (-Real.pi / 2) (Real.pi / 2), mixedEdgeMassDefect d.phi x / Real.cos x) -
    ∑ σ : Bool, ((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2) -
      ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2)

/-- The centered edge cutoff converges after pairing the signed energies.
The Neumann energy minus its trace mass contributes the weighted tangential
energy and the two endpoint terms. -/
theorem mixed_gradient_cutoff_limit {ω : L2} (d : MixedQuotientData ω) :
    Tendsto (mixedGradientFluxCutoff d.phi) atTop (𝓝 (mixedGradientFluxFinitePart d / 2)) := by
  let E (σ : Bool) (T : ℝ) := 2 * (∫ t in Ioo (-T) T,
    ‖deriv (mixedNeumannStream d.phi σ) t / (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2) -
      ∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2
  let B (σ : Bool) := (∫ x in Ioo (-1) 1,
    boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2) -
      ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2
  have he (σ : Bool) : Tendsto (E σ) atTop (𝓝 (B σ)) := by
    let f := fun x : ℝ ↦ boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2
    let F := fun t : ℝ ↦ boundaryWeight (Real.tanh t) * f (Real.tanh t)
    have hi : Integrable F := by
      rw [← integrableOn_univ]
      apply mixed_tanh_integrable (f := f) MeasurableSet.univ
      rw [Real.tanh_bijOn.image_eq]
      exact (mixed_neumann_stream_trace d σ).2.2.2.2
    have hI : (∫ t, F t) = ∫ x in Ioo (-1) 1, f x := by
      simpa only [F, boundaryWeight_tanh, smul_eq_mul] using integral_tanh_subst f
    have hh := intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
    rw [hI] at hh
    apply (hh.sub (mixed_neumann_corner_limit d σ)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [id_eq, intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Ioc_eq_integral_Ioo]
    change ((∫ t in Ioo (-T) T, boundaryWeight (Real.tanh t) * f (Real.tanh t)) - _) = E σ T
    rw [mixed_tanh_integral]
    exact (mixed_neumann_energy_cutoff d σ T hT).2.symm
  have hsum : Tendsto (fun T ↦ ∑ σ : Bool, E σ T) atTop (𝓝 (∑ σ : Bool, B σ)) := by
    simp only [Fintype.sum_bool]
    exact (he true).add (he false)
  have h := ((mixed_trace_mass_cutoff_limit d).sub hsum).div_const (2 : ℝ)
  apply h.congr
  intro T
  simp only [E, mixedTraceMassCutoff, mixedGradientFluxCutoff, Fintype.sum_bool,
    mixedNeumannArc, Bool.false_eq_true, ite_false, ite_true, div_eq_mul_inv, integral_mul_const]
  ring

/-- Geometric trace limit on regular levels. The signed gradient energies
must be paired on the two sides of each corner before taking the limit. -/
theorem mixed_geometric_level_limit {lam : ℝ} (_hlam : lam ≠ 0) {ω : L2}
    (_hω : IsEigenSolution lam ω) (_hs : InSector false true ω) (d : MixedQuotientData ω) :
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (mixedGeometricLevelTerm ω) (𝓝[Ioo 0 1 \ N] 0)
        (𝓝 (mixedGradientFluxFinitePart d)) := by
  obtain ⟨N, hN, hfirst⟩ := mixed_level_first_limit d
  obtain ⟨M, hM, hgradient⟩ := mixed_level_signed_gradient_limit d
  refine ⟨N ∪ M, measure_union_null hN hM, ?_⟩
  let 𝓕 := 𝓝[Ioo 0 1 \ (N ∪ M)] (0 : ℝ)
  have h₁ : 𝓕 ≤ 𝓝[Ioo 0 1 \ N] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inl h)⟩)
  have h₂ : 𝓕 ≤ 𝓝[Ioo 0 1 \ M] 0 :=
    nhdsWithin_mono _ (fun _ hs ↦ ⟨hs.1, fun h ↦ hs.2 (Or.inr h)⟩)
  have hscale : Tendsto (fun s : ℝ ↦ 1 - s) 𝓕 (𝓝 1) := by
    simpa only [sub_zero, id_eq] using
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓕)).sub
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓕 ≤ 𝓝 (0 : ℝ))))
  have h := (hfirst.mono_left h₁).add (hscale.mul (hgradient.mono_left h₂))
  simp only [zero_add, one_mul] at h
  have he (σ : Bool) :
      (∫ a in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a) =
        -((∫ x in Ioo (-1) 1, boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2) -
          ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2) := by
    obtain ⟨hc, hd⟩ := mixed_quotient_edge_h1 d σ
    change AbsolutelyContinuousOnInterval (mixedEdgeValue 1 σ d.phi) _ _ at hc
    change MemLp (deriv (mixedEdgeValue 1 σ d.phi)) 2 _ at hd
    rw [← neg_div, (mixed_rellich_edge_integral hc hd).2.2,
      mixed_neumann_weighted_energy_eq, Fintype.sum_bool]
    change ‖d.phi (-Real.pi / 2, cellEdgeNormal σ)‖ ^ 2 +
      ‖d.phi (Real.pi / 2, cellEdgeNormal σ)‖ ^ 2 - _ = -(_ - (_ + _))
    simp only [cellEdgeNormal, Bool.false_eq_true, ite_true, ite_false]
    ring
  have hfin : (∫ a in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        mixedEdgeMassDefect d.phi a / Real.cos a) +
        (∑ σ : Bool, ∫ a in Ioo (-(Real.pi / 2)) (Real.pi / 2),
          mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a) =
        mixedGradientFluxFinitePart d := by
    have hs : (∑ σ : Bool, ∫ a in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        mixedRellichEdgeDensity (mixedEdgeValue 1 σ d.phi) a) =
        ∑ σ : Bool, -((∫ x in Ioo (-1) 1,
          boundaryWeight x * ‖deriv (mixedNeumannG d.phi σ) x‖ ^ 2) -
          ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2) :=
      Finset.sum_congr rfl (fun σ _ ↦ he σ)
    rw [mixedGradientFluxFinitePart, hs, Finset.sum_neg_distrib, ← sub_eq_add_neg, neg_div]
  rw [hfin] at h
  apply h.congr
  intro s
  unfold mixedGeometricLevelTerm
  ring

/-- The two geometric limits, with the signed gradient energies paired before
taking either limit. No vorticity transport or canonical profile is used. -/
theorem mixed_geometric_flux_limit {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    ∃ L : ℝ, ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (mixedGradientFluxCutoff d.phi) atTop (𝓝 L) ∧
      Tendsto (mixedGeometricLevelTerm ω) (𝓝[Ioo 0 1 \ N] 0) (𝓝 (2 * L)) := by
  obtain ⟨N, hN, hlim⟩ := mixed_geometric_level_limit hlam hω hs d
  refine ⟨mixedGradientFluxFinitePart d / 2, N, hN, mixed_gradient_cutoff_limit d, ?_⟩
  rwa [show 2 * (mixedGradientFluxFinitePart d / 2) = mixedGradientFluxFinitePart d by ring]

private theorem mixed_paired_flux_split {lam : ℝ} {ω : L2} (d : MixedQuotientData ω)
    (T : ℝ) :
    mixedPairedFluxCutoff lam d.phi T = mixedGradientFluxCutoff d.phi T -
      ∑ σ : Bool, ∫ t in Ioo (-T) T, mixedNeumannPairing lam d.phi σ t := by
  have he (σ : Bool) : mixedNeumannFluxCutoff lam d.phi σ T =
      (∫ t in Ioo (-T) T, ‖deriv (mixedNeumannStream d.phi σ) t /
        (Real.sqrt 2 / Real.cosh t : ℝ)‖ ^ 2) +
      ∫ t in Ioo (-T) T, mixedNeumannPairing lam d.phi σ t := by
    exact integral_add (mixed_neumann_energy_cutoff_integrable d σ T)
      ((mixed_canonical_pairing_cutoff_limit (lam := lam) d).1 σ).integrableOn
  simp only [mixedPairedFluxCutoff, mixedGradientFluxCutoff, he, Fintype.sum_bool]
  ring

/-- The normal-field paired flux. The transport part uses canonical profiles,
not a physical vorticity trace. -/
theorem mixed_paired_flux {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedNormalVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedNormalVirialDensity d q)) := by
  obtain ⟨L, N, hN, hcut, hlevel⟩ := mixed_geometric_flux_limit hlam hω hs d
  obtain ⟨seq, hseq, hlim, hbulk, hpair⟩ := mixed_normal_and_pairing_levels hlam hω hs d
    (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN))
  let A := ∑ k ∈ Finset.range 4, ∫ t, (canonicalProfile lam (contStream ω ∘ cellArc k) t *
    conj (contStream ω (cellArc k t))).re
  have hseq' : Tendsto seq atTop (𝓝[Ioo 0 1 \ N] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, .of_forall hseq⟩
  have hc : Tendsto (fun n ↦ 2 - 2 * seq n) atTop (𝓝 2) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hlim.const_mul (2 : ℝ))
  have hb : Tendsto (fun n ↦ eeLevelTerm ω (seq n)) atTop (𝓝 (2 * L - 2 * A)) := by
    apply ((hlevel.comp hseq').sub (hc.mul hpair)).congr
    intro n
    dsimp only [Function.comp_apply, eeLevelTerm, mixedGeometricLevelTerm]
    ring
  rw [tendsto_nhds_unique hbulk hb]
  refine ⟨mixed_normal_virial_integrable d, ?_⟩
  have hpairCut := (mixed_canonical_pairing_cutoff_limit (lam := lam) d).2
  have h := (hcut.sub hpairCut).const_mul (2 : ℝ)
  rw [mul_sub] at h
  exact h.congr (fun T ↦ by rw [mixed_paired_flux_split d T])

/-- The mixed-field virial. The boundary profile in the paired expression is
the physical vorticity trace by `mixed_boundary_square_traces`. -/
theorem mixed_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedVirialDensity d q)) := by
  refine ⟨(mixed_rellich_volume_integrable d).1, ?_⟩
  rw [mixed_tangential_virial hlam hω hs d]
  exact (mixed_paired_flux hlam hω hs d).2

/-- Static identity and its sign for the original mixed eigenproblem. -/
theorem mixed_static_identity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    0 = mixedStaticForm d + (∑ σ : Bool, ∫ x in Ioo (-1) 1,
      boundaryWeight x * ‖mixedBoundarySquare lam (mixedNeumannF lam d.phi σ) x‖ ^ 2) ∧
    mixedStaticForm d ≤ 0 := by
  let square (σ : Bool) : ℝ := ∫ x in Ioo (-1) 1,
    boundaryWeight x * ‖mixedBoundarySquare lam (mixedNeumannF lam d.phi σ) x‖ ^ 2
  let corner (σ : Bool) : ℝ := ∑ a : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal σ)‖ ^ 2
  let edge (σ : Bool) (T : ℝ) : ℝ := 2 * mixedNeumannFluxCutoff lam d.phi σ T -
    ∫ t in Ioo (-T) T, ‖d.phi (diagCoord (mixedNeumannArc σ t))‖ ^ 2
  have hEdge (σ : Bool) : Tendsto (edge σ) atTop (𝓝 (square σ - corner σ)) := by
    have h := mixed_neumann_flux_renormalized hlam hω hs d σ
    dsimp only at h
    rw [(mixed_boundary_square_traces hlam hω hs d σ).2.2.2.2.2.2.2.2.2.1] at h
    exact h
  have hSum : Tendsto (fun T ↦ ∑ σ : Bool, edge σ T) atTop
      (𝓝 (∑ σ : Bool, (square σ - corner σ))) := by
    simp only [Fintype.sum_bool]
    exact (hEdge true).add (hEdge false)
  have hlim := (mixed_trace_mass d).2.2.2.sub hSum
  have hCutoff (T : ℝ) :
      mixedTraceMassCutoff d.phi T - (∑ σ : Bool, edge σ T) =
        2 * mixedPairedFluxCutoff lam d.phi T := by
    simp only [mixedTraceMassCutoff, mixedPairedFluxCutoff, edge, mixedNeumannArc,
      Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, div_eq_mul_inv, integral_mul_const]
    ring
  have hEq := tendsto_nhds_unique (mixed_virial hlam hω hs d).2
    (hlim.congr (fun T ↦ hCutoff T))
  have hCorners : (∑ σ : Bool, corner σ) =
      ∑ a : Bool, ∑ b : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal b)‖ ^ 2 :=
    Finset.sum_comm
  rw [Finset.sum_sub_distrib, hCorners] at hEq
  have hId : 0 = mixedStaticForm d + ∑ σ : Bool, square σ := by
    unfold mixedStaticForm
    linarith only [hEq]
  refine ⟨hId, ?_⟩
  have hNonneg : 0 ≤ ∑ σ : Bool, square σ := by
    apply Finset.sum_nonneg
    intro σ _
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))]
      with x hx
    have hw : 0 ≤ boundaryWeight x := by
      unfold boundaryWeight
      have hl : 0 ≤ x + 1 := by linarith [hx.1]
      have hr : 0 ≤ 1 - x := by linarith [hx.2]
      nlinarith only [mul_nonneg hl hr]
    exact mul_nonneg hw (sq_nonneg _)
  linarith only [hId, hNonneg]

end NoEmbeddedEigenvalues
