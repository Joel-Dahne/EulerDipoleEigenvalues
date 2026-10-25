import NoEmbeddedEigenvalues.EvenEven
import NoEmbeddedEigenvalues.DipoleOrthogonality
import NoEmbeddedEigenvalues.CorrectedBoundaryForm

/-!
# Odd–odd exclusion: the final analytic interfaces

The exclusion is assembled from the quotient domain, orthogonality, the Picone current,
bulk coercivity and corrected interval positivity. The analytic interfaces have explicit
Sobolev domains, representatives and integrability conclusions. Their proofs are separate
from the algebraic and measure-theoretic assembly.

The bulk uses specified Fourier first derivatives, not pointwise derivatives of an arbitrary
Sobolev representative. Arc values use the continuous representative of the H² quotient.
Endpoint conditions use interval H¹ traces, never raw endpoint values. Boundary regularity
uses the even H² arc theorem and the abstract canonical-profile theorem. The quotient's
rotation character extends through the separatrix by continuity.

Picone uses the actual outward current on `Ψ = ε`, represented by orbit parameter `ε/2`.
The bulk and current renormalizations use one common counterterm, including the same
corner multiplicities. Absolute integrability is a separate input from their cancellation;
no residual sign certificate or corrected-form positivity is used in the current assembly.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

/-- The weight `μ = Ψ²` on the lifted positive cell. -/
def ddWeight (p : ℝ × ℝ) : ℝ := dipoleLift p ^ 2

/-- The potential coefficient `F = s(8-s³)δ²/(3r²)`, with `r = |∇s|²`. -/
def ddF (p : ℝ × ℝ) : ℝ :=
  dipoleLift p * (8 - dipoleLift p ^ 3) * (Real.cos p.1 - Real.cos p.2) ^ 2 /
    (3 * gradSq dipoleLift p ^ 2)

/-- The tangential eigenvalue of `M`. -/
def ddC (p : ℝ × ℝ) : ℝ :=
  dipoleLift p * (8 - dipoleLift p ^ 3) / (3 * gradSq dipoleLift p)

/-- The normal eigenvalue of `M`. -/
def ddA (p : ℝ × ℝ) : ℝ :=
  2 * dipoleLift p ^ 2 / 3 + 32 / (3 * dipoleLift p) - ddC p

/-- The Cartesian entries of the real symmetric Picone matrix. Values at its singular
    points are totalized by real division and do not specify limiting values there. -/
def ddMxx (p : ℝ × ℝ) : ℝ :=
  ddC p + (ddA p - ddC p) * Real.sin p.1 ^ 2 / gradSq dipoleLift p

def ddMxy (p : ℝ × ℝ) : ℝ :=
  (ddA p - ddC p) * Real.sin p.1 * Real.sin p.2 / gradSq dipoleLift p

def ddMyy (p : ℝ × ℝ) : ℝ :=
  ddC p + (ddA p - ddC p) * Real.sin p.2 ^ 2 / gradSq dipoleLift p

/-- `⟨M∇u,∇u⟩` for a complex gradient supplied explicitly. -/
def ddMatrixForm (p : ℝ × ℝ) (vx vy : ℂ) : ℝ :=
  ddA p * ‖normalDeriv (fun _ ↦ vx) (fun _ ↦ vy) p‖ ^ 2 +
    ddC p * ‖tangentDeriv (fun _ ↦ vx) (fun _ ↦ vy) p‖ ^ 2

/-- The logarithmic comparison function; `Real.log 0 = 0` gives the continuous value
    of the factor `r² log(r/2)` at `r = 0`. -/
def ddGround (p : ℝ × ℝ) : ℝ :=
  1 + (gradSq dipoleLift p + dipoleLift p ^ 2) / 16 -
    gradSq dipoleLift p ^ 2 / 256 * Real.log (gradSq dipoleLift p / 2)

/-- `Pw = -div(M∇w) - Fw`, differentiated only for the explicit comparison function. -/
def ddGroundResidual (p : ℝ × ℝ) : ℝ :=
  -(partialX (fun q ↦ ddMxx q * partialX ddGround q + ddMxy q * partialY ddGround q) p +
    partialY (fun q ↦ ddMxy q * partialX ddGround q + ddMyy q * partialY ddGround q) p) -
    ddF p * ddGround p

/-- The quotient-rule gradient of `φ/w`, for specified weak derivatives of `φ`. -/
def ddDividedPartial (φ d : L2) (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  liftL2 d p / (ddGround p : ℂ) -
    liftL2 φ p * (coordPartial (E := ℝ) j ddGround p : ℂ) / (ddGround p : ℂ) ^ 2

/-- The nonnegative Picone gradient density. -/
def ddPiconeGradient (φ dx dy : L2) (p : ℝ × ℝ) : ℝ :=
  ddGround p ^ 2 * ddMatrixForm p (ddDividedPartial φ dx 0 p) (ddDividedPartial φ dy 1 p)

/-- The Picone potential density, whose sign need not be positive. -/
def ddPiconePotential (φ : L2) (p : ℝ × ℝ) : ℝ :=
  ddGroundResidual p / ddGround p * ‖liftL2 φ p‖ ^ 2

/-- The vorticity term `F|ν|² = F|Eφ|²`. -/
def ddVorticityDensity (ν : L2) (p : ℝ × ℝ) : ℝ := ddF p * ‖liftL2 ν p‖ ^ 2

/-- The mass density controlled by the final coercivity estimate. -/
def ddMassDensity (φ : L2) (p : ℝ × ℝ) : ℝ := ddWeight p * ‖liftL2 φ p‖ ^ 2

/-- Quotient conclusions used by the final exclusion. Weighted corner remainders are
    deliberately not part of this interface. -/
structure DDQuotientData (lam : ℝ) (ω : L2) where
  phi : L2
  nu : L2
  regular : MemSobolev 2 phi
  even : InSector true true phi
  stream_eq : ∀ᵐ t, invLap ω t = (Ψ t : ℂ) * phi t
  vorticity_eq : ∀ᵐ t, ω t = (Ψ t : ℂ) * nu t
  transport : IsTransportPair lam cellNeighbourhood (liftL2 nu)
    (fun p ↦ continuousRep phi (torusProj p))
  weighted_nu : MemLp (fun p ↦ liftL2 nu p / (saddleDist p : ℂ)) 2
    (volume.restrict cellNeighbourhood)

/-- Existence of the minimal quotient data consumed by exclusion
    (`cor:dd-exclusion-domain`), without the stronger corner-jet conclusions. -/
theorem dd_exclusion_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    Nonempty (DDQuotientData lam ω) := by
  sorry

/-- Weighted mean zero and central parity of the quotient. -/
theorem dd_orthogonality {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) :
    (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 q.phi p) = 0 ∧
      centralInversion q.phi = q.phi := by
  constructor
  · have hv := hω.integral_dipole_mul_eq_zero hlam
    have hψ : (∫ t, (Ψ t : ℂ) * invLap ω t) = 0 := by
      rw [integral_dipole_mul_invLap, hv, neg_zero]
    have hsψ := hs.invLap
    have hodd : reflect₁ (invLap ω) = -invLap ω := by simpa [paritySign] using hsψ.1
    have hcell := (integral_dipole_mul_eq_two_cell (invLap ω) hodd).symm.trans hψ
    have hz : (∫ p in cellSquare, (dipoleLift p : ℂ) * liftL2 (invLap ω) p) = 0 :=
      (mul_eq_zero.mp hcell).resolve_left (by norm_num)
    rw [← hz]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_torusProj q.stream_eq)] with p hp
    dsimp only [liftL2] at hp ⊢
    rw [hp, Ψ_torusProj]
    simp only [ddWeight, Complex.ofReal_pow]
    ring
  · exact (rotate_rotate q.phi).symm.trans q.even.rotate_rotate

/-- Continuous quotient trace on an oriented cell edge. -/
def ddArcTrace (φ : L2) (k : Fin 4) (t : ℝ) : ℂ :=
  continuousRep φ (torusProj (cellArc k t))

/-- Canonical boundary unknown in the interval coordinate. -/
def ddBoundaryUnknown (lam : ℝ) (φ : L2) (k : Fin 4) (x : ℝ) : ℂ :=
  canonicalUnknown lam (ddArcTrace φ k) (Real.artanh x)

/-- Boundary domains, endpoint characters and the identification of the transformed
    boundary forcing with the actual quotient trace. No energy inequality is a field. -/
structure DDBoundaryData (lam : ℝ) (κ : Bool) (φ : L2) where
  first : Fin 4 → ℝ → ℂ
  second : Fin 4 → ℝ → ℂ
  regular : ∀ k, HasWeightedBoundaryH2 (ddBoundaryUnknown lam φ k) (first k) (second k)
  endpoints : ∀ k, intervalH1Extension (-1) 1 (ddBoundaryUnknown lam φ k) (first k) 1 =
    paritySign κ * intervalH1Extension (-1) 1 (ddBoundaryUnknown lam φ k) (first k) (-1)
  trace_eq : ∀ k, ∀ᵐ x ∂(volume.restrict (Ioo (-1) 1)),
    correctedBoundaryTrace lam (ddBoundaryUnknown lam φ k) (first k) x =
      ddArcTrace φ k (Real.artanh x)

/-- The quotient multiplication identity holds pointwise for the continuous representatives. -/
theorem DDQuotientData.contStream_eq {lam : ℝ} {ω : L2} (q : DDQuotientData lam ω)
    (p : ℝ × ℝ) :
    contStream ω p = (dipoleLift p : ℂ) * continuousRep q.phi (torusProj p) := by
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  have ha : contStream ω =ᵐ[volume]
      (fun p ↦ (dipoleLift p : ℂ) * continuousRep q.phi (torusProj p)) := by
    filter_upwards [ae_torusProj q.stream_eq,
      ae_torusProj (coeFn_eq_continuousRep q.regular), streamLift_ae_eq_contStream ω]
      with p hp hφ hψ
    change invLap ω (torusProj p) = contStream ω p at hψ
    rw [← hψ, hp, hφ, Ψ_torusProj]
  exact congrFun (Measure.eq_of_ae_eq ha (continuous_contStream ω)
    ((Complex.continuous_ofReal.comp (by unfold dipoleLift; fun_prop)).mul hc)) p

/-- Division by the rotation-invariant dipole preserves the character, including on
    the separatrix by continuity. No pointwise division by zero is used. -/
theorem DDQuotientData.continuousRep_rotLift {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) (p : ℝ × ℝ) :
    continuousRep q.phi (torusProj (rotLift p)) =
      paritySign κ * continuousRep q.phi (torusProj p) := by
  have hn : ∀ᵐ p : ℝ × ℝ, dipoleLift p ≠ 0 := by
    have hm := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (0, Real.pi)
    have h := hm.quasiMeasurePreserving.ae ae_cos_fst_ne_cos_snd
    filter_upwards [h] with p hp
    simp only [Prod.fst_add, Prod.snd_add, add_zero, Real.cos_add_pi] at hp
    unfold dipoleLift
    intro hz
    apply hp
    linarith
  have hprod (p : ℝ × ℝ) : (dipoleLift p : ℂ) *
      continuousRep q.phi (torusProj (rotLift p)) =
      (dipoleLift p : ℂ) * (paritySign κ * continuousRep q.phi (torusProj p)) := by
    have h := contStream_rotLift hκ p
    rw [q.contStream_eq, q.contStream_eq] at h
    have hR : dipoleLift (rotLift p) = dipoleLift p := by
      simp [dipoleLift, rotLift, Real.cos_neg, add_comm]
    rw [hR] at h
    linear_combination h
  have ha : (fun p ↦ continuousRep q.phi (torusProj (rotLift p))) =ᵐ[volume]
      (fun p ↦ paritySign κ * continuousRep q.phi (torusProj p)) := by
    filter_upwards [hn] with p hp
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hp) (hprod p)
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  exact congrFun (Measure.eq_of_ae_eq ha (hc.comp (by unfold rotLift; fun_prop))
    (continuous_const.mul hc)) p

/-- Pointwise iteration of the quotient's rotation character. -/
theorem DDQuotientData.continuousRep_iterate_rotLift {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) (k : ℕ)
    (p : ℝ × ℝ) : continuousRep q.phi (torusProj (rotLift^[k] p)) =
      paritySign κ ^ k * continuousRep q.phi (torusProj p) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply, ih, q.continuousRep_rotLift hκ, pow_succ]
    ring

/-- The supplied quotient transport pair has zero Melnikov integral on every cell arc. -/
theorem DDQuotientData.arc_melnikov {lam : ℝ} {ω : L2} (q : DDQuotientData lam ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) (k : ℕ) :
    Integrable (deriv (fun s ↦ continuousRep q.phi (torusProj (cellArc k s)))) ∧
      (∫ t, profileIntegrand lam
        (fun s ↦ continuousRep q.phi (torusProj (cellArc k s))) t) = 0 := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hfR : ∀ p ∈ cellNeighbourhood, continuousRep q.phi (torusProj (p.2, -p.1)) =
      c * continuousRep q.phi (torusProj p) := by
    intro p _
    rw [hcc]
    exact q.continuousRep_rotLift hκ p
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  obtain ⟨hg, hM⟩ := melnikov q.transport closure_cellSquare_subset_cellNeighbourhood hc hUR hfR
    ((continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous).continuousOn
  simp only [Function.comp_def] at hg hM
  have hArc : (fun s ↦ continuousRep q.phi (torusProj (cellArc k s))) =
      fun s ↦ paritySign κ ^ k * continuousRep q.phi (torusProj (separatrixArc s)) :=
    funext fun s ↦ q.continuousRep_iterate_rotLift hκ k (separatrixArc s)
  rw [hArc]
  refine ⟨by simpa only [deriv_const_mul_field'] using hg.const_mul (paritySign κ ^ k), ?_⟩
  simp only [profileIntegrand, deriv_const_mul_field', mul_assoc, integral_const_mul]
  simp only [profileIntegrand, mul_assoc] at hM
  rw [hM, mul_zero]

/-- The canonical profiles of the quotient have the interval domain needed for corrected
    positivity; this is a separate input from the Picone current identity. -/
theorem dd_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) :
    Nonempty (DDBoundaryData lam κ q.phi) := by
  classical
  have hc : Continuous (fun p ↦ continuousRep q.phi (torusProj p)) :=
    (continuousRep q.phi).continuous.comp isOpenQuotientMap_torusProj.continuous
  let cp (k : Fin 4) := continuousRep q.phi (torusProj (rotLift^[k.val] (0, -Real.pi)))
  let cm (k : Fin 4) := continuousRep q.phi (torusProj (rotLift^[k.val] (Real.pi, 0)))
  have hRc (k : Fin 4) : Continuous
      (fun p ↦ continuousRep q.phi (torusProj (rotLift^[k.val] p))) :=
    hc.comp (Continuous.iterate (by unfold rotLift; fun_prop) k.val)
  have hgp (k : Fin 4) : Tendsto (ddArcTrace q.phi k) atTop (𝓝 (cp k)) :=
    ((hRc k).tendsto _).comp tendsto_separatrixArc_atTop
  have hgm (k : Fin 4) : Tendsto (ddArcTrace q.phi k) atBot (𝓝 (cm k)) :=
    ((hRc k).tendsto _).comp tendsto_separatrixArc_atBot
  have ha (k : Fin 4) := even_sobolev_arc_regularity q.regular q.even k.isLt
  have hm (k : Fin 4) := q.arc_melnikov hκ k.val
  have hr (k : Fin 4) := canonical_boundary_regularity hlam (ha k).1 (ha k).2.1
    (hm k).1 (ha k).2.2 (fun s ↦ (continuousRep q.phi).norm_coe_le_norm _)
    (hm k).2 (hgp k) (hgm k)
  choose D E hW hG ht hp hm using hr
  have hchar (k : Fin 4) : cp k = paritySign κ * cm k := by
    dsimp only [cp, cm]
    rw [show ((0 : ℝ), -Real.pi) = rotLift (Real.pi, 0) by simp [rotLift],
      ← Function.iterate_succ_apply, Function.iterate_succ_apply', q.continuousRep_rotLift hκ]
  have hArc (k : Fin 4) : ddArcTrace q.phi k =
      (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) := rfl
  have hUnknown (k : Fin 4) : ddBoundaryUnknown lam q.phi k =
      (fun ξ ↦ canonicalUnknown lam
        (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) (Real.artanh ξ)) := by
    funext ξ
    rw [ddBoundaryUnknown, hArc]
  refine ⟨⟨D, E, ?_, ?_, ?_⟩⟩
  · intro k
    rw [hUnknown k]
    exact hW k
  · intro k
    rw [hUnknown k, hp k, hm k, hchar k]
    ring
  · intro k
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ by
      simp only [correctedBoundaryTrace, hUnknown k, hArc k]
      exact ht k x hx

/-! ### Truncations, finite parts and the ground-state current -/

/-- The lifted positive cell above the actual stream level `ε` (not the orbit parameter). -/
def ddTruncatedCell (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ cellSquare ∧ ε < dipoleLift p}

/-- The untransformed gradient/potential energy. -/
def ddRawEnergy (φ dx dy : L2) (p : ℝ × ℝ) : ℝ :=
  ddMatrixForm p (liftL2 dx p) (liftL2 dy p) - ddF p * ‖liftL2 φ p‖ ^ 2

/-- The truncated virial bulk, including the vorticity term. -/
def ddRawBulk (φ ν dx dy : L2) (ε : ℝ) : ℝ :=
  ∫ p in ddTruncatedCell ε, ddVorticityDensity ν p + ddRawEnergy φ dx dy p

/-- The three separate ordinary integrals after the Picone transformation. -/
def ddPiconeBulk (φ ν dx dy : L2) (ε : ℝ) : ℝ :=
  (∫ p in ddTruncatedCell ε, ddVorticityDensity ν p) +
    (∫ p in ddTruncatedCell ε, ddPiconeGradient φ dx dy p) +
    ∫ p in ddTruncatedCell ε, ddPiconePotential φ p

/-- The two actual saddle endpoint values of a lifted arc. -/
def ddArcEnd (φ : L2) (k : Fin 4) (positive : Bool) : ℂ :=
  continuousRep φ (torusProj (rotLift^[k.val]
    (if positive then (0, -Real.pi) else (Real.pi, 0))))

/-- Half the endpoint sum: each of the four lifted corners is incident to two arcs.
    The two torus saddles are counted with their lifted multiplicities. -/
def ddCornerMass (φ : L2) : ℝ :=
  (1 / 2 : ℝ) * ∑ k : Fin 4, (‖ddArcEnd φ k false‖ ^ 2 + ‖ddArcEnd φ k true‖ ^ 2)

/-- Arc value mass with its two endpoint constants removed. The choice at `t = 0`
    is immaterial for integration. -/
def ddArcValueRemainder (φ : L2) (k : Fin 4) (t : ℝ) : ℝ :=
  ‖ddArcTrace φ k t‖ ^ 2 -
    if t < 0 then ‖ddArcEnd φ k false‖ ^ 2 else ‖ddArcEnd φ k true‖ ^ 2

/-- The value finite part for truncation by `Ψ = ε`, including its `log 8` constant. -/
def ddValueFinitePart (φ : L2) : ℝ :=
  (∑ k : Fin 4, ∫ t, ddArcValueRemainder φ k t) + Real.log 8 * ddCornerMass φ

/-- The identical counterterm used for the virial bulk and the boundary current. -/
def ddLogCounterterm (φ : L2) (ε : ℝ) : ℝ :=
  (8 / 3 : ℝ) * ddCornerMass φ * Real.log (1 / ε)

/-- The comparison function restricted to `s = 0`. -/
def ddBoundaryGround (r : ℝ) : ℝ := 1 + r / 16 - r ^ 2 / 256 * Real.log (r / 2)

/-- The explicit boundary coefficient, in expanded rational/logarithmic form. -/
def ddBoundaryB (r : ℝ) : ℝ :=
  (5 * r / 16 + r / 256 * ((32 - 25 * r) * Real.log (r / 2) + 16 - 12 * r)) /
    ddBoundaryGround r

/-- The actual outward Picone current coefficient in flow time. The outward normal of
    `C_ε` is `-∇Ψ/|∇Ψ|`, so the coefficient has a minus sign. -/
def ddGroundCurrentCoeff (p : ℝ × ℝ) : ℝ :=
  -ddA p * (partialX dipoleLift p * partialX ddGround p +
    partialY dipoleLift p * partialY ddGround p) / ddGround p

/-- Level value mass. `levelIntegral h` is on `Ψ = 2h`, hence the argument `ε/2`. -/
def ddLevelMass (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- The `B`-weighted value mass on the same level. -/
def ddLevelBMass (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ddBoundaryB (gradSq dipoleLift p) *
    ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- The actual level current, using continuous values rather than raw L² representatives. -/
def ddGroundCurrent (φ : L2) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦ ddGroundCurrentCoeff p *
    ‖continuousRep φ (torusProj p)‖ ^ 2)

/-- On a separatrix arc, `r = 2 sech² t`. -/
def ddArcCorrection (φ : L2) (k : Fin 4) (t : ℝ) : ℝ :=
  ddBoundaryB (2 / Real.cosh t ^ 2) * ‖ddArcTrace φ k t‖ ^ 2

/-- Absolute integrability from `ν/d ∈ L²`, independently of the eigenvalue equation. -/
theorem dd_vorticityDensity_integrable (ν : L2)
    (hν : MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood)) :
    IntegrableOn (ddVorticityDensity ν) cellSquare := by
  sorry

/-- The even boundary Hardy estimate controls the original and divided gradient energies. -/
theorem dd_gradient_energies_integrable {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) (hdx : HasFourierPartial 0 φ dx)
    (hdy : HasFourierPartial 1 φ dy) :
    IntegrableOn (fun p ↦ ddMatrixForm p (liftL2 dx p) (liftL2 dy p)) cellSquare ∧
      IntegrableOn (ddPiconeGradient φ dx dy) cellSquare := by
  sorry

/-- Integrability of the actual differentiated residual, not a sign certificate for it. -/
theorem dd_piconePotential_integrable {φ : L2} (hφ : MemSobolev 2 φ) :
    IntegrableOn (ddPiconePotential φ) cellSquare := by
  sorry

/-- Sobolev Picone on every positive truncation, with bulk and current integrability.
    The center is included; its removal and limiting argument belong to this input. -/
theorem dd_truncated_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (ddRawEnergy φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconeGradient φ dx dy) (ddTruncatedCell ε) ∧
      IntegrableOn (ddPiconePotential φ) (ddTruncatedCell ε) ∧
      IntervalIntegrable (fun t ↦ ddGroundCurrentCoeff (dipoleOrbit (ε / 2) t) *
        ‖continuousRep φ (torusProj (dipoleOrbit (ε / 2) t))‖ ^ 2)
        volume 0 (orbitPeriod (ε / 2)) ∧
      (∫ p in ddTruncatedCell ε, ddRawEnergy φ dx dy p) =
        (∫ p in ddTruncatedCell ε, ddPiconeGradient φ dx dy p) +
          (∫ p in ddTruncatedCell ε, ddPiconePotential φ p) + ddGroundCurrent φ ε := by
  sorry

/-- Character-wise renormalized virial for supplied quotient data. This is a full bulk
    limit; pairing convergence along good levels is sufficient to identify it. -/
theorem dd_character_virial_limit {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    Tendsto (fun ε ↦ ddRawBulk q.phi q.nu dx dy ε + ddLogCounterterm q.phi ε)
      (𝓝[>] 0) (𝓝 (-(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) + ddValueFinitePart q.phi))) := by
  sorry

/-- The scalar value finite part and absolute integrability of its renormalized arc terms. -/
theorem dd_value_finite_part {φ : L2} (hφ : MemSobolev 2 φ) :
    (∀ k : Fin 4, Integrable (ddArcValueRemainder φ k)) ∧
      Tendsto (fun ε ↦ ddLevelMass φ ε - ddCornerMass φ * Real.log (1 / ε))
        (𝓝[>] 0) (𝓝 (ddValueFinitePart φ)) := by
  sorry

/-- The logarithmic `B` weight is integrable on every arc and has a full level limit. -/
theorem dd_boundaryB_trace_limit {φ : L2} (hφ : MemSobolev 2 φ) :
    (∀ k : Fin 4, Integrable (ddArcCorrection φ k)) ∧
      Tendsto (ddLevelBMass φ) (𝓝[>] 0)
        (𝓝 (∑ k : Fin 4, ∫ t, ddArcCorrection φ k t)) := by
  sorry

/-- The error in replacing the actual current coefficient by `-(8/3)(1-B)` integrates
    to zero: the uniform `O(ε)` coefficient error times the logarithmic period vanishes. -/
theorem dd_current_remainder_limit {φ : L2} (hφ : MemSobolev 2 φ) :
    Tendsto (fun ε ↦ ddGroundCurrent φ ε + (8 / 3 : ℝ) * ddLevelMass φ ε -
      (8 / 3 : ℝ) * ddLevelBMass φ ε) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- The boundary comparison function is positive on the geometric range of `r`. -/
theorem ddBoundaryGround_pos {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    0 < ddBoundaryGround r := by
  have hl : Real.log (r / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hmul : r ^ 2 / 256 * Real.log (r / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hl
  unfold ddBoundaryGround
  linarith

/-- Explicit derivative of the one-dimensional boundary comparison function. -/
theorem hasDerivAt_ddBoundaryGround {r : ℝ} (hr : 0 < r) :
    HasDerivAt ddBoundaryGround
      (1 / 16 - r / 128 * Real.log (r / 2) - r / 256) r := by
  have hlog := ((hasDerivAt_id r).div_const 2).log (by positivity : r / 2 ≠ 0)
  have h := ((hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).div_const 16)).sub
    ((((hasDerivAt_id r).pow 2).div_const 256).mul hlog)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    field_simp [hr.ne']
    ring

/-- The expanded coefficient agrees with the derivative formula for the boundary current. -/
theorem ddBoundaryB_eq {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ddBoundaryB r = 1 - 4 * (r / 8 + (4 - 3 * r) * deriv ddBoundaryGround r) /
      ddBoundaryGround r := by
  rw [(hasDerivAt_ddBoundaryGround hr).deriv]
  dsimp only [ddBoundaryB]
  field_simp [(ddBoundaryGround_pos hr hr2).ne']
  unfold ddBoundaryGround
  ring

/-- The explicit expanded boundary coefficient has exactly the normalization used in β. -/
theorem ddBoundaryB_two_weight (x : ℝ) :
    ddBoundaryB (2 * boundaryWeight x) = boundaryWeight x * correctedBoundaryBeta x := by
  have h : 2 * boundaryWeight x / 2 = boundaryWeight x := by ring
  dsimp only [ddBoundaryB, ddBoundaryGround, correctedBoundaryBeta]
  rw [h]
  ring_nf

/-- The arc correction in flow time is the Jacobian-weighted interval correction. -/
theorem ddBoundaryB_cosh (t : ℝ) : ddBoundaryB (2 / Real.cosh t ^ 2) =
    (1 / Real.cosh t ^ 2) * correctedBoundaryBeta (Real.tanh t) := by
  rw [show 2 / Real.cosh t ^ 2 = 2 * boundaryWeight (Real.tanh t) by
    rw [boundaryWeight_tanh]; ring, ddBoundaryB_two_weight, boundaryWeight_tanh]

/-- Renormalizing the actual current uses the very same counterterm as the virial bulk. -/
theorem dd_ground_current_limit {φ : L2} (hφ : MemSobolev 2 φ) :
    Tendsto (fun ε ↦ ddGroundCurrent φ ε + ddLogCounterterm φ ε) (𝓝[>] 0)
      (𝓝 (-(8 / 3 : ℝ) * (ddValueFinitePart φ -
        ∑ k : Fin 4, ∫ t, ddArcCorrection φ k t))) := by
  have h := ((dd_current_remainder_limit hφ).sub
    ((dd_value_finite_part hφ).2.const_mul (8 / 3 : ℝ))).add
      ((dd_boundaryB_trace_limit hφ).2.const_mul (8 / 3 : ℝ))
  convert h using 1
  · funext ε
    dsimp only [ddLogCounterterm]
    ring
  · congr 1
    ring

/-- Integrable functions converge under exhaustion by the actual stream levels. This is
    dominated convergence and does not assume any sign of the integrand. -/
theorem tendsto_ddTruncatedCell_integral {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f cellSquare) :
    Tendsto (fun ε ↦ ∫ p in ddTruncatedCell ε, f p) (𝓝[>] 0)
      (𝓝 (∫ p in cellSquare, f p)) := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hm (ε : ℝ) : MeasurableSet {p : ℝ × ℝ | ε < dipoleLift p} :=
    measurableSet_lt measurable_const (by unfold dipoleLift; fun_prop)
  have hrep (ε : ℝ) : (∫ p in ddTruncatedCell ε, f p) =
      ∫ p in cellSquare, {p | ε < dipoleLift p}.indicator f p := by
    rw [setIntegral_indicator (hm ε)]
    rfl
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict cellSquare)
    (F := fun ε ↦ {p | ε < dipoleLift p}.indicator f) (f := f) (fun p ↦ ‖f p‖)
    (Eventually.of_forall fun ε ↦ hf.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ {p | ε < dipoleLift p}
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp, norm_zero]
        exact norm_nonneg _)
    hf.norm (by
      filter_upwards [ae_restrict_mem hcell] with p hp
      have hs : 0 < dipoleLift p := by
        simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < dipoleLift p :=
        nhdsWithin_le_nhds (Iio_mem_nhds hs)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with ε hε
      rw [indicator_of_mem (show p ∈ {p | ε < dipoleLift p} from hε)])
  exact h.congr' (Eventually.of_forall fun ε ↦ (hrep ε).symm)

/-- Changing variables in the correction preserves absolute integrability and identifies
    the actual canonical forcing supplied by the boundary data. No positivity is used. -/
theorem dd_boundary_correction_eq {lam : ℝ} {κ : Bool} {φ : L2}
    (b : DDBoundaryData lam κ φ) (k : Fin 4) :
    IntegrableOn (correctedBoundaryTerm lam (ddBoundaryUnknown lam φ k) (b.first k))
      (Ioo (-1) 1) ∧
      (∫ t, ddArcCorrection φ k t) =
        ∫ x in (-1 : ℝ)..1, correctedBoundaryTerm lam
          (ddBoundaryUnknown lam φ k) (b.first k) x := by
  have ha := ae_comp_tanh ((ae_restrict_iff' measurableSet_Ioo).1 (b.trace_eq k))
  have ht : ∀ᵐ t, correctedBoundaryTrace lam (ddBoundaryUnknown lam φ k) (b.first k)
      (Real.tanh t) = ddArcTrace φ k t := by
    filter_upwards [ha] with t ht
    simpa only [Real.artanh_tanh] using ht ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  have he : (fun t ↦ (1 / Real.cosh t ^ 2) • correctedBoundaryTerm lam
      (ddBoundaryUnknown lam φ k) (b.first k) (Real.tanh t)) =ᵐ[volume] ddArcCorrection φ k := by
    filter_upwards [ht] with t ht
    simp only [smul_eq_mul, correctedBoundaryTerm, ht, ddArcCorrection, ddBoundaryB_cosh]
    ring
  refine ⟨(b.regular k).integrable_correctedBoundaryTerm lam, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_tanh_subst]
  exact (integral_congr_ae he).symm

/-- The canonical arc form is the uncorrected interval form for the specified derivatives. -/
theorem DDQuotientData.canonicalArcForm_eq_boundaryForm {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hlam : lam ≠ 0) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (b : DDBoundaryData lam κ q.phi) (k : Fin 4) :
    canonicalArcForm lam (ddArcTrace q.phi k) =
      boundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  have hg := (q.arc_melnikov hκ k.val).1
  have he := (even_sobolev_arc_regularity q.regular q.even k.isLt).2.2
  have hArc : ddArcTrace q.phi k =
      (fun s ↦ continuousRep q.phi (torusProj (cellArc k.val s))) := rfl
  rw [← hArc] at hg he
  have hUnknown : ddBoundaryUnknown lam q.phi k =
      (fun ξ ↦ canonicalUnknown lam (ddArcTrace q.phi k) (Real.artanh ξ)) := rfl
  have hw := b.regular k
  rw [hUnknown] at hw ⊢
  exact (canonicalArcForm_eq_flowBoundaryForm hlam hg he hw).trans (hw.flowBoundaryForm_eq lam)

/-- Identification with the corrected interval form for arbitrary supplied boundary data. -/
theorem DDQuotientData.correctedBoundaryForm_eq {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hlam : lam ≠ 0) {κ : Bool}
    (hκ : InRotationCharacter κ ω) (b : DDBoundaryData lam κ q.phi) (k : Fin 4) :
    canonicalArcForm lam (ddArcTrace q.phi k) + (∫ t, ddArcCorrection q.phi k t) =
      correctedBoundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  rw [q.canonicalArcForm_eq_boundaryForm hlam hκ b k,
    (dd_boundary_correction_eq b k).2]
  rfl

/-- Ordinary-integral Picone identity after cancellation of the corner finite parts. -/
theorem dd_picone_current {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω)
    (b : DDBoundaryData lam κ q.phi) {dx dy : L2}
    (hdx : HasFourierPartial 0 q.phi dx) (hdy : HasFourierPartial 1 q.phi dy) :
    IntegrableOn (ddVorticityDensity q.nu) cellSquare ∧
      IntegrableOn (ddPiconeGradient q.phi dx dy) cellSquare ∧
      IntegrableOn (ddPiconePotential q.phi) cellSquare ∧
      (∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
        (∫ p in cellSquare, ddPiconePotential q.phi p) =
      -(8 / 3 : ℝ) * ∑ k : Fin 4,
        correctedBoundaryForm lam (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
  have hv := dd_vorticityDensity_integrable q.nu q.weighted_nu
  obtain ⟨_, hg⟩ := dd_gradient_energies_integrable q.regular q.even hdx hdy
  have hp := dd_piconePotential_integrable q.regular
  refine ⟨hv, hg, hp, ?_⟩
  have hBulk : Tendsto (ddPiconeBulk q.phi q.nu dx dy) (𝓝[>] 0)
      (𝓝 ((∫ p in cellSquare, ddVorticityDensity q.nu p) +
        (∫ p in cellSquare, ddPiconeGradient q.phi dx dy p) +
          ∫ p in cellSquare, ddPiconePotential q.phi p)) :=
    ((tendsto_ddTruncatedCell_integral hv).add
      (tendsto_ddTruncatedCell_integral hg)).add (tendsto_ddTruncatedCell_integral hp)
  have h := (dd_character_virial_limit hlam hω hs q hκ hdx hdy).sub
    (dd_ground_current_limit q.regular)
  have hLevel := h.congr' (f₂ := ddPiconeBulk q.phi q.nu dx dy) (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with ε hε
    obtain ⟨hr, _, _, _, ht⟩ := dd_truncated_picone q.regular hdx hdy hε
    have hvε := hv.mono_set (show ddTruncatedCell ε ⊆ cellSquare from fun _ hp ↦ hp.1)
    dsimp only [ddRawBulk, ddPiconeBulk]
    rw [integral_add hvε hr, ht]
    ring)
  have hforms : (∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
      (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t) =
      ∑ k : Fin 4, correctedBoundaryForm lam
        (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ q.correctedBoundaryForm_eq hlam hκ b k
  calc
    _ = -(8 / 3 : ℝ) *
        ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) + ddValueFinitePart q.phi) -
        (-(8 / 3 : ℝ) * (ddValueFinitePart q.phi -
          ∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := tendsto_nhds_unique hBulk hLevel
    _ = -(8 / 3 : ℝ) * ((∑ k : Fin 4, canonicalArcForm lam (ddArcTrace q.phi k)) +
        (∑ k : Fin 4, ∫ t, ddArcCorrection q.phi k t)) := by ring
    _ = _ := by rw [hforms]

/-- Bulk coercivity on the finite-energy domain. Integrability is a hypothesis, so the
    default value of a divergent Bochner integral cannot masquerade as an energy. -/
theorem dd_bulk_picone {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hdx : HasFourierPartial 0 φ dx) (hdy : HasFourierPartial 1 φ dy)
    (hc : centralInversion φ = φ)
    (hmean : (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 φ p) = 0)
    (hgrad : IntegrableOn (ddPiconeGradient φ dx dy) cellSquare)
    (hpot : IntegrableOn (ddPiconePotential φ) cellSquare) :
    (25 / 54 : ℝ) * (∫ p in cellSquare, ddMassDensity φ p) ≤
      (∫ p in cellSquare, ddPiconeGradient φ dx dy p) +
        ∫ p in cellSquare, ddPiconePotential φ p := by
  sorry

/-- Nonnegativity of the retained vorticity term. -/
theorem ddVorticityDensity_nonneg {p : ℝ × ℝ} (hp : p ∈ cellSquare) (ν : L2) :
    0 ≤ ddVorticityDensity ν p := by
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hle : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
  have hcube : dipoleLift p ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le hle 3
  have h8 : 0 ≤ 8 - dipoleLift p ^ 3 := by linarith
  unfold ddVorticityDensity ddF
  positivity

/-- The mass density is integrable on the cell for every torus L² function. -/
theorem integrableOn_ddMassDensity (φ : L2) : IntegrableOn (ddMassDensity φ) cellSquare := by
  have hsub : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    intro p hp
    obtain ⟨ha0, ha1⟩ := abs_lt.mp hp.1
    obtain ⟨hb0, hb1⟩ := abs_lt.mp hp.2
    simp only [diagCoord] at ha0 ha1 hb0 hb1
    exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  have hbase := ((integrableOn_norm_liftL2_sq φ).mono_set hsub).const_mul 4
  have hφ : Measurable (liftL2 φ) :=
    (Lp.stronglyMeasurable φ).measurable.comp isOpenQuotientMap_torusProj.continuous.measurable
  have hmeas : Measurable (ddMassDensity φ) := by
    unfold ddMassDensity ddWeight dipoleLift
    fun_prop
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  refine hbase.mono' hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem hcell ?_)
  intro p hp
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hle : dipoleLift p ≤ 2 := by simpa [Ψ_torusProj] using Ψ_le_two (torusProj p)
  have hsq : dipoleLift p ^ 2 ≤ 4 := by nlinarith
  rw [Real.norm_of_nonneg (by unfold ddMassDensity ddWeight; positivity)]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Zero weighted mass gives zero quotient in the even sector. -/
theorem dd_eq_zero_of_mass_eq_zero {φ : L2} (hs : InSector true true φ)
    (hmass : (∫ p in cellSquare, ddMassDensity φ p) = 0) : φ = 0 := by
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hn : 0 ≤ᵐ[volume.restrict cellSquare] ddMassDensity φ :=
    Eventually.of_forall fun p ↦ by unfold ddMassDensity ddWeight; positivity
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (integrableOn_ddMassDensity φ)).1 hmass
  apply hs.eq_zero_of_lift_ae_zero_on_cellSquare
  filter_upwards [hz, ae_restrict_mem hcell] with p hp hpc
  have hpos : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hpc
  change dipoleLift p ^ 2 * ‖liftL2 φ p‖ ^ 2 = 0 at hp
  have hsq : ‖liftL2 φ p‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hpos.ne')
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (liftL2 φ p)])

/-- Recovering the vorticity from a vanishing quotient uses only the Poisson relation. -/
theorem DDQuotientData.vorticity_eq_zero {lam : ℝ} {ω : L2}
    (q : DDQuotientData lam ω) (hm : MeanZero ω) (hz : q.phi = 0) : ω = 0 := by
  have hφ := Lp.eq_zero_iff_ae_eq_zero.mp hz
  have hψ : invLap ω = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [q.stream_eq, hφ] with t ht hzt
    simp only [Pi.zero_apply] at hzt ⊢
    rw [ht, hzt, mul_zero]
  apply fourierCoeff_ext
  intro k
  simpa only [hψ, fourierCoeff_zero_fun, mul_zero] using hasFourierLaplacian_invLap ω hm k

/-- Final contradiction in one rotation character, conditional on the analytic interfaces. -/
theorem odd_odd_character_exclusion {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) : ω = 0 := by
  obtain ⟨q⟩ := dd_exclusion_domain hlam hω hs
  obtain ⟨hmean, hc⟩ := dd_orthogonality hlam hω hs q
  obtain ⟨b⟩ := dd_boundary_regularity hlam q hκ
  have h1 : MemSobolev 1 q.phi := q.regular.mono (by norm_num)
  obtain ⟨dx, hdx⟩ := h1.exists_hasFourierPartial 0
  obtain ⟨dy, hdy⟩ := h1.exists_hasFourierPartial 1
  obtain ⟨hv, hg, hp, hid⟩ := dd_picone_current hlam hω hs q hκ b hdx hdy
  have hbulk := dd_bulk_picone q.regular hdx hdy hc hmean hg hp
  have hsum : 0 ≤ ∑ k : Fin 4, correctedBoundaryForm lam
      (ddBoundaryUnknown lam q.phi k) (b.first k) (b.second k) :=
    Finset.sum_nonneg fun k _ ↦
      (correctedBoundaryForm_nonneg hlam (b.regular k) (b.endpoints k)).2
  have hcell : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hν : 0 ≤ ∫ p in cellSquare, ddVorticityDensity q.nu p :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem hcell fun p hp ↦
      ddVorticityDensity_nonneg hp q.nu)
  have hmass : (∫ p in cellSquare, ddMassDensity q.phi p) = 0 := by
    have hn : 0 ≤ ∫ p in cellSquare, ddMassDensity q.phi p :=
      integral_nonneg fun p ↦ by unfold ddMassDensity ddWeight; positivity
    nlinarith
  exact q.vorticity_eq_zero hω.1 (dd_eq_zero_of_mass_eq_zero q.even hmass)

/-- An eigenfunction odd under both separatrix reflections vanishes
    at every nonzero real spectral parameter. -/
theorem odd_odd_exclusion (lam : ℝ) (hlam : lam ≠ 0) (ω : L2)
    (hω : IsEigenSolution lam ω) (hsector : InSector false false ω) : ω = 0 := by
  obtain ⟨ωp, ωm, heq, hsp, hsm, hkp, hkm, hep, hem⟩ := hω.rotation_decomposition hsector
  rw [heq, odd_odd_character_exclusion hlam hep hsp hkp,
    odd_odd_character_exclusion hlam hem hsm hkm, add_zero]

end NoEmbeddedEigenvalues
