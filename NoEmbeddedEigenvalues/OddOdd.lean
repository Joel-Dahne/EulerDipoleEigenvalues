import NoEmbeddedEigenvalues.EvenEven

/-!
# Odd–odd exclusion: the final analytic interfaces

The exclusion is assembled from the quotient domain, orthogonality, the Picone current,
bulk coercivity and corrected interval positivity. The analytic interfaces have explicit
Sobolev domains, representatives and integrability conclusions. Their proofs are separate
from the algebraic and measure-theoretic assembly.

The bulk uses specified Fourier first derivatives, not pointwise derivatives of an arbitrary
Sobolev representative. Arc values use the continuous representative of the H² quotient.
Endpoint conditions use interval H¹ traces, never raw endpoint values.
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

/-- The regular quotient and its transport pair, without additional corner-jet claims. -/
theorem dd_quotient_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    Nonempty (DDQuotientData lam ω) := by
  sorry

/-- Weighted mean zero and central parity of the quotient. -/
theorem dd_orthogonality {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    (q : DDQuotientData lam ω) :
    (∫ p in cellSquare, (ddWeight p : ℂ) * liftL2 q.phi p) = 0 ∧
      centralInversion q.phi = q.phi := by
  sorry

/-- The transformed edge trace `g = -iwf' - λf`. -/
def correctedBoundaryTrace (lam : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * (boundaryWeight x : ℂ) * D x - (lam : ℂ) * F x

/-- The correction `β`, expressed in the interval coordinate. Endpoint values are
    irrelevant to the integrals and the domain uses genuine H¹ traces. -/
def correctedBoundaryBeta (x : ℝ) : ℝ :=
  (3 / 4 - 3 / 16 * boundaryWeight x +
      (1 / 4 - 25 / 64 * boundaryWeight x) * Real.log (boundaryWeight x)) /
    (1 + 1 / 8 * boundaryWeight x -
      1 / 64 * boundaryWeight x ^ 2 * Real.log (boundaryWeight x))

/-- The ordinary interval correction density. -/
def correctedBoundaryTerm (lam : ℝ) (F D : ℝ → ℂ) (x : ℝ) : ℝ :=
  correctedBoundaryBeta x * ‖correctedBoundaryTrace lam F D x‖ ^ 2

/-- The corrected boundary form, with the existing weighted-domain boundary form. -/
def correctedBoundaryForm (lam : ℝ) (F D E : ℝ → ℂ) : ℝ :=
  boundaryForm lam F D E + ∫ x in (-1 : ℝ)..1, correctedBoundaryTerm lam F D x

/-- Nonnegativity on the weighted second-order domain, including integrability.
    The exclusion needs no strict positivity or boundary equality classification. -/
theorem correctedBoundaryForm_nonneg {lam : ℝ} (hlam : lam ≠ 0) {κ : Bool}
    {F D E : ℝ → ℂ} (hF : HasWeightedBoundaryH2 F D E)
    (hends : intervalH1Extension (-1) 1 F D 1 =
      paritySign κ * intervalH1Extension (-1) 1 F D (-1)) :
    IntegrableOn (correctedBoundaryTerm lam F D) (Ioo (-1) 1) ∧
      0 ≤ correctedBoundaryForm lam F D E := by
  sorry

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

/-- The canonical profiles of the quotient have the interval domain needed for corrected
    positivity; this is a separate input from the Picone current identity. -/
theorem dd_boundary_regularity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (q : DDQuotientData lam ω) {κ : Bool} (hκ : InRotationCharacter κ ω) :
    Nonempty (DDBoundaryData lam κ q.phi) := by
  sorry

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
  sorry

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
  obtain ⟨q⟩ := dd_quotient_domain hlam hω hs
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
