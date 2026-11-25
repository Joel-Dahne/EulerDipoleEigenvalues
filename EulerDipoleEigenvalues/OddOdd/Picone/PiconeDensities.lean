module

public import EulerDipoleEigenvalues.OddOdd.WeightedVirial.VirialCoefficients

/-! # Ground state and Picone densities -/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology

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

end EulerDipoleEigenvalues
