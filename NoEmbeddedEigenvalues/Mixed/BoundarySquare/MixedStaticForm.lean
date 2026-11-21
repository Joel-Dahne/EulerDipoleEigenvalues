module

public import NoEmbeddedEigenvalues.Regularity.MixedSeparatrix.MixedQuotientData

/-! # The mixed static form and its trace-mass field -/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- A real quadratic gradient form with equal diagonal entries. -/
def mixedGradientForm (g j : ℝ) (da db : ℂ) : ℝ :=
  g * (‖da‖ ^ 2 + ‖db‖ ^ 2) + 2 * j * (da * conj db).re

/-- Mixed virial density in diagonal measure, including both Jacobian factors. -/
def mixedVirialDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  2 * mixedFieldCoeff q * ‖liftL2 ω (diagInv q)‖ ^ 2 +
    mixedGradientForm 1 (mixedFieldMatrixOffDiagonal q) (d.streamA q) (d.streamB q)

/-- Cutoff trace mass. Rotation indices 1 and 3 are Dirichlet edges; 0 and 2 are
Neumann edges. Every arc uses the same cutoff in its own centered flow time. -/
def mixedTraceMassCutoff (φ : Plane → ℂ) (T : ℝ) : ℝ :=
  let mass := fun k : ℕ ↦ ∫ t in Ioo (-T) T, ‖φ (diagCoord (cellArc k t))‖ ^ 2
  mass 1 + mass 3 - (mass 0 + mass 2)

/-- Absolutely convergent volume representation of the paired trace mass on
the quotient domain. The equality with the cutoff limit is a separate result. -/
def mixedTraceMassDensity (φ da db : Plane → ℂ) (q : Plane) : ℝ :=
  2 * ((mixedFieldA q • da q - mixedFieldB q • db q) * conj (φ q)).re

/-- Static form using the volume representation of the trace mass. -/
def mixedStaticForm {ω : L2} (d : MixedQuotientData ω) : ℝ :=
  (∫ q in mixedOpenCell, mixedVirialDensity d q) -
    (∫ q in mixedOpenCell, mixedTraceMassDensity d.phi (d.jet [0]) (d.jet [1]) q) -
    ∑ a : Bool, ∑ b : Bool, ‖d.phi (cellEdgeNormal a, cellEdgeNormal b)‖ ^ 2

/-- The signed trace-mass field is divergence free. Its derivative of the
corner cutoff parameter `cos a + cos b` is `cos a - cos b`, so the cutoff
flux itself becomes small at a corner. -/
theorem mixed_trace_mass_field {q : Plane} (hq : q ∈ mixedOpenCell) :
    divergence mixedFieldA (fun r ↦ -mixedFieldB r) q = 0 ∧
    fieldDeriv mixedFieldA (fun r ↦ -mixedFieldB r)
      (fun r ↦ Real.cos r.1 + Real.cos r.2) q = Real.cos q.1 - Real.cos q.2 := by
  have hab : 0 < Real.cos q.1 + Real.cos q.2 := by
    exact add_pos (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.1))
      (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hq.2))
  have ha := (Real.hasDerivAt_cos q.1).add_const (Real.cos q.2)
  have hb := (hasDerivAt_const q.2 (Real.cos q.1)).add (Real.hasDerivAt_cos q.2)
  have hx := (Real.hasDerivAt_sin q.1).div ha hab.ne'
  have hy := (Real.hasDerivAt_sin q.2).div hb hab.ne'
  constructor
  · unfold divergence partialX partialY
    have hx' : deriv (fun t ↦ mixedFieldA (t, q.2)) q.1 = _ := hx.deriv
    have hy' : deriv (fun t ↦ -mixedFieldB (q.1, t)) q.2 = _ := hy.neg.deriv
    rw [hx', hy']
    simp only [Pi.add_apply, zero_add]
    have h₁ := Real.sin_sq_add_cos_sq q.1
    have h₂ := Real.sin_sq_add_cos_sq q.2
    field_simp
    nlinarith only [h₁, h₂]
  · unfold fieldDeriv partialX partialY
    have ha' : deriv (fun t ↦ Real.cos t + Real.cos q.2) q.1 = _ := ha.deriv
    have hb' : deriv (fun t ↦ Real.cos q.1 + Real.cos t) q.2 = _ := hb.deriv
    dsimp only
    rw [ha', hb']
    have h₁ := Real.sin_sq_add_cos_sq q.1
    have h₂ := Real.sin_sq_add_cos_sq q.2
    simp only [mixedFieldA, mixedFieldB, smul_eq_mul, zero_add]
    field_simp
    nlinarith only [h₁, h₂]

/-- The signed normal flux of the trace-mass field on the regular edges. -/
theorem mixed_trace_mass_edge_flux {x : ℝ} (_hx : x ∈ Ioo (-Real.pi / 2) (Real.pi / 2))
    (σ : Bool) :
    let sign : ℝ := if σ then 1 else -1
    sign * mixedFieldA (cellEdgeNormal σ, x) = 1 / Real.cos x ∧
      -sign * mixedFieldB (x, cellEdgeNormal σ) = -1 / Real.cos x := by
  cases σ <;> simp [mixedFieldA, mixedFieldB, cellEdgeNormal, neg_div]

end NoEmbeddedEigenvalues
