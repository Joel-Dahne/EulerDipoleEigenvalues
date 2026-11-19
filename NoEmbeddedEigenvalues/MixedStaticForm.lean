import NoEmbeddedEigenvalues.MixedComparisonForm
import NoEmbeddedEigenvalues.MixedField
import NoEmbeddedEigenvalues.OrbitCoordinates
import NoEmbeddedEigenvalues.Sectors

/-!
# Static forms for the odd–even quotient

Use `(a,b)` and Lebesgue measure throughout, unless an integral is explicitly
over the Cartesian lift `cellSquare`. The Cartesian Jacobian is 2, and each
physical orthonormal derivative along a diagonal axis is the corresponding
coordinate derivative divided by `√2`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- Edge value of a representative continuous on the closed diagonal cell. -/
def mixedEdgeValue (j : Fin 2) (positive : Bool) (φ : Plane → ℂ) (a : ℝ) : ℂ :=
  φ (axisTraceChart j (a, cellEdgeNormal positive))

/-- The four edge traces used here are in the tangential coordinate (not flow time). -/
def HasMixedEdgeTrace (j : Fin 2) (positive : Bool) (f : Plane → ℂ) (T : ℝ → ℂ) : Prop :=
  HasTransverseH1Trace (-Real.pi / 2) (Real.pi / 2) (-Real.pi / 2) (Real.pi / 2)
    (cellEdgeNormal positive) (axisTraceChart j) f T

/-- Quotient operator `∂aa + ∂bb - 2 tan(a) ∂a` evaluated on a weak jet. -/
def mixedWeightedLaplacian (D : List (Fin 2) → Plane → ℂ) (q : Plane) : ℂ :=
  D [0, 0] q + D [1, 1] q - (2 * Real.tan q.1 : ℝ) • D [0] q

/-- The cell part of the odd–even quotient domain. The quotient has an actual
continuous representative at the corners and zero normal derivative on each
edge. The latter is a Sobolev trace, not an evaluation of the raw jet. -/
structure MixedQuotientData (ω : L2) where
  phi : Plane → ℂ
  jet : List (Fin 2) → Plane → ℂ
  h2 : MemSobolevOn 2 mixedOpenCell phi
  weakJet : HasWeakJetOn 2 mixedOpenCell phi jet
  continuous : ContinuousOn phi (closure mixedOpenCell)
  stream_eq : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
    liftL2 (invLap ω) (diagInv q) = (Real.cos q.1 : ℂ) * phi q
  vorticity_divided : MemLp (fun q ↦ liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)) 2
    (volume.restrict mixedOpenCell)
  laplace_eq : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
    mixedWeightedLaplacian jet q = 2 * (liftL2 ω (diagInv q) / (Real.cos q.1 : ℂ)) + phi q
  normal_zero : ∀ (j : Fin 2) (positive : Bool),
    HasMixedEdgeTrace j positive (jet [j]) (fun _ ↦ 0)
  central_odd : ∀ q ∈ closure mixedOpenCell, phi (-q) = -phi q

/-- The stream gradient in diagonal coordinates, computed by the product rule
from the quotient. -/
def MixedQuotientData.streamA {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℂ :=
  (Real.cos q.1 : ℂ) * d.jet [0] q - (Real.sin q.1 : ℂ) * d.phi q

/-- Second diagonal component of the stream gradient. -/
def MixedQuotientData.streamB {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℂ :=
  (Real.cos q.1 : ℂ) * d.jet [1] q

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

/-- Trace-mass limit and the divergence-free algebra in the diagonal chart. -/
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
  sorry

/-- Rellich density, in diagonal measure (including the Cartesian Jacobian). -/
def mixedRellichDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  2 * mixedFieldCoeff q * ‖liftL2 ω (diagInv q)‖ ^ 2 +
    ‖d.streamA q‖ ^ 2 + ‖d.streamB q‖ ^ 2 -
    4 * ((mixedFieldA q • d.streamA q + mixedFieldB q • d.streamB q) *
      conj (liftL2 ω (diagInv q))).re

/-- The Rellich identity removes the corner masses from the static form. -/
theorem mixed_rellich {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    IntegrableOn (mixedRellichDensity d) mixedOpenCell ∧
    (∀ σ : Bool, IntegrableOn
      (fun a ↦ Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2)
      (Ioo (-Real.pi / 2) (Real.pi / 2))) ∧
    mixedStaticForm d = (∫ q in mixedOpenCell, mixedRellichDensity d q) -
      ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
        Real.cos a * ‖deriv (mixedEdgeValue 1 σ d.phi) a‖ ^ 2 := by
  sorry

/-- `C₀ = 1 - div_μ W`, in diagonal coordinates. -/
def mixedC₀ (q : Plane) : ℝ :=
  -mixedFieldCoeff q + 2 * Real.sin q.1 ^ 2 / (Real.cos q.1 * (Real.cos q.1 + Real.cos q.2))

/-- Density of the weighted interior form, before completion of the square. -/
def mixedWeightedDensity (φ : Plane → ℂ) (D : List (Fin 2) → Plane → ℂ) (q : Plane) : ℝ :=
  Real.cos q.1 ^ 2 * (
    mixedFieldCoeff q / 2 * ‖mixedWeightedLaplacian D q‖ ^ 2 +
    mixedGradientForm (1 + mixedFieldCoeff q) (mixedFieldMatrixOffDiagonal q) (D [0] q) (D [1] q) +
    (2 * mixedFieldA q - partialX mixedC₀ q) * (φ q * conj (D [0] q)).re +
    (2 * mixedFieldB q - partialY mixedC₀ q) * (φ q * conj (D [1] q)).re +
    (1 - mixedC₀ q - mixedFieldCoeff q / 2) * ‖φ q‖ ^ 2)

/-- The weighted interior form of the mixed static functional. -/
theorem mixed_weighted_form {ω : L2} (d : MixedQuotientData ω) :
    (∀ q ∈ mixedOpenCell, mixedC₀ q =
      1 - divergence mixedFieldA mixedFieldB q + 2 * Real.tan q.1 * mixedFieldA q) ∧
    IntegrableOn (mixedWeightedDensity d.phi d.jet) mixedOpenCell ∧
    mixedStaticForm d = ∫ q in mixedOpenCell, mixedWeightedDensity d.phi d.jet q := by
  sorry

/-- Interior density of the second-order form. -/
def mixedSecondOrderDensity (φ da db : Plane → ℂ) (q : Plane) : ℝ :=
  mixedGradientForm (mixedComparisonDiagonal q) (mixedComparisonOffDiagonal q) (da q) (db q) +
    mixedComparisonPotential q * ‖φ q‖ ^ 2

/-- Full-cell second-order form. The inputs on the Robin sides are canonical
Sobolev traces for H¹ functions; for the continuous quotient use `mixedEdgeValue`. -/
def mixedSecondOrderForm (φ da db : Plane → ℂ) (edge : Bool → ℝ → ℂ) : ℝ :=
  (∫ q in mixedOpenCell, mixedSecondOrderDensity φ da db q) +
  ∑ σ : Bool, ∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a * ‖edge σ a‖ ^ 2

/-- Nonnegative fourth-order square, with the ratio totalized at the center. -/
def mixedCompletionDensity (φ : Plane → ℂ) (D : List (Fin 2) → Plane → ℂ) (q : Plane) : ℝ :=
  Real.cos q.1 ^ 2 * mixedFieldCoeff q / 2 *
    ‖mixedWeightedLaplacian D q + (mixedC₀ q / mixedFieldCoeff q : ℝ) • φ q‖ ^ 2

/-- Static completion, with integrability of the square (not a totalized
identity between potentially divergent integrals). -/
theorem mixed_completion {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (mixedCompletionDensity d.phi d.jet) mixedOpenCell ∧
    IntegrableOn (mixedSecondOrderDensity d.phi (d.jet [0]) (d.jet [1])) mixedOpenCell ∧
    (∀ σ : Bool, IntegrableOn (fun a ↦ Real.cos a * ‖mixedEdgeValue 1 σ d.phi a‖ ^ 2)
      (Ioo (-Real.pi / 2) (Real.pi / 2))) ∧
    mixedStaticForm d = (∫ q in mixedOpenCell, mixedCompletionDensity d.phi d.jet q) +
      mixedSecondOrderForm d.phi (d.jet [0]) (d.jet [1]) (fun σ ↦ mixedEdgeValue 1 σ d.phi) := by
  sorry

/-- H¹ bound for the second-order form with canonical traces. As this is a
real quadratic form, the norm bound gives continuity by polarization. -/
theorem mixed_second_order_form_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ da db : Plane → ℂ) (edge : Bool → ℝ → ℂ),
      MemSobolevOn 1 mixedOpenCell φ →
      HasWeakPartialOn mixedOpenCell 0 φ da → HasWeakPartialOn mixedOpenCell 1 φ db →
      (∀ σ, HasMixedEdgeTrace 1 σ φ (edge σ)) →
      |mixedSecondOrderForm φ da db edge| ≤
        C * ∫ q in mixedOpenCell, ‖φ q‖ ^ 2 + ‖da q‖ ^ 2 + ‖db q‖ ^ 2 := by
  sorry

/-- Projection onto odd-in-a (`true`) or even-in-a (`false`). On a centrally
odd function, the respective b parities are even and odd. -/
def mixedParityPart (oddA : Bool) (φ : Plane → ℂ) (q : Plane) : ℂ :=
  (φ q + (if oddA then -1 else 1) * φ (-q.1, q.2)) / 2

/-- Parity splitting, with the actual weak gradients of the projected functions. -/
theorem mixed_parity_split {ω : L2} (d : MixedQuotientData ω) :
    let U := mixedParityPart true d.phi
    let V := mixedParityPart false d.phi
    (∀ q ∈ closure mixedOpenCell,
      d.phi q = U q + V q ∧ U (-q.1, q.2) = -U q ∧ U (q.1, -q.2) = U q ∧
        V (-q.1, q.2) = V q ∧ V (q.1, -q.2) = -V q) ∧
    ∃ Ua Ub Va Vb : Plane → ℂ,
      MemSobolevOn 1 mixedOpenCell U ∧ MemSobolevOn 1 mixedOpenCell V ∧
      HasWeakPartialOn mixedOpenCell 0 U Ua ∧ HasWeakPartialOn mixedOpenCell 1 U Ub ∧
      HasWeakPartialOn mixedOpenCell 0 V Va ∧ HasWeakPartialOn mixedOpenCell 1 V Vb ∧
      mixedSecondOrderForm d.phi (d.jet [0]) (d.jet [1]) (fun σ ↦ mixedEdgeValue 1 σ d.phi) =
        mixedSecondOrderForm U Ua Ub (fun σ ↦ mixedEdgeValue 1 σ U) +
        mixedSecondOrderForm V Va Vb (fun σ ↦ mixedEdgeValue 1 σ V) := by
  sorry

/-- Coercivity with the two normalizations of the mass. -/
theorem mixed_static_coercivity {ω : L2} (d : MixedQuotientData ω) :
    let mass := ∫ q in mixedOpenCell, Real.cos q.1 ^ 2 * ‖d.phi q‖ ^ 2
    (1 / 200 : ℝ) * mass ≤ mixedStaticForm d ∧
    (1 / 200 : ℝ) * mass =
      (1 / 400 : ℝ) * ∫ p in cellSquare, ‖liftL2 (invLap ω) p‖ ^ 2 := by
  sorry

end NoEmbeddedEigenvalues
