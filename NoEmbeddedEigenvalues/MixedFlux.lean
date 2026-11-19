import NoEmbeddedEigenvalues.MixedStaticForm
import NoEmbeddedEigenvalues.MixedBoundarySquare
import NoEmbeddedEigenvalues.CanonicalProfile
import NoEmbeddedEigenvalues.NormalField
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! # Paired mixed-sector flux and its Neumann trace -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

local notation "Plane" => ℝ × ℝ

/-- An absolute-level collar in the Cartesian lift. -/
def mixedSeparatrixCollar (ε : ℝ) : Set Plane := {p | |dipoleLift p| < ε}

/-- Regularity across the separatrix and the one-factor cell quotient. -/
theorem mixed_quotient_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) :
    Nonempty (MixedQuotientData ω) ∧
      ∃ ε : ℝ, 0 < ε ∧
        MemSobolevLocOn 1 (mixedSeparatrixCollar ε) (liftL2 ω) ∧
        MemSobolevLocOn 3 (mixedSeparatrixCollar ε) (liftL2 (invLap ω)) ∧
        ∀ σ : Bool, HasCellEdgeTrace (cellSquare ∩ mixedSeparatrixCollar ε) 0 σ
          (liftL2 ω) (fun _ ↦ 0) := by
  sorry

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
  sorry

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

/-- Normal-field virial density in diagonal measure. The normal and tangent
are still physical unit directions in Cartesian coordinates. -/
def mixedNormalVirialDensity {ω : L2} (d : MixedQuotientData ω) (q : Plane) : ℝ :=
  let p := diagInv q
  let dx := fun r ↦ (d.streamA (diagCoord r) + d.streamB (diagCoord r)) / 2
  let dy := fun r ↦ (d.streamA (diagCoord r) - d.streamB (diagCoord r)) / 2
  2 * (normalCoeff p * ‖liftL2 ω p‖ ^ 2 +
    (2 - normalC p) * ‖normalDeriv dx dy p‖ ^ 2 +
    normalC p * ‖tangentDeriv dx dy p‖ ^ 2)

/-- The normal-field paired flux. This uses the canonical profile and takes
no physical vorticity trace. The mixed-character limit remains to be proved. -/
theorem mixed_paired_flux {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedNormalVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedNormalVirialDensity d q)) := by
  sorry

/-- The mixed-field virial. The boundary profile in the paired expression is
the physical vorticity trace by `mixed_boundary_square_traces`. -/
theorem mixed_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false true ω) (d : MixedQuotientData ω) :
    IntegrableOn (mixedVirialDensity d) mixedOpenCell ∧
    Tendsto (fun T ↦ 2 * mixedPairedFluxCutoff lam d.phi T) atTop
      (𝓝 (∫ q in mixedOpenCell, mixedVirialDensity d q)) := by
  sorry

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
  sorry

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
