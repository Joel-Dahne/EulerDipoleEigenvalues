import NoEmbeddedEigenvalues.LineMollifier
import NoEmbeddedEigenvalues.Transport

/-!
# The transversal mollifier

Blueprint: `def:transversal-mollifier`; stated: `lem:action-angle-weak`,
`lem:transversal-mollifier`, `lem:transversal-mollifier-derivatives`,
`lem:transversal-mollifier-commutator`.

In action-angle coordinates `(h, θ)` on the punctured cell (`OrbitCoordinates.lean`), `L₀`
is `S(h)⁻¹ ∂_θ`. The transversal mollifier cuts off with `χ(h)` and mollifies in `h` at fixed
`θ`, `J_ε u = M_ε(χ U) ∘ (h, θ)` with `U = u ∘ (h, θ)⁻¹`, extended by zero off the cell.
It almost commutes with `L₀`: the commutator only sees the variation of `S` over the
smoothing window, which costs `O(ε)` times `‖L₀ u‖`. Its derivatives are `O(1/ε)`, in fact
`o(1/ε)`. This is what the `L²` virial identity (`VirialL2.lean`) needs; it uses no flow of
the virial field.

All statements are on the lift: inputs are functions on the cell square, outputs are
functions on `ℝ²` supported in a fixed compact subset of the punctured cell.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal

/-! ### Weak derivatives in action-angle coordinates (`lem:action-angle-weak`, stated) -/

/-- `L₀ u = k` weakly on the punctured cell if and only if `∂_θ U = S(h) K` weakly on the
    strip, where `U, K` are `u, k` in action-angle coordinates. -/
theorem hasWeakL0On_iff_actionAngle {u k : ℝ × ℝ → ℂ} :
    HasWeakL0On puncturedCell u k ↔
      HasWeakPartialOn actionStrip 1 (u ∘ actionAngleInv)
        (fun q ↦ (orbitPeriod q.1 : ℂ) * k (actionAngleInv q)) := by
  sorry

/-- The chain rule for weak derivatives from the cell to the strip. -/
theorem HasWeakPartialOn.comp_actionAngleInv {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ i, HasWeakPartialOn puncturedCell i u (g i)) (j : Fin 2) :
    HasWeakPartialOn actionStrip j (u ∘ actionAngleInv) (fun q ↦
      ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * g 0 (actionAngleInv q) +
        ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * g 1 (actionAngleInv q)) := by
  sorry

/-- The chain rule for weak derivatives from the strip to the cell, for functions that are
    `1`-periodic in `θ`. The angle jumps across its cut, a null set, where its partial
    derivatives are irrelevant. -/
theorem HasWeakPartialOn.comp_actionAngle {F : ℝ × ℝ → ℂ} {G : Fin 2 → ℝ × ℝ → ℂ}
    (hper : ∀ q : ℝ × ℝ, F (q.1, q.2 + 1) = F q)
    (hG : ∀ i, HasWeakPartialOn actionStrip i F (G i)) (j : Fin 2) :
    HasWeakPartialOn puncturedCell j (F ∘ actionAngle) (fun p ↦
      ((coordPartial j levelCoord p : ℝ) : ℂ) * G 0 (actionAngle p) +
        ((coordPartial j angleCoord p : ℝ) : ℂ) * G 1 (actionAngle p)) := by
  sorry

/-! ### The mollifier (`def:transversal-mollifier`) -/

open scoped Classical in
/-- The cutoff `χ(Ψ/2)` on the cell square, extended by zero. -/
def cellCutoff (χ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := if p ∈ cellSquare then χ (levelCoord p) else 0

open scoped Classical in
/-- The transversal mollifier `J_ε u = M_ε(χ U) ∘ (h, θ)` on the punctured cell, with
    `U = u ∘ (h, θ)⁻¹`, and zero elsewhere. -/
def transversalMollifier (χ : ℝ → ℝ) (ε : ℝ) (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if p ∈ puncturedCell then
    mollifyFst ε (fun q ↦ (χ q.1 : ℂ) * u (actionAngleInv q)) (actionAngle p)
  else 0

/-! ### Statements -/

section Statements

variable {χ : ℝ → ℝ}

/-- Scalars pass through `J_ε`. -/
theorem transversalMollifier_const_mul (ε : ℝ) (c : ℂ) (u : ℝ × ℝ → ℂ) :
    transversalMollifier χ ε (fun p ↦ c * u p) = fun p ↦ c * transversalMollifier χ ε u p := by
  funext p
  simp only [transversalMollifier, mollifyFst]
  split_ifs
  · rw [← integral_const_mul]
    congr 1
    funext h'
    simp only [Complex.real_smul]
    ring
  · simp

/-! #### `lem:transversal-mollifier` (stated) -/

/-- For small `ε`, `J_ε u` vanishes off a fixed compact subset of the punctured cell. -/
theorem transversalMollifier_eq_zero (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ K, IsCompact K ∧ K ⊆ puncturedCell ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ u p, p ∉ K →
      transversalMollifier χ ε u p = 0 := by
  sorry

/-- `J_ε` is additive on `L²` of the cell, up to null sets. -/
theorem transversalMollifier_add {ε : ℝ} (hε : 0 < ε) {u v : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) (hv : MemLp v 2 (volume.restrict cellSquare)) :
    transversalMollifier χ ε (u + v) =ᵐ[volume]
      transversalMollifier χ ε u + transversalMollifier χ ε v := by
  sorry

/-- `J_ε u` depends only on the class of `u` in `L²` of the cell. -/
theorem transversalMollifier_congr_ae {ε : ℝ} {u v : ℝ × ℝ → ℂ}
    (huv : u =ᵐ[volume.restrict cellSquare] v) :
    transversalMollifier χ ε u =ᵐ[volume] transversalMollifier χ ε v := by
  sorry

/-- For small `ε`, `J_ε` is bounded from `L²` of the cell to `L²(ℝ²)`, uniformly in `ε`. -/
theorem memLp_transversalMollifier (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ ε₀ > 0, ∃ C : ℝ≥0, ∀ ε ∈ Ioo 0 ε₀, ∀ u, MemLp u 2 (volume.restrict cellSquare) →
      MemLp (transversalMollifier χ ε u) 2 volume ∧
        eLpNorm (transversalMollifier χ ε u) 2 volume ≤
          C * eLpNorm u 2 (volume.restrict cellSquare) := by
  sorry

/-- `J_ε u → χ(Ψ/2) u` in `L²`. -/
theorem tendsto_transversalMollifier (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1)
    {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict cellSquare)) :
    Tendsto (fun ε ↦ eLpNorm (fun p ↦ transversalMollifier χ ε u p - cellCutoff χ p * u p) 2
      volume) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-! #### `lem:transversal-mollifier-derivatives` (stated) -/

/-- For `u ∈ H¹` of the cell, `J_ε u → χ(Ψ/2) u` in `H¹(ℝ²)`. -/
theorem tendsto_transversalMollifier_partial (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare))
    (hg : ∀ i, HasWeakPartialOn cellSquare i u (g i))
    (hg2 : ∀ i, MemLp (g i) 2 (volume.restrict cellSquare)) :
    ∃ d : Fin 2 → ℝ → ℝ × ℝ → ℂ,
      (∀ᶠ ε in 𝓝[>] 0, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
        MemLp (d j ε) 2 volume) ∧
      ∀ j, Tendsto (fun ε ↦ eLpNorm (fun p ↦ d j ε p -
          (((coordPartial j (cellCutoff χ) p : ℝ) : ℂ) * u p + cellCutoff χ p * g j p)) 2 volume)
        (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- For `u, L₀ u ∈ L²` of the cell, `J_ε u ∈ H¹(ℝ²)` with `ε ‖∇J_ε u‖ → 0`. -/
theorem transversalMollifier_hasWeakPartialOn (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) {u k : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict cellSquare)) (hk : MemLp k 2 (volume.restrict cellSquare))
    (hL : HasWeakL0On cellSquare u k) :
    ∃ d : Fin 2 → ℝ → ℝ × ℝ → ℂ,
      (∀ᶠ ε in 𝓝[>] 0, ∀ j, HasWeakPartialOn univ j (transversalMollifier χ ε u) (d j ε) ∧
        MemLp (d j ε) 2 volume) ∧
      ∀ j, Tendsto (fun ε ↦ ENNReal.ofReal ε * eLpNorm (d j ε) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-! #### `lem:transversal-mollifier-commutator` (stated) -/

/-- `[L₀, J_ε] u = O(ε ‖L₀ u‖)`, uniformly in `u`. -/
theorem transversalMollifier_hasWeakL0On (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo 0 1) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₀, ∀ u k : ℝ × ℝ → ℂ,
      MemLp u 2 (volume.restrict cellSquare) → MemLp k 2 (volume.restrict cellSquare) →
      HasWeakL0On cellSquare u k →
      ∃ kε, HasWeakL0On univ (transversalMollifier χ ε u) kε ∧ MemLp kε 2 volume ∧
        eLpNorm (kε - transversalMollifier χ ε k) 2 volume ≤
          ENNReal.ofReal (C * ε) * eLpNorm k 2 (volume.restrict cellSquare) := by
  sorry

end Statements

end NoEmbeddedEigenvalues
