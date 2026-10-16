import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import NoEmbeddedEigenvalues.SobolevLocal

/-!
# Mollification in one variable

Blueprint: `def:line-mollifier`; stated: `lem:line-mollifier`.

Functions `F(h, θ)` on `ℝ²` are mollified in the first variable only,
`M_ε F(h, θ) = ∫ ρ_ε(h - h') F(h', θ) dh'` with `ρ_ε(h) = ε⁻¹ ρ(h/ε)` for a fixed smooth even
bump `ρ` supported in `[-1, 1]` with integral one. `L²` statements are for the measure
`dh ⊗ μ` with an arbitrary `σ`-finite `μ` in `θ`, since `M_ε` acts on each line `θ = const`
separately. This is the one-dimensional input of the transversal mollifier
(`TransversalMollifier.lean`), where `(h, θ)` are action-angle coordinates.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal

/-- The fixed bump `ρ`: smooth, even, nonnegative, positive exactly on `(-1, 1)`, with
    integral one. -/
def stdBump : ℝ → ℝ :=
  (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume

/-- The rescaled bump `ρ_ε(h) = ε⁻¹ ρ(h/ε)`. -/
def mollifierKernel (ε h : ℝ) : ℝ := ε⁻¹ * stdBump (h / ε)

/-- Mollification in the first variable, `M_ε F(h, θ) = ∫ ρ_ε(h - h') F(h', θ) dh'`. -/
def mollifyFst (ε : ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ h', mollifierKernel ε (q.1 - h') • F (h', q.2)

/-- `∂_h M_ε F = ∫ ρ_ε'(h - h') F(h', θ) dh'`. -/
def mollifyFstDeriv (ε : ℝ) (F : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ h', deriv (mollifierKernel ε) (q.1 - h') • F (h', q.2)

theorem contDiff_stdBump : ContDiff ℝ ∞ stdBump :=
  ContDiffBump.contDiff_normed _

theorem stdBump_nonneg (h : ℝ) : 0 ≤ stdBump h :=
  ContDiffBump.nonneg_normed _ h

theorem stdBump_neg (h : ℝ) : stdBump (-h) = stdBump h :=
  ContDiffBump.normed_neg _ h

theorem support_stdBump : Function.support stdBump = Ioo (-1) 1 := by
  rw [stdBump, ContDiffBump.support_normed_eq, Real.ball_eq_Ioo]
  norm_num

theorem integral_stdBump : ∫ h, stdBump h = 1 :=
  ContDiffBump.integral_normed _

/-! ### `lem:line-mollifier` (stated) -/

section LineMollifier

variable {μ : Measure ℝ} [SFinite μ] {ε : ℝ} {F : ℝ × ℝ → ℂ}

/-- `M_ε` is a contraction of `L²(dh ⊗ μ)`. -/
theorem eLpNorm_mollifyFst_le (hε : 0 < ε) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    MemLp (mollifyFst ε F) 2 ((volume : Measure ℝ).prod μ) ∧
      eLpNorm (mollifyFst ε F) 2 ((volume : Measure ℝ).prod μ) ≤
        eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  sorry

/-- `M_ε F → F` in `L²(dh ⊗ μ)`. -/
theorem tendsto_mollifyFst (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    Tendsto (fun ε ↦ eLpNorm (mollifyFst ε F - F) 2 ((volume : Measure ℝ).prod μ))
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- `ε ∂_h M_ε F → 0` in `L²(dh ⊗ μ)`, because `ε ρ_ε'` is the rescaling of `ρ'`, which has
    integral zero. -/
theorem tendsto_smul_mollifyFstDeriv (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    (∀ ε > 0, MemLp (mollifyFstDeriv ε F) 2 ((volume : Measure ℝ).prod μ)) ∧
      Tendsto (fun ε ↦ eLpNorm (ε • mollifyFstDeriv ε F) 2 ((volume : Measure ℝ).prod μ))
        (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- The commutator with an `L`-Lipschitz function of `h` is `O(εL)`. -/
theorem eLpNorm_mollifyFst_mul_sub_le (hε : 0 < ε) {s : ℝ → ℝ} {L : ℝ≥0}
    (hs : LipschitzWith L s) (hF : MemLp F 2 ((volume : Measure ℝ).prod μ)) :
    eLpNorm (fun q ↦ mollifyFst ε (fun q ↦ (s q.1 : ℂ) * F q) q - (s q.1 : ℂ) * mollifyFst ε F q)
        2 ((volume : Measure ℝ).prod μ) ≤
      ENNReal.ofReal (ε * L) * eLpNorm F 2 ((volume : Measure ℝ).prod μ) := by
  sorry

/-- `M_ε' F` is the weak `h`-derivative of `M_ε F`. -/
theorem hasWeakPartialOn_mollifyFst (hε : 0 < ε) (hF : LocallyIntegrable F) :
    HasWeakPartialOn univ 0 (mollifyFst ε F) (mollifyFstDeriv ε F) := by
  sorry

/-- `M_ε` commutes with weak derivatives. -/
theorem HasWeakPartialOn.mollify (hε : 0 < ε) {j : Fin 2} {G : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn univ j F G) :
    HasWeakPartialOn univ j (mollifyFst ε F) (mollifyFst ε G) := by
  sorry

/-- If `∂_h F = G` weakly, then `M_ε' F = M_ε G`. -/
theorem mollifyFstDeriv_ae_eq (hε : 0 < ε) {G : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn univ 0 F G) :
    mollifyFstDeriv ε F =ᵐ[volume] mollifyFst ε G := by
  sorry

end LineMollifier

end NoEmbeddedEigenvalues
