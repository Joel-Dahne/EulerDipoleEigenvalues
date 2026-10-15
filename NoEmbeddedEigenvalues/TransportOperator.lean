import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import NoEmbeddedEigenvalues.SymmetryL2
import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.LiftTorus

/-!
# The transport operator `H = -iL₀`

Blueprint: `def:transport-operator`, `lem:H-selfadjoint` (stated).

`H = -iL₀` with domain `{u ∈ L² : L₀u ∈ L²}`, where `L₀u` is taken in the weak sense of
`HasL0` (tested against the characters), is a partially defined operator on `L²(𝕋²)`. The
dipole flow descends to the torus, since the velocity is periodic. The lemma states that `H`
is self-adjoint, that smooth functions form a core, and that `H` generates the group
`u ↦ u ∘ Φₜ`. Mathlib has no theory of strongly continuous groups or Stone's theorem, so the
last part is stated through difference quotients.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Complex Filter Topology

/-- The domain `{u ∈ L² : L₀u ∈ L²}` of the transport operator. -/
def transportDomain : Submodule ℂ L2 where
  carrier := {g | ∃ h, HasL0 g h}
  add_mem' := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ ⟨_, h₁.add h₂⟩
  zero_mem' := ⟨0, HasL0.zero⟩
  smul_mem' := fun c _ ⟨_, h⟩ ↦ ⟨_, h.smul c⟩

/-- `L₀` on its domain. -/
def transportL0 : transportDomain →ₗ[ℂ] L2 where
  toFun g := Classical.choose g.2
  map_add' g₁ g₂ :=
    HasL0.unique (Classical.choose_spec (g₁ + g₂).2)
      ((Classical.choose_spec g₁.2).add (Classical.choose_spec g₂.2))
  map_smul' c g :=
    HasL0.unique (Classical.choose_spec (c • g).2) ((Classical.choose_spec g.2).smul c)

theorem hasL0_transportL0 (g : transportDomain) : HasL0 g (transportL0 g) :=
  Classical.choose_spec g.2

/-- The transport operator `H = -iL₀` with its maximal domain. -/
def transportH : L2 →ₗ.[ℂ] L2 := ⟨transportDomain, (-I) • transportL0⟩

/-- The smooth functions in `L²(𝕋²)`. -/
def smoothL2 : Submodule ℂ L2 :=
  Submodule.span ℂ {g | ∃ φ, IsSmoothTorusTest φ ∧ g = ContinuousMap.toLp 2 volume ℂ φ}

/-- The dipole flow on the torus, `Φₜ(π p) = π(φₜ(p))`. -/
def torusFlow (t : ℝ) (q : Torus) : Torus :=
  torusProj (dipoleFlow (Function.surjInv torusProj_surjective q) t)

/-- The flow is area preserving. -/
theorem measurePreserving_torusFlow (t : ℝ) : MeasurePreserving (torusFlow t) := by
  sorry

/-- `H` is self-adjoint. -/
theorem isSelfAdjoint_transportH : IsSelfAdjoint transportH := by
  sorry

/-- Smooth functions form a core for `H`. -/
theorem hasCore_transportH : transportH.HasCore smoothL2 := by
  sorry

/-- `H` generates the group `u ↦ u ∘ Φₜ`: `u` is in the domain exactly when the difference
    quotient `(u ∘ Φₛ - u)/s` converges in `L²` as `s → 0`, and then the limit is
    `L₀u = iHu`. -/
theorem tendsto_torusFlow_sub_iff (g : L2) :
    g ∈ transportDomain ↔ ∃ v : L2, Tendsto
      (fun s : ℝ ↦ (s⁻¹ : ℂ) • (pullback (torusFlow s) (measurePreserving_torusFlow s) g - g))
      (𝓝[≠] 0) (𝓝 v) := by
  sorry

theorem tendsto_torusFlow_sub (g : transportDomain) :
    Tendsto
      (fun s : ℝ ↦ (s⁻¹ : ℂ) • (pullback (torusFlow s) (measurePreserving_torusFlow s) g - g))
      (𝓝[≠] 0) (𝓝 (I • transportH g)) := by
  sorry

end NoEmbeddedEigenvalues
