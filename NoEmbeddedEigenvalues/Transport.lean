import NoEmbeddedEigenvalues.SobolevLocal
import NoEmbeddedEigenvalues.DipoleFlow

/-!
# Transport pairs

Blueprint: `def:transport-pair`, `lem:transport-unknown`.

The eigenvalue equation `H(ω + ψ) = λω`, with `H = -i L₀` and `L₀ = Y · ∇`, is a transport
equation along the orbits of the dipole flow. A transport pair `(v, f)` on an open union of
orbits `U ⊆ ℝ²` abstracts it: `v ∈ L²(U)`, `f ∈ H²(U)` and `H(v + f) = λv` weakly on `U`.
Since `Y` is divergence free, the weak form of `L₀ g = h` is `∫ g L₀φ = -∫ h φ` for test
functions `φ` on `U`. The transport unknown `z = -(v + f)/λ` satisfies `Hz = -v` and
`(H - λ)z = f`.

Transport pairs live on the lift. The lift of a periodic function is not in `L²` of an
unbounded set, so in the applications `U` is bounded: a neighbourhood of the closed cell
made of whole orbits, or a compact annulus of orbits.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Complex

/-- `U` is an open union of orbits of the dipole flow. -/
def IsOrbitUnion (U : Set (ℝ × ℝ)) : Prop :=
  IsOpen U ∧ ∀ p ∈ U, ∀ t, dipoleFlow p t ∈ U

/-- `L₀ g = h` weakly on `U`: both are locally integrable on `U` and `∫ g L₀φ = -∫ h φ` for
    every test function `φ` on `U`. -/
def HasWeakL0On (U : Set (ℝ × ℝ)) (g h : ℝ × ℝ → ℂ) : Prop :=
  LocallyIntegrableOn g U ∧ LocallyIntegrableOn h U ∧
    ∀ φ, IsTestFunctionOn U φ → ∫ p, g p * classicalL0 φ p = -∫ p, h p * φ p

/-- A transport pair `(v, f)` on `U` with parameter `λ ≠ 0`: `v ∈ L²(U)`, `f ∈ H²(U)` and
    `H(v + f) = λv` weakly on `U`, that is `L₀(v + f) = iλv`. -/
structure IsTransportPair (lam : ℝ) (U : Set (ℝ × ℝ)) (v f : ℝ × ℝ → ℂ) : Prop where
  ne_zero : lam ≠ 0
  isOrbitUnion : IsOrbitUnion U
  memLp : MemLp v 2 (volume.restrict U)
  memSobolevOn : MemSobolevOn 2 U f
  hasWeakL0On : HasWeakL0On U (fun p ↦ v p + f p) (fun p ↦ I * (lam * v p))

/-- The transport unknown `z = -(v + f)/λ`. -/
def transportUnknown (lam : ℝ) (v f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p ↦ -(v p + f p) / lam

/-- The weak `L₀` is linear: scalar multiples. -/
theorem HasWeakL0On.const_mul {U : Set (ℝ × ℝ)} {g h : ℝ × ℝ → ℂ} (hd : HasWeakL0On U g h)
    (c : ℂ) : HasWeakL0On U (fun p ↦ c * g p) (fun p ↦ c * h p) := by
  refine ⟨by simpa [Pi.smul_def] using hd.1.smul c, by simpa [Pi.smul_def] using hd.2.1.smul c,
    fun φ hφ ↦ ?_⟩
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hd.2.2 φ hφ]
  ring

/-- `Hz = -v`, that is `L₀ z = -iv`. -/
theorem IsTransportPair.hasWeakL0On_transportUnknown {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f) :
    HasWeakL0On U (transportUnknown lam v f) (fun p ↦ I * -v p) := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne_zero
  convert hp.hasWeakL0On.const_mul (-1 / lam) using 1
  · funext p
    simp only [transportUnknown]
    field_simp
  · funext p
    field_simp

/-- `(H - λ)z = f`, that is `L₀ z = i(λz + f)`. -/
theorem IsTransportPair.hasWeakL0On_transportUnknown_sub {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f) :
    HasWeakL0On U (transportUnknown lam v f)
      (fun p ↦ I * (lam * transportUnknown lam v f p + f p)) := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne_zero
  convert hp.hasWeakL0On_transportUnknown using 1
  funext p
  simp only [transportUnknown]
  field_simp
  ring

end NoEmbeddedEigenvalues
