import NoEmbeddedEigenvalues.SobolevLocal
import NoEmbeddedEigenvalues.DipoleFlow
import NoEmbeddedEigenvalues.CanonicalProfile
import NoEmbeddedEigenvalues.SeparatrixArc
import NoEmbeddedEigenvalues.OrbitCoordinates

/-!
# Transport pairs

Blueprint: `def:transport-pair`, `lem:transport-unknown`; stated: `lem:transport-pair-eigen`,
`lem:melnikov`, `lem:good-windows`, `lem:coarea`, `lem:resonant-vanishing`,
`lem:pairing-limit`.

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

/-! ### Statements (`lem:transport-pair-eigen`, `lem:melnikov`, `lem:good-windows`) -/

/-- The lifts of an eigenfunction and its stream function form a transport pair on every
    bounded open union of orbits. -/
theorem isTransportPair_of_isEigenSolution {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U)
    (hb : Bornology.IsBounded U) :
    IsTransportPair lam U (liftL2 ω) (liftL2 (invLap ω)) := by
  sorry

/-- The Melnikov condition. Let `(v, f)` be a transport pair on a neighbourhood of the closed
    cell square that transforms with the character `κ = ±1` under the rotation
    `R(x, y) = (y, -x)`, with `f` continuous. Then the trace `g = f ∘ γ` on the separatrix arc
    has `g' ∈ L¹` and `∫ g'(s) e^{-iλs} ds = 0`. -/
theorem melnikov {lam κ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hvR : ∀ᵐ p ∂(volume.restrict U), v (p.2, -p.1) = κ * v p) (hfc : ContinuousOn f U) :
    Integrable (deriv (f ∘ separatrixArc)) ∧
      ∫ s, profileIntegrand lam (f ∘ separatrixArc) s = 0 := by
  sorry

/-- The good windows `|λS(h) - 2π(j + ½)| < π/3` have positive measure near `h = 0`. -/
theorem volume_goodWindows_pos {lam : ℝ} (hlam : lam ≠ 0) {η : ℝ} (hη : 0 < η) :
    0 < volume {h ∈ Set.Ioo 0 η |
      ∃ j : ℤ, |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3} := by
  sorry

/-- On a good window `e^{iλS(h)/4}` stays at distance at least `2 sin(π/12)` from `κ = ±1`. -/
theorem norm_exp_sub_ge_of_goodWindow {lam h : ℝ} {j : ℤ}
    (hj : |lam * orbitPeriod h - 2 * Real.pi * (j + 1 / 2)| < Real.pi / 3) {κ : ℂ}
    (hκ : κ = 1 ∨ κ = -1) :
    2 * Real.sin (Real.pi / 12) ≤ ‖exp (I * (lam * orbitPeriod h / 4)) - κ‖ := by
  sorry

/-! ### Restriction to orbits, resonances and the pairing limit (stated) -/

open Filter Topology in
/-- Restriction to almost every orbit (`lem:coarea`): if `L₀g = h` weakly on an orbit annulus,
    then on almost every orbit `g ∘ γ_h` agrees a.e. with a periodic, locally absolutely
    continuous function whose derivative in flow time is `h ∘ γ_h`. -/
theorem ae_orbit_restriction {U : Set (ℝ × ℝ)} {g Lg : ℝ × ℝ → ℂ} {h₁ h₂ : ℝ}
    (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U)
    (hg : MemLp g 2 (volume.restrict U)) (hLg : MemLp Lg 2 (volume.restrict U))
    (hd : HasWeakL0On U g Lg) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∃ G : ℝ → ℂ,
      (∀ᵐ t, G t = g (dipoleOrbit h t)) ∧ Function.Periodic G (orbitPeriod h) ∧
      (∀ c d, AbsolutelyContinuousOnInterval G c d) ∧
      ∀ᵐ t, HasDerivAt G (Lg (dipoleOrbit h t)) t := by
  sorry

/-- Orbitwise transport and resonant vanishing (`lem:resonant-vanishing`). On almost every orbit
    of an annulus the transport unknown solves `(-i∂ₜ - λ)z = f`, the angular modes satisfy
    `(k b(h) - λ) v_k = -k b(h) f_k`, and if `f` is continuous then `f_k` vanishes at every
    resonant level `k b(h_k) = λ`. -/
theorem resonant_vanishing {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1)
    (hA : orbitAnnulus h₁ h₂ ⊆ U) :
    (∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
      Function.Periodic Z (orbitPeriod h) ∧ (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
      ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t) ∧
    (∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∀ k : ℤ,
      (k * orbitFrequency h - lam) * angularMode h k v =
        -(k * orbitFrequency h) * angularMode h k f) ∧
    (ContinuousOn f U → ∀ k : ℤ, ∀ hk ∈ Set.Ioo h₁ h₂, k * orbitFrequency hk = lam →
      angularMode hk k f = 0) := by
  sorry

open Filter Topology in
/-- The limit of the vorticity pairing (`lem:pairing-limit`). Under the hypotheses of
    `melnikov`, for every null set `N` there are good levels `h_j → 0` outside `N` along which
    `∮ Re(v f̄) dt` tends to `∑_γ ∫ Re(Ω_γ ḡ_γ) ds` over the four arcs of the cell. -/
theorem pairing_limit {lam κ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hvR : ∀ᵐ p ∂(volume.restrict U), v (p.2, -p.1) = κ * v p) (hfc : ContinuousOn f U)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j ∉ N ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun j ↦ levelIntegral (hs j) (fun p ↦ (v p * (starRingEnd ℂ) (f p)).re)) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ s, (canonicalProfile lam (f ∘ cellArc k) s *
          (starRingEnd ℂ) (f (cellArc k s))).re)) := by
  sorry

end NoEmbeddedEigenvalues
