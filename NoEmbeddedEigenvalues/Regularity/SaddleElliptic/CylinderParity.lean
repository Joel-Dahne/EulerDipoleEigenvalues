import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderData
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.AxisReflectionJets
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SmoothJetBounds

/-!
# Parity of the cylinder forcing and Taylor jets

The weak Poisson forcing inherits parity from the solution by affine weak-jet
pullback and uniqueness. For a smooth representative, the resulting derivative
identities hold at the center by continuity. A nonzero ordered jet must have the
prescribed sign in each coordinate, so its degree is allowed. Harmonicity is not
needed for this finite-jet assertion.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- Continuous representatives inherit the axis identities everywhere on a disk. -/
theorem HasAxisParityOn.eqOn_disk {ρ : ℝ} {ε : Fin 2 → Bool} {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) f) (hf : ContinuousOn f (localDisk 0 ρ))
    (j : Fin 2) :
    EqOn (fun p ↦ f (axisReflect j p)) (fun p ↦ paritySign (ε j) * f p) (localDisk 0 ρ) := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hc : Continuous (axisReflect j) := by
    unfold axisReflect
    split_ifs <;> fun_prop
  apply Measure.eqOn_open_of_ae_eq (hp j) hU
  · exact hf.comp hc.continuousOn fun p hp ↦ by
      change localRadius 0 (axisReflect j p) < ρ
      rwa [localRadius_axisReflect]
  · exact continuousOn_const.mul hf

/-- No additional symmetry hypothesis on the weak Poisson forcing is needed. -/
theorem HasAxisParityOn.weak_laplacian {ρ : ℝ} {ε : Fin 2 → Bool}
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p) :
    HasAxisParityOn ε (localDisk 0 ρ) F := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  intro j
  exact hD.axisReflect_laplacian hU j (axisReflect_preimage_localDisk j ρ) hΔ (hp j)

/-- Reflection parity for a smooth jet, at the actual center of its disk. -/
theorem HasAxisParityOn.classicalJet_at_zero {ρ : ℝ} (hρ : 0 < ρ)
    {ε : Fin 2 → Bool} {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) f) (hf : ContDiffOn ℝ ∞ f (localDisk 0 ρ))
    (w : List (Fin 2)) (j : Fin 2) :
    (-1 : ℂ) ^ w.count j * classicalComplexJet w f 0 =
      paritySign (ε j) * classicalComplexJet w f 0 := by
  have hU : IsOpen (localDisk 0 ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have h0 : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hD := classicalComplexJet_weakOn hU hf w.length
  have he := hD.axisReflect_entries hU j (axisReflect_preimage_localDisk j ρ) (hp j) w le_rfl
  have hc := (contDiffOn_classicalComplexJet hU hf w).continuousOn
  have hR : Continuous (axisReflect j) := by
    unfold axisReflect
    split_ifs <;> fun_prop
  have hmaps : MapsTo (axisReflect j) (localDisk 0 ρ) (localDisk 0 ρ) := by
    intro p hpU
    change p ∈ axisReflect j ⁻¹' localDisk 0 ρ
    rwa [axisReflect_preimage_localDisk]
  have hEq := Measure.eqOn_open_of_ae_eq he hU
    (continuousOn_const.mul (hc.comp hR.continuousOn hmaps)) (continuousOn_const.mul hc)
  have hR0 : axisReflect j 0 = 0 := by simp [axisReflect]
  simpa only [hR0] using hEq h0

/-- Forbidden total degrees have zero Taylor jets for every smooth function
with the prescribed axis parity, independently of the harmonic equation. -/
theorem HasAxisParityOn.forbidden_jet_zero {ρ : ℝ} (hρ : 0 < ρ)
    {ε : Fin 2 → Bool} {f : ℝ × ℝ → ℂ}
    (hp : HasAxisParityOn ε (localDisk 0 ρ) f) (hf : ContDiffOn ℝ ∞ f (localDisk 0 ρ))
    (w : List (Fin 2)) (hw : ¬AllowedSaddleDegree ε w.length) :
    classicalComplexJet w f 0 = 0 := by
  by_contra hn
  have hs (j : Fin 2) : (-1 : ℂ) ^ w.count j = paritySign (ε j) :=
    mul_right_cancel₀ hn (hp.classicalJet_at_zero hρ hf w j)
  have hcounts : w.count (0 : Fin 2) + w.count 1 = w.length := by
    suffices h : ∀ v : List (Fin 2), v.count 0 + v.count 1 = v.length from h w
    intro v
    induction v with
    | nil => simp
    | cons i v ih =>
      fin_cases i <;>
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
  have hsprod : (-1 : ℂ) ^ w.length = paritySign (ε 0) * paritySign (ε 1) := by
    rw [← hcounts, pow_add, hs 0, hs 1]
  apply hw
  refine ⟨?_, ?_⟩
  · rw [← neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), hsprod]
    cases hε0 : ε 0 <;> cases hε1 : ε 1 <;> norm_num [paritySign, hε0, hε1]
  · intro hlen
    have hnil : w = [] := List.length_eq_zero_iff.mp hlen
    have htrue (j : Fin 2) : ε j = true := by
      cases hε : ε j with
      | false =>
        have h := hs j
        norm_num [hnil, paritySign, hε] at h
      | true => rfl
    exact ⟨htrue 0, htrue 1⟩

end NoEmbeddedEigenvalues
