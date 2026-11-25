module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.AffineJets
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.WeakJetOperations

/-!
# Axis reflection of specified weak jets

Reflection acts diagonally on the ordered derivative indices. Comparing the
reflected jet with a scalar multiple by weak uniqueness transfers an a.e. parity
identity to every specified entry. In particular the weak Laplacian retains the
parity of the function; no separate symmetry assumption on the forcing is needed.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set

/-- The Cartesian reflection as a continuous linear equivalence. -/
def axisReflectionLinear (j : Fin 2) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  if j = 0 then
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr (.refl ℝ ℝ)
  else (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (.neg ℝ)

@[simp] theorem axisReflectionLinear_apply (j : Fin 2) (p : ℝ × ℝ) :
    axisReflectionLinear j p = axisReflect j p := by
  fin_cases j <;> rfl

theorem planeAffine_axisReflectionLinear (j : Fin 2) :
    (planeAffine (axisReflectionLinear j) 0 : (ℝ × ℝ) → ℝ × ℝ) = axisReflect j := by
  funext p
  simp only [planeAffine_apply, axisReflectionLinear_apply, add_zero]

/-- Cartesian axis reflections preserve planar volume. -/
theorem measurePreserving_axisReflect (j : Fin 2) :
    MeasurePreserving (axisReflect j) := by
  rw [Measure.volume_eq_prod]
  fin_cases j
  · change MeasurePreserving (Prod.map Neg.neg id) _ _
    exact (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
  · change MeasurePreserving (Prod.map id Neg.neg) _ _
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

/-- Euclidean disks centered at the origin are invariant under axis reflection. -/
theorem localRadius_axisReflect (j : Fin 2) (p : ℝ × ℝ) :
    localRadius 0 (axisReflect j p) = localRadius 0 p := by
  unfold axisReflect
  split_ifs <;> simp [localRadius]

theorem axisReflect_preimage_localDisk (j : Fin 2) (ρ : ℝ) :
    axisReflect j ⁻¹' localDisk 0 ρ = localDisk 0 ρ := by
  ext p
  simp only [mem_preimage, localDisk, mem_ofPred_eq, localRadius_axisReflect]

/-- Every occurrence of the reflected direction contributes one minus sign.
The supplied mixed entries are neither exchanged nor assumed equal. -/
theorem affineJet_axisReflectionLinear (j : Fin 2)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (w : List (Fin 2)) (p : ℝ × ℝ) :
    affineJet (axisReflectionLinear j) 0 D w p =
      (-1 : ℂ) ^ w.count j * D w (axisReflect j p) := by
  induction w generalizing D with
  | nil => simp [affineJet, planeAffine_axisReflectionLinear]
  | cons i w ih =>
    simp only [affineJet, ih]
    fin_cases i <;> fin_cases j <;>
      simp [affineCoeff, planeDirection, axisCoord, axisReflect, pow_succ]

/-- A.e. scalar reflection parity determines all ordered weak jet entries. -/
theorem HasWeakJetOn.axisReflect_entries {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (j : Fin 2) (hR : axisReflect j ⁻¹' U = U)
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) {c : ℂ}
    (hp : ∀ᵐ p ∂(volume.restrict U), f (axisReflect j p) = c * f p) :
    ∀ w, w.length ≤ n → ∀ᵐ p ∂(volume.restrict U),
      (-1 : ℂ) ^ w.count j * D w (axisReflect j p) = c * D w p := by
  have hmp : MeasurePreserving (planeAffine (axisReflectionLinear j) 0) := by
    rw [planeAffine_axisReflectionLinear]
    exact measurePreserving_axisReflect j
  have hpre : planeAffine (axisReflectionLinear j) 0 ⁻¹' U = U := by
    rwa [planeAffine_axisReflectionLinear]
  have hT := hD.comp_planeAffine (axisReflectionLinear j) 0 hmp hU
  rw [hpre] at hT
  have hS : HasWeakJetOn n U (fun p ↦ c * f p) (fun w p ↦ c * D w p) :=
    ⟨by simp only [hD.1], fun w hw k ↦ (hD.2 w hw k).const_mul c⟩
  have heq := hT.ae_eq_of_value_ae hU hS (by
    filter_upwards [hp] with p hp
    simpa only [Function.comp_apply, planeAffine_axisReflectionLinear] using hp)
  intro w hw
  have h := (ae_restrict_iff' hU.measurableSet).mpr (heq w hw)
  simpa only [affineJet_axisReflectionLinear] using h

/-- The specified weak Laplacian inherits reflection parity from its solution. -/
theorem HasWeakJetOn.axisReflect_laplacian {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (j : Fin 2) (hR : axisReflect j ⁻¹' U = U)
    {f F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 U f D)
    (hΔ : ∀ᵐ p ∂(volume.restrict U), D [0, 0] p + D [1, 1] p = F p) {c : ℂ}
    (hp : ∀ᵐ p ∂(volume.restrict U), f (axisReflect j p) = c * f p) :
    ∀ᵐ p ∂(volume.restrict U), F (axisReflect j p) = c * F p := by
  have he (k : Fin 2) : ∀ᵐ p ∂(volume.restrict U),
      D [k, k] (axisReflect j p) = c * D [k, k] p := by
    have h := hD.axisReflect_entries hU j hR hp [k, k] (by simp)
    fin_cases k <;> fin_cases j <;> simpa using h
  have hmaps : MapsTo (axisReflect j) U U := by
    intro p hpU
    change p ∈ axisReflect j ⁻¹' U
    rwa [hR]
  have hΔR := ((measurePreserving_axisReflect j).quasiMeasurePreserving.restrict hmaps).ae hΔ
  filter_upwards [he 0, he 1, hΔ, hΔR] with p h0 h1 hΔp hΔRp
  rw [← hΔRp, h0, h1, ← mul_add, hΔp]

end EulerDipoleEigenvalues
