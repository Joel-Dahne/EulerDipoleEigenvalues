module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderWeak
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderJointForcing
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderCartesianWeak
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakJetFiniteness

/-!
# Weighted physical particular solution from the specified cylinder jet

The logarithmic cylinder solution is transported as an ordered weak jet, with
finite weighted physical norms. Whole-disk weak identities include the center.
The pointwise logarithmic-polar identity ties the physical solution to the same
actual cylinder candidate. No harmonic comparison is part of this interface.

The candidate formulas and area Jacobian provide genuine whole-disk norms
independently of weak derivative identification. Transport of compact tests
uses overlapping real-angle patches with variable Jacobian -r²; the
constant-Jacobian quarter-chart theorem does not apply directly. Once each
punctured weak pair is identified, whole-disk local integrability removes the
center separately at both derivative levels.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Transport a bounded continuous cylinder solution and its specified finite
weak jet to a whole-disk weighted Poisson solution
(`lem:cylinder-cartesian-particular`). The uniform value bound is unchanged. -/
theorem cylinder_cartesian_particular {ρ a C : ℝ} (hρ : 0 < ρ) (ha : 1 < a)
    {ε : Fin 2 → Bool} {F : ℝ × ℝ → ℂ}
    {S : ℝ × AddCircle (2 * Real.pi) → ℂ}
    {J : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hJ : HasCylinderH2Jet S J)
    (hP : cylinderJetOperator a J =ᵐ[logCylinderMeasure] cylinderForcing a ρ F)
    (hS : Continuous S)
    (hp : ∀ t : ℝ, ∀ θ : AddCircle (2 * Real.pi),
      S (t, (Real.pi : AddCircle (2 * Real.pi)) - θ) = paritySign (ε 0) * S (t, θ) ∧
      S (t, -θ) = paritySign (ε 1) * S (t, θ))
    (hbound : ∀ q, ‖S q‖ ≤ C) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ρ₁ < ρ ∧
      ∃ (u₀ : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (localDisk 0 ρ₁) u₀ ∧
        HasWeakJetOn 2 (localDisk 0 ρ₁) u₀ E ∧
        ContinuousOn u₀ (localDisk 0 ρ₁) ∧
        (∀ p ∈ localDisk 0 ρ₁, ‖u₀ p‖ ≤ C * Real.rpow (localRadius 0 p) a) ∧
        (∀ k ≤ 2, RadialJetRpowLp k (a + 1 - (k : ℝ)) (localDisk 0 ρ₁) 0 E) ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ₁)), E [0, 0] p + E [1, 1] p = F p) ∧
        HasAxisParityOn ε (localDisk 0 ρ₁) u₀ ∧
        ∀ q, logCylinderPlane q ∈ localDisk 0 ρ₁ →
          u₀ (logCylinderPlane q) = (Real.exp (-a * q.1) : ℂ) * S q := by
  let u₀ := cylinderPhysicalValue a S
  let E := cylinderCartesianJet a J
  let U := localDisk 0 (ρ / 2)
  have hE0 : E [] = u₀ := by
    dsimp only [E, cylinderCartesianJet, u₀]
    rw [hJ.1]
  have hL : ∀ w, w.length ≤ 2 → MemLp (E w) 2 (volume.restrict U) :=
    cylinderCartesianJet_memLp ha hJ.2.2
  have hW : HasWeakJetOn 2 (U \ {0}) u₀ E := by
    refine ⟨hE0, ?_⟩
    intro w hw j
    exact (cylinderCartesianJet_hasWeakPartial ha hJ w hw j).mono
      (fun p hp ↦ ⟨mem_univ p, hp.2⟩)
  have hwhole := hW.remove_point hL
  have hU : U ⊆ localDisk 0 ρ := by
    intro p hp
    exact lt_trans (show localRadius 0 p < ρ / 2 from hp) (by linarith)
  have hEq : ∀ᵐ p ∂(volume.restrict U), E [0, 0] p + E [1, 1] p = F p :=
    (cylinderCartesianJet_forcing hP).filter_mono
      (ae_mono (Measure.restrict_mono hU le_rfl))
  refine ⟨ρ / 2, by positivity, by linarith, u₀, E,
    hwhole.memSobolevOn hL, hwhole,
    (continuous_cylinderPhysicalValue (by linarith) hS hbound).continuousOn,
    fun p _ ↦ norm_cylinderPhysicalValue_le hbound p, ?_, hEq, ?_,
    fun q _ ↦ cylinderPhysicalValue_plane a S q⟩
  · intro k hk w hw
    simpa only [E, hw] using
      (cylinderCartesianJet_weighted hJ.2.2 w (by omega)).mono_measure
        (show volume.restrict U ≤ volume from Measure.restrict_le_self)
  · intro j
    exact Filter.Eventually.of_forall
      (cylinderPhysicalValue_axis_parity (by linarith) hp j)

/-- The original Poisson data supply all premises of physical reconstruction;
the same actual signed candidate is retained (`lem:cylinder-forcing-particular`). -/
theorem cylinder_forcing_particular {ρ a : ℝ} (hρ : 0 < ρ) (ha : 1 < a)
    {ε : Fin 2 → Bool} (hgap : ∀ m : ℕ, AllowedSaddleDegree ε m → a ≠ (m : ℝ))
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), D [0, 0] p + D [1, 1] p = F p)
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hF : MemLp (fun p ↦ F p / (Real.rpow (localRadius 0 p) (a - 1) : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) :
    ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ ρ₁ < ρ ∧ 0 < C ∧
      ∃ (u₀ : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (localDisk 0 ρ₁) u₀ ∧
        HasWeakJetOn 2 (localDisk 0 ρ₁) u₀ E ∧
        ContinuousOn u₀ (localDisk 0 ρ₁) ∧
        (∀ p ∈ localDisk 0 ρ₁, ‖u₀ p‖ ≤ C * Real.rpow (localRadius 0 p) a) ∧
        (∀ k ≤ 2, RadialJetRpowLp k (a + 1 - (k : ℝ)) (localDisk 0 ρ₁) 0 E) ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ₁)), E [0, 0] p + E [1, 1] p = F p) ∧
        HasAxisParityOn ε (localDisk 0 ρ₁) u₀ ∧
        ∀ q, logCylinderPlane q ∈ localDisk 0 ρ₁ →
          u₀ (logCylinderPlane q) = (Real.exp (-a * q.1) : ℂ) *
            cylinderJointSynthesis (cylinderSignedInverse a (cylinderForcing_memLp hF)) q := by
  have hG := cylinderForcing_memLp hF
  obtain ⟨J, hJ, hP⟩ := cylinder_signed_inverse_weak ha.le
    (M := {m | AllowedSaddleDegree ε m}) hgap hG
    (cylinder_forcing_fourier_data hp hD hΔ hF).2.2
  have hS := cylinder_forcing_joint_inverse ha.le hgap hp hD hΔ hF
  obtain ⟨C, hC, hb⟩ := hS.2.2.2.2.2
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, u₀, E, he⟩ :=
    cylinder_cartesian_particular hρ ha hJ hP hS.1 hS.2.2.2.2.1 hb
  exact ⟨ρ₁, C, hρ₁, hρ₁ρ, hC, u₀, E, he⟩

end NoEmbeddedEigenvalues
