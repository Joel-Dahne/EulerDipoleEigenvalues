module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleChartPullback
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SaddleDistanceWeights
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.StreamElliptic
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderInverse

/-!
# Canonical stream data for saddle cylinder inversion

The orthonormal chart transports the actual Fourier second jet, not unrelated
derivative witnesses. Orthogonality identifies its Laplacian with the raw
vorticity pullback. Finite H² norms and axis parity precede cylinder inversion;
neither ordinary separatrix regularity nor weighted forcing is used.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Every bounded saddle disk has finite ordinary H² mass for the actual stream. -/
theorem memSobolevOn_contStream_saddleChart (ω : L2)
    {P : ℝ × ℝ} (hP : P ∈ saddleSet) (ρ : ℝ) :
    MemSobolevOn 2 (localDisk 0 ρ) (contStream ω ∘ saddleOrthoChart P) := by
  have hU : IsOpen (localDisk P ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hb : Bornology.IsBounded (localDisk P ρ) :=
    Metric.isBounded_ball.subset fun p hp ↦ (dist_le_localRadius P p).trans_lt hp
  have hf := (memSobolevOn_liftL2 (memSobolev_two_invLap ω) hb).congr_value
    (streamLift_ae_eq_contStream ω)
  have he := hf.comp_planeAffine (saddleLinear P hP) P
    (by simpa only [planeAffine_saddleLinear] using measurePreserving_saddleChart hP) hU
  have hpre : planeAffine (saddleLinear P hP) P ⁻¹' localDisk P ρ = localDisk 0 ρ := by
    ext q
    change localRadius P (planeAffine (saddleLinear P hP) P q) < ρ ↔ _
    rw [planeAffine_saddleLinear P hP, localRadius_saddleChart hP]
    rfl
  rw [hpre] at he
  simpa only [planeAffine_saddleLinear] using he

/-- The charted specified jet is the affine transform of the fixed Fourier jet. -/
theorem streamJet2_saddle_weak (ω : L2) {P : ℝ × ℝ} (hP : P ∈ saddleSet) (ρ : ℝ) :
    HasWeakJetOn 2 (localDisk 0 ρ) (contStream ω ∘ saddleOrthoChart P)
      (affineJet (saddleLinear P hP) P (streamJet2 ω)) := by
  have hU : IsOpen (localDisk P ρ) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hd := (streamJet2_weak ω (localDisk P ρ)).comp_planeAffine
    (saddleLinear P hP) P
    (by simpa only [planeAffine_saddleLinear] using measurePreserving_saddleChart hP) hU
  have hpre : planeAffine (saddleLinear P hP) P ⁻¹' localDisk P ρ = localDisk 0 ρ := by
    ext q
    change localRadius P (planeAffine (saddleLinear P hP) P q) < ρ ↔ _
    rw [planeAffine_saddleLinear P hP, localRadius_saddleChart hP]
    rfl
  rw [hpre] at hd
  simpa only [planeAffine_saddleLinear] using hd

/-- The Euclidean Laplacian has no Jacobian or mixed-derivative defect in the chart. -/
theorem streamJet2_saddle_laplacian {ω : L2} (hω : MeanZero ω)
    {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∀ᵐ q, affineJet (saddleLinear P hP) P (streamJet2 ω) [0, 0] q +
      affineJet (saddleLinear P hP) P (streamJet2 ω) [1, 1] q =
      liftL2 ω (saddleOrthoChart P q) := by
  filter_upwards [(measurePreserving_saddleChart hP).quasiMeasurePreserving.ae
    (streamJet2_laplacian hω)] with q hq
  rw [affineJet_saddle_laplacian hP]
  exact hq

/-- Both odd reflection identities hold for the actual continuous stream in
saddle coordinates. No raw values on a null axis are evaluated. -/
theorem contStream_chart_parity {P : ℝ × ℝ} (hP : P ∈ saddleSet) {ω : L2}
    (hs : InSector false false ω) :
    ∀ j, ∀ᵐ q, contStream ω (saddleOrthoChart P (axisReflect j q)) =
      -contStream ω (saddleOrthoChart P q) := by
  have heq : liftL2 (invLap ω) =ᵐ[volume] contStream ω := streamLift_ae_eq_contStream ω
  have hc := (measurePreserving_saddleChart hP).quasiMeasurePreserving.ae heq
  intro j
  filter_upwards [saddle_chart_parity hP hs.invLap j, hc,
    (measurePreserving_axisReflect j).quasiMeasurePreserving.ae hc] with q hq h0 h1
  rwa [h0, h1] at hq

/-- Cylinder inversion applied to the canonical odd–odd stream and raw vorticity.
The physical forcing weight remains an explicit input, to be supplied by the
first or second transport gain at the corresponding exponent. -/
theorem oddOdd_stream_cylinder_inverse {ω : L2} (hω : MeanZero ω)
    (hs : InSector false false ω) {P : ℝ × ℝ} (hP : P ∈ saddleSet)
    {ρ a : ℝ} (hρ : 0 < ρ) (ha : 1 < a)
    (hgap : ∀ m : ℕ, AllowedSaddleDegree (fun _ ↦ false) m → a ≠ (m : ℝ))
    (hF : MemLp (fun q ↦ liftL2 ω (saddleOrthoChart P q) /
      (Real.rpow (localRadius 0 q) (a - 1) : ℂ)) 2
        (volume.restrict (localDisk 0 ρ))) :
    ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ ρ₁ < ρ ∧ 0 < C ∧
      ∃ (u₀ h : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (localDisk 0 ρ₁) u₀ ∧
        HasWeakJetOn 2 (localDisk 0 ρ₁) u₀ E ∧
        ContinuousOn u₀ (localDisk 0 ρ₁) ∧
        (∀ q ∈ localDisk 0 ρ₁, ‖u₀ q‖ ≤ C * Real.rpow (localRadius 0 q) a) ∧
        (∀ k ≤ 2, RadialJetRpowLp k (a + 1 - (k : ℝ)) (localDisk 0 ρ₁) 0 E) ∧
        (∀ᵐ q ∂(volume.restrict (localDisk 0 ρ₁)), E [0, 0] q + E [1, 1] q =
          liftL2 ω (saddleOrthoChart P q)) ∧
        HasAxisParityOn (fun _ ↦ false) (localDisk 0 ρ₁) u₀ ∧
        IsPlaneHarmonicOn (localDisk 0 ρ₁) h ∧
        HasAxisParityOn (fun _ ↦ false) (localDisk 0 ρ₁) h ∧
        (∀ w : List (Fin 2), ¬AllowedSaddleDegree (fun _ ↦ false) w.length →
          classicalComplexJet w h 0 = 0) ∧
        (∀ᵐ q ∂(volume.restrict (localDisk 0 ρ₁)),
          contStream ω (saddleOrthoChart P q) = u₀ q + h q) := by
  exact cylinder_inverse hρ ha hgap (memSobolevOn_contStream_saddleChart ω hP ρ)
    (streamJet2_saddle_weak ω hP ρ)
    (ae_restrict_of_ae (streamJet2_saddle_laplacian hω hP))
    (by
      intro j
      simpa only [paritySign, Bool.false_eq_true, ite_false, neg_one_mul] using
        ae_restrict_of_ae (contStream_chart_parity hP hs j)) hF

end NoEmbeddedEigenvalues
