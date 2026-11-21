module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.TransportRotations

/-!
# Four complex quarter-character projections of raw transport fields

Blueprint: `def:transport-quarter-projection`, `lem:transport-quarter-projections`.

The finite Fourier formula is pointwise, including on exceptional sets.
Restricted measure-preserving rotations separately transfer the a.e. agreement
of the original forcing and its supplied continuous representative.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Projection onto the quarter character κ, for κ⁴ = 1. The definition makes
sense for every complex κ and every raw spatial function. -/
def quarterCharacterProjection (κ : ℂ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 / 4 : ℂ) * (F p + κ ^ 3 * F (rotLift p) +
    κ ^ 2 * F (rotLift (rotLift p)) + κ * F (rotLift (rotLift (rotLift p))))

/-- The four-term Fourier projection has its character everywhere, not just a.e. -/
theorem quarterCharacterProjection_rotLift {κ : ℂ} (hκ : κ ^ 4 = 1)
    (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    quarterCharacterProjection κ F (rotLift p) = κ * quarterCharacterProjection κ F p := by
  have he : rotLift (rotLift (rotLift (rotLift p))) = p := by simp [rotLift]
  dsimp only [quarterCharacterProjection]
  rw [he]
  linear_combination -(F (rotLift p) / 4) * hκ

/-- The four complex characters reconstruct the original raw field pointwise. -/
theorem quarterCharacterProjection_sum (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    quarterCharacterProjection 1 F p + quarterCharacterProjection (-1) F p +
      quarterCharacterProjection Complex.I F p +
      quarterCharacterProjection (-Complex.I) F p = F p := by
  simp [quarterCharacterProjection, pow_succ]
  ring

/-- On an invariant domain the same finite projection of both fields preserves
all transport-pair hypotheses, including the original real frequency. -/
theorem IsTransportPair.quarterCharacterProjection {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f)
    (hRU : rotLift ⁻¹' U = U) (κ : ℂ) :
    IsTransportPair lam U (quarterCharacterProjection κ v) (quarterCharacterProjection κ f) := by
  have h1 := hp.comp_rotLift
  rw [hRU] at h1
  have h2 := h1.comp_rotLift
  rw [hRU] at h2
  have h3 := h2.comp_rotLift
  rw [hRU] at h3
  exact (((hp.add (h1.const_mul (κ ^ 3))).add (h2.const_mul (κ ^ 2))).add
    (h3.const_mul κ)).const_mul (1 / 4)

/-- The projected supplied forcing remains continuous on the same invariant domain. -/
theorem continuousOn_quarterCharacterProjection {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ}
    (hg : ContinuousOn g U) (hRU : rotLift ⁻¹' U = U) (κ : ℂ) :
    ContinuousOn (quarterCharacterProjection κ g) U := by
  have hR : MapsTo rotLift U U := fun p hp ↦ by
    change p ∈ rotLift ⁻¹' U
    rwa [hRU]
  have hc : Continuous rotLift := by unfold rotLift; fun_prop
  have h1 := hg.comp hc.continuousOn hR
  have h2 := h1.comp hc.continuousOn hR
  have h3 := h2.comp hc.continuousOn hR
  exact (((hg.add (h1.const_mul (κ ^ 3))).add (h2.const_mul (κ ^ 2))).add
    (h3.const_mul κ)).const_mul (1 / 4)

/-- Projection preserves a.e. equality on the restricted invariant domain;
no global measurability or equality outside that domain is used. -/
theorem quarterCharacterProjection_congr_ae {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    (hRU : rotLift ⁻¹' U = U) {f g : ℝ × ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict U] g) (κ : ℂ) :
    quarterCharacterProjection κ f =ᵐ[volume.restrict U] quarterCharacterProjection κ g := by
  have hm : MeasurePreserving rotLift (volume.restrict U) (volume.restrict U) := by
    simpa only [hRU] using measurePreserving_rotLift.restrict_preimage hU
  have h1 := hm.quasiMeasurePreserving.ae hfg
  have h2 := hm.quasiMeasurePreserving.ae h1
  have h3 := hm.quasiMeasurePreserving.ae h2
  filter_upwards [hfg, h1, h2, h3] with p h0 h1 h2 h3
  simp only [quarterCharacterProjection, h0, h1, h2, h3]

/-- The original continuous corner zeros persist under every finite projection. -/
theorem quarterCharacterProjection_zero_at_saddles {g : ℝ × ℝ → ℂ}
    (hz : ∀ P ∈ saddleSet, P ∈ closure cellSquare → g P = 0) (κ : ℂ) :
    ∀ P ∈ saddleSet, P ∈ closure cellSquare → quarterCharacterProjection κ g P = 0 := by
  intro P hP hPc
  have hs1 := rotLift_mem_saddleSet hP
  have hs2 := rotLift_mem_saddleSet hs1
  have hs3 := rotLift_mem_saddleSet hs2
  have hc1 := rotLift_mem_closure_cellSquare hPc
  have hc2 := rotLift_mem_closure_cellSquare hc1
  have hc3 := rotLift_mem_closure_cellSquare hc2
  simp only [quarterCharacterProjection, hz P hP hPc, hz _ hs1 hc1,
    hz _ hs2 hc2, hz _ hs3 hc3, mul_zero, zero_add]

end NoEmbeddedEigenvalues
