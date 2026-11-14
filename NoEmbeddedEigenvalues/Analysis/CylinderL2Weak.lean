import NoEmbeddedEigenvalues.Analysis.CylinderIntegralWeak
import NoEmbeddedEigenvalues.Analysis.CylinderLiftL2
import NoEmbeddedEigenvalues.Analysis.CylinderSpectralCutoff
import NoEmbeddedEigenvalues.WeakPartialLimit
import NoEmbeddedEigenvalues.WeakPartialLocality
import NoEmbeddedEigenvalues.LocalJets

/-!
# Weak differentiation of the normalized cylinder L² inverse

Finite-mass spectral cutoffs make both members of a specified derivative pair
integrable. Their actual inverse integrals satisfy whole-plane weak identities.
The inverse isometry and exact strip mass transport joint strong L² convergence
to every translated angular period. Weak-pair closedness and genuine open-patch
locality then give the identity everywhere, including every angular seam.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- An L² spectral multiplier gives the specified weak partial derivative on the
entire real-angle lift. Neither spectrum is assumed integrable. -/
theorem cylinderInverseL2_hasWeakPartial {H : ℝ × ℤ → ℂ}
    (hH : MemLp H 2 cylinderFourierMeasure) (j : Fin 2)
    (hD : MemLp (fun p ↦ cylinderDerivativeSymbol j p * H p) 2 cylinderFourierMeasure) :
    HasWeakPartialOn univ j
      ((cylinderInverseL2 (hH.toLp H) : ℝ × AddCircle (2 * Real.pi) → ℂ) ∘
        logCylinderProjection)
      ((cylinderInverseL2 (hD.toLp (fun p ↦ cylinderDerivativeSymbol j p * H p)) :
        ℝ × AddCircle (2 * Real.pi) → ℂ) ∘ logCylinderProjection) := by
  let D := fun p ↦ cylinderDerivativeSymbol j p * H p
  let S (N : ℕ) := cylinderJointSynthesis (cylinderSpectralCutoff N H)
  let T (N : ℕ) := cylinderJointSynthesis (cylinderSpectralCutoff N D)
  have hS (N : ℕ) : MemLp (S N) 2 logCylinderMeasure :=
    cylinderJointSynthesis_cutoff_memLp hH N
  have hT (N : ℕ) : MemLp (T N) 2 logCylinderMeasure :=
    cylinderJointSynthesis_cutoff_memLp hD N
  have he (N : ℕ) :
      (fun p ↦ cylinderDerivativeSymbol j p * cylinderSpectralCutoff N H p) =
        cylinderSpectralCutoff N D := by
    have hjet (K : ℝ × ℤ → ℂ) :
        cylinderSpectralJet [j] K = fun p ↦ cylinderDerivativeSymbol j p * K p := by
      funext p
      simp only [cylinderSpectralJet, cylinderJetSymbol, mul_one]
    simpa only [hjet] using cylinderSpectralJet_cutoff [j] N H
  have hw (N : ℕ) : HasWeakPartialOn univ j
      (S N ∘ logCylinderProjection) (T N ∘ logCylinderProjection) := by
    have hi : Integrable (fun p ↦ cylinderDerivativeSymbol j p * cylinderSpectralCutoff N H p)
        cylinderFourierMeasure := by
      rw [he N]
      exact cylinderSpectralCutoff_integrable hD N
    simpa only [he N] using
      cylinderJointSynthesis_hasWeakPartial (cylinderSpectralCutoff_integrable hH N) j hi
  have hs : Tendsto (fun N ↦ (hS N).toLp (S N)) atTop
      (𝓝 (cylinderInverseL2 (hH.toLp H))) :=
    cylinderJointSynthesis_cutoff_tendsto hH
  have ht : Tendsto (fun N ↦ (hT N).toLp (T N)) atTop
      (𝓝 (cylinderInverseL2 (hD.toLp D))) :=
    cylinderJointSynthesis_cutoff_tendsto hD
  apply hasWeakPartialOn_of_locally
  intro q _
  let a := q.2 - Real.pi
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioo a (a + 2 * Real.pi)
  let V : Set (ℝ × ℝ) := univ ×ˢ Ioc a (a + 2 * Real.pi)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hq : q ∈ U := by
    refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp only [a] <;> linarith [Real.pi_pos]
  refine ⟨U, hU, hq, ?_⟩
  have hs' := tendsto_L2_logCylinderProjection_strip hS
    (Lp.memLp (cylinderInverseL2 (hH.toLp H)))
    (by simpa only [Lp.toLp_coeFn] using hs) a
  have ht' := tendsto_L2_logCylinderProjection_strip hT
    (Lp.memLp (cylinderInverseL2 (hD.toLp D)))
    (by simpa only [Lp.toLp_coeFn] using ht) a
  exact (HasWeakPartialOn.of_tendsto_L2 (fun N ↦ (hw N).mono (subset_univ V))
    (fun N ↦ memLp_logCylinderProjection_strip (hS N) a)
    (fun N ↦ memLp_logCylinderProjection_strip (hT N) a)
    (memLp_logCylinderProjection_strip (Lp.memLp _) a)
    (memLp_logCylinderProjection_strip (Lp.memLp _) a) hs' ht').mono
      (prod_mono Subset.rfl Ioo_subset_Ioc_self)

/-- Every ordered inverse-class identification gives the same specified weak
jet, retaining a pointwise actual nil integral and without commuting entries. -/
theorem cylinderInverseL2_family_hasWeakJet {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {E : List (Fin 2) → ℝ × AddCircle (2 * Real.pi) → ℂ}
    (hE0 : E [] = cylinderJointSynthesis H)
    (hEA : ∀ (w : List (Fin 2)) (hw : w.length ≤ 2),
      E w =ᵐ[logCylinderMeasure]
        (cylinderInverseL2 ((cylinderSpectralJet_memLp hH hWH hw).toLp
          (cylinderSpectralJet w H)) : ℝ × AddCircle (2 * Real.pi) → ℂ)) :
    HasWeakJetOn 2 univ (cylinderJointSynthesis H ∘ logCylinderProjection)
      (fun w ↦ E w ∘ logCylinderProjection) := by
  refine ⟨congrArg (fun f ↦ f ∘ logCylinderProjection) hE0, ?_⟩
  intro w hw j
  have hw' : w.length ≤ 2 := Nat.le_of_lt hw
  have hjw : (j :: w).length ≤ 2 := by simpa using Nat.succ_le_of_lt hw
  have he : (fun p ↦ cylinderDerivativeSymbol j p * cylinderSpectralJet w H p) =
      cylinderSpectralJet (j :: w) H := by
    funext p
    simp only [cylinderSpectralJet, cylinderJetSymbol, mul_assoc]
  have hd : MemLp (fun p ↦ cylinderDerivativeSymbol j p * cylinderSpectralJet w H p) 2
      cylinderFourierMeasure := by
    rw [he]
    exact cylinderSpectralJet_memLp hH hWH hjw
  have hp := cylinderInverseL2_hasWeakPartial (cylinderSpectralJet_memLp hH hWH hw') j hd
  have heLp : hd.toLp (fun p ↦ cylinderDerivativeSymbol j p * cylinderSpectralJet w H p) =
      (cylinderSpectralJet_memLp hH hWH hjw).toLp (cylinderSpectralJet (j :: w) H) := by
    exact hd.toLp_congr (cylinderSpectralJet_memLp hH hWH hjw)
      (Filter.Eventually.of_forall (congrFun he))
  rw [heLp] at hp
  apply hp.congr_ae_on MeasurableSet.univ
  · exact (ae_logCylinderProjection (hEA w hw').symm).mono fun p hp _ ↦ hp
  · exact (ae_logCylinderProjection (hEA (j :: w) hjw).symm).mono fun p hp _ ↦ hp

end NoEmbeddedEigenvalues
