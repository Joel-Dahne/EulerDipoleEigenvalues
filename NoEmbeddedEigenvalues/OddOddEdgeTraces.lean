import NoEmbeddedEigenvalues.DiagonalH1
import NoEmbeddedEigenvalues.ReflectedTraces
import NoEmbeddedEigenvalues.PeriodicWeightedGradient

/-!
# Odd–odd canonical traces on adjacent cell sides

Blueprint: `lem:odd-odd-reflected-edge-traces`.

Both diagonal symmetries act by minus one on the actual vorticity lift.
Normal reflection in any of the four regular cell edges is the corresponding
torus symmetry, modulo periods. Transport ordinary H¹ before constructing the
opposite-side trace, then identify it with minus the original canonical trace.
Zero therefore gives matching traces, without evaluating the raw lift on an edge.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open Real

/-- Normal reflection of a diagonal cell-edge chart is exactly a torus symmetry,
for either sign of its normal endpoint. -/
theorem torusProj_diagonalTraceChart_reflection (j : Fin 2) (side : Bool) (q : ℝ × ℝ) :
    torusProj (diagonalTraceChart j (normalReflection (2 * cellEdgeNormal side) q)) =
      (if j = 0 then S₁ else S₂) (torusProj (diagonalTraceChart j q)) := by
  have hc : ((2 * cellEdgeNormal side : ℝ) : Angle) = (π : Angle) := by
    cases side
    · rw [show 2 * cellEdgeNormal false = -π by simp [cellEdgeNormal]; ring]
      exact Angle.neg_coe_pi
    · congr 1
      simp only [cellEdgeNormal, ite_true]
      ring
  fin_cases j
  · change torusProj (diagInv ((normalReflection (2 * cellEdgeNormal side) q).2,
        (normalReflection (2 * cellEdgeNormal side) q).1)) =
      S₁ (torusProj (diagInv (q.2, q.1)))
    ext <;> simp only [normalReflection_apply, diagInv_apply, torusProj, S₁,
      Angle.coe_add, Angle.coe_sub, hc] <;> abel
  · change torusProj (diagInv (normalReflection (2 * cellEdgeNormal side) q)) =
      S₂ (torusProj (diagInv q))
    ext
    · simp only [normalReflection_apply, diagInv_apply, torusProj, S₂,
        Angle.coe_add, Angle.coe_sub, hc]
      abel
    · simp only [normalReflection_apply, diagInv_apply, torusProj, S₂,
        Angle.coe_add, Angle.coe_sub, hc]
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg, Angle.neg_coe_pi]
      abel

/-- Odd parity of the actual pullback in each of the four cell-edge charts. -/
theorem liftL2_diagonalTraceChart_reflection_ae {ω : L2} (hs : InSector false false ω)
    (j : Fin 2) (side : Bool) :
    ∀ᵐ q : ℝ × ℝ, liftL2 ω (diagonalTraceChart j
      (normalReflection (2 * cellEdgeNormal side) q)) =
        -liftL2 ω (diagonalTraceChart j q) := by
  have htor (S : Torus → Torus) (hm : MeasurePreserving S volume volume)
      (he : pullback S hm ω = (-1 : ℂ) • ω) : ∀ᵐ t : Torus, ω (S t) = -ω t := by
    filter_upwards [ae_comp_of_pullback_eq he, Lp.coeFn_smul (-1 : ℂ) ω] with t ht hsm
    simp only [ht, hsm, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  have hp : ∀ᵐ p : ℝ × ℝ, ω ((if j = 0 then S₁ else S₂) (torusProj p)) =
      -ω (torusProj p) := by
    fin_cases j
    · exact ae_torusProj (htor S₁ measurePreserving_S₁ hs.1)
    · exact ae_torusProj (htor S₂ measurePreserving_S₂ hs.2)
  filter_upwards [(quasiMeasurePreserving_diagonalTraceChart j).ae hp] with q hq
  change ω (torusProj (diagonalTraceChart j
    (normalReflection (2 * cellEdgeNormal side) q))) = -ω (torusProj (diagonalTraceChart j q))
  rw [torusProj_diagonalTraceChart_reflection]
  exact hq

/-- A supplied ordinary cell H¹ strip and its canonical zero edge trace produce
ordinary H¹ and the same zero trace on the adjacent reflected rectangle. -/
theorem HasCellEdgeTrace.oddOdd_reflected {ω : L2} (hs : InSector false false ω)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hF : MemSobolevOn 1 V (liftL2 ω))
    {j : Fin 2} {side : Bool}
    (hT : HasCellEdgeTrace V j side (liftL2 ω) (fun _ ↦ 0))
    {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    (hI : Icc l r ⊆ Ioo (-π / 2) (π / 2))
    (hedge : if side then b = cellEdgeNormal side else a = cellEdgeNormal side)
    (hsub : diagonalTraceChart j '' (Ioo l r ×ˢ Ioo a b) ⊆ V) :
    MemSobolevOn 1
      (Ioo l r ×ˢ Ioo (2 * cellEdgeNormal side - b) (2 * cellEdgeNormal side - a))
      (liftL2 ω ∘ diagonalTraceChart j) ∧
    HasTransverseH1Trace l r (2 * cellEdgeNormal side - b) (2 * cellEdgeNormal side - a)
      (cellEdgeNormal side) (diagonalTraceChart j) (liftL2 ω) (fun _ ↦ 0) := by
  have hS := (hF.comp_diagonalTraceChart hV j).mono (image_subset_iff.mp hsub)
  have ht := hT l r a b hlr hab hI hedge hsub
  have hR := ht.reflect_normal (c := 2 * cellEdgeNormal side) hS (-1)
  have he : (fun q ↦ (-1 : ℂ) * liftL2 ω (diagonalTraceChart j
      (normalReflection (2 * cellEdgeNormal side) q))) =ᵐ[volume]
      (liftL2 ω ∘ diagonalTraceChart j) := by
    filter_upwards [liftL2_diagonalTraceChart_reflection_ae hs j side] with q hq
    simp only [Function.comp_apply, hq, neg_one_mul, neg_neg]
  refine ⟨hR.1.congr_ae he, ?_⟩
  have htrace := hR.2.congr_ae_pullback (C' := diagonalTraceChart j) (F' := liftL2 ω)
    (ae_restrict_of_ae he)
  simpa only [show 2 * cellEdgeNormal side - cellEdgeNormal side = cellEdgeNormal side by ring,
    mul_zero] using htrace

/-- Periodic translation preserves the actual pullback and hence the canonical
trace on every one of these local windows. -/
theorem HasTransverseH1Trace.liftShift {l r a b t : ℝ}
    {C : ℝ × ℝ → ℝ × ℝ} {ω : L2} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t C (liftL2 ω) T) (n : ℤ × ℤ) :
    HasTransverseH1Trace l r a b t (liftShift n ∘ C) (liftL2 ω) T := by
  apply h.congr_ae_pullback
  exact Eventually.of_forall fun q ↦ (liftL2_liftShift ω n (C q)).symm

end NoEmbeddedEigenvalues
