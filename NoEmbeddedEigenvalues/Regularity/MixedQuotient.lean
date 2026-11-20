import NoEmbeddedEigenvalues.Regularity.MixedDividedEquation
import NoEmbeddedEigenvalues.Regularity.MixedVorticityDivision
import NoEmbeddedEigenvalues.Regularity.MixedQuotientTraces
import NoEmbeddedEigenvalues.LocalContinuousRepresentative

/-! # Construction of the mixed quotient on the closed cell -/

noncomputable section
namespace NoEmbeddedEigenvalues

open Set MeasureTheory Filter
local notation "π" => Real.pi
local notation "Plane" => ℝ × ℝ

private theorem contStream_diagInv_neg {ω : L2} (hs : InSector false true ω) (q : Plane) :
    contStream ω (diagInv (-q)) = -contStream ω (diagInv q) := by
  have ha := contStream_diagonalTraceChart_character hs 0 true (q.2, q.1)
  have hb := contStream_diagonalTraceChart_character hs 1 true (π - q.1, q.2)
  have ht : 2 * cellEdgeNormal true = π := by simp [cellEdgeNormal]; ring
  have h₁ : contStream ω (diagInv (π - q.1, q.2)) = -contStream ω (diagInv q) := by
    simpa only [paritySign, normalReflection_apply, ht, diagonalTraceChart, ite_true,
      Bool.false_eq_true, ite_false, neg_one_mul, Prod.mk.eta] using ha
  have h₂ : contStream ω (diagInv (π - q.1, π - q.2)) =
      contStream ω (diagInv (π - q.1, q.2)) := by
    simpa only [paritySign, normalReflection_apply, ht, diagonalTraceChart, one_ne_zero,
      ite_false, ite_true, one_mul] using hb
  have hp : diagInv (π - q.1, π - q.2) = liftShift (1, 0) (diagInv (-q)) := by
    ext <;> simp [liftShift] <;> ring
  rw [hp, contStream, torusProj_liftShift, ← contStream] at h₂
  exact h₂.trans h₁

private theorem mixed_closedCell :
    closure mixedOpenCell = Icc (-π / 2) (π / 2) ×ˢ Icc (-π / 2) (π / 2) := by
  rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by linarith [Real.pi_pos] : -π / 2 ≠ π / 2)]

private theorem mixed_quotient_central_odd {ω : L2} (hs : InSector false true ω)
    {φ : Plane → ℂ} (hc : ContinuousOn φ (closure mixedOpenCell))
    (he : (contStream ω ∘ diagInv) =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ (Real.cos q.1 : ℂ) * φ q) :
    ∀ q ∈ closure mixedOpenCell, φ (-q) = -φ q := by
  have hU : IsOpen mixedOpenCell := isOpen_Ioo.prod isOpen_Ioo
  have hprod : EqOn (contStream ω ∘ diagInv) (fun q ↦ (Real.cos q.1 : ℂ) * φ q)
      mixedOpenCell := Measure.eqOn_open_of_ae_eq he hU
    ((continuous_contStream ω).comp diagInv.continuous).continuousOn
    ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).continuousOn.mul
      (hc.mono subset_closure))
  have hmap : MapsTo Neg.neg mixedOpenCell mixedOpenCell := by
    intro p hp
    change (-π / 2 < -p.1 ∧ -p.1 < π / 2) ∧ (-π / 2 < -p.2 ∧ -p.2 < π / 2)
    exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩,
      ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩
  have hcmap : MapsTo Neg.neg (closure mixedOpenCell) (closure mixedOpenCell) := by
    rw [mixed_closedCell]
    intro p hp
    change (-π / 2 ≤ -p.1 ∧ -p.1 ≤ π / 2) ∧ (-π / 2 ≤ -p.2 ∧ -p.2 ≤ π / 2)
    exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩,
      ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩
  have hodd : EqOn (fun q ↦ φ (-q)) (fun q ↦ -φ q) mixedOpenCell := by
    intro p hp
    have h := contStream_diagInv_neg hs p
    have h₀ := hprod hp
    have h₁ := hprod (hmap hp)
    change contStream ω (diagInv p) = _ at h₀
    change contStream ω (diagInv (-p)) = _ at h₁
    rw [h₀, h₁] at h
    change (Real.cos (-p.1) : ℂ) * φ (-p) = -((Real.cos p.1 : ℂ) * φ p) at h
    rw [Real.cos_neg, ← mul_neg] at h
    have hc₀ := Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hp.1)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc₀.ne') h
  exact hodd.of_subset_closure (hc.comp continuous_neg.continuousOn hcmap)
    hc.neg subset_closure Subset.rfl

/-- Construct all the quotient data using the H¹ vorticity and H³ stream
on the same absolute-level collar, without a Sobolev gain at the cell center. -/
theorem mixed_quotient_data_of_collar {ω : L2} (hm : MeanZero ω)
    (hs : InSector false true ω) {ε : ℝ} (hε : 0 < ε)
    (hω : MemSobolevLocOn 1 {p | |dipoleLift p| < ε} (liftL2 ω))
    (hψ : MemSobolevLocOn 3 {p | |dipoleLift p| < ε} (contStream ω)) :
    Nonempty (MixedQuotientData ω) := by
  let U : Set Plane := {q | |q.1| < π}
  let J := Ioo (-(3 * π / 4)) (3 * π / 4)
  let K := J ×ˢ J
  let Q := fun q : Plane ↦ contStream ω (diagInv q) / (Real.cos q.1 : ℂ)
  have hU : IsOpen U := isOpen_lt continuous_fst.abs continuous_const
  have hK : IsOpen K := isOpen_Ioo.prod isOpen_Ioo
  have hπ := Real.pi_pos
  have hclK : closure K = Icc (-(3 * π / 4)) (3 * π / 4) ×ˢ Icc (-(3 * π / 4)) (3 * π / 4) := by
    rw [show K = J ×ˢ J from rfl, closure_prod_eq,
      show closure J = Icc _ _ from closure_Ioo (by linarith)]
  have hcomp : IsCompact (closure K) := hclK ▸ isCompact_Icc.prod isCompact_Icc
  have hKU : closure K ⊆ U := by
    rw [hclK]
    intro q hq
    change |q.1| < π
    exact abs_lt.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
  have hcellK : closure mixedOpenCell ⊆ K := by
    rw [mixed_closedCell]
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  have hloc := mixed_stream_quotient_local_h2 hs hε hψ
  obtain ⟨φ, hc, he⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two hU hloc
  have heK := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hKU) he
  have hφ : MemSobolevOn 2 K φ := (hloc _ hK hcomp hKU).congr_ae_on hK.measurableSet
    ((ae_restrict_iff' hK.measurableSet).mp heK)
  obtain ⟨D, hD, _⟩ := memSobolevOn_iff_exists_weakJet.mp hφ
  have hsub : mixedOpenCell ⊆ K := subset_closure.trans hcellK
  have hc' := hc.mono (hcellK.trans (subset_closure.trans hKU))
  have hprod : (contStream ω ∘ diagInv) =ᵐ[volume.restrict mixedOpenCell]
      fun q ↦ (Real.cos q.1 : ℂ) * φ q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heK,
      ae_restrict_mem (isOpen_Ioo.prod isOpen_Ioo).measurableSet] with p hp hpU
    have hn : (Real.cos p.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using hpU.1)).ne'
    change Q p = φ p at hp
    change contStream ω (diagInv p) = _
    rw [← hp]
    exact (mul_div_cancel₀ _ hn).symm
  have hfactor : ∀ᵐ q ∂(volume.restrict mixedOpenCell),
      liftL2 (invLap ω) (diagInv q) = (Real.cos q.1 : ℂ) * φ q := by
    filter_upwards [ae_restrict_of_ae (quasiMeasurePreserving_diagInv.ae
      (streamLift_ae_eq_contStream ω)), hprod] with q hq hp
    exact hq.trans hp
  exact ⟨{
    phi := φ
    jet := D
    h2 := hφ.mono hsub
    weakJet := hD.mono hsub
    continuous := hc'
    stream_eq := hfactor
    vorticity_divided := mixed_vorticity_divided_of_collar hs hε hω
    laplace_eq := mixed_divided_equation hm (hD.mono hsub) hfactor
    normal_zero := mixed_quotient_normal_zero hs hφ hD heK
    central_odd := mixed_quotient_central_odd hs hc' hprod }⟩

end NoEmbeddedEigenvalues
