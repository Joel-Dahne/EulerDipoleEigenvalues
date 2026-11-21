import NoEmbeddedEigenvalues.Mixed.VirialIdentities.MixedLevelTrace
import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterCellCover

/-! # Full level integrals in signed side coordinates -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Real
open scoped Interval

local notation "Plane" => (ℝ × ℝ)

/-- The regular time density in every signed side chart. -/
def mixedQuarterTimeWeight (s a : ℝ) : ℝ := 1 / √(cos a ^ 2 - s ^ 2)

private def quarterJ (k : ℕ) : Fin 2 := if k = 0 ∨ k = 2 then 0 else 1
private def quarterSign (k : ℕ) : Bool := decide (k = 0 ∨ k = 3)
private def quarterParam (k : ℕ) (a : ℝ) : ℝ := if k < 2 then a else -a

private theorem quarter_rotate (s a : ℝ) {k : ℕ} (hk : k < 4) :
    rotLift^[k] (diagInv (a, quarterHeight s a)) =
      diagInv (mixedQuarterPoint (quarterJ k) (quarterSign k) s (quarterParam k a)) := by
  have hβ : quarterHeight s (-a) = quarterHeight s a := by simp only [quarterHeight, cos_neg]
  interval_cases k <;>
    simp [quarterJ, quarterSign, quarterParam, mixedQuarterPoint, mixedQuarterHeight,
      traceSideCoords, hβ, rotLift, diagInv_apply, Function.iterate_succ_apply'] <;>
    constructor <;> ring

private theorem neg_preimage_levelInterval (s : ℝ) :
    Neg.neg ⁻¹' mixedLevelInterval s = mixedLevelInterval s := by
  ext a
  change (-arccos √s < -a ∧ -a < arccos √s) ↔ _
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

private theorem quarter_neg_mp (s : ℝ) :
    MeasurePreserving Neg.neg (volume.restrict (mixedLevelInterval s))
      (volume.restrict (mixedLevelInterval s)) := by
  simpa only [neg_preimage_levelInterval] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (s := mixedLevelInterval s) measurableSet_Ioo

private theorem quarter_weight_even (s a : ℝ) :
    mixedQuarterTimeWeight s (-a) = mixedQuarterTimeWeight s a := by
  simp only [mixedQuarterTimeWeight, cos_neg]

private theorem orbit_quarter_pair {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {k : ℕ} (hk : k < 4)
    (f : Plane → ℝ) :
    let J := Ioo (-eighthPeriod s) (eighthPeriod s)
    let g := fun a ↦ mixedQuarterTimeWeight s a *
      f (diagInv (mixedQuarterPoint (quarterJ k) (quarterSign k) s a))
    (IntegrableOn (fun t ↦ f (rotLift^[k] (dipoleOrbit s t))) J ↔
      IntegrableOn g (mixedLevelInterval s)) ∧
    (∫ t in J, f (rotLift^[k] (dipoleOrbit s t))) = ∫ a in mixedLevelInterval s, g a := by
  dsimp only
  rw [integrableOn_quarter_iff hs.1 hs.2 (fun p ↦ f (rotLift^[k] p)),
    integral_quarter_eq hs.1 hs.2 (fun p ↦ f (rotLift^[k] p))]
  simp only [quarter_rotate s _ hk, smul_eq_mul]
  by_cases h : k < 2
  · simp only [quarterParam, ite_eq_left h]
    exact ⟨Iff.rfl, rfl⟩
  · simp only [quarterParam, ite_eq_right h]
    let G := fun a ↦ mixedQuarterTimeWeight s a *
      f (diagInv (mixedQuarterPoint (quarterJ k) (quarterSign k) s a))
    have he : (fun a ↦ (1 / √(cos a ^ 2 - s ^ 2)) *
        f (diagInv (mixedQuarterPoint (quarterJ k) (quarterSign k) s (-a)))) = G ∘ Neg.neg := by
      funext a
      rw [Function.comp_apply]
      dsimp only [G]
      rw [quarter_weight_even]
      rfl
    rw [he]
    exact ⟨(quarter_neg_mp s).integrable_comp_emb
        (MeasurableEquiv.neg ℝ).measurableEmbedding,
      (quarter_neg_mp s).integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding G⟩

/-- If the four graph integrands are integrable in the common time density,
their sum is the full level integral, with no extra geometric factor. -/
theorem mixed_levelIntegral_eq_signed_quarters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (f : Plane → ℝ)
    (hf : ∀ (j : Fin 2) (σ : Bool), IntegrableOn
      (fun a ↦ mixedQuarterTimeWeight s a * f (diagInv (mixedQuarterPoint j σ s a)))
      (mixedLevelInterval s)) :
    levelIntegral s f = ∑ j : Fin 2, ∑ σ : Bool, ∫ a in mixedLevelInterval s,
      mixedQuarterTimeWeight s a * f (diagInv (mixedQuarterPoint j σ s a)) := by
  have hL : -eighthPeriod s ≤ eighthPeriod s := by linarith [eighthPeriod_pos hs.1 hs.2]
  rw [levelIntegral_eq_sum_quarter' hs.1 hs.2 (fun k hk ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL).2
      ((orbit_quarter_pair hs hk f).1.mpr (hf _ _)))]
  trans ∑ k ∈ Finset.range 4, ∫ a in mixedLevelInterval s,
    mixedQuarterTimeWeight s a * f (diagInv (mixedQuarterPoint (quarterJ k) (quarterSign k) s a))
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [intervalIntegral.integral_of_le hL, integral_Ioc_eq_integral_Ioo]
    exact (orbit_quarter_pair hs (Finset.mem_range.1 hk) f).2
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_two, Fintype.sum_bool]
    simp only [quarterJ, quarterSign]
    norm_num
    abel

/-- A cell a.e. identity is valid on all four signed quarter graphs for
almost every level. -/
theorem ae_mixedQuarterPoint_of_ae {P : Plane → Prop}
    (hP : ∀ᵐ q ∂volume.restrict mixedOpenCell, P q) :
    ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ (j : Fin 2) (σ : Bool),
      ∀ᵐ a ∂volume.restrict (mixedLevelInterval s), P (mixedQuarterPoint j σ s a) := by
  let J := Ioo (-(π / 2)) (π / 2)
  have hU : mixedOpenCell = J ×ˢ J := by simp only [mixedOpenCell, neg_div, J]
  have hUm : MeasurableSet mixedOpenCell := measurableSet_Ioo.prod measurableSet_Ioo
  have hC (j : Fin 2) : ∀ᵐ q ∂volume.restrict (J ×ˢ J), P (traceSideCoords j q) := by
    fin_cases j
    · exact hU ▸ hP
    · have hx := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae
          (show ∀ᵐ q ∂(volume : Measure ℝ).prod volume, q ∈ mixedOpenCell → P q from by
            simpa only [← Measure.volume_eq_prod] using (ae_restrict_iff' hUm).1 hP)
      rw [← Measure.volume_eq_prod] at hx
      refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 ?_
      filter_upwards [hx] with q hq hqm
      exact hq (hU.symm ▸ (show q.swap ∈ J ×ˢ J from ⟨hqm.2, hqm.1⟩))
  have hG (j : Fin 2) (σ : Bool) := ae_mixed_quarterGraph_signed_of_ae σ (hC j)
  filter_upwards [ae_all_iff.2 (fun j ↦ ae_all_iff.2 (hG j))] with s hs h j σ
  exact hs j σ h

/-- Planar integrability gives time integrability on each of the signed
quarter graphs for almost every regular level. -/
theorem ae_mixedQuarter_integrable {f : Plane → ℝ} (hf : IntegrableOn f cellSquare) :
    ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ (j : Fin 2) (σ : Bool),
      IntegrableOn (fun a ↦ mixedQuarterTimeWeight s a *
        f (diagInv (mixedQuarterPoint j σ s a))) (mixedLevelInterval s) := by
  have hpre (k : ℕ) : rotLift^[k] ⁻¹' cellSquare = cellSquare := by
    induction k with
    | zero => rfl
    | succ k ih =>
      ext p
      simp only [mem_preimage, Function.iterate_succ_apply', (rotLift_cell_level _).1]
      exact Set.ext_iff.mp ih p
  have hg (k : ℕ) : IntegrableOn (fun p ↦ f (rotLift^[k] p)) cellSquare := by
    have hm : MeasurePreserving (rotLift^[k]) (volume.restrict cellSquare)
        (volume.restrict cellSquare) := by
      have hc : MeasurableSet cellSquare := by
        exact (measurableSet_lt (continuous_diagCoord.fst.abs.measurable) measurable_const).inter
          (measurableSet_lt (continuous_diagCoord.snd.abs.measurable) measurable_const)
      simpa only [hpre k] using (measurePreserving_rotLift.iterate k).restrict_preimage hc
    exact hm.integrable_comp_of_integrable hf
  have hq (k : ℕ) := (ae_restrict_iff' measurableSet_Ioo).1 (integral_cellSquare_eq (hg k)).1
  filter_upwards [ae_all_iff.2 hq] with s hs h j σ
  have go (k : ℕ) (hk : k < 4) := (orbit_quarter_pair h hk f).1.mp
    ((hs k h).mono_set (fun _ ht ↦
      ⟨by linarith [ht.1, eighthPeriod_pos h.1 h.2],
       by linarith [ht.2, eighthPeriod_pos h.1 h.2]⟩))
  fin_cases j <;> cases σ
  · exact go 2 (by decide)
  · exact go 0 (by decide)
  · exact go 1 (by decide)
  · exact go 3 (by decide)

end NoEmbeddedEigenvalues
