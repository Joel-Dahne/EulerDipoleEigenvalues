module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SaddleDistanceWeights
public import EulerDipoleEigenvalues.Transport.WeightedForcing.PeriodicWeightedGradient
public import EulerDipoleEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport

/-!
# Bounded weighted mass for the saddle bootstrap

Periodic box data and reflected positive-cell data supply finite norms on
bounded lift sets, never on the whole periodic plane. Radius weights are
weaker than lattice-distance weights at any fixed saddle.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open Real

/-- Square-integrable periodic box data give finite norms on bounded sets. -/
theorem memLp_of_periodic_periodBox {F : ℝ × ℝ → ℂ} (hper : IsPeriodicLift F)
    (hF : MemLp F 2 (volume.restrict periodBox)) {U : Set (ℝ × ℝ)}
    (hU : Bornology.IsBounded U) : MemLp F 2 (volume.restrict U) := by
  have he := liftL2_ae_eq (coeFn_boxPeriodize hF)
  apply (memLp_liftL2 (boxPeriodize F) hU).ae_eq
  filter_upwards [ae_restrict_of_ae he] with p hp
  exact hp.trans (hper.eq_of_torusProj_eq (torusProj_torusRep _))

/-- The standard Cartesian period box lies strictly in the fixed cell neighbourhood. -/
theorem periodBox_subset_cellNeighbourhood : periodBox ⊆ cellNeighbourhood := by
  intro p hp
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hp
  change -π < p.1 at hx0
  change p.1 ≤ -π + 2 * π at hx1
  change -π < p.2 at hy0
  change p.2 ≤ -π + 2 * π at hy1
  change |(p.1 + p.2) / 2| < 3 * π / 2 ∧ |(p.1 - p.2) / 2| < 3 * π / 2
  rw [abs_lt, abs_lt]
  constructor <;> constructor <;> linarith [Real.pi_pos]

/-- A lattice-weighted norm on the fixed neighbourhood localizes at every lift. -/
theorem memLp_saddleDist_of_neighbourhood {ω : L2} {s : ℝ}
    (hF : MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) s : ℂ)) 2
      (volume.restrict cellNeighbourhood)) {U : Set (ℝ × ℝ)}
    (hU : Bornology.IsBounded U) :
    MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) s : ℂ)) 2
      (volume.restrict U) := by
  apply memLp_of_periodic_periodBox (hF := hF.mono_measure
    (Measure.restrict_mono periodBox_subset_cellNeighbourhood le_rfl)) (hU := hU)
  intro p
  have hx := saddleDist_cellFold false (1, 0) p
  have hy := saddleDist_cellFold false (0, 1) p
  simp only [cellFold_apply, Bool.false_eq_true, ite_false, liftShift,
    Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero] at hx hy
  constructor
  · dsimp only
    rw [(isPeriodicLift_liftL2 ω p).1, hx]
  · dsimp only
    rw [(isPeriodicLift_liftL2 ω p).2, hy]

/-- Positive-cell norms of a lift and its reflection cover every bounded lift set. -/
theorem memLp_saddleDist_of_reflected_cells {ω : L2} {t : ℝ}
    (hF : MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) t : ℂ)) 2
      (volume.restrict cellSquare))
    (hneg : MemLp (fun p ↦ liftL2 ω (separatrixReflect p) /
      (Real.rpow (saddleDist p) t : ℂ)) 2 (volume.restrict cellSquare))
    {U : Set (ℝ × ℝ)} (hU : Bornology.IsBounded U) :
    MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) t : ℂ)) 2
      (volume.restrict U) := by
  let F := fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) t : ℂ)
  have hd : Measurable (fun p ↦ (Real.rpow (saddleDist p) t : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    exact (Metric.continuous_infDist_pt saddleSet).measurable.pow_const t
  have hm : Measurable F := (measurable_liftL2 ω).div hd
  have hstrip : cellSeparatrixStrip 3 = cellSquare := by
    ext p
    constructor
    · exact fun hp ↦ hp.1
    · intro hp
      refine ⟨hp, ?_, ?_⟩
      · rw [dipoleLift_eq_diag]
        exact mul_pos (mul_pos (by norm_num)
          (cos_pos_of_mem_Ioo (abs_lt.mp hp.1))) (cos_pos_of_mem_Ioo (abs_lt.mp hp.2))
      · have hb := Ψ_le_two (torusProj p)
        rw [Ψ_torusProj] at hb
        linarith
  have hfold (s : Bool) (n : ℤ × ℤ) : MemLp F 2
      (volume.restrict (univ ∩ cellFold s n ⁻¹' cellSeparatrixStrip 3)) := by
    rw [hstrip, univ_inter]
    cases s
    · have he := memLp_comp_planeAffine (cellFoldLinear false) (cellFoldTranslation false n)
        (measurePreserving_cellFold false n) isOpen_cellSquare.measurableSet hF
      apply he.ae_eq
      exact Filter.Eventually.of_forall fun p ↦ by
        change liftL2 ω (cellFold false n p) /
          (Real.rpow (saddleDist (cellFold false n p)) t : ℂ) = F p
        rw [saddleDist_cellFold]
        simp only [cellFold_apply, Bool.false_eq_true, ite_false, liftL2_liftShift, F]
    · have he := memLp_comp_planeAffine (cellFoldLinear true) (cellFoldTranslation true n)
        (measurePreserving_cellFold true n) isOpen_cellSquare.measurableSet hneg
      apply he.ae_eq
      exact Filter.Eventually.of_forall fun p ↦ by
        change liftL2 ω (separatrixReflect (cellFold true n p)) /
          (Real.rpow (saddleDist (cellFold true n p)) t : ℂ) = F p
        have href : separatrixReflect (cellFold true n p) = liftShift (-n.2, -n.1) p := by
          ext <;> simp [cellFold_apply, liftShift, separatrixReflect] <;> ring
        rw [saddleDist_cellFold, href, liftL2_liftShift]
  have hlocal := memSobolevLocOn_zero_of_cellFold_cover hm hfold
  have hall : {p : ℝ × ℝ | |dipoleLift p| < 3} = univ := by
    apply eq_univ_of_forall
    intro p
    have h0 := neg_two_le_Ψ (torusProj p)
    have h1 := Ψ_le_two (torusProj p)
    rw [Ψ_torusProj] at h0 h1
    change |dipoleLift p| < (3 : ℝ)
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [hall, univ_inter] at hlocal
  exact hlocal.zero_memLp_of_isBounded hU

/-- Positive-cell mass extends by odd reflection and a finite periodic cover. -/
theorem memLp_saddleDist_of_oddOdd_cell {ω : L2} (hs : InSector false false ω) {t : ℝ}
    (hF : MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) t : ℂ)) 2
      (volume.restrict cellSquare)) {U : Set (ℝ × ℝ)} (hU : Bornology.IsBounded U) :
    MemLp (fun p ↦ liftL2 ω p / (Real.rpow (saddleDist p) t : ℂ)) 2
      (volume.restrict U) := by
  apply memLp_saddleDist_of_reflected_cells hF (hU := hU)
  apply hF.neg.ae_eq
  filter_upwards [ae_restrict_of_ae (liftL2_separatrixReflect_ae hs)] with p hp
  dsimp only [Function.comp_apply] at hp
  dsimp only [Pi.neg_apply]
  rw [hp]
  ring

/-- Replacing distance to the lattice by distance to one saddle weakens a
nonnegative radial weight. This transfers norms, not weak derivatives. -/
theorem memLp_div_radius_of_saddleDist {F : ℝ × ℝ → ℂ} (hFm : Measurable F)
    {P : ℝ × ℝ} (hP : P ∈ saddleSet) {s : ℝ} (hs : 0 ≤ s)
    {U : Set (ℝ × ℝ)}
    (hF : MemLp (fun p ↦ F p / (Real.rpow (saddleDist p) s : ℂ)) 2
      (volume.restrict U)) :
    MemLp (fun p ↦ F p / (Real.rpow (localRadius P p) s : ℂ)) 2
      (volume.restrict U) := by
  have hr : Measurable (localRadius P) := by unfold localRadius; fun_prop
  apply hF.norm.mono'
    (hFm.div (Complex.measurable_ofReal.comp (hr.pow_const s))).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae ae_saddleDist_ne_zero] with p hp
  have hd : 0 < saddleDist p := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hp)
  have hpow := Real.rpow_le_rpow hd.le (saddleDist_le_localRadius hP p) hs
  dsimp only [Pi.div_apply, Function.comp_apply]
  have hrpow : 0 ≤ Real.rpow (localRadius P p) s := Real.rpow_nonneg (Real.sqrt_nonneg _) s
  have hdpow : 0 ≤ Real.rpow (saddleDist p) s := Real.rpow_nonneg Metric.infDist_nonneg s
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
  simp only [Real.rpow_eq_pow] at hrpow hdpow ⊢
  rw [abs_of_nonneg hrpow, abs_of_nonneg hdpow]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hd s) hpow

end EulerDipoleEigenvalues
