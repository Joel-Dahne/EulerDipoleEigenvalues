import NoEmbeddedEigenvalues.SeparableMultiplier
import NoEmbeddedEigenvalues.LogarithmicWeights
import NoEmbeddedEigenvalues.SobolevMultipliers
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-!
# The physical logarithmic multiplier

Blueprint: `lem:dipole-log-multiplier`.

The identity Ψ = 2 cos(a) cos(b) separates the two logarithmic singularities
in diagonal coordinates, including regular edges and saddle crossings at once.
Coordinate slicing uses only integrability of log |cos| and ordinary H¹.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The physical weight is positive and bounded by a sum of integrable coordinate
weights. Separatrix values are handled without composing a.e. representatives. -/
theorem dipoleLogWeight_bounds (p : ℝ × ℝ) :
    0 ≤ dipoleLogWeight p ∧ dipoleLogWeight p ≤
      1 + |Real.log (Real.cos (diagCoord p).1)| +
        |Real.log (Real.cos (diagCoord p).2)| := by
  by_cases hp : dipoleLift p = 0
  · simp only [dipoleLogWeight, hp, ↓reduceIte]
    constructor
    · norm_num
    · linarith [abs_nonneg (Real.log (Real.cos (diagCoord p).1)),
        abs_nonneg (Real.log (Real.cos (diagCoord p).2))]
  have ha : Real.cos (diagCoord p).1 ≠ 0 := by
    intro hz
    exact hp (by rw [dipoleLift_eq_diag, hz]; ring)
  have hb : Real.cos (diagCoord p).2 ≠ 0 := by
    intro hz
    exact hp (by rw [dipoleLift_eq_diag, hz]; ring)
  have he : dipoleLogWeight p = 1 - Real.log (Real.cos (diagCoord p).1) -
      Real.log (Real.cos (diagCoord p).2) := by
    rw [dipoleLogWeight, ite_eq_right hp, logLevelWeight, dipoleLift_eq_diag,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show 2 * |Real.cos (diagCoord p).1| * |Real.cos (diagCoord p).2| / 2 =
      |Real.cos (diagCoord p).1| * |Real.cos (diagCoord p).2| by ring]
    rw [one_div, Real.log_inv, Real.log_mul (abs_ne_zero.2 ha) (abs_ne_zero.2 hb),
      Real.log_abs, Real.log_abs]
    ring
  rw [he]
  constructor
  · have hla : Real.log (Real.cos (diagCoord p).1) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_cos_le_one _)
    have hlb : Real.log (Real.cos (diagCoord p).2) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_cos_le_one _)
    linarith
  · linarith [neg_le_abs (Real.log (Real.cos (diagCoord p).1)),
      neg_le_abs (Real.log (Real.cos (diagCoord p).2))]

/-- Measurability includes the assigned values on the separatrix. -/
theorem measurable_dipoleLogWeight : Measurable dipoleLogWeight := by
  unfold dipoleLogWeight logLevelWeight
  have hd : Measurable dipoleLift := by unfold dipoleLift; fun_prop
  apply Measurable.ite (by measurability) measurable_const
  fun_prop

/-- H¹ on a bounded diagonal rectangle absorbs the physical logarithm. -/
theorem MemSobolevOn.log_dipole_mul {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn 1 (diagRect (Ioo a b) (Ioo c d)) F) :
    MemLp (fun p ↦ (Real.sqrt (dipoleLogWeight p) : ℂ) * F p) 2
      (volume.restrict (diagRect (Ioo a b) (Ioo c d))) := by
  let U := diagRect (Ioo a b) (Ioo c d)
  have hU : IsOpen U := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have he : diagInv ⁻¹' U = Ioo a b ×ˢ Ioo c d := by
    ext q; exact mem_diagRect_diagInv
  obtain ⟨Dx, hx, hDx⟩ := hF.2 0
  obtain ⟨Dy, hy, hDy⟩ := hF.2 1
  have hG := memLp_comp_diagInv hU.measurableSet hF.1
  have hA := memLp_comp_diagInv hU.measurableSet (hDx.add hDy)
  have hB := memLp_comp_diagInv hU.measurableSet (hDx.sub hDy)
  have hda := hx.comp_diagInv_fst hU hy
  have hdb := hx.comp_diagInv_snd hU hy
  rw [he] at hG hA hB hda hdb
  let w := fun t ↦ |Real.log (Real.cos t)|
  have mw : Measurable w := by unfold w; fun_prop
  have hw : ∀ t, 0 ≤ w t := fun _ ↦ abs_nonneg _
  have iw (s t : ℝ) : IntegrableOn w (Ioo s t) := by
    exact (intervalIntegrable_log_cos (a := s) (b := t)).abs.1.mono_set Ioo_subset_Ioc_self
  have hW₁ := (hda.sqrt_weight_fst hab hcd mw hw (iw a b) hG hA).1
  have hW₂ := (hdb.sqrt_weight_snd hab hcd mw hw (iw c d) hG hB).1
  have hWG := memLp_sqrt_weight_of_le_sum
    (measurable_dipoleLogWeight.comp diagInv.continuous.measurable)
    (fun q ↦ (dipoleLogWeight_bounds (diagInv q)).1)
    (fun q ↦ hw q.1) (fun q ↦ hw q.2)
    (fun q ↦ by simpa only [diagCoord_diagInv, Function.comp_apply, w] using
      (dipoleLogWeight_bounds (diagInv q)).2)
    hG hW₁ hW₂
  apply memLp_of_comp_diagInv hU.measurableSet
  rwa [he]

/-- Local H¹ absorbs the physical logarithm on any open set. Compact cutoffs
avoid claiming a global finite norm for a periodic lift. -/
theorem MemSobolevLocOn.log_dipole_mul {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 1 U F) :
    MemSobolevLocOn 0 U (fun p ↦ (Real.sqrt (dipoleLogWeight p) : ℂ) * F p) := by
  apply memSobolevLocOn_of_locally_ae
  intro p hp
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  let η : ContDiffBump p := ⟨r / 2, r, by positivity, by linarith⟩
  let χ : ℝ × ℝ → ℂ := fun q ↦ (η q : ℂ)
  have hχsub : tsupport χ ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero η).trans (by
      simpa only [η.tsupport_eq] using hsub)
  have hG := hF.cutoff 1 hU (Complex.ofRealCLM.contDiff.comp η.contDiff)
    (η.hasCompactSupport.comp_left Complex.ofReal_zero) hχsub
  let R := ‖diagCoord p‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let W := diagRect (Ioo (-R) R) (Ioo (-R) R)
  have hW : IsOpen W := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have hpW : p ∈ W := by
    constructor
    · apply abs_lt.1
      have hn : |(diagCoord p).1| ≤ ‖diagCoord p‖ := by
        simpa only [Real.norm_eq_abs] using norm_fst_le (diagCoord p)
      exact hn.trans_lt (by dsimp [R]; linarith)
    · apply abs_lt.1
      have hn : |(diagCoord p).2| ≤ ‖diagCoord p‖ := by
        simpa only [Real.norm_eq_abs] using norm_snd_le (diagCoord p)
      exact hn.trans_lt (by dsimp [R]; linarith)
  have hlog := (hG.mono (subset_univ W)).log_dipole_mul
    (by linarith : -R < R) (by linarith : -R < R)
  obtain ⟨O, hηO, hO, hpO⟩ := eventually_nhds_iff.mp η.eventuallyEq_one
  refine ⟨O ∩ W, hO.inter hW, ⟨hpO, hpW⟩,
    fun q ↦ (Real.sqrt (dipoleLogWeight q) : ℂ) * (χ q * F q),
    (show MemSobolevOn 0 W _ from hlog).memSobolevLocOn.mono inter_subset_right, ?_⟩
  apply (ae_restrict_iff' (hO.inter hW).measurableSet).2
  exact Filter.Eventually.of_forall fun q hq ↦ by simp [χ, hηO q hq.1]

end NoEmbeddedEigenvalues
