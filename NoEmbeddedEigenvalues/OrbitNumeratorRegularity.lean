import NoEmbeddedEigenvalues.IntervalParameterH1
import NoEmbeddedEigenvalues.OrbitTransportTraces
import NoEmbeddedEigenvalues.RadialWeakMultiplier
import NoEmbeddedEigenvalues.ScalarDivision

/-!
# Local H¹ regularity of the quarter-orbit numerator

Blueprint: `lem:numerator-local-h1`.

Normalize time by the period, so the moving quarter endpoints become the fixed
angular window [-1/8, 1/8]. A spatial cutoff on a compact annulus permits the
weak action--angle chain rule. Integration of its L² level derivative gives
H¹ regularity of the numerator formed from the original continuous forcing.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

private def normalizedQuarterWeight (lam : ℝ) (q : ℝ × ℝ) : ℂ :=
  (orbitPeriod q.1 : ℂ) *
    Complex.exp (-Complex.I * ((lam * (q.2 * orbitPeriod q.1) : ℝ) : ℂ))

/-- Normalized time fixes the integration window, including its physical period factor. -/
theorem quarterNumerator_eq_normalized (lam : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ) :
    quarterNumerator lam g h = ∫ θ in Icc (-1 / 8 : ℝ) (1 / 8),
      (orbitPeriod h : ℂ) *
        Complex.exp (-Complex.I * ((lam * (θ * orbitPeriod h) : ℝ) : ℂ)) *
          g (actionAngleInv (h, θ)) := by
  let F := fun t ↦ g (dipoleOrbit h t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))
  have he := intervalIntegral.smul_integral_comp_mul_right F
    (a := (-1 / 8 : ℝ)) (b := 1 / 8) (orbitPeriod h)
  have hm : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by
    unfold orbitPeriod; ring
  have hp : (1 / 8 : ℝ) * orbitPeriod h = eighthPeriod h := by
    unfold orbitPeriod; ring
  rw [hm, hp] at he
  rw [quarterNumerator, ← he, Complex.real_smul, ← intervalIntegral.integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num :
      (-1 / 8 : ℝ) ≤ 1 / 8)]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp [F, actionAngleInv]
  ring

/-- A coefficient continuous on a compact set preserves L² on each measurable subset. -/
theorem memLp_mul_on_compact {K R : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hR : MeasurableSet R) (hRK : R ⊆ K) {C F : ℝ × ℝ → ℂ}
    (hC : ContinuousOn C K) (hF : MemLp F 2 (volume.restrict R)) :
    MemLp (fun q ↦ C q * F q) 2 (volume.restrict R) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hC
  have hCL : MemLp C ⊤ (volume.restrict R) := memLp_top_of_bound
    ((hC.mono hRK).aestronglyMeasurable hR) B (by
      filter_upwards [ae_restrict_mem hR] with q hq
      exact hB q (hRK hq))
  exact hCL.mul hF

/-- Continuous H¹ forcing suffices for H¹ regularity of the canonical numerator
on each compact level interval. No transport equation or character is needed. -/
theorem quarterNumerator_memIntervalH1 {lam : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hgs : MemSobolevOn 1 U g)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀1 : h₀ < 1)
    (hA : orbitAnnulus 0 h₀ ⊆ U) : MemIntervalH1 a b (quarterNumerator lam g) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKs : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hh₀1)⟩, mem_univ _⟩
  have hAU : ∀ q ∈ K, actionAngleInv q ∈ U := by
    intro q hq
    have h0 := ha.trans_le hq.1.1
    have h1 := hq.1.2.trans_lt (hb.trans hh₀1)
    exact hA ⟨actionAngleInv_mem_puncturedCell h0 h1 q.2,
      by rw [levelCoord_actionAngleInv h0 h1]; exact ⟨h0, hq.1.2.trans_lt hb⟩⟩
  have hAA := contDiffOn_actionAngleInv.continuousOn.mono hKs
  have hKi : IsCompact (actionAngleInv '' K) := hK.image_of_continuousOn hAA
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hKi hU (by
      rintro _ ⟨q, hq, rfl⟩; exact hAU q hq)
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    hVo hKi.isClosed hKV
  have hχc : HasCompactSupport χ := by
    rw [HasCompactSupport, tsupport, hχs]; exact hVc
  have hχU : tsupport (fun p ↦ (χ p : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero χ).trans (by
      rw [tsupport, hχs]; exact hVU)
  let F : ℝ × ℝ → ℂ := fun p ↦ (χ p : ℂ) * g p
  have hF : MemSobolevOn 1 univ F := hgs.memSobolevLocOn.cutoff 1 hU
    (Complex.ofRealCLM.contDiff.comp hχ) (hχc.comp_left Complex.ofReal_zero) hχU
  choose G hGw hGL using hF.2
  have hFeq : ∀ q ∈ K, F (actionAngleInv q) = g (actionAngleInv q) := by
    intro q hq
    simp only [F, (hχ1 _).1 (mem_image_of_mem actionAngleInv hq),
      Complex.ofReal_one, one_mul]
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict univ)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band isOpen_univ hu ha hab hb hh₀1 (subset_univ _)
  let A : ℝ × ℝ → ℂ := fun q ↦
    ((coordPartial 0 (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * G 0 (actionAngleInv q) +
    ((coordPartial 0 (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * G 1 (actionAngleInv q)
  have hweak : HasWeakPartialOn R 0 (F ∘ actionAngleInv) A :=
    (HasWeakPartialOn.comp_actionAngleInv_fst
      (fun i ↦ (hGw i).mono (subset_univ _))).mono (hRK.trans hKs)
  have hAX := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ)
    (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) (0 : Fin 2)
  have hAY := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ)
    (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) (0 : Fin 2)
  have hAL : MemLp A 2 (volume.restrict R) :=
    (memLp_mul_on_compact hK hRo.measurableSet hRK
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hAX).continuousOn.mono hKs) (hP _ (hGL 0))).add
    (memLp_mul_on_compact hK hRo.measurableSet hRK
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hAY).continuousOn.mono hKs) (hP _ (hGL 1)))
  have hW : ContDiffOn ℝ ∞ (normalizedQuarterWeight lam) actionStrip := by
    have hS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ orbitPeriod q.1) actionStrip :=
      contDiffOn_orbitPeriod.comp contDiff_fst.contDiffOn (fun _ hq ↦ hq.1)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hS).mul
      ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (contDiffOn_const.mul (contDiffOn_snd.mul hS)))).cexp)
  have hWL : MemLp (fun q ↦ normalizedQuarterWeight lam q * (F ∘ actionAngleInv) q) 2
      (volume.restrict R) :=
    memLp_mul_on_compact hK hRo.measurableSet hRK (hW.continuousOn.mono hKs) (hP _ hF.1)
  have hDL : MemLp (fun q ↦ coordPartial 0 (normalizedQuarterWeight lam) q *
      (F ∘ actionAngleInv) q + normalizedQuarterWeight lam q * A q) 2 (volume.restrict R) :=
    (memLp_mul_on_compact hK hRo.measurableSet hRK
      ((contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ) hW 0).continuousOn.mono hKs)
      (hP _ hF.1)).add
      (memLp_mul_on_compact hK hRo.measurableSet hRK (hW.continuousOn.mono hKs) hAL)
  have hFc : ContinuousOn (F ∘ actionAngleInv) R :=
    ((Complex.continuous_ofReal.comp hχ.continuous).continuousOn.mul hg).comp
      (hAA.mono hRK) (fun q hq ↦ hAU q (hRK hq))
  have hN := (hweak.mul_contDiffOn hRo (hW.mono (hRK.trans hKs))).setIntegral_h1
    hab (by norm_num) (l := (-1 / 8 : ℝ)) (r := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num) ((hW.continuousOn.mono (hRK.trans hKs)).mul hFc) hWL hDL
  refine ⟨_, hN.congr_Ioo ?_⟩
  intro h hh
  rw [quarterNumerator_eq_normalized]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  dsimp only [Pi.mul_apply, normalizedQuarterWeight, Function.comp_apply]
  rw [hFeq _ ⟨Ioo_subset_Icc_self hh, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩]

/-- The ordinary derivative supplies one compatible local H¹ derivative on all
compact subintervals, independently of the localization cutoff. -/
theorem quarterNumerator_h1Loc {lam : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hgs : MemSobolevOn 1 U g)
    {h₀ : ℝ} (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U) :
    HasIntervalH1Loc 0 h₀ (quarterNumerator lam g) (deriv (quarterNumerator lam g)) := by
  intro a b ha hab hb
  obtain ⟨D, hD⟩ := quarterNumerator_memIntervalH1 hU hg hgs ha hab hb hh₀1 hA
  exact hD.with_deriv

end NoEmbeddedEigenvalues
