module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalParameterH2
public import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitNumeratorRegularity

/-!
# Local H² regularity of the original quarter numerator

Blueprint: `lem:numerator-local-h2`.

Normalize time to a fixed angular window. Two weak level differentiations of
the weighted pullback have actual L² norms on each compact rectangle. Fixed-window
integration retains the original continuous forcing and gives interval H².
The ordinary scalar derivatives glue the local data; no boundary gradient values
or weighted second-derivative estimate are asserted here.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Continuous H² forcing gives local interval H² of its original numerator,
without a transport equation, ray traces or weighted hypotheses. -/
theorem quarterNumerator_memIntervalH2 {lam : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hgs : MemSobolevOn 2 U g)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀1 : h₀ < 1)
    (hA : orbitAnnulus 0 h₀ ⊆ U) : MemIntervalH2 a b (quarterNumerator lam g) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hSo : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
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
  have hF : MemSobolevOn 2 univ F := hgs.memSobolevLocOn.cutoff 2 hU
    (Complex.ofRealCLM.contDiff.comp hχ) (hχc.comp_left Complex.ofReal_zero) hχU
  choose G hGw hGs using hF.2
  choose H hHw hHL using fun j ↦ (hGs j).2
  have hFeq : ∀ q ∈ K, F (actionAngleInv q) = g (actionAngleInv q) := by
    intro q hq
    simp only [F, (hχ1 _).1 (mem_image_of_mem actionAngleInv hq),
      Complex.ofReal_one, one_mul]
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict univ)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band isOpen_univ hu ha hab hb hh₀1 (subset_univ _)
  let C₀ := fun q ↦ ((coordPartial 0 (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ)
  let C₁ := fun q ↦ ((coordPartial 0 (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ)
  have hC₀ : ContDiffOn ℝ ∞ C₀ actionStrip := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_coordPartial hSo (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) 0)
  have hC₁ : ContDiffOn ℝ ∞ C₁ actionStrip := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_coordPartial hSo (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) 0)
  let T := fun (Z : Fin 2 → ℝ × ℝ → ℂ) (q : ℝ × ℝ) ↦
    C₀ q * Z 0 (actionAngleInv q) + C₁ q * Z 1 (actionAngleInv q)
  have hTL (Z : Fin 2 → ℝ × ℝ → ℂ) (hZ : ∀ j, MemLp (Z j) 2 (volume.restrict univ)) :
      MemLp (T Z) 2 (volume.restrict R) :=
    (memLp_mul_on_compact hK hRo.measurableSet hRK (hC₀.continuousOn.mono hKs)
      (hP _ (hZ 0))).add
    (memLp_mul_on_compact hK hRo.measurableSet hRK (hC₁.continuousOn.mono hKs)
      (hP _ (hZ 1)))
  have hTw (u : ℝ × ℝ → ℂ) (Z : Fin 2 → ℝ × ℝ → ℂ)
      (hZ : ∀ j, HasWeakPartialOn univ j u (Z j)) :
      HasWeakPartialOn R 0 (u ∘ actionAngleInv) (T Z) :=
    (HasWeakPartialOn.comp_actionAngleInv_fst
      (fun j ↦ (hZ j).mono (subset_univ _))).mono (hRK.trans hKs)
  have hmul {u D c : ℝ × ℝ → ℂ} (hw : HasWeakPartialOn R 0 u D)
      (hu : MemLp u 2 (volume.restrict R)) (hD : MemLp D 2 (volume.restrict R))
      (hc : ContDiffOn ℝ ∞ c actionStrip) :
      HasWeakPartialOn R 0 (fun q ↦ c q * u q)
        (fun q ↦ coordPartial 0 c q * u q + c q * D q) ∧
      MemLp (fun q ↦ c q * u q) 2 (volume.restrict R) ∧
      MemLp (fun q ↦ coordPartial 0 c q * u q + c q * D q) 2 (volume.restrict R) := by
    exact ⟨hw.mul_contDiffOn hRo (hc.mono (hRK.trans hKs)),
      memLp_mul_on_compact hK hRo.measurableSet hRK (hc.continuousOn.mono hKs) hu,
      (memLp_mul_on_compact hK hRo.measurableSet hRK
        ((contDiffOn_coordPartial hSo hc 0).continuousOn.mono hKs) hu).add
        (memLp_mul_on_compact hK hRo.measurableSet hRK (hc.continuousOn.mono hKs) hD)⟩
  have hGL (j : Fin 2) : MemLp (G j) 2 (volume.restrict univ) := (hGs j).1
  have hHL (j i : Fin 2) : MemLp (H j i) 2 (volume.restrict univ) := hHL j i
  have hA₀ := hmul (hTw (G 0) (H 0) (hHw 0)) (hP _ (hGL 0)) (hTL _ (hHL 0)) hC₀
  have hA₁ := hmul (hTw (G 1) (H 1) (hHw 1)) (hP _ (hGL 1)) (hTL _ (hHL 1)) hC₁
  have hAw : HasWeakPartialOn R 0 (T G) _ := hA₀.1.add hA₁.1
  have hAL : MemLp (T G) 2 (volume.restrict R) := hA₀.2.1.add hA₁.2.1
  have hEL := hA₀.2.2.add hA₁.2.2
  have hFw := hTw F G hGw
  have hFL := hP F hF.1
  let W := fun q : ℝ × ℝ ↦ (orbitPeriod q.1 : ℂ) *
    Complex.exp (-Complex.I * ((lam * (q.2 * orbitPeriod q.1) : ℝ) : ℂ))
  have hW : ContDiffOn ℝ ∞ W actionStrip := by
    have hS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ orbitPeriod q.1) actionStrip :=
      contDiffOn_orbitPeriod.comp contDiffOn_fst (fun q hq ↦ hq.1)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hS).mul
      (Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn
          (contDiffOn_const.mul (contDiffOn_snd.mul hS)))))
  have hN := hmul hFw hFL hAL hW
  have hD₀ := hmul hFw hFL hAL (contDiffOn_coordPartial hSo hW 0)
  have hD₁ := hmul hAw hAL hEL hW
  have hDD := hD₀.1.add hD₁.1
  have hDDL := hD₀.2.2.add hD₁.2.2
  have hFc : ContinuousOn (F ∘ actionAngleInv) R := by
    apply ((Complex.continuous_ofReal.comp hχ.continuous).continuousOn.mul hg).comp
      (hAA.mono hRK)
    intro q hq
    exact hAU q (hRK hq)
  obtain ⟨A, B, hAB⟩ := hN.1.setIntegral_h2 hab (by norm_num)
    (l := (-1 / 8 : ℝ)) (r := 1 / 8) (by norm_num) (by norm_num) (by norm_num)
    ((hW.continuousOn.mono (hRK.trans hKs)).mul hFc) hN.2.1 hN.2.2 hDDL hDD
  refine ⟨A, B, hAB.1.congr_Ioo ?_, hAB.2⟩
  intro h hh
  rw [quarterNumerator_eq_normalized]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  dsimp only [W, Pi.mul_apply, Function.comp_apply]
  rw [hFeq _ ⟨Ioo_subset_Icc_self hh, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩]

/-- Ordinary scalar derivatives provide compatible local H² data on all compact
level intervals, with the original continuous numerator values. -/
theorem quarterNumerator_h2Loc {lam : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hgs : MemSobolevOn 2 U g)
    {h₀ : ℝ} (hh₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U) :
    HasIntervalH2Loc 0 h₀ (quarterNumerator lam g) (deriv (quarterNumerator lam g))
      (deriv (deriv (quarterNumerator lam g))) := by
  intro a b ha hab hb
  obtain ⟨A, B, hAB⟩ := quarterNumerator_memIntervalH2 hU hg hgs ha hab hb hh₀1 hA
  exact hAB.with_deriv hab

/-- The original pair supplies H² for its continuous forcing representative.
The resulting local numerator data use no extra derivative or ray premise. -/
theorem IsTransportPair.quarterNumerator_h2Loc
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[volume.restrict U] g) {h₀ : ℝ} (hh₀1 : h₀ < 1)
    (hA : orbitAnnulus 0 h₀ ⊆ U) (μ : ℝ) :
    HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
      (deriv (deriv (quarterNumerator μ g))) := by
  have hU := hp.isOrbitUnion.1
  have hgs : MemSobolevOn 2 U g := MemSobolevOn.congr_ae_on hp.memSobolevOn
    hU.measurableSet ((ae_restrict_iff' hU.measurableSet).1 hfg)
  exact NoEmbeddedEigenvalues.quarterNumerator_h2Loc hU hg hgs hh₀1 hA

end NoEmbeddedEigenvalues
