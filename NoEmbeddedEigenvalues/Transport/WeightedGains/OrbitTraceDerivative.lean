module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.InteriorTraceDerivative
public import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitNumeratorDerivative
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakJetOperations

/-!
# Tangential differentiation at normalized orbit endpoints

Blueprint: `def:action-angle-pullback-gradient`, `lem:orbit-tangential-trace`.

A continuous H² forcing and its original supplied Cartesian gradient give an
H¹ function along each interior constant-angle line. Its weak derivative is the
canonical transverse trace of the normalized level contraction. This applies at
both quarter endpoints without continuous gradients or raw gradient-ray values.
Only the ordered mixed derivatives supplied by recursive H² are used.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Formal normalized chart gradient, retaining the supplied Cartesian entries. -/
def actionAnglePullbackGradient (D : Fin 2 → ℝ × ℝ → ℂ) (j : Fin 2)
    (q : ℝ × ℝ) : ℂ :=
  ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * D 0 (actionAngleInv q) +
  ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * D 1 (actionAngleInv q)

/-- Constant-angle forcing values have H¹ tangential data with the canonical
trace of the specified normalized level contraction, on every compact collar
interval. This includes both angles ±1/8 used in the moving-endpoint formula. -/
theorem normalizedOrbitTrace_hasIntervalH1 {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hgs : MemSobolevOn 2 U g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j g (D j))
    (hcell : cellSquare ⊆ U) {a b h₀ θ : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1)
    (hθ : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
    HasIntervalH1 a b (fun h ↦ g (actionAngleInv (h, θ)))
      (fun h ↦ interiorSectionTrace
        (fun s ↦ actionAnglePullbackGradient D 0 (h, θ + s))) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hSo : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKs : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hh₀)⟩, mem_univ _⟩
  have hRs : R ⊆ actionStrip := hRK.trans hKs
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict U)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band hU hu ha hab hb hh₀ (fun p hp ↦ hcell hp.1.1)
  have hM (c F : ℝ × ℝ → ℂ) (hc : ContDiffOn ℝ ∞ c actionStrip)
      (hF : MemLp F 2 (volume.restrict R)) :
      MemLp (fun q ↦ c q * F q) 2 (volume.restrict R) :=
    memLp_mul_on_compact hK hRo.measurableSet hRK (hc.continuousOn.mono hKs) hF
  have hTw (u : ℝ × ℝ → ℂ) (Z : Fin 2 → ℝ × ℝ → ℂ)
      (hZ : ∀ j, HasWeakPartialOn U j u (Z j)) (j : Fin 2) :
      HasWeakPartialOn R j (u ∘ actionAngleInv) (actionAnglePullbackGradient Z j) :=
    (HasWeakPartialOn.comp_actionAngleInv
      (fun i ↦ (hZ i).mono (sdiff_subset.trans hcell)) j).mono hRs
  have hC (i : Fin 2) : ContDiffOn ℝ ∞
      (fun q ↦ ((coordPartial i (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ)) actionStrip :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_coordPartial hSo (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) i)
  have hC' (i : Fin 2) : ContDiffOn ℝ ∞
      (fun q ↦ ((coordPartial i (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ)) actionStrip :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_coordPartial hSo (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) i)
  have hTL (Z : Fin 2 → ℝ × ℝ → ℂ) (hZ : ∀ j, MemLp (Z j) 2 (volume.restrict U))
      (j : Fin 2) : MemLp (actionAnglePullbackGradient Z j) 2 (volume.restrict R) :=
    (hM _ _ (hC j) (hP _ (hZ 0))).add (hM _ _ (hC' j) (hP _ (hZ 1)))
  have hDs (j : Fin 2) : MemSobolevOn 1 U (D j) := (hD j).memSobolevOn hU hgs
  choose E hE hEL using fun j ↦ (hDs j).2
  have hEL (j i : Fin 2) : MemLp (E j i) 2 (volume.restrict U) := hEL j i
  have hA₀ := (hTw (D 0) (E 0) (hE 0) 1).mul_contDiffOn hRo ((hC 0).mono hRs)
  have hA₁ := (hTw (D 1) (E 1) (hE 1) 1).mul_contDiffOn hRo ((hC' 0).mono hRs)
  have hAw : HasWeakPartialOn R 1 (actionAnglePullbackGradient D 0) _ := hA₀.add hA₁
  have hAL : MemLp (actionAnglePullbackGradient D 0) 2 (volume.restrict R) :=
    hTL D (fun j ↦ (hDs j).1) 0
  have hBL := ((hM _ _ (contDiffOn_coordPartial hSo (hC 0) 1) (hP _ (hDs 0).1)).add
    (hM _ _ (hC 0) (hTL (E 0) (hEL 0) 1))).add
    ((hM _ _ (contDiffOn_coordPartial hSo (hC' 0) 1) (hP _ (hDs 1).1)).add
      (hM _ _ (hC' 0) (hTL (E 1) (hEL 1) 1)))
  have hgc : ContinuousOn (g ∘ actionAngleInv) R := hg.comp
    (contDiffOn_actionAngleInv.continuousOn.mono hRs)
    (fun q hq ↦ hcell (actionAngleInv_mem_puncturedCell (hRs hq).1.1 (hRs hq).1.2 q.2).1)
  exact (hTw g D hD 0).trace_hasIntervalH1 hab (by norm_num) hθ hgc
    (hP _ hgs.1) hAL hBL hAw

/-- The original pair and its original first gradient produce these canonical
endpoint differentiation data; no second jet or continuous gradient is added. -/
theorem IsTransportPair.normalizedOrbitTrace_hasIntervalH1
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    {a b h₀ θ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1)
    (hθ : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
    HasIntervalH1 a b (fun h ↦ g (actionAngleInv (h, θ)))
      (fun h ↦ interiorSectionTrace
        (fun s ↦ actionAnglePullbackGradient D 0 (h, θ + s))) := by
  have hU := hp.isOrbitUnion.1
  have he := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hgs : MemSobolevOn 2 U g := MemSobolevOn.congr_ae_on hp.memSobolevOn
    hU.measurableSet he
  apply NoEmbeddedEigenvalues.normalizedOrbitTrace_hasIntervalH1 hU hg hgs
    (fun j ↦ (hD j).congr_ae_on hU.measurableSet he (Eventually.of_forall fun _ _ ↦ rfl))
    (subset_closure.trans hcell) ha hab hb hh₀ hθ

/-- Canonical endpoint differentiation works on any collar below level one;
in particular it does not shrink the existing all-frequency numerator collar. -/
theorem IsTransportPair.normalizedOrbitTrace_h1Loc
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    {h₀ θ : ℝ} (hh₀ : h₀ < 1) (hθ : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
    HasIntervalH1Loc 0 h₀ (fun h ↦ g (actionAngleInv (h, θ)))
      (fun h ↦ interiorSectionTrace
        (fun s ↦ actionAnglePullbackGradient D 0 (h, θ + s))) := by
  intro a b ha hab hb
  exact hp.normalizedOrbitTrace_hasIntervalH1 hcell hg hfg hD ha hab hb hh₀ hθ

/-- The actual forcing values at physical times ±L have local H¹ derivatives
represented by canonical normalized traces, with the original supplied gradient. -/
theorem IsTransportPair.quarterEndpoint_forcing_h1Loc
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    {h₀ ε : ℝ} (hh₀ : h₀ < 1) (hε : ε = -1 ∨ ε = 1) :
    HasIntervalH1Loc 0 h₀ (fun h ↦ g (dipoleOrbit h (ε * eighthPeriod h)))
      (fun h ↦ interiorSectionTrace
        (fun s ↦ actionAnglePullbackGradient D 0 (h, ε / 8 + s))) := by
  have hθ : ε / 8 ∈ Ioo (-1 / 4 : ℝ) (3 / 4) := by
    rcases hε with rfl | rfl <;> norm_num
  intro a b ha hab hb
  apply (hp.normalizedOrbitTrace_hasIntervalH1 hcell hg hfg hD ha hab hb hh₀ hθ).congr_Ioo
  intro h _
  change g (dipoleOrbit h ((ε / 8) * orbitPeriod h)) =
    g (dipoleOrbit h (ε * eighthPeriod h))
  have he : (ε / 8) * orbitPeriod h = ε * eighthPeriod h := by
    unfold orbitPeriod
    ring
  rw [he]

end NoEmbeddedEigenvalues
