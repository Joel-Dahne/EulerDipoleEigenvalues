import NoEmbeddedEigenvalues.Analysis.PlaneMollifier
import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.SobolevMultipliers
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Local H² approximation and quadratic stability

Blueprint: lem:local-h2-smooth-approximation.

Approximation is on a precompact open patch of the given open domain. Classical
derivatives of the smooth approximants converge to specified weak jets; raw
Sobolev representatives are never differentiated classically. Compact support
is inside the original domain, not necessarily inside the approximation patch.

Bounded-coefficient products of two strongly convergent L² families have
convergent integrals. This stability fact is independent of the density theorem.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

/-- Smooth compactly supported approximants converge to the full weak H² jet
    on each precompact open patch. No boundary trace or extension of the raw
    function outside its given open domain is assumed. -/
theorem local_h2_smooth_approximation {U V : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ U) (hu : MemSobolevLocOn 2 U u) :
    ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 V u D ∧
      (∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict V)) ∧
      ∃ v : ℕ → ℝ × ℝ → ℂ,
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n) ∧
          HasCompactSupport (v n) ∧ tsupport (v n) ⊆ U) ∧
        ∀ w, w.length ≤ 2 →
          (∀ n, MemLp (classicalComplexJet w (v n)) 2 (volume.restrict V)) ∧
          Tendsto (fun n ↦ eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p)
            2 (volume.restrict V)) atTop (𝓝 0) := by
  obtain ⟨W, hWo, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χR, hχR, -, hχs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hWo isClosed_closure hVW
  let χ : ℝ × ℝ → ℂ := fun x ↦ χR x
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hχR
  have hχsupport : tsupport χ ⊆ closure W := by
    exact (tsupport_comp_subset Complex.ofReal_zero χR).trans_eq (congrArg closure hχs)
  have hχc : HasCompactSupport χ := hWc.of_isClosed_subset (isClosed_tsupport _) hχsupport
  have hχU := hχsupport.trans hWU
  let f : ℝ × ℝ → ℂ := fun x ↦ χ x * u x
  have hf : MemSobolevOn 2 univ f := hu.cutoff 2 hU hχ hχc hχU
  have hfs : tsupport f ⊆ tsupport χ := tsupport_mul_subset_left
  have hfu : EqOn f u V := by
    intro x hx
    have he := (hχone x).mp (subset_closure hx)
    simp [f, χ, he]
  obtain ⟨E, hE, hEL⟩ := memSobolevOn_iff_exists_weakJet.mp hf
  have hLp (w : List (Fin 2)) (hw : w.length ≤ 2) : MemLp (E w) 2 volume := by
    simpa only [Measure.restrict_univ] using hEL w hw
  -- Only the root of the global jet needs changing on the approximation patch.
  let D : List (Fin 2) → ℝ × ℝ → ℂ
    | [] => u
    | j :: w => E (j :: w)
  have hED (w : List (Fin 2)) : EqOn (E w) (D w) V := by
    cases w with
    | nil => simpa only [hE.1] using hfu
    | cons => exact fun _ _ ↦ rfl
  have hDa (w : List (Fin 2)) : E w =ᵐ[volume.restrict V] D w :=
    (ae_restrict_iff' hV.measurableSet).mpr (Eventually.of_forall (hED w))
  have hD : HasWeakJetOn 2 V u D := by
    refine ⟨rfl, fun w hw j ↦ ?_⟩
    exact ((hE.2 w hw j).mono (subset_univ V)).congr_ae_on hV.measurableSet
      (Eventually.of_forall (hED w)) (Eventually.of_forall (hED (j :: w)))
  obtain ⟨δ, hδ, hδU⟩ := hχc.exists_cthickening_subset_open hU hχU
  let r (n : ℕ) : ℝ := δ * (1 / ((n : ℝ) + 1))
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrδ (n : ℕ) : r n ≤ δ := by
    apply mul_le_of_le_one_right hδ.le
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let b (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) :=
    ⟨r n / 2, r n, by positivity, half_lt_self (hr n)⟩
  have hb : Tendsto (fun n ↦ (b n).rOut) atTop (𝓝 0) := by
    simpa only [b, r, mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  let k (n : ℕ) := planeBumpKernel (b n)
  let v (n : ℕ) := planeConvolution f (k n)
  have hfloc : LocallyIntegrable f := by
    rw [← hE.1]
    exact (hLp [] (by simp)).locallyIntegrable (by norm_num)
  have hvdiff (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    contDiff_planeConvolution hfloc (contDiff_planeBumpKernel _)
      (hasCompactSupport_planeBumpKernel _)
  have hvs (n : ℕ) : tsupport (v n) ⊆ cthickening δ (tsupport χ) :=
    (tsupport_planeConvolution_subset_cthickening (tsupport_planeBumpKernel (b n))).trans
      ((cthickening_mono (hrδ n) _).trans (cthickening_subset_of_subset δ hfs))
  have hvc (n : ℕ) : HasCompactSupport (v n) :=
    hχc.cthickening.of_isClosed_subset (isClosed_tsupport _) (hvs n)
  have hclassical (n : ℕ) (w : List (Fin 2)) :
      ContDiff ℝ ∞ (classicalComplexJet w (v n)) ∧
        HasCompactSupport (classicalComplexJet w (v n)) := by
    induction w with
    | nil => exact ⟨hvdiff n, hvc n⟩
    | cons j w ih =>
      exact ⟨contDiff_coordPartial_top j ih.1,
        ih.2.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j _)⟩
  have hcomm (n : ℕ) (w : List (Fin 2)) (hw : w.length ≤ 2) :
      classicalComplexJet w (v n) = planeConvolution (E w) (k n) := by
    induction w with
    | nil => simp only [classicalComplexJet, v, hE.1]
    | cons j w ih =>
      have hlt : w.length < 2 := Nat.lt_of_succ_le hw
      rw [classicalComplexJet, ih hlt.le]
      exact coordPartial_planeConvolution_of_weak ((hLp w hlt.le).locallyIntegrable (by norm_num))
        (hE.2 w hlt j) (contDiff_planeBumpKernel _) (hasCompactSupport_planeBumpKernel _)
  refine ⟨D, hD, fun w hw ↦ ((hLp w hw).restrict V).ae_eq (hDa w), v,
    fun n ↦ ⟨hvdiff n, hvc n, (hvs n).trans hδU⟩, ?_⟩
  intro w hw
  refine ⟨fun n ↦ ((hclassical n w).1.continuous.memLp_of_hasCompactSupport
    (μ := volume) (hclassical n w).2).restrict V, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_planeConvolution_bump_sub (hLp w hw) b hb) (fun _ ↦ bot_le)
  intro n
  change eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p) 2 (volume.restrict V) ≤ _
  rw [hcomm n w hw]
  have he : (fun p ↦ planeConvolution (E w) (k n) p - D w p) =ᵐ[volume.restrict V]
      planeConvolution (E w) (k n) - E w := by
    filter_upwards [hDa w] with p hp
    simp only [Pi.sub_apply, hp]
  rw [eLpNorm_congr_ae he]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- A bounded coefficient preserves convergence of L² product integrals.
    The proof uses the continuous L∞ multiplier and the L² inner product,
    without density or a pointwise dominating function. -/
theorem tendsto_integral_mul_conj_of_L2
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {c : α → ℂ} (hc : MemLp c ⊤ μ)
    {f g : ι → α → ℂ} {F G : α → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hflim : Tendsto (fun n ↦ eLpNorm (fun p ↦ f n p - F p) 2 μ) l (𝓝 0))
    (hglim : Tendsto (fun n ↦ eLpNorm (fun p ↦ g n p - G p) 2 μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ p, c p * f n p * (starRingEnd ℂ) (g n p) ∂μ) l
      (𝓝 (∫ p, c p * F p * (starRingEnd ℂ) (G p) ∂μ)) := by
  let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 (hc.toLp c)
  have hfl : Tendsto (fun n ↦ (hf n).toLp (f n)) l (𝓝 (hF.toLp F)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hflim
  have hgl : Tendsto (fun n ↦ (hg n).toLp (g n)) l (𝓝 (hG.toLp G)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg G hG).mpr hglim
  have hpair {a b : α → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℂ (hb.toLp b) (M (ha.toLp a)) =
        ∫ p, c p * a p * (starRingEnd ℂ) (b p) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hm : M (ha.toLp a) =ᵐ[μ] fun p ↦ (hc.toLp c) p * (ha.toLp a) p :=
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder _ _
    filter_upwards [hm, hc.coeFn_toLp, ha.coeFn_toLp, hb.coeFn_toLp] with p hp hcp hap hbp
    simp only [RCLike.inner_apply, hp, hcp, hap, hbp]
  have ht := hgl.inner (𝕜 := ℂ) (M.continuous.tendsto _ |>.comp hfl)
  simpa only [Function.comp_apply, hpair] using ht

end NoEmbeddedEigenvalues
