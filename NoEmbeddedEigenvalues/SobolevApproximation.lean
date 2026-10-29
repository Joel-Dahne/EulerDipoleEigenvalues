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

open MeasureTheory Set Filter Topology

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
  sorry

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
