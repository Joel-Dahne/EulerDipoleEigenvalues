module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SobolevGluing

/-!
# Local smooth Sobolev multipliers

Blueprint: `lem:sobolev-local-multiplier`.

A compact cutoff equal to one near each point reduces local smooth multiplication
to cutoff localization. Inverse factors are used only on their nonzero open set.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- Restricting a local Sobolev function requires only domain inclusion. -/
theorem MemSobolevLocOn.mono {k : ℕ} {U V : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : MemSobolevLocOn k U f) (hVU : V ⊆ U) : MemSobolevLocOn k V f :=
  fun W hW hc hWV ↦ hf W hW hc (hWV.trans hVU)

/-- A smooth local multiplier need not have globally bounded derivatives. -/
theorem MemSobolevLocOn.mul_contDiffOn {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f g : ℝ × ℝ → ℂ} (hf : MemSobolevLocOn k U f) (hg : ContDiffOn ℝ ∞ g U) :
    MemSobolevLocOn k U (fun p ↦ g p * f p) := by
  apply memSobolevLocOn_of_locally_ae
  intro p hp
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  let η : ContDiffBump p := ⟨r / 2, r, by positivity, by linarith⟩
  have hηsub : tsupport η ⊆ U := by simpa only [η.tsupport_eq] using hsub
  let χ : ℝ × ℝ → ℂ := fun q ↦ (η q : ℂ) * g q
  have hχ : ContDiff ℝ ∞ χ := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport η
    · exact (Complex.ofRealCLM.contDiff.comp η.contDiff).contDiffAt.mul
        ((hg q (hηsub hq)).contDiffAt (hU.mem_nhds (hηsub hq)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with x hx
      simp [χ, hx]
  have hχsub : tsupport χ ⊆ U :=
    (tsupport_mul_subset_left (f := fun q ↦ (η q : ℂ)) (g := g)).trans
      ((tsupport_comp_subset Complex.ofReal_zero η).trans hηsub)
  have hχc : HasCompactSupport χ :=
    (η.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hprod := hf.cutoff k hU hχ hχc hχsub
  obtain ⟨W, hηW, hW, hpW⟩ := eventually_nhds_iff.mp η.eventuallyEq_one
  refine ⟨W ∩ U, hW.inter hU, ⟨hpW, hp⟩, fun q ↦ χ q * f q,
    hprod.memSobolevLocOn.mono (subset_univ _), ?_⟩
  apply (ae_restrict_iff' (hW.inter hU).measurableSet).mpr
  exact Filter.Eventually.of_forall fun q hq ↦ by simp [χ, hηW q hq.1]

/-- Division by a smooth nonvanishing real factor preserves local Sobolev regularity. -/
theorem MemSobolevLocOn.div_smooth {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℝ} (hf : MemSobolevLocOn k U f)
    (hg : ContDiff ℝ ∞ g) (hn : ∀ p ∈ U, g p ≠ 0) :
    MemSobolevLocOn k U (fun p ↦ f p / (g p : ℂ)) := by
  have hi : ContDiffOn ℝ ∞ (fun p ↦ (g p : ℂ)⁻¹) U :=
    (Complex.ofRealCLM.contDiff.comp hg).contDiffOn.inv (fun p hp ↦
      Complex.ofReal_ne_zero.mpr (hn p hp))
  simpa only [div_eq_mul_inv, mul_comm] using hf.mul_contDiffOn hU hi

end EulerDipoleEigenvalues
