module

public import EulerDipoleEigenvalues.Transport.WeightedGains.QuarterFiberIntegrals
public import EulerDipoleEigenvalues.Transport.WeightedForcing.QuarterCellCover

/-!
# Logarithmic bulk mass on a small quarter strip

Blueprint: `lem:compact-cell-collar`, `lem:log-quarter-jet-mass`.

A compact collar inside the open separatrix neighbourhood permits genuine L²
restriction before coarea. The constant-Jacobian pullback and Fubini sum the
weighted jet density; finite totalized fiber integrals alone are not used.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- A positive cell collar fits inside a relatively compact open subset of any
open neighbourhood of the full lifted separatrix. -/
theorem exists_compact_cell_collar {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsep : {p | dipoleLift p = 0} ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V, IsOpen V ∧ IsCompact (closure V) ∧
      closure V ⊆ U ∧ cellSeparatrixStrip ε ⊆ V := by
  have hK : IsCompact (closure cellSquare) :=
    (isBounded_cellNeighbourhood.subset
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)).isCompact_closure
  have hc : Continuous (fun p ↦ |dipoleLift p|) := by unfold dipoleLift; fun_prop
  obtain ⟨δ, hδ, hlo⟩ := (hK.diff hU).exists_forall_le' hc.continuousOn
    (fun p hp ↦ abs_pos.mpr (fun hz ↦ hp.2 (hsep hz)))
  let K := closure cellSquare ∩ {p | |dipoleLift p| ≤ δ / 2}
  have hKc : IsCompact K := hK.inter_right (isClosed_le hc continuous_const)
  have hKU : K ⊆ U := by
    intro p hp
    by_contra hn
    have hl := hlo p ⟨hp.1, hn⟩
    have hu := hp.2
    change |dipoleLift p| ≤ δ / 2 at hu
    linarith
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hKc hU hKU
  refine ⟨δ / 2, half_pos hδ, V, hV, hVc, hVU, ?_⟩
  intro p hp
  apply hKV
  exact ⟨subset_closure hp.1, by
    change |dipoleLift p| ≤ δ / 2
    rw [abs_of_pos hp.2.1]
    exact hp.2.2.le⟩

theorem logLevelWeight_nonneg {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    0 ≤ logLevelWeight h := by
  unfold logLevelWeight
  have hl : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by
    exact (le_div_iff₀ h0).2 (by simpa using h1))
  linarith

theorem dipoleLogWeight_dipoleOrbit {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (t : ℝ) :
    dipoleLogWeight (dipoleOrbit h t) = logLevelWeight h := by
  have he : dipoleLift (dipoleOrbit h t) = 2 * h := by
    rw [dipoleLift_dipoleOrbit h0 h1]
  rw [dipoleLogWeight, he, ite_eq_right (ne_of_gt (mul_pos (by norm_num) h0)),
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) h0)]
  congr 1
  ring

/-- Integrability on a moving strip gives integrability of its actual fiber
integrals. The zero extension is jointly integrable before applying Fubini. -/
theorem integrable_quarter_fiberIntegral {b : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : IntegrableOn F (quarterOrbitStrip b)) :
    IntegrableOn (fun h ↦ ∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), F (h, t))
      (Ioo 0 b) := by
  exact (integrable_quarterStrip_sections hF).1

/-- Logarithmic local spatial L² controls the logarithmically weighted quarter
jet mass on any strip whose image is in the supplied spatial domain. -/
theorem integrable_log_quarterJetEnergy {b : ℝ} (hb : b ≤ 1)
    {V : Set (ℝ × ℝ)} (hV : MeasurableSet V)
    (hsub : cellSeparatrixStrip (2 * b) ⊆ V)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {k : ℕ} {s : ℝ}
    (hD : ∀ w : Fin k → Fin 2, MemLp (fun p ↦
      (Real.sqrt (dipoleLogWeight p) : ℂ) * D (List.ofFn w) p /
        (Real.rpow (saddleDist p) s : ℂ)) 2 (volume.restrict V)) :
    IntegrableOn (fun h ↦ logLevelWeight h * quarterJetEnergy k s D h) (Ioo 0 b) := by
  have hj (w : Fin k → Fin 2) : IntegrableOn (fun q : ℝ × ℝ ↦ logLevelWeight q.1 *
      ‖D (List.ofFn w) (dipoleOrbit q.1 q.2) /
        (Real.rpow (saddleDist (dipoleOrbit q.1 q.2)) s : ℂ)‖ ^ 2)
      (quarterOrbitStrip b) := by
    let f := fun p ↦ ‖(Real.sqrt (dipoleLogWeight p) : ℂ) * D (List.ofFn w) p /
      (Real.rpow (saddleDist p) s : ℂ)‖ ^ 2
    have hf : IntegrableOn f V := (hD w).norm.integrable_sq
    have hi : IntegrableOn (V.indicator f) cellSquare :=
      (hf.integrable_indicator hV).integrableOn
    have hp := (integrableOn_comp_orbitMap hi).mono_set
      (quarterOrbitStrip_subset_orbitDomain hb)
    apply hp.congr
    filter_upwards [ae_restrict_mem (measurableSet_quarterOrbitStrip b)] with q hq
    have hq1 : q.1 ∈ Ioo (0 : ℝ) 1 := ⟨hq.1, hq.2.1.trans_le hb⟩
    have hmem : dipoleOrbit q.1 q.2 ∈ V := hsub ⟨
      dipoleOrbit_mem_cellSquare hq1.1 hq1.2 q.2, by
        rw [dipoleLift_dipoleOrbit hq1.1 hq1.2]
        constructor <;> linarith [hq.1, hq.2.1]⟩
    rw [indicator_of_mem hmem]
    dsimp only [f]
    rw [dipoleLogWeight_dipoleOrbit hq1.1 hq1.2, mul_div_assoc, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (logLevelWeight_nonneg hq1.1 hq1.2.le)]
  have hi : IntegrableOn (fun q : ℝ × ℝ ↦ logLevelWeight q.1 * quarterJetDensity k s D q)
      (quarterOrbitStrip b) := by
    simp_rw [quarterJetDensity, Finset.mul_sum]
    exact integrable_finsetSum Finset.univ (fun w _ ↦ hj w)
  have h := integrable_quarter_fiberIntegral hi
  simpa only [integral_const_mul, quarterJetEnergy] using h

end EulerDipoleEigenvalues
