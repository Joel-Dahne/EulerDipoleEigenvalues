module

public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderParity
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakHarmonicLocal

/-!
# Smooth harmonic comparison of two specified weak Poisson solutions

The two functions and both ordered weak jets occupy the same whole disk,
including its center. Equal weak Laplacians give a smooth harmonic representative
of their difference. Axis parity is transferred a.e.; Taylor-jet consequences
are separate from this comparison.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- Same-domain weak Poisson solutions differ by a smooth harmonic representative
with their common parity (`lem:weak-poisson-harmonic-comparison`). -/
theorem weak_poisson_harmonic_comparison {ρ : ℝ} (hρ : 0 < ρ)
    {ε : Fin 2 → Bool} {u v : ℝ × ℝ → ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hu : MemSobolevOn 2 (localDisk 0 ρ) u)
    (hv : MemSobolevOn 2 (localDisk 0 ρ) v)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ) u D)
    (hE : HasWeakJetOn 2 (localDisk 0 ρ) v E)
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)),
      D [0, 0] p + D [1, 1] p = E [0, 0] p + E [1, 1] p)
    (hp : HasAxisParityOn ε (localDisk 0 ρ) u)
    (hpv : HasAxisParityOn ε (localDisk 0 ρ) v) :
    ∃ h : ℝ × ℝ → ℂ,
      IsPlaneHarmonicOn (localDisk 0 ρ) h ∧
      HasAxisParityOn ε (localDisk 0 ρ) h ∧
      ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), u p = v p + h p := by
  classical
  let U := localDisk 0 ρ
  let f : ℝ × ℝ → ℂ := fun p ↦ u p - v p
  let F := U.indicator f
  have hU : IsOpen U := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have hbound : U ⊆ Metric.closedBall 0 (2 * ρ) := by
    intro p hp
    have hn : ‖p‖ ≤ localRadius 0 p := by
      calc
        _ = ‖Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm p)‖ := by
          rw [ContinuousLinearEquiv.apply_symm_apply]
        _ ≤ ‖Complex.equivRealProdCLM.symm p‖ := Complex.equivRealProd_apply_le _
        _ = _ := by
          simp [localRadius, Complex.equivRealProdCLM_symm_apply, Complex.norm_def,
            Complex.normSq_add_mul_I]
    change dist p 0 ≤ 2 * ρ
    rw [dist_zero_right]
    change localRadius 0 p < ρ at hp
    linarith
  have hfinite : volume U < ⊤ :=
    (measure_mono hbound).trans_lt (isCompact_closedBall (0 : ℝ × ℝ) (2 * ρ)).measure_lt_top
  let : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hfinite⟩
  have hf : MemLp f 2 (volume.restrict U) := hu.memLp.sub hv.memLp
  have hi : IntegrableOn f U := hf.integrable (by norm_num)
  have hF : Integrable F := hi.integrable_indicator hU.measurableSet
  have hFu : F =ᵐ[volume.restrict U] f :=
    (ae_restrict_iff' hU.measurableSet).mpr
      (Filter.Eventually.of_forall fun p hp ↦ indicator_of_mem hp f)
  have hDdiff : HasWeakJetOn 2 U f (fun w p ↦ D w p - E w p) := hD.sub hE
  have hw : ∀ φ, IsTestFunctionOn U φ → ∫ p, F p * planeLaplacian φ p = 0 := by
    intro φ hφ
    rw [integral_mul_test_congr_ae hU.measurableSet hFu hφ.planeLaplacian.tsupport_subset,
      hDdiff.integral_laplacian_test hφ]
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hΔ] with p hp
    by_cases hpU : p ∈ U
    · have hz : (D [0, 0] p - E [0, 0] p) + (D [1, 1] p - E [1, 1] p) = 0 := by
        linear_combination hp hpU
      simp only [hz, zero_mul, Pi.zero_apply]
    · rw [image_eq_zero_of_notMem_tsupport (fun hm ↦ hpU (hφ.tsupport_subset hm)), mul_zero]
      rfl
  obtain ⟨h, hh, hΔh, hFh⟩ := weak_harmonic_smooth_rep hU hF hw
  have heq : h =ᵐ[volume.restrict U] f := hFh.trans hFu
  refine ⟨h, ⟨hh, hΔh⟩, ?_, ?_⟩
  · intro j
    have hmaps : MapsTo (axisReflect j) U U := by
      intro p hpU
      change p ∈ axisReflect j ⁻¹' localDisk 0 ρ
      rwa [axisReflect_preimage_localDisk]
    have heqR := ((measurePreserving_axisReflect j).quasiMeasurePreserving.restrict hmaps).ae heq
    filter_upwards [heq, heqR, hp j, hpv j] with p hep heRp hup hvp
    rw [heRp, hep]
    change u (axisReflect j p) - v (axisReflect j p) = paritySign (ε j) * (u p - v p)
    rw [hup, hvp, mul_sub]
  · filter_upwards [heq] with p hp
    rw [hp]
    dsimp [f]
    ring

end NoEmbeddedEigenvalues
